#!/usr/bin/env python3
"""Compare OWL LDGBA/LDBA -> COLA ELA with the OWL TACAS DPA route."""
import argparse
from concurrent.futures import ThreadPoolExecutor, as_completed
import csv
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import subprocess


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--owl', type=Path, default=Path('build-local/external/owl-21.0/bin/owl'))
    ap.add_argument('--driver', default='build-local/tests/.libs/tela-elevator-driver')
    ap.add_argument('--artifacts', type=Path, default=Path('build-local/ldgba-comparison'))
    ap.add_argument('--csv', type=Path, default=Path('tests/ltl-ldgba-raw-results.csv'))
    ap.add_argument('--timeout', type=float, default=5)
    ap.add_argument('--reuse-inputs', type=Path,
                    help='replay retained frontend HOA from this artifact directory')
    ap.add_argument('--local-colours', action='store_true')
    ap.add_argument('--ldgba-pruning', action='store_true')
    ap.add_argument('--optimization-probes', action='store_true',
                    help='six targeted formulas: simplification, portfolio and rank allocation')
    args = ap.parse_args()
    measured_binaries = [Path(args.driver), Path('build-local/src/.libs/libcola.0.dylib')]
    binary_hashes = {str(p): hashlib.sha256(p.read_bytes()).hexdigest() for p in measured_binaries}
    spec = importlib.util.spec_from_file_location('comparison', Path(__file__).with_name('compare-ltl-sizes.py'))
    comparison = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(comparison)
    env = dict(os.environ, DYLD_LIBRARY_PATH=str(Path('build-local/src/.libs').resolve()))
    with open('tests/ltl-fragment-results.csv') as source:
        cases = [r for r in csv.DictReader(source) if r['tool'] == 'cola']
    variants = {alg.lower() + '_' + kind: [command, '-t', alg, '--skip-translation-portfolio']
                for alg in ['SEJK16', 'EKS20'] for kind, command in [('gba', 'ltl2ldgba'), ('ba', 'ltl2ldba')]}
    variants['owl_tacas_dpa'] = ['ltl2dpa', '-t', 'SEJK16_EKRS17']
    if args.optimization_probes:
        selected = {'DwyerAC98.ltl:45', 'DwyerAC98.ltl:46', 'DwyerAC98.ltl:50',
                    'DwyerAC98.ltl:55', 'Parametrised.ltl:15', 'SomenziB00.ltl:21'}
        cases = [r for r in cases if r['sources'] in selected]
        assert len(cases) == 6
        variants = {}
        for alg in ['SEJK16', 'EKS20']:
            base = ['ltl2ldgba', '-t', alg, '--skip-translation-portfolio']
            for suffix, flags in [('gba', base),
                    ('no_formula_simplifier', base + ['--skip-formula-simplifier']),
                    ('no_acceptance_simplifier', base + ['--skip-acceptance-simplifier']),
                    ('portfolio', base[:-1]), ('full_ranks', base)]:
                variants[alg.lower() + '_' + suffix] = flags
    fields = ['case', 'sources', 'formula', 'variant', 'status', 'input_states', 'input_edges',
              'input_colours', 'input_deterministic', 'input_equivalent', 'backend_attempted',
              'states', 'edges', 'colours', 'frontend_ms', 'backend_ms', 'detail']
    args.artifacts.mkdir(parents=True, exist_ok=True)

    def measure(previous, name, flags):
        directory = args.artifacts / previous['case'] / name
        directory.mkdir(parents=True, exist_ok=True)
        row = dict.fromkeys(fields, '')
        row.update({k: previous[k] for k in ['case', 'sources', 'formula']})
        row.update(variant=name, status='ok')

        def run(command, filename):
            output = directory / filename
            code, elapsed = comparison.execute(command, output,
                directory / (filename + '.stderr'), args.timeout, env)
            return code, output, elapsed

        if args.reuse_inputs:
            source = directory / 'input.hoa'
            retained = args.reuse_inputs / previous['case'] / name / 'input.hoa'
            if not retained.exists() or not retained.read_text().startswith('HOA:'):
                row.update(status='retained-input-unavailable')
                return row
            source.write_bytes(retained.read_bytes())
            code, elapsed = 0, 0
        else:
            code, source, elapsed = run([str(args.owl.resolve()), *flags, '-f', row['formula']], 'input.hoa')
        row['frontend_ms'] = round(elapsed, 3)
        if code:
            row.update(status='frontend-timeout' if code == 'timeout' else 'frontend-error', detail=str(code))
            return row
        code, stats, _ = run(['autfilt', str(source), '--stats=%s,%e,%a,%d'], 'input.stats')
        if code:
            row['status'] = 'input-metrics-failed'
            return row
        row.update(zip(['input_states', 'input_edges', 'input_colours', 'input_deterministic'],
                       stats.read_text().strip().split(',')))
        output = source
        if name != 'owl_tacas_dpa':
            row['backend_attempted'] = int(row['input_deterministic'] == '0')
            command = [args.driver, str(source), row['formula'], '--integrated']
            if not name.endswith('_full_ranks'): command += ['--compact-ranks']
            if args.local_colours: command += ['--local-colours']
            if args.ldgba_pruning: command += ['--ldgba-pruning']
            code, output, elapsed = run(command, 'native.hoa')
            row['backend_ms'] = round(elapsed, 3)
            diagnostic = (directory / 'native.hoa.stderr').read_text(errors='replace')
            row['input_equivalent'] = int('input-equivalent: 1' in diagnostic)
            if code:
                row['status'] = ('backend-timeout' if code == 'timeout' else
                    {2: 'non-elevator', 3: 'frontend-inequivalent', 4: 'backend-inequivalent',
                     5: 'input-budget', 6: 'acceptance-capacity' if 'Too many acceptance sets' in diagnostic
                     else 'backend-error'}.get(code, 'driver-error'))
                row['detail'] = diagnostic[-300:].strip()
                return row
        code, final, _ = run(['autfilt', str(output), '--simplify-acceptance', '-D', '-G', '--low',
                             '--complete', '--remove-unreachable-states'], 'final.hoa')
        if code:
            row['status'] = 'normalization-failed'
            return row
        code, stats, _ = run(['autfilt', str(final), '--stats=%s,%e,%a,%d,%p'], 'final.stats')
        if code:
            row['status'] = 'output-metrics-failed'
            return row
        states, edges, colours, deterministic, total = map(int, stats.read_text().strip().split(','))
        if deterministic != 1 or total != 1:
            row['status'] = 'not-deterministic-complete'
            return row
        row.update(states=states, edges=edges, colours=colours)
        reference = Path('build-local/owl-comparison') / row['case'] / (previous['reference_tool'] + '.hoa')
        code, _, _ = run(['autfilt', '-q', str(final), '--equivalent-to=' + str(reference)], 'equivalence.stdout')
        if code: row['status'] = 'reference-timeout' if code == 'timeout' else 'reference-inequivalent'
        return row

    rows = []
    with ThreadPoolExecutor(max_workers=2) as executor:
        futures = [executor.submit(measure, r, name, flags) for r in cases for name, flags in variants.items()]
        for future in as_completed(futures):
            r = future.result()
            rows.append(r)
            temporary = args.csv.with_suffix('.csv.tmp')
            with temporary.open('w', newline='') as out:
                writer = csv.DictWriter(out, fields, lineterminator='\n')
                writer.writeheader()
                writer.writerows(sorted(rows, key=lambda r: (r['case'], r['variant'])))
            temporary.replace(args.csv)
            print(len(rows), r['sources'], r['variant'], r['status'], r['states'], flush=True)
    paths = [args.owl, Path(args.driver), Path('build-local/src/.libs/libcola.0.dylib'),
        Path('tests/tela-elevator-driver.cpp'), Path('src/determinize_teba.cpp'), Path('src/cola.cpp'), Path(__file__)]
    manifest = {'base_commit': subprocess.check_output(['git', 'rev-parse', 'HEAD'], text=True).strip(),
        'variants': variants, 'timeout_seconds_per_process': args.timeout, 'workers': 2,
        'optimization_probes': args.optimization_probes,
        'reuse_inputs': str(args.reuse_inputs) if args.reuse_inputs else None,
        'local_colours': args.local_colours, 'ldgba_pruning': args.ldgba_pruning,
        'native_options': '--integrated --compact-ranks; 256 input-state limit',
        'sha256': {str(p): hashlib.sha256(p.read_bytes()).hexdigest() for p in paths},
        'environment': 'tests/ltl-fragment-environment.json'}
    assert all(manifest['sha256'][p] == h for p, h in binary_hashes.items()), \
        'binary changed during campaign; discard measurements and rerun after build'
    manifest['input_hoa_sha256'] = {
        str(p.relative_to(args.artifacts)): hashlib.sha256(p.read_bytes()).hexdigest()
        for p in args.artifacts.glob('*/*/input.hoa') if p.read_bytes().startswith(b'HOA:')}
    args.csv.with_suffix('.json').write_text(json.dumps(manifest, indent=2) + '\n')
    assert len(rows) == len(cases) * len(variants)
    assert not any('inequivalent' in r['status'] or r['status'] in
                   ['driver-error', 'backend-error', 'not-deterministic-complete'] for r in rows)


if __name__ == '__main__':
    main()
