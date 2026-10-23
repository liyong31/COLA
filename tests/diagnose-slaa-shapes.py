#!/usr/bin/env python3
"""Ablate SLAA construction before COLA's checked TELA determinisation.

Measure both polarities on LTL3TELA's remaining wins over integrated COLA.
Every admitted deterministic result is checked against the positive reference.
General Spot determinisation is a separately labelled diagnostic for hard TELA.
"""
import argparse
from concurrent.futures import ThreadPoolExecutor, as_completed
import csv
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import subprocess

VARIANTS = {
    'baseline': [], 'u_min_na': ['-F1'], 'u_no_alternating_loop': ['-F3'],
    'no_merging': ['-F0', '-G0', '-c0'], 'no_g_merge': ['-G0'],
    'g_single': ['-G1'], 'no_reduction': ['-c0'],
    'no_dominance': ['-d0'], 'basic_dominance': ['-d1'],
    'single_x': ['-X1'], 'merge_disjunction': ['-O1'],
    'single_initial': ['-i1'], 'tgba_acceptance': ['-t1'],
    'no_simplification': ['-s0'], 'no_na_equivalence': ['-e0'],
}


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--tool', type=Path, default=Path('build-local/external/ltl3tela-master/ltl3tela'))
    ap.add_argument('--driver', default='build-local/tests/.libs/tela-elevator-driver')
    ap.add_argument('--artifacts', type=Path, default=Path('build-local/slaa-shapes'))
    ap.add_argument('--csv', type=Path, default=Path('tests/ltl-slaa-shapes.csv'))
    ap.add_argument('--timeout', type=float, default=5)
    args = ap.parse_args()
    spec = importlib.util.spec_from_file_location('comparison', Path(__file__).with_name('compare-ltl-sizes.py'))
    comparison = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(comparison)
    env = dict(os.environ, DYLD_LIBRARY_PATH=str(Path('build-local/src/.libs').resolve()))
    with open('tests/ltl-size-results.csv') as source:
        originals = {}
        for row in csv.DictReader(source): originals.setdefault(row['case'], {})[row['tool']] = row
    with open('tests/ltl-slaa-results.csv') as source:
        positive = {r['case']: r for r in csv.DictReader(source) if r['tool'] == 'cola_slaa'}
    cases = [r for c, r in positive.items() if originals[c]['ltl3tela']['status'] == 'ok'
             and int(originals[c]['ltl3tela']['states']) < int(r['states'])]
    assert len(cases) == 10
    fields = ['case', 'sources', 'formula', 'polarity', 'variant', 'flags', 'status',
        'slaa_states', 'slaa_edges', 'slaa_colours', 'tela_states', 'tela_edges', 'tela_colours',
        'tela_deterministic', 'sccs', 'weak_sccs', 'deterministic_sccs', 'hard_sccs',
        'states', 'edges', 'colours', 'generic_states', 'generic_status',
        'cola_states', 'ltl3tela_states', 'elapsed_ms', 'detail']
    args.artifacts.mkdir(parents=True, exist_ok=True)

    def measure(previous, variant, extra, polarity):
        directory = args.artifacts / previous['case'] / (variant + '_' + polarity)
        directory.mkdir(parents=True, exist_ok=True)
        f = previous['formula'] if polarity == 'positive' else '!(' + previous['formula'] + ')'
        flags = ['-D0', '-b0', '-n0', '-l0', '-t0'] + extra
        row = dict.fromkeys(fields, '')
        row.update({k: previous[k] for k in ['case', 'sources', 'formula']})
        row.update(polarity=polarity, variant=variant, flags=' '.join(flags), status='ok',
                   cola_states=previous['states'], ltl3tela_states=originals[previous['case']]['ltl3tela']['states'])
        reference = Path('build-local/owl-comparison') / row['case'] / 'spot.hoa'

        def run(command, name, timeout=args.timeout):
            output = directory / name
            code, elapsed = comparison.execute(command, output, directory / (name + '.stderr'), timeout, env)
            return code, output, elapsed

        def stats(path, name, opts=()):
            code, out, _ = run(['autfilt', str(path), *opts, '--stats=%s,%e,%a,%d'], name)
            if code: return None
            return list(map(int, out.read_text().strip().split(',')))

        def positive_result(path, name):
            # Same Low generic deterministic normalization as the integrated
            # route, then complete before optionally flipping acceptance.
            code, final, _ = run(['autfilt', str(path), '-D', '-G', '--low',
                '--complete', '--remove-unreachable-states'], name + '.complete.hoa')
            if code: return None
            if polarity == 'negative':
                code, final, _ = run(['autfilt', str(final), '--complement-acceptance'], name + '.positive.hoa')
                if code: return None
            metrics = stats(final, name + '.stats')
            if not metrics or metrics[3] != 1: return None
            code, _, _ = run(['autfilt', '-q', str(final), '--equivalent-to=' + str(reference)], name + '.equivalent')
            return metrics if code == 0 else None

        code, slaa, _ = run([str(args.tool.resolve()), *flags, '-p1', '-f', f], 'input.slaa.hoa')
        if code == 0:
            metrics = stats(slaa, 'slaa.stats')
            if metrics: row.update(zip(['slaa_states', 'slaa_edges', 'slaa_colours'], metrics[:3]))
        code, tela, elapsed = run([str(args.tool.resolve()), *flags, '-p2', '-f', f], 'input.tela.hoa')
        row['elapsed_ms'] = round(elapsed, 3)
        if code:
            row.update(status='frontend-timeout' if code == 'timeout' else 'frontend-error', detail=str(code))
            return row
        metrics = stats(tela, 'tela.stats')
        if not metrics:
            row['status'] = 'input-metrics-failed'
            return row
        row.update(zip(['tela_states', 'tela_edges', 'tela_colours', 'tela_deterministic'], metrics))
        code, result, _ = run([args.driver, str(tela), f, '--integrated'], 'native.hoa')
        diagnostic = (directory / 'native.hoa.stderr').read_text(errors='replace')
        for key in ['sccs', 'weak-sccs', 'deterministic-sccs', 'hard-sccs']:
            for line in diagnostic.splitlines():
                if line.startswith('input-' + key + ': '): row[key.replace('-', '_')] = int(line.split(': ')[1])
        row['status'] = ('timeout' if code == 'timeout' else
            {0: 'ok', 2: 'non-elevator', 3: 'frontend-inequivalent', 4: 'backend-inequivalent',
             5: 'input-budget', 6: 'backend-error'}.get(code, 'driver-error'))
        if code == 0:
            metrics = positive_result(result, 'native')
            if metrics: row.update(zip(['states', 'edges', 'colours'], metrics[:3]))
            else: row['status'] = 'validation-failed'
        elif code == 2:
            # Diagnostic only: never conflate general determinisation with
            # an admitted elevator candidate or a SLAA manipulation.
            generic_code, general, _ = run(['autfilt', str(tela), '-D', '-G', '--high'], 'generic.hoa')
            row['generic_status'] = 'timeout' if generic_code == 'timeout' else 'error' if generic_code else 'ok'
            if generic_code == 0:
                metrics = positive_result(general, 'generic')
                if metrics: row['generic_states'] = metrics[0]
                else: row['generic_status'] = 'validation-failed'
        if row['status'] != 'ok': row['detail'] = diagnostic[-300:].strip()
        return row

    rows = []
    jobs = [(r, name, flags, p) for r in cases for name, flags in VARIANTS.items()
            for p in ['positive', 'negative']]
    with ThreadPoolExecutor(max_workers=2) as executor:
        futures = [executor.submit(measure, *job) for job in jobs]
        for future in as_completed(futures):
            row = future.result()
            rows.append(row)
            temporary = args.csv.with_suffix('.csv.tmp')
            with temporary.open('w', newline='') as out:
                writer = csv.DictWriter(out, fields, lineterminator='\n')
                writer.writeheader()
                writer.writerows(sorted(rows, key=lambda r: (r['case'], r['variant'], r['polarity'])))
            temporary.replace(args.csv)
            print(len(rows), row['sources'], row['polarity'], row['variant'],
                  row['status'], row['states'], 'generic', row['generic_states'], flush=True)
    paths = [args.tool, Path(args.driver), Path('build-local/src/.libs/libcola.0.dylib'), Path(__file__),
             Path('tests/tela-elevator-driver.cpp'), Path('src/determinize_teba.cpp'), Path('src/cola.cpp')]
    manifest = {'base_commit': subprocess.check_output(['git', 'rev-parse', 'HEAD'], text=True).strip(),
        'timeout_seconds_per_process': args.timeout, 'workers': 2, 'variants': VARIANTS,
        'sha256': {str(p): hashlib.sha256(p.read_bytes()).hexdigest() for p in paths},
        'cases': [r['case'] for r in cases], 'raw_input_limit': 256,
        'native_driver_options': '--integrated (SCC pruning enabled as in the translator)',
        'normalization': 'Generic, Deterministic, Low; complete before acceptance complement',
        'generic_diagnostic': 'Non-elevator TELA -> Spot Generic Deterministic High; separate from native route'}
    args.csv.with_suffix('.json').write_text(json.dumps(manifest, indent=2) + '\n')
    assert len(rows) == 300
    assert not any(r['status'] in ['frontend-inequivalent', 'backend-inequivalent', 'validation-failed']
                   or r['generic_status'] == 'validation-failed' for r in rows)


if __name__ == '__main__':
    main()
