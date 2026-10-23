#!/usr/bin/env python3
"""Paired corpus experiment: previous portfolios versus specialized-first routing."""
import argparse
from concurrent.futures import ThreadPoolExecutor, as_completed
import csv
import hashlib
import importlib.util
import json
import os
from pathlib import Path


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--timeout', type=float, default=30)
    parser.add_argument('--csv', type=Path, default=Path('tests/routing-effect-results.csv'))
    parser.add_argument('--artifacts', type=Path, default=Path('build-local/routing-effect'))
    args = parser.parse_args()
    spec = importlib.util.spec_from_file_location('comparison', Path(__file__).with_name('compare-ltl-sizes.py'))
    comparison = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(comparison)
    build = Path('build-local/routing-ablation').resolve()
    slaa = Path('build-local/external/ltl3tela-master/ltl3tela').resolve()
    owl = Path('build-local/external/owl-21.0/bin/owl').resolve()
    portfolio = ['--slaa-tool=' + str(slaa), '--slaa-portfolio', '--colour-elevator',
        '--ldgba-tool=' + str(owl), '--ldgba-pruning', '--ldgba-portfolio', '--ldgba-cross-scc']
    configs = {'default': [], 'finite_witness': ['--finite-witness'],
               'portfolio': portfolio, 'finite_witness_portfolio': ['--finite-witness', *portfolio]}
    measured = [build / 'build.json', slaa, owl, Path(__file__), Path('tests/compare-ltl-sizes.py')]
    for route in ['before', 'after']:
        measured += [build / route / 'ltl2dela', build / route / 'libcola.0.dylib']
    hashes = {str(p): hashlib.sha256(p.read_bytes()).hexdigest() for p in measured}
    cases = [r for r in csv.DictReader(open('tests/ltl-fragment-results.csv')) if r['tool'] == 'cola']
    keys = ['SLAA attempts', 'SLAA components', 'SLAA validation failures', 'LDGBA attempts',
            'LDGBA components', 'LDGBA validation failures', 'DBA components', 'direct formula components',
            'finite-witness monitors', 'X-advice components', 'Master profile bundles', 'acceptance-limit fallbacks']
    fields = ['case', 'sources', 'formula', 'config', 'route', 'status', 'states', 'edges', 'colours',
              'normalized_states', 'elapsed_ms', *keys, 'detail']

    def measure(case, config, route):
        row = dict.fromkeys(fields, '')
        row.update({k: case[k] for k in ['case', 'sources', 'formula']})
        row.update(config=config, route=route, status='ok')
        directory = args.artifacts / case['case'] / config / route
        directory.mkdir(parents=True, exist_ok=True)
        env = dict(os.environ, DYLD_LIBRARY_PATH=str(build / route))

        def run(command, name):
            code, elapsed = comparison.execute(command, directory / name,
                directory / (name + '.stderr'), args.timeout, env)
            return code, directory / name, elapsed

        code, source, elapsed = run([str(build / route / 'ltl2dela'), '--stats', *configs[config],
            '-f', case['formula']], 'output.hoa')
        row['elapsed_ms'] = round(elapsed, 3)
        diagnostic = (directory / 'output.hoa.stderr').read_text(errors='replace')
        for line in diagnostic.splitlines():
            key, separator, value = line.strip().partition(': ')
            if separator and key in keys:
                row[key] = int(value)
        if code:
            row.update(status='translation-timeout' if code == 'timeout' else 'translation-error', detail=str(code))
            return row
        code, final, _ = run(['autfilt', str(source), '--complete', '--remove-unreachable-states'], 'complete.hoa')
        if code:
            row.update(status='completion-error', detail=str(code))
            return row
        code, metrics, _ = run(['autfilt', str(final), '--stats=%s,%e,%a,%d,%p'], 'metrics')
        if code:
            raise RuntimeError('metrics failed')
        states, edges, colours, deterministic, complete = map(int, metrics.read_text().strip().split(','))
        assert deterministic == complete == 1
        row.update(states=states, edges=edges, colours=colours)
        code, normalized, _ = run(['autfilt', str(source), '--simplify-acceptance', '-D', '-G', '--low',
            '--complete', '--remove-unreachable-states', '--stats=%s'], 'normalized.metrics')
        if code:
            row.update(status='normalization-timeout' if code == 'timeout' else 'normalization-error', detail=str(code))
            return row
        row['normalized_states'] = int(normalized.read_text().strip())
        reference = Path('build-local/owl-comparison') / case['case'] / (case['reference_tool'] + '.hoa')
        code, _, _ = run(['autfilt', '-q', str(final), '--equivalent-to=' + str(reference)], 'equivalence')
        if code:
            row.update(status='equivalence-timeout' if code == 'timeout' else 'inequivalent', detail=str(code))
        return row

    rows = []
    with ThreadPoolExecutor(max_workers=2) as pool:
        futures = [pool.submit(measure, case, config, route)
            for case in cases for config in configs for route in ['before', 'after']]
        for future in as_completed(futures):
            row = future.result()
            rows.append(row)
            temporary = args.csv.with_suffix('.tmp')
            with temporary.open('w', newline='') as output:
                writer = csv.DictWriter(output, fields, lineterminator='\n')
                writer.writeheader()
                writer.writerows(sorted(rows, key=lambda r: (r['case'], r['config'], r['route'])))
            temporary.replace(args.csv)
            print(len(rows), row['sources'], row['config'], row['route'], row['status'], row['states'], flush=True)
    assert all(hashlib.sha256(Path(p).read_bytes()).hexdigest() == h for p, h in hashes.items())
    args.csv.with_suffix('.json').write_text(json.dumps({'build': json.loads((build / 'build.json').read_text()),
        'configs': configs, 'sha256': hashes, 'timeout_seconds': args.timeout, 'workers': 2,
        'primary_size': 'Complete reachable output states, without further minimization.',
        'secondary_size': 'Identical Spot low generic deterministic normalization followed by completion.',
        'timing_scope': 'Concurrent single translation process wall time; descriptive, not a runtime ranking.'}, indent=2) + '\n')
    assert len(rows) == 8 * len(cases)
    assert not any(r['status'] == 'inequivalent' for r in rows)


if __name__ == '__main__':
    main()
