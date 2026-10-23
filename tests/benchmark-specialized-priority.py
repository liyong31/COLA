#!/usr/bin/env python3
"""Measure specialized-first routing on the retained OWL literature corpus."""
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
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--artifacts', type=Path, default=Path('build-local/specialized-priority'))
    parser.add_argument('--csv', type=Path, default=Path('tests/specialized-priority-results.csv'))
    parser.add_argument('--timeout', type=float, default=30)
    args = parser.parse_args()
    spec = importlib.util.spec_from_file_location('comparison', Path(__file__).with_name('compare-ltl-sizes.py'))
    comparison = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(comparison)
    binary = Path('build-local/.libs/ltl2dela')
    slaa = Path('build-local/external/ltl3tela-master/ltl3tela')
    owl = Path('build-local/external/owl-21.0/bin/owl')
    variants = {'specialized': [], 'slaa_residual': ['--slaa-tool=' + str(slaa.resolve()), '--colour-elevator'],
                'ldgba_residual': ['--ldgba-tool=' + str(owl.resolve()), '--ldgba-construction=SEJK16',
                                   '--ldgba-pruning', '--ldgba-cross-scc']}
    common = ['--finite-witness', '--stats']
    measured = [binary, Path('build-local/src/.libs/libcola.0.dylib'), Path('src/ltl2dela.cpp'),
                slaa, owl, Path(__file__)]
    hashes = {str(p): hashlib.sha256(p.read_bytes()).hexdigest() for p in measured}
    env = dict(os.environ, DYLD_LIBRARY_PATH=str(Path('build-local/src/.libs').resolve()))
    cases = [r for r in csv.DictReader(open('tests/ltl-fragment-results.csv')) if r['tool'] == 'cola']
    keys = ['SLAA attempts', 'SLAA components', 'LDGBA attempts', 'LDGBA components',
            'DBA components', 'direct formula components', 'finite-witness monitors',
            'X-advice components', 'Master profile bundles', 'acceptance-limit fallbacks']
    fields = ['case', 'sources', 'formula', 'variant', 'status', 'states', 'edges', 'colours', 'elapsed_ms', *keys, 'detail']

    def measure(case, variant, flags):
        row = dict.fromkeys(fields, '')
        row.update({k: case[k] for k in ['case', 'sources', 'formula']})
        row.update(variant=variant, status='ok')
        directory = args.artifacts / case['case'] / variant
        directory.mkdir(parents=True, exist_ok=True)

        def run(command, name):
            code, elapsed = comparison.execute(command, directory / name,
                directory / (name + '.stderr'), args.timeout, env)
            return code, directory / name, elapsed

        code, source, elapsed = run([str(binary.resolve()), *common, *flags, '-f', case['formula']], 'output.hoa')
        row['elapsed_ms'] = round(elapsed, 3)
        diagnostics = (directory / 'output.hoa.stderr').read_text(errors='replace')
        for line in diagnostics.splitlines():
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
        reference = Path('build-local/owl-comparison') / case['case'] / (case['reference_tool'] + '.hoa')
        code, _, _ = run(['autfilt', '-q', str(final), '--equivalent-to=' + str(reference)], 'equivalence')
        if code:
            row.update(status='equivalence-timeout' if code == 'timeout' else 'inequivalent', detail=str(code))
        return row

    rows = []
    with ThreadPoolExecutor(max_workers=2) as pool:
        futures = [pool.submit(measure, case, variant, flags) for case in cases for variant, flags in variants.items()]
        for future in as_completed(futures):
            row = future.result()
            rows.append(row)
            temporary = args.csv.with_suffix('.tmp')
            with temporary.open('w', newline='') as output:
                writer = csv.DictWriter(output, fields, lineterminator='\n')
                writer.writeheader()
                writer.writerows(sorted(rows, key=lambda r: (r['case'], r['variant'])))
            temporary.replace(args.csv)
            print(len(rows), row['sources'], row['variant'], row['status'], row['states'], flush=True)
    assert all(hashlib.sha256(Path(p).read_bytes()).hexdigest() == h for p, h in hashes.items())
    args.csv.with_suffix('.json').write_text(json.dumps({
        'base_commit': subprocess.check_output(['git', 'rev-parse', 'HEAD'], text=True).strip(),
        'sha256': hashes, 'variants': variants, 'common': common,
        'timeout_seconds': args.timeout, 'workers': 2}, indent=2) + '\n')
    assert len(rows) == 3 * len(cases)
    assert not any(r['status'] == 'inequivalent' for r in rows)


if __name__ == '__main__':
    main()
