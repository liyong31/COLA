#!/usr/bin/env python3
"""Compare the same labelled OWL LDGBA with annotation coverage off/on."""
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
    ap.add_argument('--artifacts', type=Path, default=Path('build-local/owl-annotations'))
    ap.add_argument('--csv', type=Path, default=Path('tests/owl-annotations-results.csv'))
    ap.add_argument('--timeout', type=float, default=10)
    ap.add_argument('--negative', action='store_true')
    args = ap.parse_args()
    spec = importlib.util.spec_from_file_location('comparison', Path(__file__).with_name('compare-ltl-sizes.py'))
    comparison = importlib.util.module_from_spec(spec); spec.loader.exec_module(comparison)
    env = dict(os.environ, DYLD_LIBRARY_PATH=str(Path('build-local/src/.libs').resolve()))
    cases = [r for r in csv.DictReader(open('tests/ltl-fragment-results.csv')) if r['tool'] == 'cola']
    measured = [Path(args.driver), Path('build-local/src/.libs/libcola.0.dylib'), args.owl,
                Path('src/owl_annotations.cpp'), Path('src/owl_annotations.hpp'),
                Path('src/determinize_teba.cpp'), Path('tests/tela-elevator-driver.cpp'), Path(__file__)]
    hashes = {str(p): hashlib.sha256(p.read_bytes()).hexdigest() for p in measured}
    fields = ['case', 'sources', 'formula', 'algorithm', 'mode', 'status', 'input_states',
              'states', 'edges', 'colours', 'elapsed_ms', 'annotation-decoded',
              'annotation-certified', 'annotation-rejected', 'annotation-pair-proofs',
              'annotation-union-proofs', 'detail']

    def measure(previous, alg):
        formula = '!(' + previous['formula'] + ')' if args.negative else previous['formula']
        directory = args.artifacts / previous['case'] / alg
        directory.mkdir(parents=True, exist_ok=True)
        def run(cmd, name):
            output = directory / name
            code, elapsed = comparison.execute(cmd, output, directory / (name + '.stderr'), args.timeout, env)
            return code, output, elapsed
        code, source, _ = run([str(args.owl.resolve()), 'ltl2ldgba', '-t', alg,
            '--skip-translation-portfolio', '--state-labels', '-f', formula], 'input.hoa')
        input_states = ''
        if not code:
            status, metrics, _ = run(['autfilt', str(source), '--stats=%s'], 'input.stats')
            if status: raise RuntimeError('input metrics failed')
            input_states = int(metrics.read_text().strip())
        results = []
        for mode in ['off', 'on']:
            r = dict.fromkeys(fields, '')
            r.update({k: previous[k] for k in ['case', 'sources']})
            r.update(formula=formula, algorithm=alg, mode=mode, status='ok')
            r['input_states'] = input_states
            if code:
                r['status'] = 'frontend-timeout' if code == 'timeout' else 'frontend-error'
                results.append(r); continue
            cmd = [args.driver, str(source), formula, '--integrated', '--compact-ranks',
                   '--local-colours', '--ldgba-pruning']
            if mode == 'on': cmd += ['--owl-annotations']
            native_code, native, elapsed = run(cmd, mode + '.hoa')
            r['elapsed_ms'] = round(elapsed, 3)
            diagnostic = (directory / (mode + '.hoa.stderr')).read_text(errors='replace')
            for line in diagnostic.splitlines():
                if ': ' in line:
                    key, value = line.split(': ', 1)
                    if key in fields: r[key] = value
            if native_code:
                r['status'] = ('backend-timeout' if native_code == 'timeout' else
                    {2: 'non-elevator', 3: 'input-inequivalent', 4: 'native-inequivalent',
                     5: 'input-budget', 6: 'acceptance-capacity' if 'Too many acceptance sets' in diagnostic
                     else 'backend-error'}.get(native_code, 'driver-error'))
                r['detail'] = diagnostic[-300:].strip()
                results.append(r); continue
            status, final, _ = run(['autfilt', str(native), '--simplify-acceptance', '-D', '-G', '--low',
                '--complete', '--remove-unreachable-states'], mode + '.final.hoa')
            if status: raise RuntimeError('normalisation failed')
            status, metrics, _ = run(['autfilt', str(final), '--stats=%s,%e,%a,%d,%p'], mode + '.stats')
            if status: raise RuntimeError('metrics failed')
            states, edges, colours, det, complete = map(int, metrics.read_text().strip().split(','))
            if det != 1 or complete != 1: raise RuntimeError('not deterministic and complete')
            r.update(states=states, edges=edges, colours=colours)
            # The driver already checks source/native languages. Verify the
            # completed normalisation against that independently checked input too.
            status, _, _ = run(['autfilt', '-q', str(final), '--equivalent-to=' + str(source)], mode + '.equivalence')
            if status: r['status'] = 'normalised-inequivalent'
            results.append(r)
        return results

    rows = []
    with ThreadPoolExecutor(max_workers=2) as pool:
        futures = [pool.submit(measure, r, alg) for r in cases for alg in ['SEJK16', 'EKS20']]
        for future in as_completed(futures):
            batch = future.result(); rows += batch
            temporary = args.csv.with_suffix('.csv.tmp')
            with temporary.open('w', newline='') as out:
                w = csv.DictWriter(out, fields, lineterminator='\n'); w.writeheader()
                w.writerows(sorted(rows, key=lambda r: (r['case'], r['algorithm'], r['mode'])))
            temporary.replace(args.csv)
            print(len(rows), batch[0]['sources'], batch[0]['algorithm'],
                  [(r['mode'], r['status'], r['states'], r['annotation-certified']) for r in batch], flush=True)
    assert all(hashlib.sha256(Path(p).read_bytes()).hexdigest() == h for p, h in hashes.items()), 'measured file changed'
    manifest = {'base_commit': subprocess.check_output(['git', 'rev-parse', 'HEAD'], text=True).strip(),
        'sha256': hashes, 'timeout_seconds': args.timeout, 'workers': 2, 'negative': args.negative,
        'input_hoa_sha256': {str(p.relative_to(args.artifacts)): hashlib.sha256(p.read_bytes()).hexdigest()
                            for p in args.artifacts.glob('*/*/input.hoa')},
        'flags': '--integrated --compact-ranks --local-colours --ldgba-pruning [--owl-annotations]'}
    args.csv.with_suffix('.json').write_text(json.dumps(manifest, indent=2) + '\n')
    assert len(rows) == 908
    assert not any(r['status'] in ['input-inequivalent', 'native-inequivalent', 'normalised-inequivalent',
                                  'backend-error', 'driver-error'] for r in rows)


if __name__ == '__main__': main()
