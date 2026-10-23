#!/usr/bin/env python3
"""Measure state-preserving colour-choice rewriting on retained TELA inputs."""
import argparse
import csv
import hashlib
import importlib.util
import json
import os
from concurrent.futures import ThreadPoolExecutor, as_completed
from pathlib import Path


def read(name):
    with open('tests/' + name) as source:
        return list(csv.DictReader(source))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--csv', type=Path, default=Path('tests/colour-choice-results.csv'))
    parser.add_argument('--artifacts', type=Path, default=Path('build-local/colour-choice'))
    parser.add_argument('--weakify', action='store_true', help='also apply bounded local co-Buchi weakification')
    args = parser.parse_args()
    spec = importlib.util.spec_from_file_location('comparison', Path(__file__).with_name('compare-ltl-sizes.py'))
    comparison = importlib.util.module_from_spec(spec); spec.loader.exec_module(comparison)
    env = dict(os.environ, DYLD_LIBRARY_PATH=str(Path('build-local/src/.libs').resolve()))
    driver = 'build-local/tests/.libs/tela-elevator-driver'
    cases = []
    for r in read('ltl-fragment-results.csv'):
        if r['tool'] == 'cola':
            cases.append(dict(case=r['case'], family='literature', formula=r['formula'],
                sources=r['sources'], path=Path('build-local/slaa-comparison') / r['case'] / 'input.tela.hoa'))
    for r in read('ltl-slaa-shapes.csv'):
        cases.append(dict(case=r['case'] + '_' + r['variant'] + '_' + r['polarity'], family='shape',
            formula=r['formula'] if r['polarity'] == 'positive' else '!(' + r['formula'] + ')', sources=r['sources'],
            path=Path('build-local/slaa-shapes') / r['case'] / (r['variant'] + '_' + r['polarity']) / 'input.tela.hoa'))
    for name, formula in [('response', 'G(a -> F b)'), ('persistence', 'FG p'), ('recurrence', 'GF p')]:
        cases.append(dict(case=name, family='targeted', formula=formula, sources=name,
            path=Path('tests/colour-choice-cases') / (name + '.hoa')))
    if args.weakify:
        cases.append(dict(case='hard-cobuchi', family='targeted', formula='F(a & X b)', sources='hard-cobuchi',
                          path=Path('tests/colour-choice-cases/hard-cobuchi.hoa')))
    fields = ['case', 'family', 'sources', 'formula', 'status', 'input_states', 'input_edges', 'input_colours',
              'target_sccs', 'rewritten_sccs', 'weakified_sccs', 'added_states', 'budget_sccs', 'new_states', 'new_edges', 'new_colours',
              'old_native_status', 'old_states', 'new_unpacked_native_status', 'unpacked_states', 'unpacked_colours',
              'new_native_status', 'states', 'colours', 'elapsed_ms', 'detail']
    args.artifacts.mkdir(parents=True, exist_ok=True)

    def measure(c):
        row = dict.fromkeys(fields, '')
        row.update({k: c[k] for k in ['case', 'family', 'sources', 'formula']})
        row['status'] = 'ok'
        d = args.artifacts / c['case']; d.mkdir(exist_ok=True)

        def run(command, filename):
            out = d / filename
            rc, elapsed = comparison.execute(command, out, d / (filename + '.stderr'), 5, env)
            return rc, out, elapsed

        if not c['path'].exists() or not c['path'].stat().st_size:
            row['status'] = 'unavailable-frontend'; return row
        for path, prefix in [(c['path'], 'input')]:
            rc, output, _ = run(['autfilt', str(path), '--stats=%s,%e,%a'], prefix + '.stats')
            if rc: row['status'] = 'unavailable-frontend'; return row
            row.update(zip([prefix + '_states', prefix + '_edges', prefix + '_colours'], output.read_text().strip().split(',')))
        command = [driver, str(c['path']), c['formula'], '--preprocess-only']
        if args.weakify: command += ['--colour-elevator']
        rc, rewritten, elapsed = run(command, 'rewritten.hoa')
        row['elapsed_ms'] = round(elapsed, 3)
        if rc:
            row['status'] = 'preprocess-timeout' if rc == 'timeout' else 'preprocess-error'
            row['detail'] = (d / 'rewritten.hoa.stderr').read_text()[-500:]; return row
        diagnostic = (d / 'rewritten.hoa.stderr').read_text()
        certificates = [line for line in diagnostic.splitlines() if line.startswith('colour-scc:')]
        row['target_sccs'] = sum('target=1' in line for line in certificates)
        row['rewritten_sccs'] = sum('reason=rewritten' in line for line in certificates)
        row['weakified_sccs'] = sum('reason=co-buchi-weakified' in line for line in diagnostic.splitlines())
        row['budget_sccs'] = sum('-budget' in line for line in certificates)
        rc, metrics, _ = run(['autfilt', str(rewritten), '--stats=%s,%e,%a'], 'rewritten.stats')
        if rc: row['status'] = 'metrics-error'; return row
        row.update(zip(['new_states', 'new_edges', 'new_colours'], metrics.read_text().strip().split(',')))
        row['added_states'] = int(row['new_states']) - int(row['input_states'])
        if not args.weakify and row['added_states']: raise AssertionError('states changed')
        controls = [('old', c['path'])]
        if args.weakify: controls += [('new_unpacked', rewritten)]
        controls += [('new', rewritten)]
        for mode, source in controls:
            if mode != 'old' and not row['rewritten_sccs'] and not row['weakified_sccs']:
                row[mode + '_native_status'] = row['old_native_status']
                if mode == 'new': row.update(states=row['old_states'], colours=row.get('old_colours', ''))
                else: row.update(unpacked_states=row['old_states'], unpacked_colours=row.get('old_colours',''))
                continue
            command = [driver, str(source), c['formula'], '--integrated', '--compact-ranks']
            if mode == 'new' and args.weakify: command += ['--local-colours']
            rc, native, _ = run(command, mode + '.hoa')
            diagnostic = (d / (mode + '.hoa.stderr')).read_text()
            status = ('ok' if rc == 0 else 'timeout' if rc == 'timeout' else
                      {2: 'non-elevator', 3: 'source-inequivalent', 4: 'backend-inequivalent',
                       5: 'input-budget', 6: 'acceptance-capacity' if 'Too many acceptance sets' in diagnostic
                       else 'backend-error'}.get(rc, 'driver-error'))
            row[mode + '_native_status'] = status
            if rc: continue
            rc, output, _ = run(['autfilt', str(native), '--simplify-acceptance', '-D', '-G', '--low',
                                 '--complete', '--remove-unreachable-states', '--stats=%s,%a'], mode + '.stats')
            if rc: row['status'] = 'normalization-error'; return row
            states, colours = output.read_text().strip().split(',')
            if mode == 'old': row['old_states'] = states; row['old_colours'] = colours
            elif mode == 'new_unpacked': row.update(unpacked_states=states,unpacked_colours=colours)
            else: row['states'], row['colours'] = states, colours
        row.pop('old_colours', None)
        return row

    rows = []
    with ThreadPoolExecutor(max_workers=2) as pool:
        for future in as_completed([pool.submit(measure, c) for c in cases]):
            row = future.result(); rows.append(row)
            with args.csv.open('w', newline='') as out:
                writer = csv.DictWriter(out, fields, lineterminator='\n'); writer.writeheader()
                writer.writerows(sorted(rows, key=lambda r: (r['family'], r['case'])))
            print(len(rows), row['family'], row['sources'], row['status'], row['rewritten_sccs'],
                  row['old_native_status'], row['new_native_status'], flush=True)
    paths = [Path(driver), Path('build-local/src/.libs/libcola.0.dylib'), Path(__file__),
             Path('src/colour_choice.cpp'), Path('src/colour_choice.hpp'),
             Path('src/cobuchi_weak.cpp'), Path('src/cobuchi_weak.hpp'),
             Path('src/determinize_teba.cpp'), Path('src/cola.hpp'), Path('tests/tela-elevator-driver.cpp')]
    args.csv.with_suffix('.json').write_text(json.dumps({'sha256':
        {str(p): hashlib.sha256(p.read_bytes()).hexdigest() for p in paths},
        'timeout_seconds_per_process': 5, 'workers': 2,
        'native_options': '--integrated --compact-ranks throughout; changed new weakification outputs also use --local-colours',
        'weakification': args.weakify,
        'unchanged_inputs': 'new native result reuses old result when no SCC was rewritten'}, indent=2) + '\n')
    assert len(rows) == len(cases)
    assert not any('inequivalent' in r[k] or 'error' in r[k] for r in rows
                   for k in ['status', 'old_native_status', 'new_unpacked_native_status', 'new_native_status'])


if __name__ == '__main__':
    main()
