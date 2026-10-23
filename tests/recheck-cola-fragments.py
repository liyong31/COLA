#!/usr/bin/env python3
"""Recheck both COLA modes against the retained OWL/Spot reference artifacts."""
import argparse
import csv
import importlib.util
import os
from pathlib import Path


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--ltld', default='build-local/.libs/ltl2dela')
    ap.add_argument('--library', type=Path, default=Path('build-local/src/.libs'))
    ap.add_argument('--reference-artifacts', type=Path, default=Path('build-local/owl-comparison'))
    ap.add_argument('--artifacts', type=Path, default=Path('build-local/fragment-comparison'))
    ap.add_argument('--csv', type=Path, default=Path('tests/ltl-fragment-results.csv'))
    ap.add_argument('--timeout', type=float, default=30)
    args = ap.parse_args()
    spec = importlib.util.spec_from_file_location('comparison',
                                                Path(__file__).with_name('compare-ltl-sizes.py'))
    comparison = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(comparison)
    env = dict(os.environ, DYLD_LIBRARY_PATH=str(args.library.resolve()))
    old = {}
    for row in csv.DictReader(open('tests/ltl-size-results.csv')):
        old.setdefault(row['case'], {})[row['tool']] = row
    route_keys = {'boolean_gf_fg': 'Boolean GF/FG components',
                  'specialized_gf': 'specialized GF components',
                  'specialized_fg': 'specialized FG components',
                  'dba': 'DBA components', 'dba_fallbacks': 'DBA attempts without result',
                  'guarded': 'guarded conjunctions retained',
                  'master_splits': 'Master profile splits'}
    fields = comparison.FIELDS + ['old_status', 'old_states', 'reference_tool'] + list(route_keys)
    rows = []
    args.artifacts.mkdir(parents=True, exist_ok=True)
    for index, (case, group) in enumerate(old.items(), 1):
        directory = args.artifacts / case
        directory.mkdir(exist_ok=True)
        reference_tool = 'spot' if group['spot']['status'] == 'reference' else 'delag'
        for mode, flags in [('cola', []), ('cola_reset', ['--finite-witness'])]:
            previous = group[mode]
            row = dict.fromkeys(fields, '')
            row.update(case=case, sources=previous['sources'], formula=previous['formula'],
                       tool=mode, old_status=previous['status'], old_states=previous['states'],
                       reference_tool=reference_tool)
            output, stderr = directory / (mode + '.hoa'), directory / (mode + '.stderr')
            code, elapsed = comparison.execute([args.ltld, '--stats'] + flags +
                                               ['-f', row['formula']], output, stderr,
                                               args.timeout, env)
            row['elapsed_ms'] = round(elapsed, 3)
            diagnostic = stderr.read_text(errors='replace')
            for column, key in dict(route_keys, witness_monitors='finite-witness monitors',
                                    witness_aborts='finite-witness aborts').items():
                for line in diagnostic.splitlines():
                    if key + ': ' in line:
                        row[column] = int(line.split(key + ': ')[1])
            row['status'] = 'timeout' if code == 'timeout' else 'error' if code else 'translated'
            if code == 0:
                for complete in [False, True]:
                    metrics = directory / (mode + ('.complete' if complete else '.raw') + '.stats')
                    code, _ = comparison.execute(['autfilt', str(output)] +
                        (['--complete', '--remove-unreachable-states'] if complete else []) +
                        ['--stats=%s,%e,%a,%d,%p'], metrics, metrics.with_suffix('.stderr'),
                        args.timeout, env)
                    if code:
                        row['status'] = 'metrics-failed'
                        break
                    states, edges, colours, det, total = map(int, metrics.read_text().strip().split(','))
                    if not det:
                        row['status'] = 'nondeterministic'
                        break
                    if complete:
                        assert total == 1
                        row.update(states=states, edges=edges, colours=colours)
                    else:
                        row.update(raw_states=states, raw_edges=edges, raw_colours=colours,
                                   raw_complete=total)
                if row['status'] == 'translated':
                    code, _ = comparison.execute(['autfilt', '-q', str(output),
                        '--equivalent-to=' + str(args.reference_artifacts / case /
                                                (reference_tool + '.hoa'))],
                        directory / (mode + '.equivalence.stdout'),
                        directory / (mode + '.equivalence.stderr'), args.timeout, env)
                    row['status'] = 'ok' if code == 0 else 'equivalence-failed'
            if row['status'] != 'ok': row['detail'] = diagnostic[-400:].rstrip()
            rows.append(row)
            temporary = args.csv.with_suffix('.csv.tmp')
            with temporary.open('w', newline='') as out:
                writer = csv.DictWriter(out, fields, lineterminator='\n')
                writer.writeheader()
                writer.writerows(rows)
            temporary.replace(args.csv)
        print(index, previous['sources'], [(r['tool'], r['status'], r['states'])
                                          for r in rows[-2:]], flush=True)
    assert len(rows) == 454 and all(r['status'] == 'ok' for r in rows)
    print('All 454 updated COLA outputs passed determinism and reference equivalence.')


if __name__ == '__main__':
    main()
