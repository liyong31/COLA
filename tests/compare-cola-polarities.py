#!/usr/bin/env python3
"""Translate negated OWL formulas, complete, then flip acceptance back.

Reuse verified positive COLA and external-tool measurements, never re-minimize
the complemented graph. Retain every intermediate HOA and checkpoint each case.
"""
import argparse
from collections import Counter
import csv
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import subprocess


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--ltld', default='build-local/.libs/ltl2dela')
    ap.add_argument('--library', type=Path, default=Path('build-local/src/.libs'))
    ap.add_argument('--artifacts', type=Path, default=Path('build-local/polarity-comparison'))
    ap.add_argument('--references', type=Path, default=Path('build-local/owl-comparison'))
    ap.add_argument('--csv', type=Path, default=Path('tests/ltl-polarity-results.csv'))
    ap.add_argument('--timeout', type=float, default=30)
    args = ap.parse_args()
    spec = importlib.util.spec_from_file_location('comparison',
        Path(__file__).with_name('compare-ltl-sizes.py'))
    comparison = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(comparison)
    env = dict(os.environ, DYLD_LIBRARY_PATH=str(args.library.resolve()))
    fields = comparison.FIELDS + ['positive_states', 'reference_tool',
        'negative_raw_states', 'negative_raw_complete', 'transform_ms', 'validation_ms']
    with open('tests/ltl-fragment-results.csv') as source:
        baseline = [r for r in csv.DictReader(source) if r['tool'] == 'cola']
    rows = []
    args.artifacts.mkdir(parents=True, exist_ok=True)
    for index, positive in enumerate(baseline, 1):
        directory = args.artifacts / positive['case']
        directory.mkdir(exist_ok=True)
        row = dict.fromkeys(fields, '')
        row.update({k: positive[k] for k in ['case', 'sources', 'formula', 'reference_tool']})
        row.update(tool='cola_neg', positive_states=positive['states'], status='ok')

        def run(command, name, phase):
            output = directory / name
            code, elapsed = comparison.execute(command, output,
                directory / (name + '.stderr'), args.timeout, env)
            if code:
                row.update(status=phase + ('-timeout' if code == 'timeout' else '-failed'),
                    detail=(directory / (name + '.stderr')).read_text(errors='replace')[-400:]
                    or (f'{phase} exceeded {args.timeout:g} seconds' if code == 'timeout' else str(code)))
                raise RuntimeError(row['status'])
            return output, elapsed

        def metrics(path, name):
            output, elapsed = run(['autfilt', str(path), '--stats=%s,%e,%a,%d,%p'],
                                  name, 'metrics')
            return list(map(int, output.read_text().strip().split(','))), elapsed

        try:
            negative, elapsed = run([args.ltld, '-f', '!(' + row['formula'] + ')'],
                                    'negative.hoa', 'translation')
            row['elapsed_ms'] = round(elapsed, 3)
            raw, validation = metrics(negative, 'negative.stats')
            assert raw[3] == 1, 'negative automaton is nondeterministic'
            row.update(negative_raw_states=raw[0], negative_raw_complete=raw[4])
            complete, elapsed = run(['autfilt', str(negative), '--complete',
                '--remove-unreachable-states'], 'negative.complete.hoa', 'completion')
            final, flip_elapsed = run(['autfilt', str(complete), '--complement-acceptance'],
                                     'cola_neg.hoa', 'complement')
            row['transform_ms'] = round(elapsed + flip_elapsed, 3)
            before, elapsed = metrics(complete, 'negative.complete.stats')
            validation += elapsed
            after, elapsed = metrics(final, 'positive.stats')
            validation += elapsed
            assert before == after and after[3:] == [1, 1], 'graph changed or not total/deterministic'
            row.update(raw_states=after[0], raw_edges=after[1], raw_colours=after[2],
                       raw_complete=1, states=after[0], edges=after[1], colours=after[2])
            _, elapsed = run(['autfilt', '-q', str(final), '--equivalent-to=' +
                str(args.references / row['case'] / (row['reference_tool'] + '.hoa'))],
                'equivalence.stdout', 'equivalence')
            row['validation_ms'] = round(validation + elapsed, 3)
        except (RuntimeError, AssertionError) as error:
            if row['status'] == 'ok':
                row.update(status='invariant-failed', detail=str(error))
        rows.append(row)
        temporary = args.csv.with_suffix('.csv.tmp')
        with temporary.open('w', newline='') as out:
            writer = csv.DictWriter(out, fields, lineterminator='\n')
            writer.writeheader()
            writer.writerows(rows)
        temporary.replace(args.csv)
        print(index, row['sources'], row['status'], row['positive_states'], '->', row['states'], flush=True)
    manifest = {
        'cola_commit': subprocess.check_output(['git', 'rev-parse', 'HEAD'], text=True).strip(),
        'timeout_seconds_per_command': args.timeout,
        'method': 'translate !phi; complete; complement acceptance only; verify against phi reference',
        'sha256': {str(path): hashlib.sha256(path.read_bytes()).hexdigest() for path in
            [Path(args.ltld), args.library / 'libcola.0.dylib',
             Path('tests/ltl-fragment-results.csv'), Path('tests/ltl-size-results.csv')]}}
    args.csv.with_suffix('.json').write_text(json.dumps(manifest, indent=2) + '\n')
    assert len(rows) == 227
    # Resource-limited translations are experiment outcomes, not valid outputs.
    # Completed outputs must still pass every semantic and structural check.
    assert all(r['status'] in {'ok', 'translation-timeout'} for r in rows)
    print(dict(Counter(r['status'] for r in rows)))


if __name__ == '__main__':
    main()
