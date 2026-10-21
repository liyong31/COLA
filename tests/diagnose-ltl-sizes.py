#!/usr/bin/env python3
"""Ablate LTL3TELA's portfolio on its eleven measured wins against Spot."""
import argparse
import csv
import importlib.util
import os
from pathlib import Path


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--results', type=Path, default=Path('tests/ltl-size-results.csv'))
    ap.add_argument('--artifacts', type=Path, default=Path('build-local/size-diagnosis/wins'))
    ap.add_argument('--reference-artifacts', type=Path, default=Path('build-local/owl-comparison'))
    ap.add_argument('--ltl3tela', default='build-local/external/ltl3tela-master/ltl3tela')
    ap.add_argument('--csv', type=Path, default=Path('tests/ltl-size-ablations.csv'))
    ap.add_argument('--timeout', type=float, default=12)
    args = ap.parse_args()
    spec = importlib.util.spec_from_file_location('comparison',
                                                Path(__file__).with_name('compare-ltl-sizes.py'))
    comparison = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(comparison)
    groups = {}
    for row in csv.DictReader(args.results.open()):
        groups.setdefault(row['case'], {})[row['tool']] = row
    wins = [g for g in groups.values() if g['ltl3tela']['status'] == 'ok'
            and g['spot']['status'] == 'reference'
            and int(g['ltl3tela']['states']) < int(g['spot']['states'])]
    configurations = {
        'full': ['-D1', '-x1'],
        'slaa_only': ['-D1', '-b0', '-x1'],
        'no_spotela': ['-D1', '-b1', '-x1'],
        'no_spot': ['-D1', '-b2', '-x1'],
        'no_complement': ['-D1', '-n0', '-x1'],
        'no_split': ['-D1', '-l0', '-x1'],
        'no_merging': ['-D1', '-b0', '-c0', '-F0', '-G0', '-x1'],
    }
    fields = ['case', 'sources', 'formula', 'variant', 'status', 'states', 'edges',
              'colours', 'elapsed_ms', 'winner', 'spot_states', 'default_ltl3tela_states']
    rows = []
    args.artifacts.mkdir(parents=True, exist_ok=True)
    for group in wins:
        original = group['spot']
        case, formula = original['case'], original['formula']
        directory = args.artifacts / case
        directory.mkdir(exist_ok=True)
        for name, flags in configurations.items():
            output, stderr = directory / (name + '.hoa'), directory / (name + '.stderr')
            code, elapsed = comparison.execute([args.ltl3tela] + flags + ['-f', formula],
                                              output, stderr, args.timeout, os.environ)
            row = dict.fromkeys(fields, '')
            row.update(case=case, sources=original['sources'], formula=formula,
                       variant=name, elapsed_ms=round(elapsed, 3),
                       spot_states=original['states'],
                       default_ltl3tela_states=group['ltl3tela']['states'])
            row['winner'] = stderr.read_text(errors='replace').strip().replace('\n', ' / ')
            row['status'] = 'timeout' if code == 'timeout' else 'error' if code else 'translated'
            if code == 0:
                stats = directory / (name + '.stats')
                code, _ = comparison.execute(['autfilt', str(output), '--complete',
                                              '--stats=%s,%e,%a,%d'], stats,
                                             directory / (name + '.stats.stderr'),
                                             args.timeout, os.environ)
                if code == 0:
                    states, edges, colours, det = map(int, stats.read_text().strip().split(','))
                    row.update(states=states, edges=edges, colours=colours)
                    if not det:
                        row['status'] = 'nondeterministic'
                    else:
                        code, _ = comparison.execute(['autfilt', '-q', str(output),
                            '--equivalent-to=' + str(args.reference_artifacts / case / 'spot.hoa')],
                            directory / (name + '.equivalence.stdout'),
                            directory / (name + '.equivalence.stderr'), args.timeout, os.environ)
                        row['status'] = 'ok' if code == 0 else 'equivalence-failed'
                else:
                    row['status'] = 'metrics-failed'
            rows.append(row)
            temporary = args.csv.with_suffix('.csv.tmp')
            with temporary.open('w', newline='') as out:
                writer = csv.DictWriter(out, fields, lineterminator='\n')
                writer.writeheader()
                writer.writerows(rows)
            temporary.replace(args.csv)
        print(original['sources'], [(r['variant'], r['status'], r['states'])
                                     for r in rows if r['case'] == case], flush=True)
    assert len(wins) == 11, len(wins)
    print('All eleven measured LTL3TELA wins ablated.', flush=True)


if __name__ == '__main__':
    main()
