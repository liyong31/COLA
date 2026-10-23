#!/usr/bin/env python3
"""Produce paired size summaries, excluding failed or unchecked translations."""
import argparse
from collections import Counter, defaultdict
import csv
import math
from pathlib import Path
import statistics

TOOLS = ['spot', 'delag', 'ltl3tela', 'owl', 'cola', 'cola_reset']
LABELS = ['Spot', 'DELAG', 'LTL3TELA', 'OWL SLM21', 'COLA', 'COLA reset']
VALID = {'ok', 'reference', 'alternate-reference'}


def geomean(values):
    return math.exp(statistics.mean(math.log(v) for v in values))


def table(headers, rows):
    return '\n'.join(['| ' + ' | '.join(map(str, headers)) + ' |',
                      '| ' + ' | '.join(['---'] * len(headers)) + ' |'] +
                     ['| ' + ' | '.join(map(str, row)) + ' |' for row in rows])


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('csv', type=Path)
    ap.add_argument('--output', type=Path, required=True)
    ap.add_argument('--overlay', type=Path,
                    help='replace matching case/tool rows with a later campaign')
    args = ap.parse_args()
    with args.csv.open() as source:
        rows = list(csv.DictReader(source))
    if args.overlay:
        replacements = list(csv.DictReader(args.overlay.open()))
        overlay = {(r['case'], r['tool']): r for r in replacements}
        assert len(overlay) == len(replacements), 'Duplicate overlay row'
        assert set(overlay) <= {(r['case'], r['tool']) for r in rows}, 'Unknown overlay row'
        rows = [overlay.get((r['case'], r['tool']), r) for r in rows]
    cases = defaultdict(dict)
    for row in rows:
        assert row['tool'] not in cases[row['case']], 'Duplicate case/tool row'
        cases[row['case']][row['tool']] = row
    assert all(set(case) == set(TOOLS) for case in cases.values()), 'Incomplete campaign'
    common = [case for case in cases.values()
              if all(r['status'] in VALID for r in case.values())]
    lines = ['# OWL literature: measured size summary', '',
             f'{len(cases)} unique formula strings; {len(rows)} tool runs; '
             f'{len(common)} formulas in the common verified cohort.', '',
             'References are deterministic; other valid rows are deterministic '
             'and language-equivalent to the reference. Where Spot fails, an '
             'explicitly labelled alternate reference is used for available pairs. '
             'All main size comparisons use the same '
             'common cohort. Automata are completed and unreachable states removed; '
             'no common minimisation is applied.', '', '## Outcomes', '']
    if args.overlay:
        lines[2:2] = [f'Updated rows: `{args.overlay.name}`; other tool outputs are reused '
                      'from the original campaign.', '']
    statuses = sorted({r['status'] for r in rows})
    lines += [table(['Tool'] + statuses,
                    [[label] + [sum(r['tool'] == tool and r['status'] == status for r in rows)
                                for status in statuses]
                     for tool, label in zip(TOOLS, LABELS)]), '',
              '## Complete reachable automata', '',
              'Best counts include ties; strict best requires being smaller than '
              'every other configuration. State ratios are geometric means of '
              'per-formula tool/Spot ratios; lower is better.', '']
    comparison = []
    for tool, label in zip(TOOLS, LABELS):
        states = [int(c[tool]['states']) for c in common]
        edges = [int(c[tool]['edges']) for c in common]
        best = sum(int(c[tool]['states']) == min(int(r['states']) for r in c.values())
                   for c in common)
        strict = sum(all(int(c[tool]['states']) < int(c[t]['states'])
                         for t in TOOLS if t != tool) for c in common)
        ratio = geomean([int(c[tool]['states']) / int(c['spot']['states']) for c in common])
        comparison.append([label, best, strict, sum(states), f'{statistics.median(states):g}',
                           max(states), f'{ratio:.4f}', sum(edges)])
    lines += [table(['Tool', 'Best incl. ties', 'Strict best', 'Total states',
                     'Median states', 'Max states', 'State ratio / Spot', 'Total edges'],
                    comparison), '', '## Paired state comparisons', '',
              'Each cell is row-tool wins / ties / losses against the column tool. '
              'These comparisons use every formula verified for that particular '
              'pair, including formulas excluded from the all-tool cohort.', '']
    paired = []
    for tool, label in zip(TOOLS, LABELS):
        cells = [label]
        for other in TOOLS:
            if tool == other:
                cells.append('—')
                continue
            pairs = [c for c in cases.values() if c[tool]['status'] in VALID
                     and c[other]['status'] in VALID]
            counts = Counter((int(c[tool]['states']) > int(c[other]['states'])) -
                             (int(c[tool]['states']) < int(c[other]['states'])) for c in pairs)
            cells.append(f'{counts[-1]} / {counts[0]} / {counts[1]}')
        paired.append(cells)
    lines += [table(['Row vs column'] + LABELS, paired), '',
              '## Raw reachable state counts', '',
              'The same common cohort before completion. Missing rejecting sinks '
              'can reduce these counts by one.', '']
    lines += [table(['Tool', 'Total raw states', 'Best incl. ties'], [
        [label, sum(int(c[tool]['raw_states']) for c in common),
         sum(int(c[tool]['raw_states']) == min(int(r['raw_states']) for r in c.values())
             for c in common)] for tool, label in zip(TOOLS, LABELS)]), '',
              '## Common-cohort state ratios by collection', '',
              'Geometric mean tool/Spot state ratio. A formula appearing in multiple '
              'collections contributes once to each relevant collection.', '']
    sources = sorted({s.split(':')[0] for c in common
                      for s in c['spot']['sources'].split(';')})
    collections = []
    for source in sources:
        subset = [c for c in common if source in {s.split(':')[0]
                  for s in c['spot']['sources'].split(';')}]
        collections.append([source, len(subset)] + [f'{geomean([int(c[t]["states"]) / int(c["spot"]["states"]) for c in subset]):.4f}' for t in TOOLS])
    lines += [table(['Collection', 'N'] + LABELS, collections), '',
              '## Cases with the largest state spread', '',
              'Sorted by largest/smallest complete state count in the common cohort. '
              'All formulas and source lines are in the CSV.', '']
    ordered = sorted(common, key=lambda c: max(int(r['states']) for r in c.values()) /
                     min(int(r['states']) for r in c.values()), reverse=True)
    lines += [table(['Source'] + LABELS, [[c['spot']['sources'].split(';')[0]] +
               [c[t]['states'] for t in TOOLS] for c in ordered[:12]]), '',
              '## Reset routing', '']
    reset = [r for r in rows if r['tool'] == 'cola_reset']
    lines += [f'- Formula runs with completed finite-witness monitors: '
              f'{sum(int(r["witness_monitors"] or 0) > 0 for r in reset)}.',
              f'- Formula runs with budget aborts: '
              f'{sum(int(r["witness_aborts"] or 0) > 0 for r in reset)}.', '',
              'Do not attribute unchanged fast-path or fallback outputs to the reset '
              'construction. Timings in the CSV are single-process diagnostic '
              'elapsed times, not repeated performance benchmarks.', '']
    args.output.write_text('\n'.join(lines))
    print(table(['Tool', 'Best incl. ties', 'Strict best', 'Total states',
                 'Median', 'Max', 'Ratio / Spot', 'Edges'], comparison))


if __name__ == '__main__':
    main()
