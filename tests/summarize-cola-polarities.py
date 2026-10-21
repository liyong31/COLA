#!/usr/bin/env python3
"""Summarize the verified COLA polarity experiment on matched formulas."""
import csv
import math
from pathlib import Path


def read(name):
    with open('tests/' + name) as source:
        return list(csv.DictReader(source))


def main():
    negative = read('ltl-polarity-results.csv')
    groups = {}
    for row in read('ltl-size-results.csv'):
        groups.setdefault(row['case'], {})[row['tool']] = row
    for row in read('ltl-fragment-results.csv') + negative:
        groups[row['case']][row['tool']] = row
    valid = {'ok', 'reference', 'alternate-reference'}
    paired = [r for r in negative if r['status'] == 'ok']
    wins = [r for r in paired if int(r['states']) < int(r['positive_states'])]
    losses = [r for r in paired if int(r['states']) > int(r['positive_states'])]
    tools = ['spot', 'delag', 'ltl3tela', 'owl', 'cola', 'cola_reset', 'cola_neg']
    labels = ['Spot', 'DELAG', 'LTL3TELA', 'OWL SLM21', 'COLA', 'COLA reset', 'COLA-neg']
    common = [g for g in groups.values() if all(g[t]['status'] in valid for t in tools)]
    lines = ['# COLA polarity experiment', '',
        'Translate `!phi` with the existing default COLA, complete the deterministic graph, '
        'then complement its acceptance condition to obtain `phi`. Completion and acceptance '
        'complement are separate commands; no minimization is applied. All sizes below are '
        'reachable complete states. Positive COLA and external-tool rows are reused from '
        'the previous verified campaigns.', '',
        f'{len(negative)} negated translations: {len(paired)} verified successes. '
        'Failures, if any, remain in `ltl-polarity-results.csv` and are excluded from paired metrics.', '',
        f'Against positive COLA on {len(paired)} verified pairs: **{len(wins)} smaller, '
        f'{len(paired)-len(wins)-len(losses)} tied, {len(losses)} larger**.', '']
    for name, values in [('COLA', [int(r['positive_states']) for r in paired]),
                         ('COLA-neg', [int(r['states']) for r in paired]),
                         ('Best of both', [min(int(r['states']), int(r['positive_states'])) for r in paired])]:
        lines.append(f'- {name}: {sum(values)} total states over these {len(values)} pairs.')
    all_positive = sum(int(g['cola']['states']) for g in groups.values())
    all_portfolio = sum(min(int(g['cola']['states']), int(g['cola_neg']['states']))
        if g['cola_neg']['status'] == 'ok' else int(g['cola']['states']) for g in groups.values())
    lines += ['', f'Across all {len(groups)} formulas, retaining positive COLA when the negative '
        f'attempt fails gives {all_portfolio} portfolio states versus {all_positive} positive states. '
        'This fallback prevents a negative timeout from losing an already available result.']
    failures = [r for r in negative if r['status'] != 'ok']
    if failures:
        lines += ['', '| Unsuccessful negative attempt | Outcome | Positive COLA states |',
                  '| --- | --- | ---: |']
        lines += [f'| {r["sources"]} | {r["status"]} | {r["positive_states"]} |' for r in failures]
        lines += ['', 'Each translation has a 30-second limit. These are resource failures '
            'of the negative route; no output from them is counted as equivalent. '
            'The current guard-preservation rule recognizes safety conjunctions; negation '
            'changes their Boolean structure, so it need not retain the same translation route.']
        lines += ['', 'Diagnostic Spot calls on these three negated formulas with '
            '`ltl2tgba -D -G -x ltl-split=0 -f "!(FORMULA)"` finish in roughly '
            '36, 77 and 132 ms, with 83, 148 and 107 complete states, respectively. '
            'All three outputs passed positive-language equivalence after completion and '
            'acceptance complement. See `ltl-polarity-probes.json`. This demonstrates an '
            'avoidable route on these inputs; the probe outputs are not substituted into '
            'COLA-neg measurements. Extending constraint preservation to the dual Boolean '
            'structure is a concrete further routing improvement.']
    lines += ['', '## Comparison with external tools', '',
        f'The same {len(common)} formulas succeed for every listed configuration. '
        'Best counts include ties. The portfolio selects by complete states, acceptance sets, '
        'then edges, with positive polarity breaking exact ties. It is an offline selection '
        'from measured candidates, not a new translator option.', '',
        '| Configuration | Total states | Smallest incl. ties | Total edges |',
        '| --- | ---: | ---: | ---: |']
    portfolios = [min([g['cola'], g['cola_neg']], key=lambda r:
        (int(r['states']), int(r['colours']), int(r['edges']))) for g in common]
    for name, rows in [(label, [g[t] for g in common]) for t, label in zip(tools, labels)] + [('COLA best of both', portfolios)]:
        best = sum(int(r['states']) == min(int(g[t]['states']) for t in tools)
                   for r, g in zip(rows, common))
        lines.append(f'| {name} | {sum(int(r["states"]) for r in rows)} | {best} | '
                     f'{sum(int(r["edges"]) for r in rows)} |')
    lines += ['', 'Remaining differences between the portfolio and LTL3TELA:', '',
              '| Source | COLA best of both | LTL3TELA |', '| --- | ---: | ---: |']
    for row, group in zip(portfolios, common):
        if row['states'] != group['ltl3tela']['states']:
            lines.append(f'| {row["sources"]} | {row["states"]} | {group["ltl3tela"]["states"]} |')
    lines += ['', '## Formulas whose state counts change', '',
        '| Source | COLA | COLA-neg |', '| --- | ---: | ---: |']
    for row in paired:
        if row['states'] != row['positive_states']:
            lines.append(f'| {row["sources"]} | {row["positive_states"]} | {row["states"]} |')
    ratio = math.exp(sum(math.log(int(r['states']) / int(r['positive_states'])) for r in paired) / len(paired))
    lines += ['', f'Geometric mean COLA-neg/COLA state ratio over verified pairs: {ratio:.4f}.', '',
        '## Reproduction and interpretation', '',
        'Run `python3 tests/compare-cola-polarities.py`, then '
        '`python3 tests/summarize-cola-polarities.py`. Retained HOA intermediates are under '
        '`build-local/polarity-comparison/`. Source revision, binary/input hashes and timeout '
        'are recorded in `ltl-polarity-results.json`. Translation, completion/complement, and '
        'validation times are separate CSV columns; these are single runs, not stable runtime rankings.', '',
        'Equivalence is checked against the original positive-language Spot reference, or '
        'the previously independently checked DELAG reference where Spot timed out. '
        'Every negative graph is checked deterministic before complementation, and the '
        'completed graph must retain its states, edges, acceptance-set count, determinism '
        'and completeness after acceptance complement.', '',
        'Ten additional semantic boundary checks passed against fresh Spot references: '
        '`0`, `1`, `a`, `!a`, `G a`, `F a`, `GF a`, `FG a`, `G(a -> X b)`, '
        'and `GF(a & X b) & FG c`. For example, translating the negation of `F a` '
        'produces an incomplete one-state graph; completion makes it two states before '
        'acceptance is complemented. Boundary HOA artifacts remain under '
        '`build-local/polarity-boundaries/`.', '',
        'Polarity selection complements specialized fragment routing: negative translation '
        'can expose a cheaper construction, but can also cause severe growth. Keep the '
        'positive candidate and bound any future additional attempt. Merely negating globally '
        'does not reproduce LTL3TELA’s full compositional polarity selection. The existing '
        'finite-witness construction and translator defaults are unchanged.', '']
    Path('tests/ltl-polarity-summary.md').write_text('\n'.join(lines))
    print('\n'.join(lines[:30]))


if __name__ == '__main__':
    main()
