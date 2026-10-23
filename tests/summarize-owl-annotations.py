#!/usr/bin/env python3
"""Summarise certified OWL annotation ablations and integrated equivalence."""
import csv
from collections import Counter
from pathlib import Path


def main():
    lines = ['# Certified OWL annotations in native determinisation', '',
        'OWL is invoked with --state-labels. The decoder supports the measured OWL 21',
        'SEJK16 and EKS20 accepting-state descriptions. Indexed fixed-point APs are',
        'mapped through the HOA AP order; monitor formulas use original names.',
        'An indexed-token lexer handles OWL strings such as p0Up1. Quoted AP names',
        'and nested lists/records are preserved.', '',
        'Every reconstructed state-language formula is checked against the input',
        'automaton rooted at that state before it can justify deletion. Unsupported,',
        'malformed or unverified names remain unknown. Certification examines at',
        'most the first 256 state indices, matching the default frontend admission cap.', '',
        'Certified formulas prove pair dominance and full older-prefix union coverage',
        'through propositional BDDs over maximal temporal subformulas. A Boolean',
        'implication is sufficient for the corresponding language inclusion. These',
        'proofs precede the bounded exact-query policy and do not consume its budget.',
        'Only younger runs are deleted; the oldest is retained. Original Emerson–Lei',
        'colours and rank-discontinuation acceptance remain unchanged.', '',
        '## Identical-input ablations', '',
        'Both modes use the same labelled HOA input and the existing wider exact',
        'policy/colour packing. Only --owl-annotations differs. Each process has a',
        '10-second deadline, with two workers per raw campaign. Campaigns may overlap;',
        'elapsed times are diagnostic, not runtime rankings.', '',
        '| Polarity | Algorithm | Paired successes | Smaller / tied / larger | Off / on states |',
        '| --- | --- | ---: | ---: | ---: |']
    counts = {}
    improvements = []
    raw_stats = Counter()
    all_rows = []
    for polarity, suffix in [('positive', 'results'), ('negative', 'negative-results')]:
        rows = list(csv.DictReader(open('tests/owl-annotations-' + suffix + '.csv')))
        assert len(rows) == 908
        assert not any('inequivalent' in r['status'] or r['status'] in ['backend-error', 'driver-error'] for r in rows)
        all_rows += rows
        paired = {}
        for r in rows: paired.setdefault((r['case'], r['algorithm']), {})[r['mode']] = r
        for alg in ['SEJK16', 'EKS20']:
            pairs = [p for (case, a), p in paired.items() if a == alg
                     and len(p) == 2 and all(r['status'] == 'ok' for r in p.values())]
            diff = Counter((int(p['on']['states']) > int(p['off']['states']))
                           - (int(p['on']['states']) < int(p['off']['states'])) for p in pairs)
            totals = [sum(int(p[m]['states']) for p in pairs) for m in ['off', 'on']]
            counts[polarity, alg] = (len(pairs), totals)
            lines += [f'| {polarity} | {alg} | {len(pairs)} | {diff[-1]} / {diff[0]} / {diff[1]} | {totals[0]} / {totals[1]} |']
            for p in pairs:
                if p['on']['states'] != p['off']['states']:
                    improvements += [f"- {polarity} {p['on']['sources']} {alg}: {p['off']['states']} → {p['on']['states']} states."]
        for p in paired.values():
            if p['off']['status'] != p['on']['status']:
                improvements += [f"- {polarity} {p['on']['sources']} {p['on']['algorithm']}: "
                    f"{p['off']['status']} → {p['on']['status']} ({p['on']['states']} states)."]
        for r in rows:
            if r['mode'] == 'on':
                for key in ['decoded', 'certified', 'rejected', 'pair-proofs', 'union-proofs']:
                    raw_stats[key] += int(r['annotation-' + key] or 0)
    lines += ['', 'Non-tied paired results:', ''] + (improvements or ['None.'])
    lines += ['', '| Polarity | Mode | Status | Count |', '| --- | --- | --- | ---: |']
    for polarity, offset in [('positive', 0), ('negative', 908)]:
        for (mode, status), number in sorted(Counter((r['mode'], r['status'])
                for r in all_rows[offset:offset + 908]).items()):
            lines += [f'| {polarity} | {mode} | {status} | {number} |']
    lines += ['', f"Across raw on-mode outputs: {raw_stats['certified']} certified state annotations, "
              f"{raw_stats['rejected']} rejected decoded annotations, {raw_stats['pair-proofs']} "
              f"successful pair proofs and {raw_stats['union-proofs']} union pruning events.",
              'Counts include repeated proof uses across macrostates; they are not unique-language counts.', '']
    integrated = list(csv.DictReader(open('tests/owl-annotations-integrated.csv')))
    assert len(integrated) == 454 and all(r['status'] == 'ok' for r in integrated)
    assert not any(int(r['LDGBA validation failures'] or 0) for r in integrated)
    previous = {(r['case'], r['tool']): r for r in csv.DictReader(open('tests/ltl-ldgba-polarity-integrated.csv'))}
    lines += ['## Integrated portfolio', '',
        '| Mode | Smaller / tied / larger | Previous / annotated total |', '| --- | ---: | ---: |']
    integrated_totals = {}
    for mode in ['cola_ldgba', 'cola_combined']:
        pairs = [(previous[r['case'], mode], r) for r in integrated if r['tool'] == mode]
        diff = Counter((int(b['states']) > int(a['states'])) - (int(b['states']) < int(a['states'])) for a, b in pairs)
        totals = [sum(int(p[i]['states']) for p in pairs) for i in [0, 1]]
        integrated_totals[mode] = totals
        lines += [f'| {mode} | {diff[-1]} / {diff[0]} / {diff[1]} | {totals[0]} / {totals[1]} |']
    lines += ['', 'All integrated outputs pass deterministic/completeness and independent language checks,',
        'and no LDGBA candidate fails language validation. The annotated mode is default',
        'when an OWL LDGBA tool is supplied; --no-ldgba-annotations supplies the ablation.', '',
        '## Proof scope and regression evidence', '',
        'The independent per-state equivalence check supplies the exactness certificate;',
        'OWL toString() output is not trusted solely because it resembles a formula.',
        'Unknown older formulas can be omitted from a proposed cover safely. The BDD',
        'check is complete for the Boolean abstraction, not for arbitrary LTL implication.', '',
        'This now supplies checked formula pruning. The remaining TACAS complexity',
        'obligations are a certified deterministic prefix and a singly exponential bound',
        'on the total basis/rank width and weak bookkeeping across SCCs. Formula names',
        'alone do not prove those hypotheses; the conditional counting contract remains',
        'in research/colour-elevator.tex.', '',
        'The 26 C++ regressions include a genuinely joint union cover, actual union',
        'pruning with all automaton-inclusion query budgets disabled, forged/malformed',
        'names, indexed AP collisions, punctuation in AP names, symmetric monitor',
        'fields and unspaced U/W/R/M tokens. The existing construction tests remain.', '',
        '## Reproduction', '', '```sh',
        'make -C build-local -j4 check',
        'python3 tests/benchmark-owl-annotations.py',
        'python3 tests/benchmark-owl-annotations.py --negative \\',
        '  --artifacts build-local/owl-annotations-negative \\',
        '  --csv tests/owl-annotations-negative-results.csv',
        'python3 tests/benchmark-slaa.py --tool PATH_TO_LTL3TELA \\',
        '  --ldgba-pruning --ldgba-portfolio --modes cola_ldgba cola_combined \\',
        '  --artifacts build-local/owl-annotations-integrated \\',
        '  --csv tests/owl-annotations-integrated.csv',
        'python3 tests/summarize-owl-annotations.py', '```', '',
        'JSON manifests record measured source/binary hashes and raw input hashes.',
        'Builds must finish before campaigns start. Interrupted decoder-development',
        'measurements were discarded; only final stable-binary campaigns are reported.', '',
        '[OWL options](https://github.com/owl-toolkit/owl#quick-start),',
        '[TACAS 2017](https://arxiv.org/html/1701.06103v1).', '']
    finite = list(csv.DictReader(open('tests/finite-witness-owl-annotations.csv')))
    assert len(finite) == 387 and all(r['status'] == 'ok' for r in finite)
    lines += ['The complete finite-witness rerun has 387 equivalent outputs and 585',
              'budget/bypass checks, with no timeout or capacity failure.', '']
    Path('tests/owl-annotations-report.md').write_text('\n'.join(lines))
    tex = [r'\subsection{Certified formula annotations in determinisation}',
        'The OWL frontend now exports labelled HOA. Reconstructed accepting-state',
        'formulas are certified by independent rooted-state language equivalence.',
        'Their Boolean abstractions then prove full older-prefix coverage before',
        'the bounded exact-query policy. Unsupported annotations retain the existing path.',
        'The original ranked-run and shifted Emerson--Lei acceptance construction is unchanged.', '',
        'Identical-input off/on ablations contain 1816 outputs across both polarities:',
        r'\begin{center}\begin{tabular}{llrrr}',
        r'Polarity & Algorithm & Paired & Off states & On states\\\hline']
    for (polarity, alg), (number, totals) in counts.items():
        tex += [f'{polarity} & {alg} & {number} & {totals[0]} & {totals[1]}' + r'\\']
    tex += [r'\end{tabular}\end{center}',
        f"Successful raw outputs record {raw_stats['certified']} certified annotations and "
        f"{raw_stats['union-proofs']} union pruning events. These are operational counts, not unique languages.",
        'All 454 integrated outputs pass independent language checks. The completed',
        f"LDGBA-only total changes from {integrated_totals['cola_ldgba'][0]} to {integrated_totals['cola_ldgba'][1]},",
        f"and the combined total from {integrated_totals['cola_combined'][0]} to {integrated_totals['cola_combined'][1]}.",
        'The 26 new regressions exercise joint coverage, exhausted query budgets,',
        'invalid labels and the indexed formula syntax. Exact formula certification',
        'does not yet prove the initial-prefix and total-width hypotheses needed for',
        'the unrestricted LTL counting bound. Timings are diagnostic only.', '']
    Path('research/owl-annotations.tex').write_text('\n'.join(tex))


if __name__ == '__main__': main()
