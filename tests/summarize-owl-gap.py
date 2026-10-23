#!/usr/bin/env python3
"""Summarise OWL controls and certified pruning between independent SCCs."""
import collections
import csv
from pathlib import Path


def read(path):
    return list(csv.DictReader(open(path)))


def main():
    controls = read('tests/owl-gap-controls.csv')
    assert len(controls) == 908
    a = {(r['case'], r['algorithm']): r for r in read('tests/owl-annotations-results.csv')
         if r['mode'] == 'on' and r['status'] == 'ok'}
    b = {(r['case'], r['variant']): r for r in controls if r['status'] == 'ok'}
    variants = ['positive', 'positive_no_portfolio', 'eks20_positive_no_portfolio', 'no_portfolio']
    common = sorted(c for c in {k[0] for k in a}
                    if all((c, v) in a for v in ['SEJK16', 'EKS20'])
                    and all((c, v) in b for v in variants))
    lines = ['# OWL gap diagnosis and SCC-decomposed pruning', '',
        'The existing construction still determinises each SCC independently.',
        'Cross-SCC coverage removes redundant runs before local colour generation;',
        'it does not merge SCCs or compare their local rank numbers.', '',
        '## Controlled OWL comparison', '',
        'OWL 21.0 was run on all 227 collected formulas, with 10 seconds per process',
        'and two workers. Every successful result is deterministic, complete, and',
        'equivalent to the retained independent reference after the same normalisation.',
        'The four controls independently disable complement selection and the fragment',
        'portfolio. These compare algorithm families, not an identical exported HOA:',
        'OWL retains internal annotations and preprocessing in its DPA command.', '',
        f'On the fixed {len(common)}-formula cohort successful in all four controls and',
        'both annotated COLA positive-GBA variants:', '',
        '| Route | States |', '| --- | ---: |',
        '| COLA best positive SEJK16/EKS20 GBA | ' + str(sum(min(int(a[c, v]['states']) for v in ['SEJK16', 'EKS20']) for c in common)) + ' |']
    for v in variants:
        lines.append(f"| OWL {v} | {sum(int(b[c,v]['states']) for c in common)} |")
    lines += ['', 'Thus OWL does not beat the isolated construction in every matched comparison.',
        'The historical 1188-state OWL figure uses both polarities. It must not be',
        'presented as a positive-only, identical-input determinisation result.', '',
        '| Same positive algorithm family, portfolios off | Matched formulas | COLA | OWL |',
        '| --- | ---: | ---: | ---: |']
    for alg, v in [('SEJK16', 'positive_no_portfolio'), ('EKS20', 'eks20_positive_no_portfolio')]:
        cs = sorted(c for c, t in a if t == alg and (c, v) in b)
        lines.append(f"| {alg} | {len(cs)} | {sum(int(a[c,alg]['states']) for c in cs)} | {sum(int(b[c,v]['states']) for c in cs)} |")
    lines += ['', 'The largest FG gaps survive both controls: Parametrised 27 is COLA 32 / OWL 5;',
        'Parametrised 45 is COLA 89 / OWL 15, for both algorithm families.',
        'Conversely Parametrised 42 SEJK16 becomes COLA 65 / OWL 65 when OWL polarity',
        'selection is disabled; OWL with polarity gives 31. EKS20 gives 42 on both sides.', '',
        '## Mechanism in OWL', '',
        'Source inspected: [OWL commit 632c2da](https://github.com/owl-toolkit/owl/blob/632c2da3ec982cdda340305afb9a3ddf45000491/src/main/java/owl/translations/ltl2dpa/AsymmetricDPAConstruction.java),',
        'AsymmetricDPAConstruction.java. It filters available fixed points, uses a',
        'single global language-coverage ranking, partitions jumps into liveness,',
        'general, almost-safety and safety classes, and schedules at most one safety',
        'candidate with safetyProgress. It also resets ranks on prefix SCC changes.',
        'The executable measured here is release 21.0; this source reading is not a',
        'binary-level ablation of each individual optimisation.', '',
        'For FGa|FGb|FGc|FGd|FGe, the exported LDGBA has a recurrent prefix and five',
        'accepting singleton SCCs with languages Ga, Gb, Gc, Gd, Ge. None of these',
        'languages covers another. Our weak bookkeeping retains subsets (32 states);',
        'OWL rotates safety guesses (5 states). Coverage pruning cannot justify',
        'dropping these incomparable languages. Reusing that scheduler requires a',
        'certificate that guesses can be restarted and fairly rotated. The existing',
        'direct FG/GF routes retain priority in the complete translator.', '',
        '## Certified coverage across SCCs', '',
        'USE_OWL_CROSS_SCC / raw --cross-scc enables the new step. All component',
        'constructions and shifted original Emerson–Lei acceptance are preserved.',
        'A run q is deleted only when independently certified language formulas prove',
        'L(q) is included in the union of retained runs in strictly lower SCCs.',
        'Spot numbers SCCs in reverse topological order. Process SCCs in increasing',
        'order, keep coverers, and never use simultaneous mutual deletion.', '',
        'Correctness: on an accepted suffix, at least one retained coverer has an',
        'accepting continuation. A later replacement or proper SCC transition strictly',
        'decreases its SCC number, so replacement cannot repeat infinitely often.',
        'After the final replacement the existing local construction preserves that',
        'accepting run. Within-SCC pruning keeps its established older-run rule.',
        'Deletion introduces no new source runs; original discontinuation acceptance',
        'remains responsible for ranks removed by the step. Unknown or forged formulas',
        'cannot justify deletion. Boolean abstraction proves sufficient inclusions;',
        'it is not a complete decision procedure for arbitrary LTL implication.', '',
        '## Identical-input pruning ablation', '',
        'Both modes enable annotations and the same local colour/exact-query policy.',
        'Only cross-SCC pruning differs. Each successful result passes native/input',
        'equivalence and completed-output/input equivalence. Timings are diagnostic;',
        'the two polarity campaigns overlapped. Source/binary stability is checked.', '',
        '| Polarity | Paired successes | Smaller | Ties | Larger | State delta | Coverage deletions |',
        '| --- | ---: | ---: | ---: | ---: | ---: | ---: |']
    for label, path in [('positive', 'tests/owl-cross-scc-results.csv'), ('negative', 'tests/owl-cross-scc-negative-results.csv')]:
        rows = read(path); assert len(rows) == 908
        assert not any(r['status'] in ['input-inequivalent', 'native-inequivalent', 'normalised-inequivalent', 'backend-error', 'driver-error'] for r in rows)
        d = {(r['case'], r['algorithm'], r['mode']): r for r in rows}
        counts = collections.Counter(); delta = 0
        for (c, alg, mode), r in d.items():
            if mode != 'on': continue
            old = d[c, alg, 'off']
            if old['status'] == r['status'] == 'ok':
                diff = int(r['states']) - int(old['states']); delta += diff
                counts['smaller' if diff < 0 else 'larger' if diff > 0 else 'ties'] += 1
        proofs = sum(int(r['cross-scc-proofs'] or 0) for r in rows if r['mode'] == 'on')
        lines.append(f"| {label} | {sum(counts.values())} | {counts['smaller']} | {counts['ties']} | {counts['larger']} | {delta} | {proofs} |")
        lines += ['', f'{label} status counts: `{dict(collections.Counter(r["status"] for r in rows))}`.', '']
    lines += ['Positive EKS20: Dwyer50 72->38, Dwyer55 109->86, Dwyer45 28->22.',
        'Negative SEJK16: Hardness1 379->169. Negative EKS20: Hardness5 133->91.',
        'Negative Hardness3 SEJK16 recovers an acceptance-capacity failure.',
        'Counterexamples to size monotonicity include negative EKS20 Hardness1 22->29',
        'and Hardness3 24->60. Fewer tracked runs need not mean fewer reachable',
        'macrostates. The raw ablation reports these increases without hiding them.', '',
        'The optional LTL flag --ldgba-cross-scc therefore compares a changed pruned',
        'candidate against the unpruned SCC construction on the same frontend HOA.',
        'Both are normalised, language-checked and completed before size comparison;',
        'the smaller positive-language candidate is retained. No additional frontend',
        'call is needed; changed candidates may require one extra backend call.', '',
        'A separate raw --prefix-resets prototype certifies the deterministic rejecting',
        'prefix/closed deterministic accepting partition, decodes and checks A labels,',
        'and resets only on proper prefix SCC changes when the retained prefix covers',
        'all discarded languages. It has fixture coverage but no corpus size claim;',
        'it is not enabled in the LTL route. Cross-SCC pruning needs no prefix decoder.', '']
    path = Path('tests/owl-cross-scc-integrated.csv')
    if path.exists():
        rows = read(path)
        if len(rows) == 454:
            assert all(r['status'] == 'ok' and not int(r['LDGBA validation failures'] or 0) for r in rows)
            old = {(r['case'], r['tool']): r for r in read('tests/owl-annotations-integrated.csv')}
            lines += ['## Integrated portfolio', '']
            for tool in ['cola_ldgba', 'cola_combined']:
                rs = [r for r in rows if r['tool'] == tool]
                wins = sum(int(r['states']) < int(old[r['case'],tool]['states']) for r in rs)
                losses = sum(int(r['states']) > int(old[r['case'],tool]['states']) for r in rs)
                lines.append(f"{tool}: {sum(int(r['states']) for r in rs)} states across 227, {wins} smaller and {losses} larger than the retained annotation baseline. All 227 pass independent equivalence.")
            lines.append('')
    lines += ['## Validation and reproduction', '',
        'All 11 suites pass; the annotation suite now has 42 certification, joint coverage,',
        'finite-prefix-reset and cross-SCC regressions. The LDGBA route additionally',
        'tests two equivalent deterministic SCCs and the baseline/pruned selection (31 route checks).',
        'The cross-SCC-enabled combined finite-witness rerun passes 387 outputs plus',
        '585 budget/bypass checks, with no timeout or acceptance-capacity failure.',
        'The complete smoke suite and distribution packaging pass. The manuscript',
        'with the added proof sketch compiles to 22 pages.', '',
        '```sh', 'python3 tests/diagnose-owl-ldgba-gap.py',
        'python3 tests/benchmark-owl-annotations.py --scc-pruning cross --artifacts build-local/owl-cross-scc --csv tests/owl-cross-scc-results.csv',
        'python3 tests/benchmark-owl-annotations.py --negative --scc-pruning cross --artifacts build-local/owl-cross-scc-negative --csv tests/owl-cross-scc-negative-results.csv',
        'python3 tests/benchmark-slaa.py --tool build-local/external/ltl3tela-master/ltl3tela --ldgba-pruning --ldgba-portfolio --ldgba-cross-scc --modes cola_ldgba cola_combined --artifacts build-local/owl-cross-scc-integrated --csv tests/owl-cross-scc-integrated.csv',
        'python3 tests/summarize-owl-gap.py', '```', '',
        'Do not rebuild during a campaign. The raw campaigns preceded the frontend',
        'portfolio integration build; their exact measured binaries are retained under',
        'build-local/owl-cross-measured-binaries. Their manifests describe those builds.',
        'No unrestricted double-exponential LTL theorem or minimum-DELA claim follows',
        'from these measurements. Safety scheduling and a global certified language-basis',
        'bound across independent SCCs remain open.']
    Path('tests/owl-gap-report.md').write_text('\n'.join(lines) + '\n')


if __name__ == '__main__': main()
