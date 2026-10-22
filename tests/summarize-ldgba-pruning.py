#!/usr/bin/env python3
"""Summarise retained-input LDGBA pruning ablations and integrated regressions."""
import csv
from collections import Counter
from pathlib import Path


def read(name, column='variant'):
    return {(r['case'], r[column]): r for r in csv.DictReader(open('tests/' + name))}


def main():
    names = ['raw-results', 'cache', 'packed', 'packed-pruning']
    data = [read('ltl-ldgba-' + name + '.csv') for name in names]
    variants = ['sejk16_gba', 'eks20_gba', 'sejk16_ba', 'eks20_ba']
    lines = ['# LDGBA pruning: retained-input experiment', '',
        'All new runs replay the same retained OWL HOA inputs. Frontend time is zero',
        'by construction; unavailable retained inputs are not new frontend timeouts.',
        'Each completed result passes source-LTL equivalence, native equivalence,',
        'determinism, completeness and equivalence to the retained independent reference.',
        'Five seconds per process, two workers; timings are diagnostic.', '',
        'Cache means the existing 8-state SCC / 4-run prefix / 64-query policy with',
        'memoised exact union proofs. Packed adds SCC-local colour restriction.',
        'Wider adds 256-state SCC / full admitted prefix / 512-query limits.',
        'The shared query budget also expands the reserved static semantic-order',
        'budget; this control measures their combined effect, not union pruning alone.',
        'All deletions still require exact language inclusion against older retained runs.', '',
        '| Change | Variant | Paired successes | Smaller / tied / larger | States before / after |',
        '| --- | --- | ---: | ---: | ---: |']
    for i in range(1, len(data)):
        before, after = data[i - 1:i + 1]
        for variant in variants:
            pairs = [(before[k], after[k]) for k in before if k[1] == variant
                     and before[k]['status'] == after[k]['status'] == 'ok']
            diff = Counter((int(y['states']) > int(x['states']))
                           - (int(y['states']) < int(x['states'])) for x, y in pairs)
            assert not diff[1], (names[i], variant, 'state regression')
            totals = [sum(int(p[j]['states']) for p in pairs) for j in (0, 1)]
            lines += [f'| {names[i-1]} → {names[i]} | {variant} | {len(pairs)} | '
                      f'{diff[-1]} / {diff[0]} / {diff[1]} | {totals[0]} / {totals[1]} |']
    lines += ['', '## Final status and fixed-cohort comparison', '',
              '| Variant | OK | Capacity | Backend timeout | Input unavailable |',
              '| --- | ---: | ---: | ---: | ---: |']
    for v in variants + ['owl_tacas_dpa']:
        status = Counter(r['status'] for k, r in data[-1].items() if k[1] == v)
        lines += [f"| {v} | {status['ok']} | {status['acceptance-capacity']} | "
                  f"{status['backend-timeout']} | {status['retained-input-unavailable']} |"]
    cohort = [case for case, v in data[0] if v == 'owl_tacas_dpa'
              and all(d[case, variant]['status'] == 'ok'
                      for d in (data[0], data[-1])
                      for variant in variants + ['owl_tacas_dpa'])]
    lines += ['', f'Fixed original five-way common cohort: **{len(cohort)} formulas**.', '',
              '| Variant | Original states | Optimised states |', '| --- | ---: | ---: |']
    for v in variants + ['owl_tacas_dpa']:
        sums = [sum(int(d[case, v]['states']) for case in cohort) for d in (data[0], data[-1])]
        lines += [f'| {v} | {sums[0]} | {sums[1]} |']
    lines += ['', 'Recovered original failures:', '']
    for k, r in data[-1].items():
        if r['status'] == 'ok' and data[0][k]['status'] != 'ok':
            lines += [f"- {r['sources']} {r['variant']}: {data[0][k]['status']} → {r['states']} states."]
    previous = read('ltl-ldgba-results.csv', 'tool')
    lines += ['', '## Integrated portfolio', '',
              '| Control | Mode | Smaller / tied / larger | Original total | New total |',
              '| --- | --- | ---: | ---: | ---: |']
    for control in ['optimized', 'polarity']:
        integrated = read('ltl-ldgba-' + control + '-integrated.csv', 'tool')
        assert len(integrated) == 454
        assert all(r['status'] == 'ok' for r in integrated.values())
        assert not any(int(r['LDGBA validation failures'] or 0)
                       for r in integrated.values()), 'a rejected LDGBA language candidate needs investigation'
        for v in ['cola_ldgba', 'cola_combined']:
            pairs = [(previous[k], r) for k, r in integrated.items() if k[1] == v]
            diff = Counter((int(y['states']) > int(x['states']))
                           - (int(y['states']) < int(x['states'])) for x, y in pairs)
            assert not diff[1]
            sums = [sum(int(p[j]['states']) for p in pairs) for j in (0, 1)]
            lines += [f'| {control} | {v} | {diff[-1]} / {diff[0]} / {diff[1]} | {sums[0]} | {sums[1]} |']
    lines += ['', 'The polarity control adds --ldgba-portfolio to --ldgba-pruning.',
              'Positive and negative frontend calls share the eight-attempt budget.', '']
    for k, r in integrated.items():
        if r['states'] != previous[k]['states']:
            lines += [f"- {r['sources']} {r['tool']}: {previous[k]['states']} → {r['states']} states."]
    default = read('ltl-ldgba-pruning-default.csv', 'tool')
    assert len(default) == 227 and all(r['status'] == 'ok' for r in default.values())
    assert sum(int(r['states']) for r in default.values()) == 1388
    lines += ['', 'The additional 227-formula default-mode check passes and reproduces',
              'every historical default state count (1388 total).', '']
    lines += ['', '## Complexity: what this implementation establishes', '',
        'TACAS 2017 §4.1–4.2 requires initial determinism and a singly exponential',
        'language basis, not merely limit determinism. Removing every covered younger',
        'run bounds the ranking length by the basis size plus one. Together with the',
        'double-exponential LDGBA size this bounds ordered configurations doubly',
        'exponentially. Generalized Büchi marks can remain on persistent runs; they',
        'need not be replaced by a Büchi counter for this counting argument.', '',
        'Our bounded SCC-local exact checks are safe engineering approximations.',
        'The installed HOA interface carries neither certified state-language formulas',
        'nor their basis. Exhausted budgets keep runs, SCC ranks are independent,',
        'and elevator admission does not certify initial determinism. Consequently',
        '**the TACAS double-exponential LTL bound is not yet established for this route**.',
        'Observed rank widths and a larger fixed query budget do not repair that proof.', '',
        'The next architectural step is an annotated LDGBA boundary exposing each',
        'state language and basis support, a certified deterministic prefix and closed',
        'accepting region, followed by complete oldest-first basis coverage pruning',
        'across that region. Its interaction with SCC rank resets, weak accepting',
        'components and original Emerson–Lei acceptance needs a proof. OWL language()',
        'annotations are suitable candidates; match_states() overapproximations and',
        'unverified HOA state-name strings are not sufficient deletion certificates.', '',
        'OWL additionally uses fixpoint availability, safety/liveness partitions,',
        'blocking and safety-progress rotation. Those rules depend on annotations;',
        'copying them onto an arbitrary elevator automaton would be unjustified.', '',
        '## Reproduction', '', '```sh',
        'python3 tests/benchmark-ldgba.py --reuse-inputs build-local/ldgba-comparison \\',
        '  --local-colours --ldgba-pruning --artifacts build-local/ldgba-packed-pruning \\',
        '  --csv tests/ltl-ldgba-packed-pruning.csv',
        'python3 tests/benchmark-slaa.py --tool PATH_TO_LTL3TELA --ldgba-pruning \\',
        '  --modes cola_ldgba cola_combined --artifacts build-local/ldgba-optimized-integrated \\',
        '  --csv tests/ltl-ldgba-optimized-integrated.csv',
        'python3 tests/summarize-ldgba-pruning.py', '```', '',
        'For cache-only omit both raw flags; for packed-only omit --ldgba-pruning.',
        'Repeat the integrated command with --ldgba-portfolio and distinct output',
        'paths to reproduce the polarity control.',
        'Use distinct artifact/CSV paths for each ablation. JSON manifests identify',
        'the measured sources, binaries and replay inputs; the original raw campaign',
        'keeps its historical provenance.', '',
        '[TACAS 2017 full paper](https://arxiv.org/html/1701.06103v1),',
        '[OWL ranking source](https://github.com/owl-toolkit/owl/blob/632c2da3ec982cdda340305afb9a3ddf45000491/src/main/java/owl/translations/ltl2dpa/AsymmetricDPAConstruction.java).', '']
    Path('tests/ltl-ldgba-pruning-report.md').write_text('\n'.join(lines))
    tex = [r'\subsection{LDGBA pruning controls}',
        'Three retained-input campaigns contain 3405 rows, with identical OWL',
        'intermediates and separate cache, colour-packing and wider-pruning controls.',
        'On the fixed original 219-formula common cohort the completed state totals are',
        r'\begin{center}\begin{tabular}{lrr}',
        r'Route & Original & Optimised\\\hline']
    for v, label in zip(variants + ['owl_tacas_dpa'],
            ['SEJK16 GBA', 'EKS20 GBA', 'SEJK16 BA', 'EKS20 BA', 'OWL TACAS DPA']):
        sums = [sum(int(d[case, v]['states']) for case in cohort) for d in (data[0], data[-1])]
        tex += [f'{label} & {sums[0]} & {sums[1]}' + r'\\']
    tex += [r'\end{tabular}\end{center}',
        'There are no paired successful state-count losses. Five historical capacity',
        'failures recover without changing the installed 32-set Spot build. The four',
        'historical BA backend timeouts remain explicit. Missing retained frontend',
        'outputs are unavailable inputs, not newly measured frontend timeouts.',
        'Colour packing alone changes no paired successful final state count.',
        'All completed boundaries pass independent language checks.', '',
        'Two integrated controls contain 908 checked outputs. Wider pruning alone',
        'does not change the final portfolio counts. Adding negative-formula LDGBA',
        'candidates improves ten LDGBA-only cases, reducing the total from 1350 to',
        '1337 states. The stronger combined portfolio remains at 1336 states over',
        'all 227 formulas and 984 over the common 222. Thus the raw gains improve',
        'the isolated construction without a new state-count gain for the strongest',
        'portfolio. These measurements do not certify the language-basis hypotheses',
        'of the preceding counting contract. Timings are diagnostic only.', '']
    Path('research/ldgba-experiments.tex').write_text('\n'.join(tex))


if __name__ == '__main__':
    main()
