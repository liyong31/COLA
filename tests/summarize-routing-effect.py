#!/usr/bin/env python3
"""Summarize the matched routing ablation without mixing policies or cohorts."""
import csv
import json
from pathlib import Path
import statistics


def main():
    rows = list(csv.DictReader(open('tests/routing-effect-results.csv')))
    assert len(rows) == 1816 and all(r['status'] == 'ok' for r in rows)
    data = {(r['case'], r['config'], r['route']): r for r in rows}
    cases = sorted({r['case'] for r in rows})
    configs = ['default', 'finite_witness', 'portfolio', 'finite_witness_portfolio']
    build = json.loads(Path('tests/routing-effect-results.json').read_text())['build']
    lines = ['# Effect of specialized-first routing', '',
        'Both implementation PRs were merged on 23 October 2026 into `ltl2dela`:',
        '[PR #2](https://github.com/liyong31/COLA/pull/2) and',
        '[PR #3](https://github.com/liyong31/COLA/pull/3).',
        'The final merge is `178da6c148323a0aa52d052ade8f97899c3750a0`.', '',
        'Strict specialized priority substantially reduces external frontend work,',
        'but gives up some state-count improvements of the previous portfolio.',
        'This is a routing-policy comparison, not a ranking of primitive algorithms.', '',
        '## Controlled build and correctness', '',
        f"Before: `{build['before_commit']}`. After: `{build['after_commit']}`.",
        'The only changed production file is `src/ltl2dela.cpp`. The old version of',
        'that file was rebuilt with the same compiler/options and linked against',
        'identical other object files. Both variants use the same executable and',
        'separate frozen runtime libraries selected through `DYLD_LIBRARY_PATH`.',
        'The native SCC determiniser, acceptance implementation, Spot installation,',
        'LTL3TELA and OWL executables are identical. Build commands and all measured',
        'hashes are recorded in the result manifest.', '',
        'All **1816 outputs** (227 formulas × four configurations × two policies)',
        'pass independent language equivalence, determinism and completeness.',
        'There are no translation/checking timeouts or language failures.', '',
        'Primary sizes count complete reachable output states without extra',
        'minimization. A second identical Spot low/generic normalization is also',
        'recorded; it is kept separate from the primary metric.', '',
        '## State counts and external calls', '',
        '| Configuration | Before states | After states | Smaller / equal / larger | Frontend calls before → after |',
        '| --- | ---: | ---: | --- | ---: |']
    totals = {}
    for config in configs:
        pairs = [(data[c, config, 'before'], data[c, config, 'after']) for c in cases]
        before = sum(int(a['states']) for a, b in pairs)
        after = sum(int(b['states']) for a, b in pairs)
        smaller = sum(int(b['states']) < int(a['states']) for a, b in pairs)
        equal = sum(b['states'] == a['states'] for a, b in pairs)
        calls = [sum(int(data[c, config, route]['SLAA attempts']) + int(data[c, config, route]['LDGBA attempts'])
                     for c in cases) for route in ['before', 'after']]
        totals[config] = {'states': [before, after], 'calls': calls}
        lines.append(f'| {config} | {before} | {after} | {smaller} / {equal} / {227-smaller-equal} | {calls[0]} → {calls[1]} |')
    lines += ['', '`default` has no external frontends. `finite_witness` enables the optional',
        'bounded reset construction. `portfolio` enables both SLAA polarities,',
        'colour/weak preprocessing, both OWL LDGBA algorithms and polarities,',
        'annotation pruning and same-input cross-SCC comparison.',
        '`finite_witness_portfolio` enables both options. All other budgets and',
        'translation settings are matched exactly.', '',
        'The state-count benefit of a generic candidate is therefore not implied',
        'by applicability of a specialized construction. The requested strict',
        'priority remains implemented: this experiment does not re-enable generic',
        'competition after specialization succeeds.', '',
        'Additional normalization totals:', '',
        '| Configuration | Before | After |', '| --- | ---: | ---: |']
    for config in configs:
        sums = [sum(int(data[c, config, route]['normalized_states']) for c in cases) for route in ['before', 'after']]
        lines.append(f'| {config} | {sums[0]} | {sums[1]} |')
    lines += ['', 'Largest portfolio state increases:', '',
        '| Formula source | Before | After | Increase |', '| --- | ---: | ---: | ---: |']
    changes = sorted([(int(data[c, 'portfolio', 'after']['states']) - int(data[c, 'portfolio', 'before']['states']), c)
                      for c in cases], reverse=True)
    for increase, case in changes[:10]:
        if increase <= 0:
            continue
        a, b = data[case, 'portfolio', 'before'], data[case, 'portfolio', 'after']
        lines.append(f"| {a['sources']} | {a['states']} | {b['states']} | {increase} |")
    lines += ['', 'The two largest losses expose different previously winning routes:',
        'Liberouter36 used an LDGBA result (34 states), whereas Dwyer45 used an',
        'SLAA result (six states). Both now return from the recognized-fragment',
        'route (50 and 17 states). That broad route invokes the existing Spot',
        'deterministic Low/High translation; syntactic class membership alone is',
        'not a certificate that a dedicated fragment construction was selected',
        'inside Spot. Tightening this distinction is a useful follow-up, without',
        'overriding successful direct monitors or checked DBA/DCA constructions.', '',
        '## Serial timing controls', '',
        'The full corpus used two workers; its single-run timings are descriptive',
        'and are not used as a runtime ranking. After it finished, seven selected',
        'formulas were timed serially, with three repetitions and randomly',
        'interleaved before/after order. Every run starts fresh translator and',
        'frontend processes. The timer excludes subsequent validation and metric',
        'extraction. All repeated output state counts match the corpus campaign.', '',
        '| Formula source | Default before / after (ms) | Portfolio before / after (ms) |',
        '| --- | ---: | ---: |']
    timed = list(csv.DictReader(open('tests/routing-effect-serial.csv')))
    assert len(timed) == 84 and all(r['status'] == 'ok' for r in timed)
    selection = json.loads(Path('tests/routing-effect-serial.json').read_text())['selection']
    for source in selection:
        medians = []
        for config in ['default', 'portfolio']:
            medians.append(' / '.join(f'{statistics.median(float(r["elapsed_ms"]) for r in timed if source in r["sources"].split(";") and r["config"] == config and r["route"] == route):.1f}'
                                      for route in ['before', 'after']))
        lines.append(f'| {source} | {medians[0]} | {medians[1]} |')
    lines += ['', 'These selected-case medians support a local runtime tradeoff; they do not',
        'establish a full-corpus speedup or a universal performance ordering.', '',
        '## Interpretation and next work', '',
        'Keep specialized-first routing as requested. The next size optimizations',
        'should target the specialized outputs themselves, especially the cases',
        'listed above, and distinguish a merely syntactic applicability test from',
        'a construction that exploits all relevant formula constraints. General',
        'SLAA-to-elevator or limit-deterministic Emerson–Lei work remains confined',
        'to residual formulas. These results do not prove that dealternation is',
        'universally better, and do not establish the TACAS complexity bound.', '',
        '## Reproduction', '', '```sh', 'python3 tests/build-routing-ablation.py',
        'python3 tests/benchmark-routing-effect.py', 'python3 tests/time-routing-effect.py',
        'python3 tests/summarize-routing-effect.py', '```', '',
        'The build driver targets this macOS/Spot setup and requires retained',
        'objects from the current checked local build. Keep all sources and',
        'frozen binaries unchanged during measurements. Corpus runs have a',
        '30-second subprocess deadline; native candidate construction and exact',
        'checking inside COLA retain their existing bounds/limitations.', '']
    Path('tests/routing-effect-report.md').write_text('\n'.join(lines))
    print(json.dumps(totals, indent=2))


if __name__ == '__main__':
    main()
