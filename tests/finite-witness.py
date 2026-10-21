#!/usr/bin/env python3
"""Independent equivalence regressions and reproducible reset-path benchmark.

PATH must contain Spot's ltl2tgba and autfilt. Each timed run starts a fresh
process; the reported median includes process startup and HOA serialisation.
"""
import argparse
import csv
import os
import random
import re
from pathlib import Path
import statistics
import subprocess
import tempfile
import time

CASES = [
    ('flat_fast', 'GF(c & (a U b))'),
    ('boolean_fast', 'GF a'),
    ('nested_x', 'GF(a & X X b)'),
    ('next_contradiction', 'GF(a & X (b & !b))'),
    ('next_true', 'GF(a & X X 1)'),
    ('nested_f', 'GF(a & X (b & F(c & X d)))'),
    ('nested_u', 'GF(a & (b U (c & X(d U e))))'),
    ('nested_m', 'GF(a & (b M (c | X(d M e))))'),
    ('correlated', 'GF(a & (b U c) & (d U e))'),
    ('mixed', 'GF(a & X((b U c) & (d M (e | F f))))'),
    ('dual_x', 'FG(!a | X X !b)'),
    ('dual_nested', '!(GF(a & X((b U c) & (d M e))))'),
    ('dual_flat', '!(GF(c & (a U b)))'),
    ('boolean_product', 'GF(a & X X b) & !(GF(c & X(d U e)))'),
    ('stable_guard', 'GF((G z | F y) & a & X(b U c))'),
    ('overlap', 'GF(a & X(a & X !a))'),
    ('impossible', 'GF(a & !a & X b)'),
]


class CommandFailure(RuntimeError):
    def __init__(self, cmd, result):
        self.stderr = result.stderr
        super().__init__(f'Command failed ({result.returncode}): {cmd!r}\n'
                         + result.stderr)


def routing_stats(stderr):
    return [int(match.group(1)) if (match := re.search(
        r'finite-witness ' + key + r': (\d+)', stderr)) else ''
        for key in ['monitors', 'duals', 'aborts']]


def run(cmd, timeout, **kw):
    result = subprocess.run(cmd, text=True, timeout=timeout,
                            stdout=subprocess.PIPE, stderr=subprocess.PIPE, **kw)
    if result.returncode:
        raise CommandFailure(cmd, result)
    return result


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--ltld', default=os.environ.get('LTLD', './ltl2dela'))
    ap.add_argument('--csv', help='write benchmark measurements')
    ap.add_argument('--state-limit', type=int, default=256)
    ap.add_argument('--repeats', type=int, default=3)
    ap.add_argument('--stress', type=int, default=0,
                    help='include X-window family up to this depth')
    ap.add_argument('--random-cases', type=int, default=0,
                    help='additional seeded nested co-safety kernels and duals')
    ap.add_argument('--timeout', type=float, default=30)
    args = ap.parse_args()
    if args.repeats < 1 or args.state_limit < 0 or args.timeout <= 0:
        ap.error('repeats and timeout must be positive; state-limit must be nonnegative')
    cases = CASES + [(f'window_{k}', 'GF(a & ' + 'X '*k + 'b)')
                     for k in range(3, args.stress+1)]
    cases += [(f'until_width_{k}', 'GF(t & ' + ' & '.join(
        f'(g{i} U h{i})' for i in range(k)) + ')')
        for k in range(2, min(args.stress, 5)+1)]
    rng = random.Random(20261020)
    def kernel(depth):
        if depth == 0:
            return rng.choice(['a', 'b', '!a', '!b', '0', '1'])
        op = rng.choice(['X', 'F', 'U', 'M', '&', '|'])
        if op in ['X', 'F']:
            return op + '(' + kernel(depth-1) + ')'
        return '(' + kernel(depth-1) + ' ' + op + ' ' + kernel(depth-1) + ')'
    for i in range(args.random_cases):
        f = 'GF(a & ' + kernel(3) + ')'
        cases.extend([(f'random_{i}', f), (f'random_dual_{i}', '!(' + f + ')')])
    rows = []
    def save_results():
        if args.csv:
            with open(args.csv, 'w', newline='') as f:
                writer = csv.writer(f)
                writer.writerow(['case', 'formula', 'mode', 'states', 'edges',
                                 'colours', 'median_ms', 'status',
                                 'witness_monitors', 'witness_duals', 'witness_aborts'])
                writer.writerows(rows)

    with tempfile.TemporaryDirectory() as tmp:
        for name, formula in cases:
            scaling = name.startswith(('window_', 'until_width_'))
            ref = Path(tmp)/'spot.hoa'
            paths = {}
            for mode, command in [
                ('baseline', [args.ltld]),
                ('reset', [args.ltld, '--finite-witness',
                           '--finite-witness-state-limit='+str(args.state_limit)]),
                ('spot', ['ltl2tgba', '--deterministic', '--generic'])]:
                path = Path(tmp)/(mode+'.hoa')
                elapsed = []
                routing = ['', '', '']
                try:
                    if mode == 'reset':
                        # Diagnostics are outside the timed runs.  Do this
                        # first to retain abort counts even if fallback fails.
                        stats = run(command + ['--stats', '-f', formula], args.timeout)
                        routing = routing_stats(stats.stderr)
                    for _ in range(args.repeats):
                        start = time.perf_counter()
                        result = run(command + ['-f', formula], args.timeout)
                        elapsed.append((time.perf_counter()-start)*1000)
                    path.write_text(result.stdout)
                    metrics = run(['autfilt', str(path),
                                   '--stats=%s,%e,%a'], args.timeout).stdout.strip()
                    states, edges, colours = map(int, metrics.split(','))
                    # autfilt -q returns failure if the filter matches nothing.
                    run(['autfilt', '-q', '--is-deterministic', str(path)], args.timeout)
                    paths[mode] = path
                    rows.append([name, formula, mode, states, edges, colours,
                                 round(statistics.median(elapsed), 3), 'translated'] + routing)
                except subprocess.TimeoutExpired:
                    rows.append([name, formula, mode, '', '', '', '', 'timeout'] + routing)
                except CommandFailure as error:
                    # This is an installed Spot capacity bound, not an
                    # equivalence failure.  Required regressions still fail.
                    if not scaling or 'Too many acceptance sets used.' not in error.stderr:
                        raise
                    if mode == 'reset':
                        routing = routing_stats(error.stderr)
                    rows.append([name, formula, mode, '', '', '', '',
                                 'acceptance-limit'] + routing)
                save_results()
            if not scaling and len(paths) != 3:
                raise RuntimeError('Required regression timed out: ' + name)
            if paths and 'spot' not in paths:
                raise RuntimeError('No independent reference for: ' + name)
            for mode, path in paths.items():
                if 'spot' in paths:
                    run(['autfilt', '-q', str(path), '--equivalent-to='+str(ref)],
                        args.timeout)
                    next(r for r in rows if r[0] == name and r[2] == mode)[7] = 'ok'
            if 'spot' in paths and not scaling:
                # Both budget fallbacks and bypassing fast paths preserve language.
                for option in ['--finite-witness-state-limit=0',
                               '--finite-witness-work-limit=0',
                               '--finite-witness-state-limit=1',
                               '--finite-witness-work-limit=1',
                               '--no-recurrence']:
                    result = run([args.ltld, '--finite-witness', option, '-f', formula],
                                 args.timeout)
                    fallback = Path(tmp)/'fallback.hoa'
                    fallback.write_text(result.stdout)
                    run(['autfilt', '-q', '--is-deterministic', str(fallback),
                         '--equivalent-to='+str(ref)], args.timeout)
            print(name, ':', ', '.join(f'{r[2]}={r[3]} states/{r[6]} ms ({r[7]})'
                                       for r in rows if r[0] == name), flush=True)
            save_results()
        # Check routing, so equivalence cannot pass with a silently unused feature.
        for name, formula, expected in [
            ('reset', 'GF(a & X X b)', 'finite-witness monitors: 1'),
            ('dual', 'FG(!a | X X !b)', 'finite-witness duals: 1'),
            ('fast', 'GF(c & (a U b))', 'flat-Until monitors: 1')]:
            result = run([args.ltld, '--finite-witness', '--stats', '-f', formula],
                         args.timeout)
            assert expected in result.stderr, (name, result.stderr)
        for option in ['--finite-witness-state-limit=0',
                       '--finite-witness-work-limit=0',
                       '--finite-witness-state-limit=1',
                       '--finite-witness-work-limit=1']:
            result = run([args.ltld, '--finite-witness', option,
                          '--stats', '-f', 'GF(a & X X b)'], args.timeout)
            monitors, duals, aborts = routing_stats(result.stderr)
            # Existing profile exploration can retry the bounded construction
            # on multiple residuals; every abandoned attempt is counted.
            assert aborts >= 1 and monitors == 0 and duals == 0, result.stderr
    save_results()
    print('Finite-witness equivalence and routing regressions passed; '
          + str(sum(r[7] == 'timeout' for r in rows)) + ' timed-out benchmark runs; '
          + str(sum(r[7] == 'acceptance-limit' for r in rows))
          + ' benchmark runs exceeded the installed acceptance-set limit.')


if __name__ == '__main__':
    main()
