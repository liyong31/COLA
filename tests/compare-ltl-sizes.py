#!/usr/bin/env python3
"""Compare deterministic generic-acceptance translations on OWL literature LTL.

Retains HOA and stderr artifacts, checkpoints each tool, and supports resume.
Rank complete reachable automata; raw sizes are retained for comparison.
"""
import argparse
import csv
import hashlib
import json
import os
from pathlib import Path
import signal
import subprocess
import time


FIELDS = ['case', 'sources', 'formula', 'tool', 'status', 'raw_states',
          'raw_edges', 'raw_colours', 'raw_complete', 'states', 'edges',
          'colours', 'elapsed_ms', 'witness_monitors', 'witness_aborts', 'detail']


def verify_alternates(rows, artifacts, timeout, env):
    """Retain paired evidence when Spot cannot construct the reference."""
    groups = {}
    for row in rows:
        groups.setdefault(row['case'], []).append(row)
    for case, group in groups.items():
        if any(r['status'] == 'reference' for r in group):
            continue
        candidates = [r for r in group if r['status'] == 'no-reference']
        if not candidates:
            continue
        reference = candidates[0]
        reference['status'] = 'alternate-reference'
        reference['detail'] = 'Spot unavailable; reference=' + reference['tool']
        directory = artifacts / case
        for row in candidates[1:]:
            name = row['tool']
            code, _ = execute(['autfilt', '-q', str(directory / (name + '.hoa')),
                               '--equivalent-to=' + str(directory / (reference['tool'] + '.hoa'))],
                              directory / (name + '.alternate.stdout'),
                              directory / (name + '.alternate.stderr'), timeout, env)
            row['status'] = ('ok' if code == 0 else 'equivalence-timeout'
                             if code == 'timeout' else 'inequivalent'
                             if code == 1 else 'equivalence-error')
            row['detail'] = 'Spot unavailable; reference=' + reference['tool']


def execute(command, output, errors, timeout, env):
    start = time.perf_counter()
    with output.open('w') as out, errors.open('w') as err:
        process = subprocess.Popen(command, stdout=out, stderr=err, env=env,
                                   start_new_session=True)
        try:
            code = process.wait(timeout=timeout)
        except subprocess.TimeoutExpired:
            os.killpg(process.pid, signal.SIGKILL)
            process.wait()
            return 'timeout', (time.perf_counter() - start) * 1000
    return code, (time.perf_counter() - start) * 1000


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--formulas', type=Path, required=True)
    ap.add_argument('--cola', type=Path, required=True)
    ap.add_argument('--cola-library', type=Path, required=True)
    ap.add_argument('--owl', type=Path, required=True)
    ap.add_argument('--ltl3tela', type=Path, required=True)
    ap.add_argument('--csv', type=Path, required=True)
    ap.add_argument('--artifacts', type=Path, required=True)
    ap.add_argument('--timeout', type=float, default=30)
    ap.add_argument('--check-timeout', type=float, default=30)
    ap.add_argument('--resume', action='store_true')
    ap.add_argument('--limit', type=int, help='pilot: first N unique formulas')
    args = ap.parse_args()
    env = dict(os.environ, DYLD_LIBRARY_PATH=str(args.cola_library.resolve()))
    tools = {
        'spot': ['ltl2tgba', '--deterministic', '--generic'],
        'delag': [str(args.owl.resolve()), 'ltl2dela', '-t', 'MS17'],
        'ltl3tela': [str(args.ltl3tela.resolve()), '-D1'],
        'owl': [str(args.owl.resolve()), 'ltl2dela', '-t', 'SLM21'],
        'cola': [str(args.cola.resolve())],
        'cola_reset': [str(args.cola.resolve()), '--finite-witness', '--stats'],
    }
    formulas = {}
    hashes = {}
    for path in sorted(args.formulas.glob('*.ltl')):
        hashes[path.name] = hashlib.sha256(path.read_bytes()).hexdigest()
        for line, text in enumerate(path.read_text().splitlines(), 1):
            text = text.strip()
            if text and not text.startswith('#'):
                formulas.setdefault(text, []).append(f'{path.name}:{line}')
    inputs = list(formulas.items())[:args.limit]
    args.artifacts.mkdir(parents=True, exist_ok=True)
    manifest = {'tools': tools, 'formula_files_sha256': hashes,
                'timeout': args.timeout, 'check_timeout': args.check_timeout,
                'unique_formulas': len(inputs)}
    manifest_path = args.artifacts / 'commands.json'
    if args.resume:
        assert json.loads(manifest_path.read_text()) == manifest, 'Configuration changed'
        with args.csv.open() as source:
            rows = list(csv.DictReader(source))
    else:
        if args.csv.exists():
            ap.error('CSV already exists: use --resume or choose a new destination')
        manifest_path.write_text(json.dumps(manifest, indent=2) + '\n')
        rows = []
    previous = {(r['case'], r['tool']): r for r in rows}

    def checkpoint():
        temporary = args.csv.with_suffix('.csv.tmp')
        for row in rows:
            row['detail'] = row['detail'].rstrip()
        with temporary.open('w', newline='') as out:
            writer = csv.DictWriter(out, fieldnames=FIELDS, lineterminator='\n')
            writer.writeheader()
            writer.writerows(rows)
        temporary.replace(args.csv)

    for index, (formula, sources) in enumerate(inputs, 1):
        case = hashlib.sha256(formula.encode()).hexdigest()[:16]
        directory = args.artifacts / case
        directory.mkdir(exist_ok=True)
        (directory / 'formula.ltl').write_text(formula + '\n')
        reference = directory / 'spot.hoa'
        outcomes = []
        for name, command in tools.items():
            if (case, name) in previous:
                outcomes.append(name + '=' + previous[case, name]['status'])
                continue
            row = dict.fromkeys(FIELDS, '')
            row.update(case=case, sources=';'.join(sources), formula=formula, tool=name)
            path = directory / (name + '.hoa')
            stderr = directory / (name + '.stderr')
            code, elapsed = execute(command + ['-f', formula], path, stderr,
                                    args.timeout, env)
            row['elapsed_ms'] = round(elapsed, 3)
            diagnostic = stderr.read_text(errors='replace')
            if name == 'cola_reset':
                for key, column in [('monitors', 'witness_monitors'),
                                    ('aborts', 'witness_aborts')]:
                    prefix = 'finite-witness ' + key + ': '
                    for line in diagnostic.splitlines():
                        if prefix in line:
                            row[column] = int(line.split(prefix)[1])
            if code != 0:
                row['status'] = ('timeout' if code == 'timeout' else
                                 'acceptance-limit' if 'Too many acceptance sets' in diagnostic
                                 else 'translation-error')
                row['detail'] = str(code) + ': ' + diagnostic[:400]
            else:
                row['status'] = 'translated'
                for complete in [False, True]:
                    metric = directory / (name + ('.complete' if complete else '.raw') + '.stats')
                    errors = metric.with_suffix('.stderr')
                    options = ['--complete', '--remove-unreachable-states'] if complete else []
                    code, _ = execute(['autfilt', str(path)] + options +
                                      ['--stats=%s,%e,%a,%d,%p'], metric, errors,
                                      args.check_timeout, env)
                    if code != 0:
                        row['status'] = 'metrics-timeout' if code == 'timeout' else 'metrics-error'
                        row['detail'] = errors.read_text(errors='replace')[:400]
                        break
                    values = metric.read_text().strip().split(',')
                    if len(values) != 5:
                        row['status'] = 'invalid-output'
                        break
                    states, edges, colours, deterministic, is_complete = map(int, values)
                    if deterministic != 1:
                        row['status'] = 'nondeterministic'
                        break
                    if complete:
                        assert is_complete == 1
                        row.update(states=states, edges=edges, colours=colours)
                    else:
                        row.update(raw_states=states, raw_edges=edges,
                                   raw_colours=colours, raw_complete=is_complete)
                if row['status'] == 'translated':
                    if name == 'spot':
                        row['status'] = 'reference'
                    elif previous[case, 'spot']['status'] != 'reference':
                        row['status'] = 'no-reference'
                    else:
                        code, _ = execute(['autfilt', '-q', str(path),
                                           '--equivalent-to=' + str(reference)],
                                          directory / (name + '.equivalence.stdout'),
                                          directory / (name + '.equivalence.stderr'),
                                          args.check_timeout, env)
                        row['status'] = ('ok' if code == 0 else 'equivalence-timeout'
                                         if code == 'timeout' else 'inequivalent'
                                         if code == 1 else 'equivalence-error')
            rows.append(row)
            previous[case, name] = row
            checkpoint()
            outcomes.append(name + '=' + row['status'] + ':' + str(row['states']))
        print(f'{index}/{len(inputs)} {sources[0]} ' + ', '.join(outcomes), flush=True)
    verify_alternates(rows, args.artifacts, args.check_timeout, env)
    checkpoint()
    print('Campaign finished; sizes are comparable only for ok/reference/alternate-reference rows.',
          flush=True)


if __name__ == '__main__':
    main()
