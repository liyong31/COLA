#!/usr/bin/env python3
"""Measure integrated SLAA routing and the raw SLAA/TELA elevator boundary."""
import argparse
import csv
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import subprocess


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--tool', type=Path, required=True)
    ap.add_argument('--ltld', default='build-local/.libs/ltl2dela')
    ap.add_argument('--driver', default='build-local/tests/.libs/tela-elevator-driver')
    ap.add_argument('--owl', type=Path, default=Path('build-local/external/owl-21.0/bin/owl'))
    ap.add_argument('--artifacts', type=Path, default=Path('build-local/slaa-comparison'))
    ap.add_argument('--csv', type=Path, default=Path('tests/ltl-slaa-results.csv'))
    ap.add_argument('--modes', nargs='+', choices=['cola_current', 'cola_slaa',
                    'cola_slaa_portfolio', 'cola_ldgba', 'cola_combined', 'tela_elevator'],
                    default=['cola_current', 'cola_slaa', 'tela_elevator'])
    args = ap.parse_args()
    spec = importlib.util.spec_from_file_location('comparison',
        Path(__file__).with_name('compare-ltl-sizes.py'))
    comparison = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(comparison)
    env = dict(os.environ, DYLD_LIBRARY_PATH=str(Path('build-local/src/.libs').resolve()))
    with open('tests/ltl-fragment-results.csv') as source:
        baseline = [r for r in csv.DictReader(source) if r['tool'] == 'cola']
    routes = ['SLAA attempts', 'SLAA frontend failures', 'SLAA non-elevator candidates',
              'SLAA validation failures', 'SLAA backend attempts', 'SLAA candidates', 'SLAA components',
              'SLAA negative attempts', 'SLAA negative candidates', 'SLAA negative components',
              'SLAA formula candidates', 'SLAA formula components', 'SLAA formula failures',
              'LDGBA attempts', 'LDGBA frontend/construction failures', 'LDGBA rejected candidates',
              'LDGBA backend attempts', 'LDGBA validation failures', 'LDGBA candidates', 'LDGBA components',
              'LDGBA cache hits', 'LDGBA budget skips']
    fields = ['case', 'sources', 'formula', 'tool', 'status', 'states', 'edges', 'colours',
              'elapsed_ms', 'old_states', 'input_states', 'input_colours', 'input_deterministic',
              'input_equivalent', 'detail'] + routes
    rows = []
    args.artifacts.mkdir(parents=True, exist_ok=True)
    for index, previous in enumerate(baseline, 1):
        directory = args.artifacts / previous['case']
        directory.mkdir(exist_ok=True)
        for mode in args.modes:
            row = dict.fromkeys(fields, '')
            row.update({key: previous[key] for key in ['case', 'sources', 'formula']})
            row.update(tool=mode, old_states=previous['states'], status='ok')
            output, stderr = directory / (mode + '.hoa'), directory / (mode + '.stderr')
            command = [args.ltld, '--stats']
            if mode in ['cola_slaa', 'cola_slaa_portfolio', 'cola_combined']:
                command += ['--slaa-tool=' + str(args.tool.resolve())]
            if mode in ['cola_slaa_portfolio', 'cola_combined']: command += ['--slaa-portfolio']
            if mode in ['cola_ldgba', 'cola_combined']:
                command += ['--ldgba-tool=' + str(args.owl.resolve())]
            command += ['-f', row['formula']]
            try:
                if mode == 'tela_elevator':
                    source = directory / 'input.tela.hoa'
                    code, elapsed = comparison.execute([str(args.tool.resolve()), '-D0', '-b0',
                        '-n0', '-l0', '-t0', '-p2', '-f', row['formula']], source,
                        directory / 'frontend.stderr', 5, env)
                    if code:
                        row.update(status='frontend-timeout' if code == 'timeout' else 'frontend-error',
                                   detail=str(code), elapsed_ms=round(elapsed, 3))
                        raise RuntimeError('frontend')
                    metrics = directory / 'input.stats'
                    code, _ = comparison.execute(['autfilt', str(source), '--stats=%s,%a,%d'],
                        metrics, directory / 'input.metrics.stderr', 30, env)
                    if code: raise ValueError('input metrics failed')
                    states, colours, deterministic = metrics.read_text().strip().split(',')
                    row.update(input_states=states, input_colours=colours,
                               input_deterministic=deterministic)
                    command = [args.driver, str(source), row['formula']]
                code, elapsed = comparison.execute(command, output, stderr, 30, env)
                row['elapsed_ms'] = round(elapsed, 3)
                diagnostic = stderr.read_text(errors='replace')
                for key in routes:
                    for line in diagnostic.splitlines():
                        if line.strip().startswith(key + ': '): row[key] = int(line.split(': ')[1])
                if mode == 'tela_elevator':
                    row['input_equivalent'] = int('input-equivalent: 1' in diagnostic)
                if code:
                    row['status'] = ('timeout' if code == 'timeout' else
                        {2: 'non-elevator', 3: 'frontend-inequivalent', 4: 'backend-inequivalent',
                         5: 'input-budget', 6: 'backend-error'}.get(code, 'error')
                        if mode == 'tela_elevator' else 'translation-error')
                    row['detail'] = diagnostic[-400:].strip()
                    raise RuntimeError('translation')
                metrics = directory / (mode + '.stats')
                code, _ = comparison.execute(['autfilt', str(output), '--complete',
                    '--remove-unreachable-states', '--stats=%s,%e,%a,%d,%p'], metrics,
                    metrics.with_name(metrics.name + '.stderr'), 30, env)
                if code: raise ValueError('output metrics failed')
                states, edges, colours, deterministic, total = map(int, metrics.read_text().strip().split(','))
                if deterministic != 1 or total != 1: raise ValueError('output not deterministic/complete')
                row.update(states=states, edges=edges, colours=colours)
                reference = Path('build-local/owl-comparison') / row['case'] / (previous['reference_tool'] + '.hoa')
                code, _ = comparison.execute(['autfilt', '-q', str(output), '--equivalent-to=' + str(reference)],
                    directory / (mode + '.equivalence.stdout'), directory / (mode + '.equivalence.stderr'), 30, env)
                if code: raise ValueError('reference equivalence failed: ' + str(code))
                if mode == 'cola_current' and states != int(previous['states']):
                    raise ValueError('default state count changed')
            except RuntimeError:
                pass
            except ValueError as error:
                row.update(status='validation-failed', detail=str(error))
            rows.append(row)
            temporary = args.csv.with_suffix('.csv.tmp')
            with temporary.open('w', newline='') as out:
                writer = csv.DictWriter(out, fields, lineterminator='\n')
                writer.writeheader()
                writer.writerows(rows)
            temporary.replace(args.csv)
        print(index, previous['sources'], [(r['tool'], r['status'], r['states'])
                                         for r in rows[-len(args.modes):]], flush=True)
    paths = [Path(args.ltld), Path(args.driver), args.tool,
             Path('build-local/src/.libs/libcola.0.dylib'), Path('tests/ltl-fragment-results.csv')]
    if any(m in ['cola_ldgba', 'cola_combined'] for m in args.modes): paths.append(args.owl)
    # Hash measured sources, not unrelated documentation being edited while
    # the campaign runs. Build metadata and reports do not affect the route.
    paths += [Path(p) for p in subprocess.check_output(['git', 'diff', '--name-only'], text=True).splitlines()
              if p.startswith('src/')]
    paths += [Path(p) for p in ['src/slaa_frontend.cpp', 'src/slaa_frontend.hpp',
        'tests/tela-elevator-driver.cpp', 'tests/generic-elevator.cpp',
        'tests/slaa-route.py', 'tests/benchmark-slaa.py']]
    manifest = {'base_commit': subprocess.check_output(['git', 'rev-parse', 'HEAD'], text=True).strip(),
                'environment': 'tests/ltl-fragment-environment.json',
                'sha256': {str(p): hashlib.sha256(p.read_bytes()).hexdigest() for p in paths},
                'frontend_flags': ['-D0', '-b0', '-n0', '-l0', '-t0', '-p2'],
                'modes': args.modes,
                'frontend_timeout_seconds': 5, 'integrated_input_state_limit': 256,
                'outer_timeout_seconds': 30,
                'raw_driver_codes': {'2': 'non-elevator', '3': 'frontend-inequivalent',
                    '4': 'backend-inequivalent', '5': 'input-budget', '6': 'backend-error'}}
    args.csv.with_suffix('.json').write_text(json.dumps(manifest, indent=2) + '\n')
    assert len(rows) == len(baseline) * len(args.modes)
    assert all(r['status'] == 'ok' for r in rows if r['tool'] != 'tela_elevator')
    assert not any(r['status'] in {'backend-inequivalent', 'validation-failed'} for r in rows)


if __name__ == '__main__':
    main()
