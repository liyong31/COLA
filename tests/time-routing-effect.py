#!/usr/bin/env python3
"""Serial, interleaved timing controls after the paired corpus campaign finishes."""
import csv
import hashlib
import json
import os
from pathlib import Path
import random
import statistics
import subprocess
import time


def main():
    manifest = json.loads(Path('tests/routing-effect-results.json').read_text())
    results = list(csv.DictReader(open('tests/routing-effect-results.csv')))
    selected = ['DwyerAC98.ltl:45', 'DwyerAC98.ltl:46', 'DwyerAC98.ltl:50',
                'DwyerAC98.ltl:55', 'Parametrised.ltl:27', 'Parametrised.ltl:45', 'Liberouter04.ltl:43']
    build = Path('build-local/routing-ablation').resolve()
    directory = Path('build-local/routing-effect-serial')
    directory.mkdir(parents=True, exist_ok=True)
    fields = ['case', 'sources', 'formula', 'config', 'route', 'repeat', 'status', 'elapsed_ms', 'states']
    rows = []
    generator = random.Random(20261023)
    measured = {**manifest['sha256'], str(Path(__file__)): hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
    assert all(hashlib.sha256(Path(p).read_bytes()).hexdigest() == h for p, h in measured.items())
    for source in selected:
        for config in ['default', 'portfolio']:
            for repeat in range(3):
                routes = ['before', 'after']
                generator.shuffle(routes)
                for route in routes:
                    previous = next(r for r in results if source in r['sources'].split(';')
                                    and r['config'] == config and r['route'] == route)
                    row = {k: previous[k] for k in ['case', 'sources', 'formula', 'config', 'route']}
                    row.update(repeat=repeat, status='ok', states='')
                    env = dict(os.environ, DYLD_LIBRARY_PATH=str(build / route))
                    start = time.perf_counter_ns()
                    try:
                        result = subprocess.run([str(build / route / 'ltl2dela'), '--stats',
                            *manifest['configs'][config], '-f', previous['formula']],
                            capture_output=True, env=env, timeout=30)
                        row['elapsed_ms'] = round((time.perf_counter_ns() - start) / 1e6, 3)
                        if result.returncode:
                            row['status'] = 'translation-error'
                        else:
                            output = directory / (previous['case'] + '-' + config + '-' + route + '-' + str(repeat) + '.hoa')
                            output.write_bytes(result.stdout)
                            output.with_suffix('.stderr').write_bytes(result.stderr)
                            stats = subprocess.check_output(['autfilt', str(output), '--complete',
                                '--remove-unreachable-states', '--stats=%s'], text=True)
                            row['states'] = int(stats.strip())
                            assert row['states'] == int(previous['states'])
                    except subprocess.TimeoutExpired:
                        row.update(status='timeout', elapsed_ms=30000)
                    rows.append(row)
                    with Path('tests/routing-effect-serial.csv').open('w', newline='') as out:
                        writer = csv.DictWriter(out, fields, lineterminator='\n')
                        writer.writeheader()
                        writer.writerows(rows)
                    print(len(rows), source, config, route, row['status'], row['elapsed_ms'], flush=True)
    assert all(hashlib.sha256(Path(p).read_bytes()).hexdigest() == h for p, h in measured.items())
    assert all(r['status'] == 'ok' for r in rows)
    Path('tests/routing-effect-serial.json').write_text(json.dumps({'sha256': measured,
        'selection': selected, 'configs': ['default', 'portfolio'], 'repeats': 3,
        'seed': 20261023, 'execution': 'One process at a time, randomly interleaved before/after within each repeat; fresh translator and frontend processes.',
        'timing': 'perf_counter_ns around subprocess.run capture_output; validation and metrics excluded; no corpus benchmark running concurrently.'}, indent=2) + '\n')
    for source in selected:
        for config in ['default', 'portfolio']:
            print(source, config, {route: statistics.median(r['elapsed_ms'] for r in rows
                if source in r['sources'].split(';') and r['config'] == config and r['route'] == route)
                for route in ['before', 'after']})


if __name__ == '__main__':
    main()
