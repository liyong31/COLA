#!/usr/bin/env python3
"""Build a controlled macOS before/after routing ablation using identical other objects."""
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess


def main():
    before = 'cc2dc27634fd187758051275ad2a0175468991dd'
    after = '2c83c3c7aad4b56df0b22aa6c33b796d60066655'
    directory = Path('build-local/routing-ablation').resolve()
    directory.mkdir(parents=True, exist_ok=True)
    changed = subprocess.check_output(['git', 'diff', '--name-only', before, after, '--', 'src'], text=True).splitlines()
    assert changed == ['src/ltl2dela.cpp'], changed
    source = subprocess.check_output(['git', 'show', after + ':src/ltl2dela.cpp'])
    assert source == Path('src/ltl2dela.cpp').read_bytes()
    previous = directory / 'before-ltl2dela.cpp'
    previous.write_bytes(subprocess.check_output(['git', 'show', before + ':src/ltl2dela.cpp']))
    for variant in ['before', 'after']:
        (directory / variant).mkdir(exist_ok=True)
        shutil.copy2('build-local/.libs/ltl2dela', directory / variant / 'ltl2dela')
    shutil.copy2('build-local/src/.libs/libcola.0.dylib', directory / 'after/libcola.0.dylib')
    objects = sorted(Path('build-local/src/.libs').glob('*.o'))
    assert len(objects) == 16
    compiler = ['g++', '-DHAVE_CONFIG_H', '-Ibuild-local', '-Isrc', '-I/usr/local/include',
                '-g', '-O2', '-std=c++17', '-fno-common', '-fPIC', '-DPIC', '-c', str(previous),
                '-o', str(directory / 'before-ltl2dela.o')]
    linker = ['g++', '-dynamiclib', '-Wl,-undefined', '-Wl,dynamic_lookup', '-Wl,-no_fixup_chains',
              '-o', str(directory / 'before/libcola.0.dylib')]
    linker += [str(directory / 'before-ltl2dela.o') if p.name == 'ltl2dela.o' else str(p) for p in objects]
    linker += ['-L/usr/local/lib', '-lspot', '-lbddx', '-g', '-O2', '-install_name',
               '/usr/local/lib/libcola.0.dylib', '-compatibility_version', '1', '-current_version', '1.0']
    commands = [compiler, linker]
    with (directory / 'build.log').open('w') as log:
        for command in commands:
            subprocess.run(command, stdout=log, stderr=subprocess.STDOUT, check=True)
    measured = [*objects, previous, Path('src/ltl2dela.cpp'), Path(__file__)]
    for variant in ['before', 'after']:
        measured += [directory / variant / 'ltl2dela', directory / variant / 'libcola.0.dylib']
        result = subprocess.run([str(directory / variant / 'ltl2dela'), '--version'], text=True,
            capture_output=True, check=True,
            env=dict(os.environ, DYLD_LIBRARY_PATH=str(directory / variant)))
        print(variant, result.stdout.strip())
    (directory / 'build.json').write_text(json.dumps({'before_commit': before, 'after_commit': after,
        'method': 'Only ltl2dela.cpp differs in production sources. Recompile that file for before; reuse identical other objects and executable. Isolate both runtime libraries using DYLD_LIBRARY_PATH.',
        'commands': commands, 'sha256': {str(p): hashlib.sha256(p.read_bytes()).hexdigest() for p in measured}}, indent=2) + '\n')


if __name__ == '__main__':
    main()
