#!/usr/bin/env python3
"""Generic frontends must not run after a specialized construction succeeds."""
import os
from pathlib import Path
import subprocess
import tempfile


def main():
    ltld = os.environ.get('LTLD', './ltl2dela')
    cases = [
        ('GF a', (), 'Boolean GF/FG components'),
        ('FG a', (), 'Boolean GF/FG components'),
        ('GF(a & X X b)', (), 'specialized GF components'),
        ('FG(!a | X X !b)', (), 'specialized FG components'),
        ('GF(a & X X b)', ('--finite-witness',), 'finite-witness monitors'),
        ('FG(!a | X X !b)', ('--finite-witness',), 'finite-witness monitors'),
        ('G(a -> X b)', (), 'direct formula components'),
        ('F(a & X b)', (), 'direct formula components'),
        ('G(a -> F b)', (), 'DBA components'),
        ('G(!a | (b U (Gc | Gd)))', (), 'X-advice components'),
        # Disable syntactic routing to exercise checked recognition at the
        # residual boundary, before either external generic frontend.
        ('G(a -> F b)', ('--no-specialized',), 'DBA components'),
    ]
    with tempfile.TemporaryDirectory(prefix='cola priority ') as temporary:
        directory = Path(temporary)
        marker = directory / 'called'
        frontend = directory / 'frontend'
        frontend.write_text('#!/usr/bin/env python3\nfrom pathlib import Path\n'
                            + 'Path(' + repr(str(marker)) + ').touch()\nraise SystemExit(7)\n')
        frontend.chmod(0o700)
        for portfolio in [(), ('--slaa-portfolio', '--ldgba-portfolio')]:
            for formula, flags, route in cases:
                result = subprocess.run([ltld, '--stats', '--specialized-first', '--slaa-tool=' + str(frontend),
                    '--ldgba-tool=' + str(frontend), *portfolio, *flags, '-f', formula],
                    text=True, capture_output=True, check=True, timeout=30)
                assert not marker.exists(), (formula, result.stderr)
                assert '  SLAA attempts: 0\n' in result.stderr, result.stderr
                assert '  LDGBA attempts: 0\n' in result.stderr, result.stderr
                assert f'  {route}: 1\n' in result.stderr, result.stderr
                output, reference = directory / 'output.hoa', directory / 'reference.hoa'
                output.write_text(result.stdout)
                reference.write_text(subprocess.check_output(
                    ['ltl2tgba', '-D', '-G', '-f', formula], text=True))
                subprocess.run(['autfilt', '-q', str(output), '--is-deterministic',
                    '--equivalent-to=' + str(reference)], check=True, timeout=30)
    print(2 * len(cases), 'specialized-priority language/routing regressions passed')


if __name__ == '__main__':
    main()
