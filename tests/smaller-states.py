#!/usr/bin/env python3
"""Checked smaller candidates beat broad fragment/X-advice early returns."""
import os
from pathlib import Path
import subprocess
import tempfile


def main():
    ltld = os.environ.get('LTLD', './ltl2dela')
    cases = [
        ('dwyer45', 'G(!a | ((!b | X(!c U (d & Fe)) | X(c R !d)) U (c | G(!b | X(!c U (d & Fe)) | X(c R !d)))))', 6, 17),
        ('pelanek7', 'G(!a | (!b U (b U (!b & (c R !b)))))', 5, 9)]
    checked = 0
    with tempfile.TemporaryDirectory(prefix='cola smaller ') as temporary:
        directory = Path(temporary)
        tool = directory / 'frontend'
        for name, formula, small, strict in cases:
            fixture = Path(__file__).resolve().parent / 'smaller-state-cases' / (name + '.hoa')
            tool.write_text('#!/usr/bin/env python3\nfrom pathlib import Path\nprint(Path(' + repr(str(fixture)) + ').read_text())\n')
            tool.chmod(0o700)
            reference = directory / 'reference.hoa'
            reference.write_text(subprocess.check_output(['ltl2tgba', '-D', '-G', '-f', formula], text=True))
            for flags, expected in [((), small), (('--specialized-first',), strict),
                                    (('--slaa-state-limit=0',), strict)]:
                result = subprocess.run([ltld, '--stats', '--slaa-tool=' + str(tool),
                    *flags, '-f', formula], text=True, capture_output=True, check=True, timeout=30)
                output = directory / 'output.hoa'
                output.write_text(result.stdout)
                subprocess.run(['autfilt', '-q', str(output), '--is-deterministic',
                    '--equivalent-to=' + str(reference)], check=True)
                count = subprocess.check_output(['autfilt', str(output), '--complete',
                    '--remove-unreachable-states', '--stats=%s'], text=True)
                assert int(count.strip()) == expected, (name, flags, count)
                if not flags:
                    assert '  SLAA components: 1\n' in result.stderr, result.stderr
                checked += 1
        # Exact direct monitors retain priority under either policy.
        tool.write_text('#!/usr/bin/env python3\nraise SystemExit(7)\n')
        for formula in ['GF a', 'FG a', 'GF(a & X X b)', 'FG(!a | X X !b)']:
            result = subprocess.run([ltld, '--stats', '--slaa-tool=' + str(tool),
                '--ldgba-tool=' + str(tool), '-f', formula], text=True,
                capture_output=True, check=True, timeout=30)
            assert '  SLAA attempts: 0\n' in result.stderr, result.stderr
            assert '  LDGBA attempts: 0\n' in result.stderr, result.stderr
            checked += 1
    print(checked, 'smaller-state candidate and monitor-priority regressions passed')


if __name__ == '__main__':
    main()
