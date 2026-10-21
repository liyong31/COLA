#!/usr/bin/env python3
"""Check LDGBA admission, generalized acceptance, fallback and direct priority."""
import os
from pathlib import Path
import subprocess
import tempfile


def main():
    ltld = os.environ.get('LTLD', './ltl2dela')
    formula = 'G(a -> F b)'
    checked = 0
    with tempfile.TemporaryDirectory(prefix='cola ldgba ') as temp:
        directory = Path(temp)
        tool, output, reference = [directory / name for name in ['front end', 'actual.hoa', 'reference.hoa']]

        def check(body, expected, flags=(), text=formula):
            nonlocal checked
            tool.write_text('#!/usr/bin/env python3\nimport sys,os,time\n' + body + '\n')
            tool.chmod(0o700)
            result = subprocess.run([ltld, '--stats', '--ldgba-tool=' + str(tool),
                '--ldgba-construction=SEJK16', *flags, '-f', text],
                capture_output=True, text=True, check=True, timeout=30)
            output.write_text(result.stdout)
            reference.write_text(subprocess.check_output(['ltl2tgba', '-D', '-G', '-f', text], text=True))
            subprocess.run(['autfilt', '-q', str(output), '--is-deterministic',
                '--equivalent-to=' + str(reference)], check=True, timeout=20)
            for key, count in expected.items():
                assert f'  {key}: {count}\n' in result.stderr, result.stderr
            checked += 1

        correct = ("assert sys.argv[1] == 'ltl2ldgba' and sys.argv[2] == '-t'\n"
                   "assert '--skip-translation-portfolio' in sys.argv\n"
                   "os.execvp('ltl2tgba', ['ltl2tgba','-D','-f',sys.argv[-1]])")
        check(correct, {'LDGBA candidates': 1, 'LDGBA validation failures': 0})
        # Generalized acceptance and nondeterministic prefix with a rejecting
        # branch; the accepting two-state region is closed and deterministic.
        generalized = ('HOA: v1\nStates: 4\nStart: 0\nAP: 2 "a" "b"\n'
            'Acceptance: 2 Inf(0)&Inf(1)\n--BODY--\nState: 0\n'
            '[!0|1] 1 {0 1}\n[0&!1] 2\n[t] 3\nState: 1\n'
            '[!0|1] 1 {0 1}\n[0&!1] 2\nState: 2\n[1] 1 {0 1}\n'
            '[!1] 2\nState: 3\n[t] 3\n--END--\n')
        check('print(' + repr(generalized) + ')',
              {'LDGBA backend attempts': 1, 'LDGBA candidates': 1, 'LDGBA validation failures': 0})
        check('print("invalid HOA")', {'LDGBA frontend/construction failures': 1})
        check('raise SystemExit(7)', {'LDGBA frontend/construction failures': 1})
        check('os.kill(os.getpid(),15)', {'LDGBA frontend/construction failures': 1})
        check('time.sleep(60)', {'LDGBA frontend/construction failures': 1}, ['--ldgba-timeout-ms=30'])
        check('sys.stdout.write("x"*(9*1024*1024))', {'LDGBA frontend/construction failures': 1})
        check(correct, {'LDGBA frontend/construction failures': 1}, ['--ldgba-state-limit=1'])
        check(correct, {'LDGBA attempts': 0}, ['--ldgba-state-limit=0'])
        check(correct, {'LDGBA attempts': 0}, ['--ldgba-timeout-ms=0'])
        check(correct, {'LDGBA attempts': 0}, ['--ldgba-attempt-limit=0'])
        check(correct, {'LDGBA attempts': 1, 'LDGBA candidates': 1},
              ['--ldgba-construction=both', '--ldgba-attempt-limit=1'])
        # This profile tree previously multiplied external calls and timed out.
        check('raise SystemExit(7)', {'LDGBA attempts': 2},
              ['--ldgba-construction=both', '--ldgba-attempt-limit=2'],
              text='G(!a | ((!b | (!c U (!c & d & !e & X((!c & !e) U f)))) U '
                   '(c | G(!b | (d & !e & X(!e U f))))))')
        wrong = ('HOA: v1\nStates: 1\nStart: 0\nAP: 0\nAcceptance: 1 Inf(0)\n'
                 '--BODY--\nState: 0\n[t] 0 {0}\n--END--\n')
        check('print(' + repr(wrong) + ')', {'LDGBA validation failures': 1})
        check('print(' + repr(wrong.replace('Inf(0)', 'Fin(0)')) + ')', {'LDGBA rejected candidates': 1})
        non_elevator = wrong.replace('[t] 0 {0}', '[t] 0 {0}\n[t] 0')
        check('print(' + repr(non_elevator) + ')', {'LDGBA rejected candidates': 1})
        check("if sys.argv[3] == 'SEJK16': raise SystemExit(7)\n" + correct,
              {'LDGBA attempts': 2, 'LDGBA candidates': 1, 'LDGBA frontend/construction failures': 1},
              ['--ldgba-construction=both'])
        check(correct, {'LDGBA attempts': 1, 'LDGBA candidates': 1}, ['--ldgba-construction=EKS20'])
        check(correct, {'LDGBA frontend/construction failures': 1}, ['--ldgba-tool=' + str(directory / 'missing')])
        check('raise SystemExit(7)', {'LDGBA attempts': 0, 'Boolean GF/FG components': 1}, text='GF a')
        check('raise SystemExit(7)', {'LDGBA attempts': 0, 'Boolean GF/FG components': 1}, text='FG a')
        check('raise SystemExit(7)', {'LDGBA attempts': 0, 'finite-witness monitors': 1},
              ['--finite-witness'], text='GF(a & X X b)')
        # One translator instance must reset cache and call budget for each
        # formula in a batch, including repeated identical formulas.
        tool.write_text('#!/usr/bin/env python3\nimport sys,os,time\n' + correct + '\n')
        batch = directory / 'formulas.ltl'
        batch.write_text(formula + '\n' + formula + '\n')
        result = subprocess.run([ltld, '--stats', '--ldgba-tool=' + str(tool),
            '--ldgba-attempt-limit=1', '-F', str(batch)],
            capture_output=True, text=True, check=True, timeout=30)
        assert result.stderr.count('  LDGBA attempts: 1\n') == 2, result.stderr
        output.write_text(result.stdout)
        reference.write_text(subprocess.check_output(['ltl2tgba', '-D', '-G', '-f', formula], text=True))
        count = subprocess.check_output(['autfilt', str(output), '--count', '--is-deterministic',
            '--equivalent-to=' + str(reference)], text=True, timeout=20)
        assert count.strip() == '2', count
        checked += 1
        bad = subprocess.run([ltld, '--ldgba-construction=invalid', '-f', formula],
                             capture_output=True, text=True)
        assert bad.returncode != 0 and 'invalid LDGBA construction' in bad.stderr
        checked += 1
    print(checked, 'LDGBA semantic admission/fallback regressions passed')


if __name__ == '__main__':
    main()
