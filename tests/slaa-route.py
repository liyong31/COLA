#!/usr/bin/env python3
"""Semantic tests for isolated frontend admission, failures, and fast paths."""
import os
from pathlib import Path
import subprocess
import tempfile


def main():
    ltld = os.environ.get('LTLD', './ltl2dela')
    formula = 'F(a & X b)'
    checked = 0
    with tempfile.TemporaryDirectory(prefix='cola slaa tests ') as temp:
        directory = Path(temp)
        tool = directory / 'front end'
        output, reference = directory / 'actual.hoa', directory / 'reference.hoa'
        reference.write_text(subprocess.check_output(['ltl2tgba', '-D', '-G', '-f', formula], text=True))

        def check(body, expected, flags=(), text=formula):
            nonlocal checked
            tool.write_text('#!/usr/bin/env python3\nimport os, sys, time\n' + body + '\n')
            tool.chmod(0o700)
            result = subprocess.run([ltld, '--stats', '--slaa-tool=' + str(tool),
                *flags, '-f', text], capture_output=True, text=True, timeout=20, check=True)
            output.write_text(result.stdout)
            target = reference
            if text != formula:
                target = directory / 'other.hoa'
                target.write_text(subprocess.check_output(['ltl2tgba', '-D', '-G', '-f', text], text=True))
            subprocess.run(['autfilt', '-q', str(output), '--equivalent-to=' + str(target)],
                           check=True, timeout=20)
            metrics = subprocess.check_output(['autfilt', str(output), '--stats=%d'], text=True)
            assert metrics.strip() == '1'
            for key, count in expected.items():
                assert f'  {key}: {count}\n' in result.stderr, result.stderr
            checked += 1

        correct = ("assert sys.argv[1:7] == ['-D0','-b0','-n0','-l0','-t0','-p2']\n"
                   "os.execvp('ltl2tgba', ['ltl2tgba','-D','-G','-f',sys.argv[-1]])")
        check(correct, {'SLAA candidates': 1, 'SLAA frontend failures': 0})
        # A genuine nondeterministic co-Buchi intermediate for F(a & X b).
        # This exercises the complete admission -> native ELA backend gate.
        co_buchi = ('HOA: v1\nStates: 3\nStart: 0\nAP: 2 "a" "b"\n'
                    'Acceptance: 1 Fin(0)\n--BODY--\nState: 0\n[t] 0 {0}\n'
                    '[0] 1 {0}\nState: 1\n[1] 2\nState: 2\n[t] 2\n--END--\n')
        check('print(' + repr(co_buchi) + ')',
              {'SLAA backend attempts': 1, 'SLAA candidates': 1, 'SLAA validation failures': 0})
        check('print("malformed HOA")', {'SLAA frontend failures': 1})
        check('raise SystemExit(7)', {'SLAA frontend failures': 1})
        check('os.kill(os.getpid(), 15)', {'SLAA frontend failures': 1})
        check('time.sleep(60)', {'SLAA frontend failures': 1}, ['--slaa-timeout-ms=30'])
        check('sys.stdout.write("x" * (9 * 1024 * 1024))', {'SLAA frontend failures': 1})
        check(correct, {'SLAA frontend failures': 1}, ['--slaa-state-limit=1'])
        check(correct, {'SLAA attempts': 0}, ['--slaa-state-limit=0'])
        check(correct, {'SLAA attempts': 0}, ['--slaa-timeout-ms=0'])
        check("os.execvp('ltl2tgba', ['ltl2tgba','-D','-G','-f','0'])",
              {'SLAA validation failures': 1, 'SLAA components': 0})
        non_elevator = 'HOA: v1\nStates: 1\nStart: 0\nAP: 0\nAcceptance: 1 Inf(0)\n--BODY--\nState: 0\n[t] 0 {0}\n[t] 0\n--END--\n'
        check('print(' + repr(non_elevator) + ')', {'SLAA non-elevator candidates': 1})
        response = ('HOA: v1\nStates: 2\nStart: 0\nAP: 2 "a" "b"\n'
                    'Acceptance: 2 Fin(0)&Inf(1)\n--BODY--\nState: 0\n'
                    '[!0|1] 0 {1}\n[!0|1] 0 {0 1}\n[0&!1] 1\n[0&!1] 1 {0}\n'
                    'State: 1\n[1] 0 {1}\n[1] 0 {0 1}\n[!1] 1\n[!1] 1 {0}\n--END--\n')
        check('print(' + repr(response) + ')', {'SLAA non-elevator candidates': 1}, text='G(a -> F b)')
        check('print(' + repr(response) + ')',
              {'colour-choice SCCs rewritten': 1, 'colour-choice elevator repairs': 1,
               'SLAA candidates': 1, 'SLAA validation failures': 0},
              ['--colour-choice'], text='G(a -> F b)')
        check('print(' + repr(response) + ')',
              {'colour-choice SCCs rewritten': 0, 'SLAA non-elevator candidates': 1},
              ['--colour-choice', '--colour-choice-clause-limit=0'], text='G(a -> F b)')
        hard_co_buchi = ('HOA: v1\nStates: 3\nStart: 0\nAP: 2 "a" "b"\n'
            'Acceptance: 1 Fin(0)\n--BODY--\nState: 0\n[t] 0 {0}\n[0] 1 {0}\n'
            'State: 1\n[1] 2\n[t] 0 {0}\nState: 2\n[t] 2\n[t] 0 {0}\n--END--\n')
        check('print(' + repr(hard_co_buchi) + ')',
              {'co-Buchi SCCs weakified': 1, 'co-Buchi states added': 3,
               'co-Buchi elevator repairs': 1, 'SLAA candidates': 1}, ['--colour-elevator'])
        check('print(' + repr(hard_co_buchi) + ')',
              {'co-Buchi SCCs weakified': 0, 'SLAA non-elevator candidates': 1},
              ['--colour-elevator', '--cobuchi-state-limit=3'])
        check('raise SystemExit(7)', {'SLAA attempts': 0, 'Boolean GF/FG components': 1}, text='GF a')
        check('raise SystemExit(7)', {'SLAA attempts': 0, 'finite-witness monitors': 1},
              ['--finite-witness'], text='GF(a & X X b)')
        check(correct, {'SLAA frontend failures': 1}, ['--slaa-tool=' + str(directory / 'missing')])
        check(correct, {'SLAA attempts': 2, 'SLAA negative candidates': 1}, ['--slaa-portfolio'])
        # Failure of either polarity must retain the other valid candidate.
        check("if sys.argv[-1].startswith('!'): raise SystemExit(7)\n" + correct,
              {'SLAA frontend failures': 1, 'SLAA candidates': 1, 'SLAA negative candidates': 0},
              ['--slaa-portfolio'])
        check("if not sys.argv[-1].startswith('!'): raise SystemExit(7)\n" + correct,
              {'SLAA frontend failures': 1, 'SLAA negative candidates': 1,
               'SLAA negative components': 1}, ['--slaa-portfolio'])
        # G !a is a partial one-state negative automaton for F a. Acceptance
        # complement without completion would incorrectly lose words with a.
        check(correct, {'SLAA negative candidates': 1}, ['--slaa-portfolio'], text='F a')
        check(correct, {'SLAA attempts': 0}, ['--slaa-portfolio', '--slaa-timeout-ms=0'])
        check('raise SystemExit(7)', {'SLAA attempts': 0, 'Boolean GF/FG components': 1},
              ['--slaa-portfolio'], text='GF a')
        check('raise SystemExit(7)', {'SLAA attempts': 0, 'finite-witness monitors': 1},
              ['--slaa-portfolio', '--finite-witness'], text='GF(a & X X b)')
    print(checked, 'SLAA admission/fallback semantic regressions passed')


if __name__ == '__main__':
    main()
