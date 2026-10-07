"""The developer evaluator: its semantics in a bare SBCL, its client, and (opt-in) real ACL2 admission.

The wire path (`fn operator CONFIG eval` over the control socket, admission in books, the logged
begin/end lines, the journal entry) is tests/dev_repl_native.py and tests/test_developer_eval_native.py
against a developer image; the book's side is tests/acl2/developer-eval-tests.lisp.
"""
import os
from pathlib import Path
import shutil
import stat
import subprocess
import sys
import tempfile
import unittest
from unittest import mock

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'tools'))
import fn_dev

SERVER_SIDE = ';;; The server side'


def evaluation_half():
    """host/native/developer-eval.lisp before its server side: the evaluator and its helpers."""
    text = (ROOT / 'host/native/developer-eval.lisp').read_text()
    assert SERVER_SIDE in text
    return text.split(SERVER_SIDE)[0]


class DeveloperEvaluator(unittest.TestCase):
    @unittest.skipUnless(shutil.which('sbcl'), 'SBCL required')
    def test_one_form_bounded_output_and_errors(self):
        with tempfile.TemporaryDirectory() as directory:
            d = Path(directory)
            (d / 'evaluation.lisp').write_text(evaluation_half())
            fixture = (ROOT / 'tests/fixtures/dev_repl.lisp').read_text()
            (d / 'run.lisp').write_text(
                fixture.replace('__TRACE__', str(ROOT / 'host/native/trace.lisp'))
                       .replace('__EVAL__', str(d / 'evaluation.lisp')))
            result = subprocess.run([shutil.which('sbcl'), '--noinform', '--disable-debugger',
                                     '--script', str(d / 'run.lisp')],
                                    capture_output=True, text=True, timeout=120)
            self.assertIn('DEV-EVAL-FIXTURE-PASS', result.stdout, result.stdout + result.stderr)
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)

    def test_the_listener_and_its_selector_are_gone(self):
        source = (ROOT / 'host/native/developer-eval.lisp').read_text()
        for gone in ('fnn-dev-repl-start', 'fnn-dev-repl-stop', 'fnn-dev-repl-close',
                     'fnn-dev-listen', 'fnn-dev-repl-loop', 'FN_NATIVE_DEV_REPL',
                     'sb-bsd-sockets:socket-listen'):
            self.assertNotIn(gone, source)
        self.assertFalse((ROOT / 'host/native/dev-repl.lisp').exists())
        io = (ROOT / 'host/native/io.lisp').read_text()
        self.assertNotIn('FN_NATIVE_DEV_REPL', io)

    @unittest.skipUnless(os.environ.get('FN_DEV_REPL_ACL2') == '1', 'opt-in real ACL2 execution')
    def test_actual_acl2_admission_and_refusal(self):
        with tempfile.TemporaryDirectory() as directory:
            d = Path(directory)
            events = d / 'events.lisp'
            events.write_text((ROOT / 'host/native/trace.lisp').read_text() + '\n'
                              + evaluation_half() + '\n'
                              + (ROOT / 'tests/fixtures/dev_repl_acl2.lisp').read_text())
            driver = (':q\n(setf sb-ext:*invoke-debugger-hook* '
                      '(lambda (condition hook) (declare (ignore hook)) '
                      '(format *error-output* "~a" condition) (sb-ext:exit :code 1)))\n'
                      '(load ' + fn_dev.lisp_string(str(events)) + ')\n(sb-ext:exit :code 0)\n')
            result = subprocess.run([sys.executable, str(ROOT / 'tools/acl2'), '--timeout', '60'],
                                    input=driver, text=True, capture_output=True, timeout=75)
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            self.assertIn('DEV-REPL-ACTUAL-LD-PASS', result.stdout)
            self.assertNotIn('debugger invoked', result.stdout + result.stderr)


class Client(unittest.TestCase):
    """fn_dev.evaluate against a stand-in `fn': the exit codes host/native/developer-eval.lisp
    gives (0 evaluated, 1 the form failed, 2 refused by name, 3 no reply) are the client's whole contract."""

    def stand_in(self, directory, code, out='', err=''):
        script = Path(directory) / 'fn'
        script.write_text('#!/bin/sh\ncat > "%s/stdin"\nprintf %%s "%s"\nprintf %%s "%s" >&2\nexit %d\n'
                          % (directory, out, err, code))
        script.chmod(script.stat().st_mode | stat.S_IEXEC)
        return str(script)

    def test_the_form_goes_in_on_stdin_and_the_config_names_the_node(self):
        with tempfile.TemporaryDirectory() as d:
            fn = self.stand_in(d, 0, '42\n')
            self.assertEqual(fn_dev.evaluate('/x/fn.toml', '(+ 20 22)', 5, fn), (True, '42\n'))
            self.assertEqual((Path(d) / 'stdin').read_text(), '(+ 20 22)')

    def test_exit_codes(self):
        with tempfile.TemporaryDirectory() as d:
            self.assertEqual(fn_dev.evaluate('c', 'x', 5, self.stand_in(d, 1, 'oops\n')), (False, 'oops\n'))
            with self.assertRaisesRegex(ValueError, 'not-developer'):
                fn_dev.evaluate('c', 'x', 5, self.stand_in(d, 2, '', 'developer eval refused: not-developer'))
            with self.assertRaisesRegex(ValueError, 'unknown'):
                fn_dev.evaluate('c', 'x', 5, self.stand_in(d, 3, '', 'developer eval: no reply'))
            with self.assertRaisesRegex(ValueError, 'exited 5'):
                fn_dev.evaluate('c', 'x', 5, self.stand_in(d, 5, '', 'usage'))

    def test_the_client_computes_no_bound_of_its_own(self):
        # ACL2 decides what is too large (fn-deval-admit, fn-deval-request-encode): a long form is sent
        with tempfile.TemporaryDirectory() as d:
            fn = self.stand_in(d, 0, 'ok\n')
            self.assertEqual(fn_dev.evaluate('c', 'x' * 70000, 5, fn), (True, 'ok\n'))
            self.assertEqual(len((Path(d) / 'stdin').read_text()), 70000)

    def test_an_image_command_line_is_split(self):
        with tempfile.TemporaryDirectory() as d:
            fn = self.stand_in(d, 0, 'ok\n')
            self.assertEqual(fn_dev.evaluate('c', 'x', 5, fn + ' --fn'), (True, 'ok\n'))

    def test_interactive_acl2_uses_selected_prover_allowance(self):
        with mock.patch('builtins.input', side_effect=[':acl2 (value-triple :ok)', ':quit']), \
             mock.patch.object(fn_dev, 'evaluate', return_value=(True, '')) as evaluate, \
             mock.patch('builtins.print'):
            self.assertEqual(fn_dev.main(['repl', '--config', '/unused/fn.toml',
                                          '--prover-steps', '37']), 0)
        evaluate.assert_called_once_with('/unused/fn.toml',
            "(fnn-dev-admit '((value-triple :ok)) :step-limit 37)", None, 'fn')

    def test_the_socket_option_is_gone(self):
        with self.assertRaises(SystemExit):
            fn_dev.main(['repl', '--socket', '/unused'])


if __name__ == '__main__':
    unittest.main()
