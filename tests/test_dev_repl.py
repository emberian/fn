"""Actual developer REPL over Unix sockets; owner/transport are named fixture seams."""
import os
from pathlib import Path
import shutil
import subprocess
import tempfile
import unittest
import sys
import socket
ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT/'tools'))
import fn_dev
from proof_repl import forms

class DeveloperRepl(unittest.TestCase):
    @unittest.skipUnless(shutil.which('sbcl'), 'SBCL required')
    def test_live_forms_output_and_lifecycle(self):
        with tempfile.TemporaryDirectory() as directory:
            d = Path(directory)
            sock = d/'debug.sock'
            selected = []
            for form in forms((ROOT/'host/native/control-transport.lisp').read_text()):
                if any(form.lower().startswith(prefix) for prefix in (
                    '(defstruct (fnn-control-state', '(defmacro fnn-with-control',
                    '(defun fnn-control-peer-is-owner-p', '(defun fnn-control-socket-path-p')):
                    selected.append(form)
            for form in forms((ROOT/'host/native/io.lisp').read_text()):
                if any(form.lower().startswith(prefix) for prefix in (
                    '(defparameter +fnn-developer-selectors+', '(defconstant +fnn-developer-selectors+',
                    '(defun fnn-developer-selector ', '(defun fnn-developer-selector-refusal ')):
                    selected.append(form)
            (d/'control.lisp').write_text('\n'.join(selected))
            fixture = (ROOT/'tests/fixtures/dev_repl.lisp').read_text()
            (d/'run.lisp').write_text(fixture.replace('__CONTROL__', str(d/'control.lisp')).replace('__REPL__', str(ROOT/'host/native/dev-repl.lisp')).replace('__TRACE__', str(ROOT/'host/native/trace.lisp')))
            env = dict(os.environ, FN_NATIVE_DEV_REPL=str(sock))
            with (d/'stderr').open('w') as err:
                process = subprocess.Popen([shutil.which('sbcl'), '--noinform', '--disable-debugger', '--script', str(d/'run.lisp')], stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=err, text=True, env=env)
                try:
                    self.assertEqual(process.stdout.readline().strip(), 'READY', (d/'stderr').read_text())
                    self.assertEqual(sock.stat().st_mode & 0o777, 0o600)  # private before accepting
                    ok, text = fn_dev.evaluate(sock, '(+ 20 22)', 3)
                    self.assertTrue(ok); self.assertEqual(text.strip(), '42')
                    self.assertTrue(fn_dev.evaluate(sock, '(defparameter *dev-test-value* 17)', 3)[0])
                    self.assertEqual(fn_dev.evaluate(sock, '*dev-test-value*', 3)[1].strip(), '17')
                    ok, text = fn_dev.evaluate(sock, '(values 1 2 3)', 3)
                    self.assertTrue(ok); self.assertEqual(text.splitlines(), ['1', '2', '3'])
                    with socket.socket(socket.AF_UNIX, socket.SOCK_STREAM) as invalid:
                        invalid.settimeout(3); invalid.connect(str(sock))
                        invalid.sendall(b'\xff'); invalid.shutdown(socket.SHUT_WR)
                        self.assertEqual(invalid.recv(128), b'')
                    self.assertFalse(fn_dev.evaluate(sock, '#.(error "reader eval")', 3)[0])
                    self.assertFalse(fn_dev.evaluate(sock, '(+ 1 2) (+ 3 4)', 3)[0])
                    self.assertTrue(fn_dev.evaluate(sock, '(+ 1 2)', 3)[0])
                    ok, text = fn_dev.evaluate(sock, '(dotimes (i 70000) (write-char #\\x))', 3)
                    self.assertTrue(ok); self.assertIn('[output truncated]', text)
                    self.assertLess(len(text), 65700)
                    self.assertFalse(fn_dev.evaluate(sock, '(error "evaluation failure")', 3)[0])
                    self.assertTrue(fn_dev.evaluate(sock, '(progn (fnn-trace-start :allocation :process) :tracing)', 3)[0])
                    self.assertTrue(fn_dev.evaluate(sock, '(+ 41 1)', 3)[0])
                    ok, text = fn_dev.evaluate(sock, '(fnn-trace-report *standard-output*)', 3)
                    self.assertTrue(ok)
                    self.assertIn('\"phase\":\"developer-eval\"', text)
                    self.assertIn('\"allocation_scope\":\"process\"', text)
                    # An unauthorized connection must never reach the evaluator.
                    self.assertTrue(fn_dev.evaluate(sock, "(setf (symbol-function 'fnn-control-peer-is-owner-p) (lambda (socket) (declare (ignore socket)) nil))", 3)[0])
                    with self.assertRaises((ValueError, OSError)):
                        fn_dev.evaluate(sock, '(error "must not evaluate")', 3)
                    process.stdin.write('stop\n'); process.stdin.flush()
                    process.wait(timeout=5)
                    self.assertEqual(process.returncode, 0, (d/'stderr').read_text())
                    self.assertFalse(sock.exists())
                finally:
                    if process.poll() is None:
                        process.terminate(); process.wait(timeout=5)
                    process.stdin.close(); process.stdout.close()

    @unittest.skipUnless(os.environ.get('FN_DEV_REPL_ACL2') == '1', 'opt-in real ACL2 execution')
    def test_actual_acl2_admission_and_refusal(self):
        with tempfile.TemporaryDirectory() as directory:
            d = Path(directory)
            source = (ROOT/'host/native/dev-repl.lisp').read_text().split('(defun fnn-dev-repl-loop')[0]
            events = d/'events.lisp'
            events.write_text((ROOT/'host/native/trace.lisp').read_text() + '\n' + source + '\n'
                              + (ROOT/'tests/fixtures/dev_repl_acl2.lisp').read_text())
            driver = (':q\n(setf sb-ext:*invoke-debugger-hook* '
                      '(lambda (condition hook) (declare (ignore hook)) '
                      '(format *error-output* "~a" condition) (sb-ext:exit :code 1)))\n'
                      '(load ' + fn_dev.lisp_string(str(events)) + ')\n(sb-ext:exit :code 0)\n')
            result = subprocess.run([sys.executable, str(ROOT/'tools/acl2'), '--timeout', '60'],
                                    input=driver, text=True, capture_output=True, timeout=75)
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            self.assertIn('DEV-REPL-ACTUAL-LD-PASS', result.stdout)
            self.assertNotIn('debugger invoked', result.stdout + result.stderr)

    def test_client_refuses_oversized_code_before_connect(self):
        with self.assertRaises(ValueError):
            fn_dev.evaluate('/missing', 'x'*65537)

if __name__ == '__main__': unittest.main()
