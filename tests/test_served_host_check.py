"""Mutations of the served load graph and executable guard check boundary."""
import pathlib
import shutil
import subprocess
import sys
import tempfile
import unittest
sys.path.insert(0, str(pathlib.Path(__file__).resolve().parents[1] / 'tools'))
import served_host_check as gate


class ServedHostCheck(unittest.TestCase):
    def tree(self, directory, host='(defun helper () 1)'):
        root = pathlib.Path(directory)
        (root / 'tools').mkdir()
        (root / 'host').mkdir()
        (root / 'tools/image-node.lsp').write_text(
            '(include-book "books/node-profile" :uncertified-okp nil)\n:q\n'
            '(load "host/main.lisp")\n(setf *fn2-nserve-base* *fn2-node-profile*)\n'
            '(sb-ext:exit :code (fn2-nserve-main))\n')
        (root / 'host/main.lisp').write_text(host)
        return root

    def test_full_recursive_graph_rejects_reader_but_not_quoted_data(self):
        with tempfile.TemporaryDirectory() as directory:
            root = self.tree(directory, '(load "host/child.lisp")')
            child = root / 'host/child.lisp'
            child.write_text("(defun helper () '(read x))")
            prefix, order, problems = gate.inspect(root)
            self.assertEqual(problems, [])
            self.assertIn('host/child.lisp', order)
            self.assertNotIn('(fn2-nserve-main)', prefix)
            child.write_text('(defun helper (x) (cl:read x))')
            self.assertTrue(any('cl:read' in p for p in gate.inspect(root)[2]))
            child.write_text('(defun helper () #.(danger))')
            self.assertTrue(any('read-time' in p for p in gate.inspect(root)[2]))

    def test_missing_or_dynamic_load_fails(self):
        with tempfile.TemporaryDirectory() as directory:
            root = self.tree(directory, '(load "host/absent.lisp")')
            self.assertTrue(gate.inspect(root)[2])
            (root / 'host/main.lisp').write_text('(load path)')
            self.assertTrue(gate.inspect(root)[2])

    @unittest.skipUnless(shutil.which('sbcl'), 'SBCL required for raw gate controls')
    def test_runtime_check_rejects_unverified_missing_and_unbound_callees(self):
        for cls, helper, bound, ok in (
            (':common-lisp-compliant', False, True, True),
            (':ideal', False, True, False),
            (':missing', False, True, False),
            (':missing', True, True, True),
            (':common-lisp-compliant', False, False, False),
        ):
            with self.subTest(cls=cls, helper=helper, bound=bound):
                stubs = ('(defvar *the-live-state* nil)\n(defun w (x) x)\n'
                         f'(defun getpropc (&rest args) (declare (ignore args)) {cls})\n')
                if bound:
                    stubs += '(defun fn2-test () 1)\n'
                program = gate.load_program(':q\n', ['fn2-test'], ['fn2-test'] if helper else [])
                with tempfile.NamedTemporaryFile(mode='w', suffix='.lisp') as f:
                    f.write(stubs + program.split(':q', 1)[1]); f.flush()
                    result = subprocess.run(['sbcl', '--script', f.name], text=True,
                                            capture_output=True, timeout=10)
                self.assertEqual(result.returncode == 0, ok, result.stdout + result.stderr)


if __name__ == '__main__':
    unittest.main()
