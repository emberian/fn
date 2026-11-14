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
            root = self.tree(directory, '(cl:load "host/child.lisp")')
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

    def test_platform_selection_is_narrow_and_unknown_features_refuse(self):
        symbol = gate.ledger.Sym
        rows = [symbol('#+linux'), [symbol('linux-entry')],
                symbol('#+darwin'), [symbol('darwin-entry')]]
        expected = 'linux-entry' if sys.platform.startswith('linux') else 'darwin-entry'
        self.assertEqual(gate.selected(rows), [[symbol(expected)]])
        with self.assertRaises(ValueError):
            gate.selected([symbol('#+mystery'), [symbol('unknown')]])

    def test_binding_positions_are_not_calls_but_qualified_calls_are(self):
        form = gate.ledger.read_forms("""
          (defun fn2-helper (fn2-argument)
            (let ((fn2-local (acl2::fn2-entry fn2-argument)))
              (multiple-value-bind (fn2-a fn2-b) (fn2-values fn2-local)
                (funcall #'acl2::fn2-result fn2-a))))
        """)[0]
        self.assertEqual(set(gate.expression_calls(form)),
                         {'fn2-entry', 'fn2-values', 'fn2-result'})

    def test_condition_reader_is_an_explicit_raw_helper(self):
        with tempfile.TemporaryDirectory() as directory:
            root = self.tree(directory, """
              (define-condition fn2-native-error (error)
                ((detail :initarg :detail :reader fn2-native-detail)))
              (defun fn2-reporter (x) (fn2-native-detail x))
            """)
            _, order, _ = gate.inspect(root)
            calls, helpers = gate.entry_names(root, order)
            self.assertIn('fn2-native-detail', calls)
            self.assertIn('fn2-native-detail', helpers)

    @unittest.skipUnless(shutil.which('sbcl'), 'SBCL required for raw gate controls')
    def test_runtime_check_rejects_unverified_missing_and_unbound_callees(self):
        for cls, helper, bound, ok in (
            (':common-lisp-compliant', False, True, True),
            (':ideal', False, True, False),
            (':missing', False, True, False),
            (':missing', True, True, True),
            (':missing', True, False, False),
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

    def binding_control(self, raw='', replacements=(), logical_names=None):
        """Load an actual raw source file over a small live-world stand-in.

        The entry calls a logical leaf never mentioned by the raw source. SBCL
        executes the generated gate's real binding detector; only ACL2 metadata
        lookup is stubbed. This does not qualify the actual certified startup.
        """
        if logical_names is None:
            logical_names = 'fn2-model-entry fn2-model-leaf'
        with tempfile.TemporaryDirectory() as directory:
            root = self.tree(directory, '(defun fn2-raw-step () (fn2-model-entry))\n' + raw)
            prefix, order, findings = gate.inspect(root)
            self.assertEqual(findings, [])
            calls, helpers = gate.entry_names(root, order)
            self.assertNotIn('fn2-model-leaf', calls)
            stubs = f"""
              (defvar *the-live-state* nil)
              (defun w (x) x)
              (defun getpropc (name key default world)
                (declare (ignore key world))
                (if (member name '({logical_names})) :common-lisp-compliant default))
              (defun fn2-model-leaf () :original)
              (defun fn2-model-entry () (fn2-model-leaf))
            """
            program = gate.load_program(prefix, calls, helpers, replacements)
            script = root / 'control.lisp'
            script.write_text(stubs + program.split(':q', 1)[1])
            return subprocess.run(['sbcl', '--script', str(script)], text=True, cwd=root,
                                  capture_output=True, timeout=10)

    @unittest.skipUnless(shutil.which('sbcl'), 'SBCL required for raw gate controls')
    def test_runtime_preserves_live_world_bindings(self):
        # ACL2 primitive special operators have no mutable FDEFINITION cell.
        result = self.binding_control('(assert (eq (fn2-raw-step) :original))',
                                      logical_names='fn2-model-entry fn2-model-leaf if quote')
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn('2 unchanged-or-declared, 0 native assumptions', result.stdout)

    @unittest.skipUnless(shutil.which('sbcl'), 'SBCL required for raw gate controls')
    def test_runtime_rejects_reached_transitive_raw_substitution(self):
        # This mutation really changes the raw->logical-entry->logical-leaf
        # result before the gate refuses it. The leaf is absent from raw calls.
        result = self.binding_control("""
          (setf (symbol-function (intern "FN2-MODEL-LEAF")) (lambda () :corrupt))
          (assert (eq (fn2-raw-step) :corrupt))
        """)
        self.assertNotEqual(result.returncode, 0)
        self.assertIn('raw replacement of ACL2 function FN2-MODEL-LEAF', result.stdout)

    @unittest.skipUnless(shutil.which('sbcl'), 'SBCL required for raw gate controls')
    def test_runtime_rejects_raw_defun_over_guarded_logical_entry(self):
        result = self.binding_control("""
          (defun fn2-model-entry () :corrupt)
          (assert (eq (fn2-raw-step) :corrupt))
        """)
        self.assertNotEqual(result.returncode, 0)
        self.assertIn('raw replacement of ACL2 function FN2-MODEL-ENTRY', result.stdout)

    @unittest.skipUnless(shutil.which('sbcl'), 'SBCL required for raw gate controls')
    def test_runtime_rejects_removed_transitive_binding(self):
        result = self.binding_control('(fmakunbound (intern "FN2-MODEL-LEAF"))')
        self.assertNotEqual(result.returncode, 0)
        self.assertIn('raw replacement of ACL2 function FN2-MODEL-LEAF', result.stdout)

    @unittest.skipUnless(shutil.which('sbcl'), 'SBCL required for raw gate controls')
    def test_runtime_rejects_new_binding_for_unbound_logical_name(self):
        result = self.binding_control('(defun fn2-unbound-model () :raw)',
                                      logical_names='fn2-model-entry fn2-model-leaf fn2-unbound-model')
        self.assertNotEqual(result.returncode, 0)
        self.assertIn('raw replacement of ACL2 function FN2-UNBOUND-MODEL', result.stdout)

    @unittest.skipUnless(shutil.which('sbcl'), 'SBCL required for raw gate controls')
    def test_runtime_checks_exact_declared_native_function_identity(self):
        replacements = (('fn2-model-leaf', 'fn2-native-leaf'),)
        for installed, ok in (('fn2-native-leaf', True), ('fn2-other-leaf', False),
                              ('fn2-model-leaf', False)):
            with self.subTest(installed=installed):
                result = self.binding_control(f"""
                  (defun fn2-native-leaf () :native)
                  (defun fn2-other-leaf () :other)
                  (setf (symbol-function 'fn2-model-leaf) (symbol-function '{installed}))
                """, replacements)
                self.assertEqual(result.returncode == 0, ok, result.stdout + result.stderr)
                if ok:
                    self.assertIn('1 native assumptions', result.stdout)
                else:
                    self.assertIn('raw replacement of ACL2 function FN2-MODEL-LEAF', result.stdout)

    @unittest.skipUnless(shutil.which('sbcl'), 'SBCL required for raw gate controls')
    def test_declared_native_target_requires_preexisting_guarded_world_binding(self):
        result = self.binding_control(
            '(defun fn2-native-leaf () :native)',
            (('fn2-absent-model', 'fn2-native-leaf'),))
        self.assertNotEqual(result.returncode, 0)
        self.assertIn('lacks a guarded ACL2 binding', result.stdout)

    def test_native_manifest_matches_current_explicit_host_map(self):
        source = gate.forms(gate.ROOT / 'host/b3-native.lisp')
        declaration = next(form for form in source
                           if gate.ledger.head(form) == 'defparameter'
                           and str(form[1]) == '*fn2-b3-native-entries*')
        pairs = tuple((str(row[0]), str(row[2])) for row in declaration[2][1])
        self.assertEqual(pairs, gate.NATIVE_REPLACEMENTS)


if __name__ == '__main__':
    unittest.main()
