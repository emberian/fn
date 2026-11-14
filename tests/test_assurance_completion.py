"""Source-executed live-world refusal controls; no ACL2/cert/cache launches."""
from pathlib import Path
from unittest import mock
import copy
import json
import shutil
import subprocess
import sys
import tempfile
import types
import unittest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'tools'))
import assurance_completion as gate
import lisp_source


class CompletionScope(unittest.TestCase):
    def test_proposed_book_binds_scope_packet_and_actual_world_assembly(self):
        from emit_served_certificate import Atom, List
        declaration = gate.scope()
        nil = List([Atom(':SYMBOL'), List([Atom(str(ord(c))) for c in 'ACL2']),
                    List([Atom(str(ord(c))) for c in 'NIL'])])
        h = {':MANIFEST': List([]), ':ARM-INVENTORY': nil, ':REFUSED': List([])}
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            packet = root / 'packet'
            packet.write_text('first canonical packet')
            with mock.patch.object(gate, 'canonical', return_value=(h, [('SERVED', List([]), {})], ['SERVED'], [])), \
                 mock.patch.object(gate, 'world_books', return_value=['tests/owed-unit']), \
                 mock.patch('emit_served_certificate.metadata_checks', return_value='(value-triple :metadata-check)'):
                first = gate.generated_book(root, packet, declaration)
                packet.write_text('changed canonical packet')
                changed_packet = gate.generated_book(root, packet, declaration)
                changed_scope = copy.deepcopy(declaration)
                changed_scope['profile'] = 'a differently scoped profile'
                changed = gate.generated_book(root, packet, changed_scope)
            forms = lisp_source.forms(first)
            self.assertIn('(fn2-resolve :coverage)', forms)
            self.assertIn('(fn2-seal :evidence :coverage :square)', forms)
            self.assertIn('(include-book "../../tests/owed-unit")', forms)
            self.assertNotEqual(first, changed_packet)
            self.assertNotEqual(changed_packet, changed)
            self.assertTrue(any(f.startswith('(fn2-assert-assurance-complete ') for f in forms))

    def test_product_scope_cannot_omit_a_feature_or_served_subject(self):
        original = gate.scope()
        for mutant in ('feature', 'entry', 'duplicate'):
            value = copy.deepcopy(original)
            if mutant == 'feature':
                value['requirements'].pop()
            elif mutant == 'entry':
                value['requirements'][0][2] = []
            else:
                value['requirements'].append(value['requirements'][0])
            with self.subTest(mutant=mutant), tempfile.TemporaryDirectory() as td:
                root = Path(td)
                (root / 'tools').mkdir()
                (root / 'tools/assurance_scope.json').write_text(json.dumps(value))
                with self.assertRaises(ValueError):
                    gate.scope(root)

    def test_current_certificate_query_binds_toolchain_and_generated_closure(self):
        import certs
        import acl2_toolchain
        identity = mock.Mock(qualified=True, identity='qualified-control')
        with mock.patch.object(acl2_toolchain, 'fingerprint', return_value=identity), \
             mock.patch.object(certs, 'book_entries', return_value=[]) as entries, \
             mock.patch.object(certs, 'choose_entry', return_value=None):
            with self.assertRaisesRegex(ValueError, 'current completion closure'):
                gate.qualified_claims(ROOT, ROOT / 'tools/acl2')
            self.assertEqual(entries.call_args.args[2], gate.BOOK)
            accepts = entries.call_args.kwargs['metadata_filter']
            self.assertTrue(accepts({'toolchain_identity': 'qualified-control'}))
            self.assertFalse(accepts({'toolchain_identity': 'stale-control'}))

    def test_stale_checker_never_queries_a_certificate(self):
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            (root / 'tools').mkdir()
            (root / 'tools/assurance_scope.json').write_text((ROOT / 'tools/assurance_scope.json').read_text())
            with mock.patch.object(gate, 'generated_book', return_value='CURRENT'), \
                 mock.patch.object(gate, 'qualified_claims') as certified, \
                 mock.patch('check_served_certificate.current', side_effect=ValueError('stale closure')):
                problems = gate.inspect(root, root / 'packet', {}, root / 'acl2')
            certified.assert_not_called()
            self.assertTrue(any('checker missing' in p for p in problems))
            self.assertTrue(any('stale closure' in p for p in problems))

    def test_missing_required_semantic_root_and_forged_completion_are_refused(self):
        # Requirements come from the canonical packet, not the report's list.
        inventory = {'schema': 1, 'kind': 'required-obligations-only', 'roots': [
            {'name': 'SERVED', 'status': 'pending', 'obligations': [{'id': 'strict_join:SERVED'}]}]}
        module = types.SimpleNamespace(function_semantics=mock.Mock(),
                                       semantic_inventory=mock.Mock(return_value=inventory))
        with mock.patch.dict(sys.modules, {'served_semantic_inventory': module}), \
             mock.patch.object(gate, 'canonical', return_value=({}, [], ['SERVED'], [])):
            with self.assertRaisesRegex(ValueError, 'missing or extra required'):
                gate.semantic_problems(Path('packet'), {'roots': []})
            forged = copy.deepcopy(inventory)
            forged['roots'][0]['status'] = 'complete'
            with self.assertRaisesRegex(ValueError, 'differs from canonical'):
                gate.semantic_problems(Path('packet'), {'roots': [{'name': 'SERVED'}], 'semantic_inventory': forged})
            problems = gate.semantic_problems(Path('packet'),
                {'roots': [{'name': 'SERVED', 'status': 'validated'}], 'semantic_inventory': inventory})
            self.assertIn('remain pending across 1 served roots', problems[0])

    def test_dependency_source_drift_after_first_query_is_refused(self):
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            (root / 'tools').mkdir()
            (root / 'meta/emit').mkdir(parents=True)
            (root / 'tools/assurance_scope.json').write_text((ROOT / 'tools/assurance_scope.json').read_text())
            (root / (gate.BOOK + '.lisp')).write_text('CURRENT')
            with mock.patch.object(gate, 'generated_book', return_value='CURRENT'), \
                 mock.patch.object(gate, 'qualified_claims', side_effect=[{}, ValueError('stale dependency closure')]), \
                 mock.patch('check_served_certificate.current', side_effect=ValueError('missing bridge')):
                problems = gate.inspect(root, root / 'packet', {}, root / 'acl2')
            self.assertIn('stale dependency closure', problems)


@unittest.skipUnless(shutil.which('sbcl'), 'SBCL required for direct source controls')
class LiveWorldControls(unittest.TestCase):
    def test_actual_registry_guard_and_completion_checker(self):
        # Evaluate the actual source functions. Only ACL2 world/property access
        # and basic ACL2 primitives are stubbed, with explicit fixture data.
        sources = []
        wanted = {'fn2-owed-teethp', 'fn2-square-tooth-names', 'fn2-square-checksp',
                  'fn2-square-sharedp', 'fn2-square-side-functions', 'fn2-square-rowp',
                  'fn2-decl-statement-body'}
        for name in ('books/declare.lisp', 'books/owed.lisp', 'books/assurance-completion.lisp'):
            for form in lisp_source.forms((ROOT / name).read_text()):
                parsed = lisp_source.read_sexp(form)
                if isinstance(parsed, list) and len(parsed) > 1 and parsed[0].lower() == 'defun':
                    if parsed[1] in wanted or parsed[1].startswith('fn2-assurance-'):
                        sources.append(form)
        harness = r'''
(defpackage "ACL2" (:use "CL"))
(in-package "ACL2")
(declaim (declaration xargs))
(defun len (x) (length x))
(defun nfix (x) (if (and (integerp x) (<= 0 x)) x 0))
(defun zp (x) (<= (nfix x) 0))
(defun natp (x) (and (integerp x) (<= 0 x)))
(defun posp (x) (and (integerp x) (< 0 x)))
(defun true-listp (x) (or (null x) (and (consp x) (true-listp (cdr x)))))
(defun symbol-listp (x) (and (true-listp x) (every #'symbolp x)))
(defun no-duplicatesp-eq (x) (= (length x) (length (remove-duplicates x))))
(defun member-eq (x xs) (member x xs))
(defun intersectp-eq (xs ys) (intersection xs ys))
(defun subsetp-eq (xs ys) (subsetp xs ys))
(defun keyword-value-listp (x)
 (or (null x) (and (consp x) (keywordp (car x)) (consp (cdr x))
                  (keyword-value-listp (cddr x)))))
(defun fn2-decl-get (key row) (getf row key))
(defun fn2-decl-row (key world) (cdr (assoc (cadr key) (cdr (assoc :rows world)))))
(defun fn2-decl-rows (kind world) (declare (ignore kind)) (cdr (assoc :rows world)))
(defun getpropc (name prop default world)
 (let ((pair (assoc (list name prop) world :test #'equal))) (if pair (cdr pair) default)))
(defun all-fnnames (term)
 (if (atom term) nil
  (if (eq (car term) 'quote) nil
   (remove-duplicates (append (list (car term)) (mapcan #'all-fnnames (cdr term)))))))
'''
        controls = r'''
(defparameter *body* '(equal (served x) (reference x)))
(defun row (&rest extra)
 (append extra (list :schema :assertion :statement 'claim$owed :vars '(x)
   :translated *body* :teeth '(positive negative) :proof '(:proved universal)
   :evidence '(:kind :formula-ground-proofs))))
(defun world (row &optional (theorem *body*) (other nil))
 (list (cons :rows (append (list (cons 'claim row)) other))
       (cons '(claim$owed formals) '(x))
       (cons '(claim$owed unnormalized-body) *body*)
       (cons '(universal theorem) theorem)))
(defun problems (row &optional (theorem *body*) (other nil))
 (fn2-assurance-required-problems '((:product claim (served))) (world row theorem other)))
; Positive control: actual admitted property equals actual live statement.
(assert (null (problems (row))))
; Raw author formula does not redirect the theorem or served binding.
(assert (null (problems (row :formula '(equal (unrelated x) 't)))))
; Required root absent, live formula redirected, witnesses without theorem,
; explicitly unreachable branch, missing served subject, missing controls.
(assert (fn2-assurance-required-problems '((:product absent (served))) (world (row))))
(assert (problems (row :translated '(equal (served x) 't))))
(assert (problems (row :proof '(:owed))))
(assert (problems (row) nil))
(assert (problems (row :unreachable-in-composition t)))
(assert (problems (row :reachability :unreachable-in-composition)))
(assert (fn2-assurance-required-problems '((:product claim (missing-served))) (world (row))))
(assert (problems (row :evidence nil)))
; An unrelated admitted proof cannot discharge this exact statement.
(assert (problems (row) '(equal 't 't)))
; Missing, owed and cyclic declared dependency closures remain incomplete.
(assert (problems (row :depends '(missing))))
(assert (problems (row :depends '(claim))))
(assert (problems (row :depends :malformed)))
(assert (problems (row :depends '(helper)) *body*
                  (list (cons 'helper (row :proof '(:owed))))))
; Rechecks schedule the root and every diamond dependency. A repeated leaf
; may be rechecked twice; it must never disappear behind a shared branch.
(let* ((w (world (row :depends '(left right)) *body*
            (list (cons 'left (row :depends '(leaf)))
                  (cons 'right (row :depends '(leaf)))
                  (cons 'leaf (row)))))
       (events (fn2-assurance-evidence-events '(claim) nil 100 w)))
 (assert (equal events '((fn2-assert-square-evidence claim)
                         (fn2-assert-square-evidence left)
                         (fn2-assert-square-evidence leaf)
                         (fn2-assert-square-evidence right)
                         (fn2-assert-square-evidence leaf)))))
; Absent child scheduling cannot silently drop a requested evidence event;
; the required-problems phase refuses it before this schedule is executed.
(assert (equal (fn2-assurance-evidence-events '(missing) nil 10 (world (row)))
               '((fn2-assert-square-evidence missing))))
(assert (equal (caar (fn2-assurance-evidence-events '(claim) nil 0 (world (row))))
               'make-event))
; A requirement without a statement cannot obtain completion from controls.
(assert (problems (list :schema :invariant :proof '(:owed))))
(format t "LIVE-WORLD-REFUSAL-CONTROLS PASS~%")
'''
        with tempfile.TemporaryDirectory() as td:
            script = Path(td) / 'controls.lisp'
            script.write_text(harness + '\n'.join(sources) + controls)
            result = subprocess.run(['sbcl', '--script', str(script)], text=True,
                                    stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=20)
        self.assertEqual(result.returncode, 0, result.stdout)
        self.assertIn('LIVE-WORLD-REFUSAL-CONTROLS PASS', result.stdout)


if __name__ == '__main__':
    unittest.main()
