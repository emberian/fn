"""Standalone host books must not borrow the surrounding image's world."""
import json
import tempfile
import unittest
from pathlib import Path
from tools import host_check as hc


class StandaloneTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name)

    def put(self, name, text):
        path = self.root / name
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(text)

    def findings(self):
        return '\n'.join(hc.standalone_findings(self.root))

    def test_an_attachment_after_its_stobj_is_defined_is_found(self):
        # HOST-ATTACH-ORDER-STANDALONE: index-writer-operation-host reached
        # payload-arena (defines fn-arena) before owner-host's attachment
        self.put('books/impl.lisp', '(defstobj impl fld)')
        self.put('books/generic.lisp', '(defstobj gen fld :attachable t)')
        self.put('books/attach.lisp', '(include-book "impl") (attach-stobj gen impl) (include-book "generic")')
        self.put('books/user.lisp', '(include-book "generic")')
        self.put('host/late.lisp', '(include-book "../books/user") (include-book "../books/attach")')
        self.assertIn('(attach-stobj gen ...) comes after books/generic.lisp defined gen in host/late.lisp', self.findings())
        self.put('host/late.lisp', '(include-book "../books/attach") (include-book "../books/user")')
        self.assertEqual('', self.findings())

    def test_attachment_order_covers_parked_host_books_and_skips_includers_locals(self):
        self.put('planning/host-parked.json', json.dumps({"parked": {"host/late.lisp": "parked"}}))
        self.put('books/impl.lisp', '(defstobj impl fld)')
        self.put('books/generic.lisp', '(defstobj gen fld :attachable t)')
        self.put('books/attach.lisp', '(include-book "impl") (attach-stobj gen impl) (include-book "generic")')
        # an included book's local include never reaches the includer's world
        self.put('books/user.lisp', '(local (include-book "generic"))')
        self.put('host/late.lisp', '(include-book "../books/user") (include-book "../books/attach")')
        self.assertEqual('', self.findings())
        self.put('host/late.lisp', '(local (include-book "../books/generic")) (include-book "../books/attach")')
        self.assertIn('defined gen in host/late.lisp', self.findings())

    def test_call_and_guard_need_their_own_include_not_an_image_or_ld(self):
        self.put('books/dep.lisp', '(defun helper (x) x) (defun guard-p (x) t)')
        self.put('host/native/build.lisp', '(include-book "books/dep")')
        source = '(defun entry (x) (declare (xargs :guard (guard-p x))) (helper x))'
        self.put('host/a.lisp', '(ld "../books/dep.lisp")' + source)
        self.assertIn('helper is not defined', self.findings())
        self.assertIn('guard-p is not defined', self.findings())
        self.put('host/a.lisp', '(include-book "../books/dep")' + source)
        self.assertEqual('', self.findings())

    def test_declaration_macro_target_keystone_and_via_are_world_dependencies(self):
        self.put('host/a.lisp', '(definterface entry :keystones ((holds :via model)))')
        before = self.findings()
        for name in ('definterface', 'entry', 'holds', 'model'):
            self.assertIn(name + ' is not defined', before)
        self.put('books/dep.lisp', '(defmacro definterface (&rest args) nil) '
                 '(defun entry (x) x) (defun model (x) x) (defthm holds t)')
        self.put('host/a.lisp', '(include-book "../books/dep") '
                 '(definterface entry :keystones ((holds :via model)))')
        self.assertEqual('', self.findings())

    def test_theorem_formula_and_hint_references(self):
        self.put('host/a.lisp', '(defthm holds (equal (missing x) x) '
                 ':hints (("Goal" :use support :in-theory (enable definition))))')
        for name in ('missing', 'support', 'definition'):
            self.assertIn(name + ' is not defined', self.findings())

    def test_locals_visible_only_in_the_certifying_book(self):
        self.put('books/dep.lisp', '(local (defun private (x) x)) '
                 '(local (defthm private-thm t)) (local (include-book "hidden"))')
        self.put('books/hidden.lisp', '(defun hidden (x) x)')
        self.put('host/a.lisp', '(include-book "../books/dep") '
                 '(defthm test (equal (private (hidden x)) x) :hints (("Goal" :use private-thm)))')
        for name in ('private', 'hidden', 'private-thm'):
            self.assertIn(name + ' is not defined', self.findings())
        self.put('host/a.lisp', '(local (include-book "../books/hidden")) '
                 '(local (defun private (x) x)) '
                 '(defthm test (equal (private (hidden x)) x))')
        self.assertEqual('', self.findings())

    def test_quotes_bindings_and_stobj_let_are_not_function_names(self):
        self.put('host/a.lisp', '(defstobj st (fld :type integer :initially 0)) '
                 '(defun entry (x) (let ((y x)) (list y \'(unknown x)))) '
                 '(defun inner (x) (stobj-let ((s (fld st))) (result) '
                 '(car x) (mv result st)))')
        self.assertEqual('', self.findings())

    def test_parked_and_raw_are_outside_scope(self):
        self.put('planning/host-parked.json', json.dumps({'parked': {'host/parked.lisp': 'parked'}}))
        self.put('host/parked.lisp', '(defun entry (x) (missing x))')
        self.put('host/native/heap.lisp', '(defun raw (x) (missing x))')
        self.assertEqual('', self.findings())
        self.put('host/unreferenced-root.lisp', '(defun entry (x) (missing x))')
        self.assertIn('missing is not defined', self.findings())

    def test_stobj_and_generator_names_belong_to_the_invoking_book(self):
        self.put('books/macros.lisp', '(defmacro emit () `(defun generated (x) x))')
        self.put('books/dep.lisp', '(include-book "macros") (emit) (def-buffer buffer)')
        self.put('host/a.lisp', '(include-book "../books/dep") '
                 '(defun entry (x) (generated (create-buffer)))')
        self.assertEqual('', self.findings())
        self.put('host/a.lisp', '(include-book "../books/macros") (defun entry (x) (generated x))')
        self.assertIn('generated is not defined', self.findings())

    def test_local_macro_does_not_export_its_names(self):
        self.put('books/dep.lisp', '(local (defmacro private () nil))')
        self.put('host/a.lisp', '(include-book "../books/dep") (defun entry (x) (private x))')
        self.assertIn('private is not defined', self.findings())

    def test_carried_writer_and_cost_generated_names(self):
        self.put('books/dep.lisp', '(def-carried-profile profile :invariant inv :suffix state) '
                 '(def-carried-writer writer :profile profile) (def-cost entry)')
        self.put('host/a.lisp', '(include-book "../books/dep") '
                 '(defthm result t :hints (("Goal" :use writer-preserves-state '
                 ':in-theory (enable entry-visits entry-route-visits))))')
        self.assertEqual('', self.findings())

    def test_cost_without_a_bound_does_not_define_a_bound_theorem(self):
        self.put('books/dep.lisp', '(def-cost entry)')
        self.put('host/a.lisp', '(include-book "../books/dep") '
                 '(defthm result t :hints (("Goal" :use entry-visits-bound)))')
        self.assertIn('entry-visits-bound is not defined', self.findings())
        self.put('books/dep.lisp', '(def-cost entry :visits 0)')
        self.assertEqual('', self.findings())

    def test_literal_theory_names_are_checked_without_a_project_prefix(self):
        self.put('host/a.lisp', "(defthm result t :hints ((\"Goal\" :in-theory '(missing-rule))))")
        self.assertIn('missing-rule is not defined', self.findings())

    def test_acl2_qualified_names_have_the_same_world_as_unqualified_names(self):
        self.put('host/a.lisp', '(defun entry (x) (acl2::helper x))')
        self.assertIn('helper is not defined', self.findings())
        self.put('host/a.lisp', '(defun acl2::helper (x) x) (defun entry (x) (helper x))')
        self.assertEqual('', self.findings())

    def test_unreadable_root_is_a_finding(self):
        self.put('host/a.lisp', '(defun broken (')
        self.assertIn('a.lisp', self.findings())

    def test_missing_include_is_a_finding(self):
        self.put('host/a.lisp', '(include-book "missing")')
        self.assertIn('missing.lisp', self.findings())


if __name__ == '__main__':
    unittest.main()
