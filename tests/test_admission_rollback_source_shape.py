"""Source-shape assurance for fresh-reservation rollback; no runtime theorem.

These reviewed AST templates are the exact allowed control/call grammar of both
registry implementations, including the legacy admitted/taken core generators.
Changing an executable call, a branch, or quasiquote/unquote placement requires
reviewing this exclusion again. Whitespace and comments are immaterial. INSTALL,
FAIL and PARK are opaque continuations: successful installation follows all
reserves; rollback precedes its failure/park continuation. This does not assert
that arbitrary callers or malformed pool states satisfy a global invariant.
"""
from pathlib import Path
import sys
import unittest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'tools'))
import lisp_rewrite as lr

REVIEWED = {
    ('books/machine-arms.lisp', 'fn2-arms-registry-releases'): r"""
(defun fn2-arms-registry-releases (n body)
  ; release ranges n-1..0, then BODY
  (declare (xargs :verify-guards nil :measure (nfix n)))
  (if (zp n) body
    (let ((i (- n 1)))
      `(mv-let (rc fn2-pool fn2-control)
         (fn2-core-release-children ,(packn-pos (list 'slot i) 'fn2-core) ,(packn-pos (list 'pgen i) 'fn2-core)
                                    kind target gen fn2-pool fn2-control)
         (declare (ignore rc))
         ,(fn2-arms-registry-releases i body)))))
""",
    ('books/machine-arms.lisp', 'fn2-arms-registry-reserves'): r"""
(defun fn2-arms-registry-reserves (specs n install fail)
  (declare (xargs :verify-guards nil))
  (if (atom specs) install
    (let ((code (packn-pos (list 'code n) 'fn2-core)))
      `(mv-let (,code ,(packn-pos (list 'slot n) 'fn2-core) ,(packn-pos (list 'pgen n) 'fn2-core) fn2-pool)
         (fn2-pool-reserve ,(fn2-machine-class-form (fn2-arm-get :class (cdar specs)) 'fn2-pool) kind target gen fn2-pool)
         (if (not (eq ,code :ok))
             ,(fn2-arms-registry-releases n fail)
           ,(fn2-arms-registry-reserves (cdr specs) (+ 1 (nfix n)) install fail))))))
""",
    ('books/machines.lisp', 'fn2-machine-range-releases'): r"""
(defun fn2-machine-range-releases (n kind body)
  ; release ranges 0..n-1 (descending) then BODY
  (declare (xargs :verify-guards nil :measure (nfix n)))
  (if (zp n) body
    (let ((i (- n 1)))
      `(mv-let (rc fn2-core)
         (fn2-core-release ,(packn-pos (list 'slot i) 'fn2-core) ,(packn-pos (list 'pgen i) 'fn2-core)
                           ,kind target gen fn2-core)
         (declare (ignore rc))
         ,(fn2-machine-range-releases i kind body)))))
""",
    ('books/machines.lisp', 'fn2-machine-range-reserves'): r"""
(defun fn2-machine-range-reserves (specs n kind install)
  (declare (xargs :verify-guards nil))
  (if (atom specs) install
    (let ((code (packn-pos (list 'code n) 'fn2-core)))
      `(mv-let (,code ,(packn-pos (list 'slot n) 'fn2-core) ,(packn-pos (list 'pgen n) 'fn2-core) fn2-core)
         (fn2-core-reserve ,(let ((c (fn2-arm-get :class (cdar specs))))
                              (if (natp c) c
                                (er hard 'defmachine "A (:bytes B) range class needs the kind's registry in child form (defmachine-registry): ~x0." kind)))
                           ,kind target gen fn2-core)
         (if (not (eq ,code :ok))
             ,(fn2-machine-range-releases n kind '(mv :pool fn2-core))
           ,(fn2-machine-range-reserves (cdr specs) (+ 1 (nfix n)) kind install))))))
""",
    ('books/machines.lisp', 'fn2-machine-taken-reserves'): r"""
(defun fn2-machine-taken-reserves (specs n kind install park)
  (declare (xargs :verify-guards nil))
  (if (atom specs) install
    (let ((code (packn-pos (list 'code n) 'fn2-core)))
      `(mv-let (,code ,(packn-pos (list 'slot n) 'fn2-core) ,(packn-pos (list 'pgen n) 'fn2-core) fn2-core)
         (fn2-core-reserve ,(fn2-arm-get :class (cdar specs)) ,kind target gen fn2-core)
         (if (not (eq ,code :ok))
             ,(fn2-machine-range-releases n kind `(let ((fn2-core ,park)) (mv :pool *fn2-none* 0 fn2-core)))
           ,(fn2-machine-taken-reserves (cdr specs) (+ 1 (nfix n)) kind install park))))))
""",
}

def shape(node):
    if isinstance(node, lr.Str):
        return ('string', node.text)
    if isinstance(node, lr.Atom):
        return ('atom', node.low)
    if isinstance(node, lr.Pre):
        return ('prefix', node.prefix, shape(node.node))
    if isinstance(node, lr.Lst):
        return ('list', tuple(shape(child) for child in node.items))
    raise AssertionError('unsupported reader syntax')


def checked_definition(text, name):
    matches = [f for f in lr.parse(text).forms
               if isinstance(f, lr.Lst) and len(f.items) > 1
               and isinstance(f.items[0], lr.Atom) and f.items[0].low == 'defun'
               and isinstance(f.items[1], lr.Atom) and f.items[1].low == name]
    if len(matches) != 1:
        raise AssertionError('expected exactly one definition: ' + name)
    return shape(matches[0])


def check_source(text, path):
    for (book, name), expected in REVIEWED.items():
        if book == path and checked_definition(text, name) != checked_definition(expected, name):
            raise AssertionError('fresh-reservation control/call grammar changed: ' + name)


class AdmissionRollbackShapeTests(unittest.TestCase):
    def test_actual_generators_match_reviewed_control_and_call_grammar(self):
        for path in {book for book, name in REVIEWED}:
            with self.subTest(book=path):
                check_source((ROOT / path).read_text(), path)

    def test_query_insertion_before_rollback_is_rejected_in_each_reserver(self):
        for (path, name), source in REVIEWED.items():
            if not name.endswith('reserves'):
                continue
            marker = '(if (not (eq ,code :ok))'
            self.assertEqual(source.count(marker), 1)
            # Executable generated query call, rather than a matching comment.
            changed = source.replace(marker, '(progn (fn2-identity-decide-start tx m mg 0 1 d dg 0 k s g fn2-core) ' + marker, 1) + ')'
            with self.subTest(generator=name), self.assertRaises(AssertionError):
                actual = checked_definition(changed, name)
                self.assertEqual(actual, checked_definition(source, name))

    def test_extra_unknown_call_and_changed_branch_are_rejected(self):
        for (path, name), source in REVIEWED.items():
            for changed in (source.replace('(if ', '(unreviewed-call ', 1),
                            source.replace('(if ', '(when ', 1)):
                with self.subTest(generator=name), self.assertRaises(AssertionError):
                    self.assertEqual(checked_definition(changed, name), checked_definition(source, name))

    def test_comments_do_not_change_assurance(self):
        for (path, name), source in REVIEWED.items():
            self.assertEqual(checked_definition(source, name),
                             checked_definition('; harmless comment\n' + source, name))


if __name__ == '__main__':
    unittest.main()
