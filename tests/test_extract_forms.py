"""X1/X2 for the forms emitter (tools/extract/forms-export.lisp): the checker's pure core on synthetic
units, each tooth a named mutation that must be refused by unit name.  The world-bound variants (the real
export and xt-verify-defs against an extraction world image) run only when FN_EXTRACT_FORMS_WORLD names a
world launcher: they are for hbox."""
import hashlib
import os
import shutil
import subprocess
import tempfile
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
FORMS = ROOT / 'tools/extract/forms-export.lisp'
SBCL = shutil.which('sbcl')

PRELUDE = '''(require :sb-cltl2)
(defpackage "ACL2" (:use "COMMON-LISP"))
(in-package "ACL2")
(handler-bind ((warning #'muffle-warning)) (load "FORMS_PATH"))
(defun show (x) (format t "~&~a~%" x))
'''.replace('FORMS_PATH', str(FORMS))


def run_lisp(body):
    with tempfile.TemporaryDirectory() as directory:
        script = Path(directory) / 'forms.lisp'
        script.write_text(PRELUDE + body)
        run = subprocess.run([SBCL, '--noinform', '--disable-debugger', '--script', str(script)],
                             capture_output=True, text=True, timeout=120)
    assert run.returncode == 0, run.stdout + run.stderr
    return run.stdout


@unittest.skipUnless(SBCL, 'SBCL required')
class FormsCheckerTests(unittest.TestCase):
    def test_sha256_matches_hashlib(self):
        samples = ['', 'abc', 'x' * 55, 'x' * 56, 'x' * 64, 'x' * 1000, ';;;; UNIT raw:ACL2::F\n(DEFUN F (X) X)\n']
        body = ''.join('(show (fe-sha256-hex %s))' % ('"%s"' % s.replace('\\', '\\\\').replace('"', '\\"')) for s in samples)
        got = run_lisp(body).split()
        self.assertEqual(got, [hashlib.sha256(s.encode('latin-1')).hexdigest() for s in samples])

    def test_canon_quoted_symbols_preserved(self):
        out = run_lisp("""
(show (fe-text '(defun f (x) (quote t123))))
(show (fe-text '(quote (oneify7 t123))))
(show (eq (cadr (fe-canon '(quote t123))) 't123))
(show (equal (fe-canon '(load-time-value '(oneify7 t123)))
             '(load-time-value '(oneify7 t123))))
""")
        self.assertIn('(COMMON-LISP:QUOTE ACL2::T123)', out)
        self.assertIn('ACL2::ONEIFY7 ACL2::T123', out)
        self.assertEqual(out.splitlines()[-2:], ['T', 'T'])

    def test_canon_free_gentemp_preserved(self):
        self.assertEqual(run_lisp("(show (fe-text '(f t9)))").strip(), '(ACL2::F ACL2::T9)')

    def test_canon_bound_temporaries_and_local_functions(self):
        out = run_lisp("""
(show (fe-text '(let ((t5 1)) (+ t5 t5))))
(show (fe-text '(labels ((oneify12 () 1)) (list (function oneify12) (oneify12)))))
""").splitlines()
        self.assertEqual(out[0], '(COMMON-LISP:LET ((ACL2::XTGT1 1)) (COMMON-LISP:+ ACL2::XTGT1 ACL2::XTGT1))')
        self.assertEqual(out[1].count('ACL2::ONEIFY1'), 3)
        self.assertNotIn('ONEIFY12', out[1])

    def test_canon_preexisting_target_not_captured(self):
        out = run_lisp("(show (fe-text '(let ((t7 2)) (+ xtgt1 t7))))")
        self.assertIn('((ACL2::XTGT2 2))', out)
        self.assertIn('ACL2::XTGT1 ACL2::XTGT2', out)

    def test_canon_shadowing_has_distinct_bindings_and_same_value(self):
        out = run_lisp("""
(let* ((form '(lambda () (let ((t3 1)) (let ((t3 2)) t3) t3)))
       (canon (fe-canon form)))
  (show (fe-text form))
  (show (= (funcall (compile nil form)) (funcall (compile nil canon)) 1)))
""").splitlines()
        self.assertEqual(out[0].count('ACL2::XTGT1'), 2)
        self.assertEqual(out[0].count('ACL2::XTGT2'), 2)
        self.assertEqual(out[1], 'T')

    def test_canon_cross_form_global_identity_preserved(self):
        out = run_lisp("""
(show (equal (fe-canon '(defun t44 () 1)) '(defun t44 () 1)))
(show (equal (fe-canon '(t44)) '(t44)))
(dolist (op '(defmacro defvar defparameter defconstant sb-ext:defglobal defstruct))
  (show (eq (cadr (fe-canon (list op 't44 nil))) 't44)))
""")
        self.assertEqual(out.split(), ['T'] * 8)

    def test_canon_bound_and_quoted_symbol_refused_by_name(self):
        out = run_lisp("""
(handler-case (progn (fe-canon '(let ((t5 1)) (list t5 (quote t5)))) (show "ACCEPTED"))
  (error (e) (show e)))
""")
        self.assertIn('T5', out)
        self.assertIn('QUOTE', out)
        self.assertNotIn('ACCEPTED', out)

    def test_canon_unknown_call_is_not_inferred_to_be_a_binder(self):
        # An unknown ordinary operator has no binding authority. In this
        # hypothetical FOO-BIND call, both T6 occurrences are free.
        out = run_lisp("""
(let ((form '(foo-bind ((t6 1)) t6)))
  (show (equal form (fe-canon form))))
""")
        self.assertEqual(out.strip(), 'T')

    def test_canon_raw_numbering_does_not_affect_text(self):
        out = run_lisp("""
(show (string= (fe-text '(let* ((t107 1) (t109 (+ t107 2))) (+ t107 t109)))
               (fe-text '(let* ((t3 1) (t4 (+ t3 2))) (+ t3 t4)))))
""")
        self.assertEqual(out.strip(), 'T')

    def test_canon_uninterned_identity_and_first_occurrence_everywhere(self):
        out = run_lisp("""
(let ((a (make-symbol "RAW77")) (b (make-symbol "RAW9")))
  (show (fe-text (list 'f a (list 'quote (list b a)) b))))
""")
        self.assertEqual(out.strip(), '(ACL2::F #1=#:G1 (COMMON-LISP:QUOTE (#2=#:G2 #1#)) #2#)')

    def test_canon_semantic_equivalence_of_three_nontrivial_lambdas(self):
        out = run_lisp("""
(dolist (form
         '((lambda ()
             (let* ((t3 4) (t4 (+ t3 2)))
               (funcall (lambda (&optional (t5 t4 t6) &key ((:k t7) (+ t5 1))
                                 &aux (t8 (+ t7 t3)))
                          (declare (ignorable t6) (type integer t5 t7 t8))
                          (list t5 t7 t8)))))
           (lambda ()
             (labels ((oneify12 (t3)
                        (if (zerop t3) 1 (* t3 (oneify12 (1- t3))))))
               (list (funcall #'oneify12 5) (oneify12 3))))
           (lambda ()
             (block t8
               (let ((t3 0))
                 (tagbody t4 (setq t3 (1+ t3))
                          (if (< t3 4) (go t4) (return-from t8 (list t3)))))))))
  (let ((original (funcall (compile nil form)))
        (canonical (funcall (compile nil (fe-canon form)))))
    (show (equal original canonical))))
""")
        self.assertEqual(out.split(), ['T'] * 3)

    def test_canon_lambda_key_interface_and_sequential_defaults(self):
        out = run_lisp("""
(let* ((form '(lambda (&optional (t3 2 t4) &rest t5 &key (t6 (+ t3 1))
                      &aux (t7 (+ t3 t6)))
               (declare (ignorable t4 t5)) (list t3 t6 t7)))
       (a (compile nil form)) (b (compile nil (fe-canon form))))
  (show (equal (funcall a 5 :t6 8) (funcall b 5 :t6 8)))
  (show (equal (funcall a) (funcall b))))
""")
        self.assertEqual(out.split(), ['T', 'T'])

    def test_canon_remaining_binders_and_declarations(self):
        out = run_lisp("""
(dolist (form
         '((lambda () (multiple-value-bind (t3 t4) (values 2 3)
                        (declare (type integer t3 t4)) (+ t3 t4)))
           (lambda () (let ((x 2)) (symbol-macrolet ((t3 (+ x 4))) (+ t3 t3))))
           (sb-int:named-lambda ordinary-name (t3 &optional (t4 t3)) (+ t3 t4))
           (lambda (t3) (flet ((oneify12 (t4) (return-from oneify12 (+ t3 t4))))
                          (declare (inline oneify12) (ftype (function (t) t) oneify12))
                          (oneify12 3)))))
  (let* ((args (if (member (car form) '(sb-int:named-lambda)) '(4)
                   (if (cadr form) '(4) nil)))
         (a (apply (compile nil form) args))
         (b (apply (compile nil (fe-canon form)) args)))
    (show (equal a b))))
""")
        self.assertEqual(out.split(), ['T'] * 4)

    def test_canon_special_global_free_and_unknown_binders_refused(self):
        out = run_lisp("""
(dolist (form '((let ((t5 1)) (declare (special t5)) t5)
                (defun t5 (t5) t5)
                (progn t5 (let ((t5 1)) t5))
                (let ((t5 t5)) t5)
                (flet ((t5 () (t5))) (t5))
                (lambda ((t5)) t5)
                (macrolet ((t5 () 1)) (t5))
                (let ((t5 1)) (declare (unknown-declaration t5)) t5)))
  (handler-case (progn (fe-canon form) (show "ACCEPTED"))
    (error (e) (show e))))
""")
        self.assertEqual(len(out.splitlines()), 8)
        self.assertTrue(all('T5' in line for line in out.splitlines()))
        self.assertNotIn('ACCEPTED', out)

    def test_canon_macroexpand_all_output_preserves_semantics(self):
        out = run_lisp("""
(dolist (form '((lambda () (let ((t3 4)) (multiple-value-bind (t4 t5) (values t3 2)
                                         (+ t4 t5))))
                (lambda () (flet ((oneify12 () 3)) (oneify12)))
                (lambda () (dotimes (t3 4 t3)))) )
  (let ((expanded (sb-cltl2:macroexpand-all form)))
    (show (equal (funcall (compile nil expanded))
                 (funcall (compile nil (fe-canon expanded)))))))
""")
        self.assertEqual(out.split(), ['T'] * 3)

    def test_canon_first_binding_order_in_labels_and_tagbody(self):
        out = run_lisp("""
(show (fe-text '(labels ((oneify12 (t3) (oneify14 t3))
                        (oneify14 (t4) t4)) (oneify12 1))))
(show (fe-text '(tagbody (let ((t3 1)) (go t4)) t4)))
""").splitlines()
        self.assertIn('ONEIFY1 (ACL2::XTGT2)', out[0])
        self.assertIn('ONEIFY3 (ACL2::XTGT4)', out[0])
        self.assertIn('(COMMON-LISP:GO ACL2::XTGT2)', out[1])
        self.assertIn('((ACL2::XTGT1 1))', out[1])

    def test_canon_namespaces_defaults_and_parallel_let_scope(self):
        out = run_lisp("""
(dolist (form
         '((lambda () (let ((t3 5))
                        (let ((t3 (+ t3 1)) (t4 t3)) (list t3 t4))))
           (lambda () (let ((t3 5))
                        (funcall (lambda (&optional (t3 t3 t4))
                                   (declare (integer t3) (ignorable t4)) t3))))
           (lambda () (let ((t3 5))
                        (flet ((t3 () 2)) (block t3 (+ t3 (t3))))))))
  (show (equal (funcall (compile nil form)) (funcall (compile nil (fe-canon form))))))
""")
        self.assertEqual(out.split(), ['T'] * 3)

    def test_canon_symbol_macro_expansion_with_renamed_dependency_refused(self):
        # A symbol macro's expansion is resolved at its use site. Renaming
        # its definition's T3 to the outer binding would return 1, not 2.
        out = run_lisp("""
(let ((form '(lambda () (let ((t3 1))
                         (symbol-macrolet ((x t3)) (let ((t3 2)) x))))))
  (show (funcall (compile nil form)))
  (handler-case (progn (fe-canon form) (show "ACCEPTED"))
    (error (e) (show e))))
""")
        self.assertEqual(out.splitlines()[0], '2')
        self.assertIn('T3', out)
        self.assertIn('SYMBOL-MACROLET-EXPANSION', out)
        self.assertNotIn('ACCEPTED', out)

    def test_canon_array_literals_preserve_identity_and_prevent_capture(self):
        out = run_lisp("""
(let* ((g (make-symbol "RAW"))
       (form (list 'quote (vector 't3 'oneify7 g g)))
       (data (cadr (fe-canon form))))
  (show (and (eq (aref data 0) 't3) (eq (aref data 1) 'oneify7)
             (eq (aref data 2) (aref data 3))
             (string= (symbol-name (aref data 2)) "G1"))))
(show (fe-text '(let ((t3 1)) (list t3 '#(xtgt1)))))
(handler-case (progn (fe-canon '(let ((t3 1)) (list t3 '#(t3)))) (show "ACCEPTED"))
  (error (e) (show e)))
""")
        self.assertEqual(out.splitlines()[0], 'T')
        self.assertIn('((ACL2::XTGT2 1))', out)
        self.assertIn('forbidden shape QUOTE', out)
        self.assertNotIn('ACCEPTED', out)

    def test_canon_defstruct_keeps_global_name_and_walks_slot_defaults(self):
        out = run_lisp("""
(show (fe-text '(defstruct t44 (slot (let ((t3 1)) t3)))))
(handler-case (progn (fe-canon '(defstruct (f (:constructor make-f (t3))) t3))
                     (show "ACCEPTED"))
  (error (e) (show e)))
""")
        self.assertIn('COMMON-LISP:DEFSTRUCT ACL2::T44', out)
        self.assertIn('((ACL2::XTGT1 1)) ACL2::XTGT1', out)
        self.assertIn('DEFSTRUCT-BOA-CONSTRUCTOR', out)
        self.assertNotIn('ACCEPTED', out)

    def test_canon_proclaimed_special_target_is_skipped(self):
        out = run_lisp("""
(declaim (special xtgt1))
(let* ((form '(lambda () (let ((t3 4)) (funcall (lambda () t3)))))
       (canonical (fe-canon form)))
  (show (fe-text form))
  (show (= (funcall (compile nil form)) (funcall (compile nil canonical)))))
""")
        self.assertIn('((ACL2::XTGT2 4))', out)
        self.assertEqual(out.splitlines()[-1], 'T')

    def test_canon_sbcl_metadata_wrappers_keep_literal_identity(self):
        out = run_lisp("""
(dolist (form '((lambda () (let ((t3 4)) (sb-kernel:the* (integer) t3)))
                (lambda () (let ((t3 4)) (sb-c::with-source-form (+ x 1) t3)))))
  (show (= (funcall (compile nil form)) (funcall (compile nil (fe-canon form))))))
(handler-case
    (progn (fe-canon '(let ((t3 4)) (sb-c::with-source-form (+ t3 1) t3)))
           (show "ACCEPTED"))
  (error (e) (show e)))
""")
        self.assertEqual(out.splitlines()[:2], ['T', 'T'])
        self.assertIn('T3', out)
        self.assertIn('WITH-SOURCE-FORM', out)
        self.assertNotIn('ACCEPTED', out)

    def test_o1_equal_and_renamed_binders(self):
        out = run_lisp('''
(dolist (pair '(((f x) (f x))
                ((let ((a 1)) (+ a a)) (let ((x 1)) (+ x x)))
                ((labels ((f (a) (f a))) (function f))
                 (labels ((g (x) (g x))) (function g)))
                ((block a (return-from a 1)) (block x (return-from x 1)))
                ((tagbody a (go a)) (tagbody x (go x)))
                ((tagbody 1 (go 1)) (tagbody 2 (go 2)))
                ((f . x) (f . x))))
  (show (fe-alpha-equal (car pair) (cadr pair))))
''')
        self.assertEqual(out.split(), ['T'] * 7)

    def test_o1_literal_free_and_global_identity(self):
        out = run_lisp('''
(dolist (pair '(((quote t123) (quote xtgt1)) ((f a) (f x))
                ((defun f (a) a) (defun g (a) a))
                ((function f) (function g))
                ((quote #2A((a b))) (quote #2A((a c))))
                ((quote #2A((a b))) (quote #(a b)))
                ((quote 1.0) (quote 1.0d0))))
  (multiple-value-bind (ok reason) (fe-alpha-equal (car pair) (cadr pair))
    (show ok) (show (and (stringp reason) (plusp (length reason))))))
''')
        self.assertEqual(out.split(), ['NIL', 'T'] * 7)

    def test_o1_capture_and_non_bijective(self):
        out = run_lisp('''
(dolist (pair '(((let ((a 1)) (let ((b 2)) a))
                 (let ((x 1)) (let ((x 2)) x)))
                ((let ((a 1) (b 2)) (+ a b)) (let ((x 1) (x 2)) (+ x x)))
                ((let ((a 1)) x) (let ((x 1)) x))
                ((let ((a 1)) (let ((a 2)) x)) (let ((x 1)) (let ((y 2)) x)))
                ((labels ((f () 1) (g () 2)) (f)) (labels ((x () 1) (x () 2)) (x)))
                ((block a (block b (return-from a 1))) (block x (block x (return-from x 1))))))
  (show (fe-alpha-equal (car pair) (cadr pair))))
''')
        self.assertEqual(out.split(), ['NIL'] * 6)

    def test_o1_uninterned_bijection(self):
        out = run_lisp('''
(let ((a (make-symbol "A")) (b (make-symbol "B"))
      (x (make-symbol "X")) (y (make-symbol "Y")))
  (show (fe-alpha-equal (list 'list a (list 'quote (vector b a)))
                        (list 'list x (list 'quote (vector y x)))))
  (show (fe-alpha-equal (list 'list a a) (list 'list x y)))
  (show (fe-alpha-equal (list 'list a b) (list 'list x x)))
  (show (fe-alpha-equal (list 'let (list (list a 1)) (list 'quote a))
                        (list 'let (list (list x 1)) (list 'quote y)))))
''')
        self.assertEqual(out.split(), ['T', 'NIL', 'NIL', 'NIL'])

    def test_o1_scope_defaults_declarations_and_shapes(self):
        out = run_lisp('''
(dolist (pair '(((lambda (&optional (a 1 p) &key ((:k b) a) &aux (c b))
                  (declare (ignorable p) (type integer a b c)) (list a b c))
                 (lambda (&optional (x 1 q) &key ((:k y) x) &aux (z y))
                  (declare (ignorable q) (type integer x y z)) (list x y z)))
                ((lambda (&key a) a) (lambda (&key ((:a x))) x))
                ((let ((a 1)) (let ((b a)) b)) (let ((x 1)) (let ((y x)) y)))
                ((let* ((a 1) (b a)) b) (let* ((x 1) (y x)) y))))
  (show (fe-alpha-equal (car pair) (cadr pair))))
(dolist (pair '(((lambda (&key a) a) (lambda (&key x) x))
                ((let ((a 1) (b a)) b) (let ((x 1) (y x)) y))
                ((flet ((f () (f))) (f)) (flet ((g () (g))) (g)))
                ((lambda (&optional (a a)) a) (lambda (&optional (x x)) x))
                ((let ((a 1)) (declare (type integer a)) a)
                 (let ((x 1)) (declare (type string x)) x))
                ((lambda (a) a) (lambda (x) x x))
                ((let ((a 1)) a) (let ((x 2)) x))))
  (show (fe-alpha-equal (car pair) (cadr pair))))
''')
        self.assertEqual(out.split(), ['T'] * 4 + ['NIL'] * 7)

    def test_o1_shadowed_scope_and_malformed_shapes(self):
        out = run_lisp('''
(show (fe-alpha-equal '(let ((a 1)) (let ((a 2)) (let ((b 3)) (+ a b))))
                      '(let ((x 1)) (let ((y 2)) (let ((x 3)) (+ y x))))))
(dolist (pair '(((block nil) (block))
                ((lambda (&key a) a) (lambda (&key ((:a x junk))) x))
                ((let ((a 1)) a) (let ((x . 1)) x))
                ((lambda (a) a) (lambda . x))))
  (multiple-value-bind (ok why) (fe-alpha-equal (car pair) (cadr pair))
    (show ok) (show (and (stringp why) (plusp (length why))))))
''')
        self.assertEqual(out.split(), ['T'] + ['NIL', 'T'] * 4)

    def test_o1_all_canon_fixtures_round_trip(self):
        # Reuse every canonicalizer fixture, including dynamically macroexpanded
        # forms. Successful FE-CANON calls are audited through the actual FE-TEXT
        # printer and FE-READ-BLOCK-FORMS reader. Refused fixtures still refuse.
        original_run = run_lisp
        prefix = '''
(defvar *o1-original-canon* (symbol-function 'fe-canon))
(defvar *o1-auditing* nil)
(defvar *o1-errors* nil)
(setf (symbol-function 'fe-canon)
      (lambda (raw)
        (let ((result (funcall *o1-original-canon* raw)))
          (unless *o1-auditing*
            (let ((*o1-auditing* t))
              (multiple-value-bind (ok why)
                  (fe-alpha-equal raw (car (fe-read-block-forms (fe-text raw))))
                (unless ok (push why *o1-errors*)))))
          result)))
'''
        def audited_run(body):
            return original_run(prefix + body + '\n(assert (null *o1-errors*) () "O1: ~s" *o1-errors*)')
        from unittest.mock import patch
        with patch(__name__ + '.run_lisp', side_effect=audited_run):
            for name in sorted(n for n in dir(self) if n.startswith('test_canon_')):
                with self.subTest(fixture=name):
                    getattr(self, name)()

    # -- X1 teeth: a manifest over synthetic units; the world's derivation is the REDERIVE table --------
    SETUP = '''
(defpackage "ACL2_*1*_ACL2" (:use))
(defvar *units* (list (cons "raw:ACL2::F" (format nil ";;;; UNIT raw:ACL2::F~%(DEFUN F (X) (CAR X))~%"))
                      (cons "star1:ACL2::F" (format nil ";;;; UNIT star1:ACL2::F~%(DEFUN ACL2_*1*_ACL2::F (X) (IF (CONSP X) (F X) (ERROR \\"guard\\")))~%"))
                      (cons "raw:ACL2::G" (format nil ";;;; UNIT raw:ACL2::G~%(DEFUN G (X) (F X))~%"))))
(defun manifest (units key)
  (format nil "#world_key~c~a~%#roots~c1~%~{~a~%~}" #\\Tab key #\\Tab
          (mapcar (lambda (u) (format nil "~a~c~a~c~a" (car u) #\\Tab (fe-sha256-hex (cdr u)) #\\Tab "world:defuns")) units)))
(defun defs (units) (format nil "~{~a~}" (mapcar #'cdr units)))
(defun synthetic-forms (text)
  (let ((*fe-dummy-pkg* (find-package "ACL2"))) (fe-read-block-forms text)))
(defun world-of (units)
  (lambda (id) (let ((text (cdr (assoc id units :test #'string=))))
                (values text (when text (synthetic-forms text))))))
(defun swap (units id from to)
  (mapcar (lambda (u) (if (string= (car u) id)
                          (cons id (let ((p (search from (cdr u)))) (concatenate 'string (subseq (cdr u) 0 p) to (subseq (cdr u) (+ p (length from))))))
                          u)) units))
(defun refusals (m d w)
  (let ((raw nil))
    (append (fe-verify-core m d (lambda (id)
                                (multiple-value-bind (text forms) (funcall w id)
                                  (when text (push (cons id forms) raw)) text)) "WORLD1")
            (fe-check-alpha-units
             (mapcar (lambda (b) (cons (car b) (synthetic-forms (cdr b)))) (fe-parse-defs d)) raw))))
(defun mentions (rs id) (and rs (every (lambda (r) (search id r)) rs) t))
'''

    def test_o1_xt_verify_defs_wiring_rejects_shared_text_defect(self):
        out = run_lisp(self.SETUP + '''
;; The synthetic world supplies both text and pre-canonicalization forms.
;; Fault injection makes the text derivation agree with the forged file,
;; exactly the failure that a shared canonicalizer used to conceal.
(let* ((*fe-dummy-pkg* (find-package "ACL2"))
       (*fe-rt* (make-hash-table :test 'eq))
       (world (world-of *units*))
       (current *units*)
       (stubs (list (cons 'fe-index-world (lambda () nil))
                    (cons 'fe-index-sources (lambda (s) (declare (ignore s)) nil))
                    (cons 'fe-read-runtime (lambda (s) (declare (ignore s)) nil))
                    (cons 'fe-specials-from-ids (lambda (ids) (declare (ignore ids)) nil))
                    (cons 'fe-star1-var-refs (lambda (forms) (declare (ignore forms)) nil))
                    (cons 'fe-file-string (lambda (path)
                           (if (search "manifest.tsv" path) (manifest current "WORLD1") (defs current))))
                    (cons 'fe-derive-unit (lambda (id stobjs specials)
                           (declare (ignore stobjs specials))
                           (cons (nth-value 1 (funcall world id)) "synthetic world")))
                    (cons 'fe-block-text (lambda (id forms)
                           (declare (ignore forms)) (cdr (assoc id current :test #'string=))))))
       (saved (mapcar (lambda (s) (cons (car s) (symbol-function (car s)))) stubs)))
  (unwind-protect
      (progn
        (dolist (s stubs) (setf (symbol-function (car s)) (cdr s)))
        (xt-verify-defs "/synthetic" "/unused" "/unused" "WORLD1")
        (setq current (swap *units* "raw:ACL2::F" "(CAR X)" "(CDR X)"))
        (show (fe-verify-core (manifest current "WORLD1") (defs current) (world-of current) "WORLD1"))
        (handler-case (progn (xt-verify-defs "/synthetic" "/unused" "/unused" "WORLD1") (show "ACCEPTED-BAD"))
          (error (e) (show e))))
    (dolist (s saved) (setf (symbol-function (car s)) (cdr s)))))
''')
        self.assertIn('XT-VERIFY-DEFS OK 3 units', out)
        self.assertIn('\nNIL\n', out)  # Existing text/digest gate accepts the injected fault.
        self.assertIn('unit raw:ACL2::F: not alpha-equivalent to the derived form:', out)
        self.assertNotIn('ACCEPTED-BAD', out)
        self.assertNotIn('text differs', out)

    def test_o1_unit_form_count(self):
        out = run_lisp('''
(show (fe-check-alpha-units '(("id" (f) (g))) '(("id" (f)))))
(show (fe-check-alpha-units '(("id" (f))) '(("id" (f) (g)))))
''')
        self.assertEqual(out.count('unit id: not alpha-equivalent to the derived form: form counts differ'), 2)

    def test_clean_defs_are_accepted(self):
        out = run_lisp(self.SETUP + '(show (refusals (manifest *units* "WORLD1") (defs *units*) (world-of *units*)))')
        self.assertEqual(out.strip(), 'NIL')

    def test_exec_swapped_for_logic_is_refused_by_name(self):
        # defs.lisp carries the :logic body where the world derives :exec; the manifest was left alone
        out = run_lisp(self.SETUP + '''
(let ((bad (swap *units* "raw:ACL2::F" "(CAR X)" "(XL-CAR X)")))
  (show (mentions (refusals (manifest *units* "WORLD1") (defs bad) (world-of *units*)) "raw:ACL2::F")))''')
        self.assertEqual(out.strip(), 'T')

    def test_swap_with_manifest_recomputed_is_still_refused(self):
        # a forger who also rewrites the manifest digest is caught by the world re-derivation
        out = run_lisp(self.SETUP + '''
(let ((bad (swap *units* "raw:ACL2::F" "(CAR X)" "(XL-CAR X)")))
  (show (mentions (refusals (manifest bad "WORLD1") (defs bad) (world-of *units*)) "raw:ACL2::F")))''')
        self.assertEqual(out.strip(), 'T')

    def test_star1_with_guard_check_dropped_is_refused_by_name(self):
        out = run_lisp(self.SETUP + '''
(let ((bad (swap *units* "star1:ACL2::F" "(IF (CONSP X) (F X) (ERROR \\"guard\\"))" "(F X)")))
  (show (mentions (refusals (manifest bad "WORLD1") (defs bad) (world-of *units*)) "star1:ACL2::F")))''')
        self.assertEqual(out.strip(), 'T')

    def test_manifest_bound_to_another_world_is_refused(self):
        out = run_lisp(self.SETUP + '''
(show (refusals (manifest *units* "WORLD2") (defs *units*) (world-of *units*)))''')
        self.assertIn('manifest is bound to world WORLD2, not WORLD1', out)

    def test_missing_and_extra_units_are_refused_by_name(self):
        out = run_lisp(self.SETUP + '''
(show (mentions (refusals (manifest *units* "WORLD1") (defs (cdr *units*)) (world-of *units*)) "raw:ACL2::F"))
(let ((extra (append *units* (list (cons "raw:ACL2::H" (format nil ";;;; UNIT raw:ACL2::H~%(DEFUN H (X) X)~%"))))))
  (show (mentions (refusals (manifest *units* "WORLD1") (defs extra) (world-of *units*)) "raw:ACL2::H")))''')
        self.assertEqual(out.split(), ['T', 'T'])

    # -- X2 teeth ---------------------------------------------------------------------------------------
    CLOSURE = '''
(defvar *blocks* (list (cons "raw:ACL2::G" (list (read-from-string "(DEFUN G (X) (F (XL-CAR X)))")))
                       (cons "raw:ACL2::F" (list (read-from-string "(DEFUN F (X) (CAR X))")))))
(defun rt (&rest names) (let ((h (make-hash-table :test 'eq))) (dolist (n names h) (setf (gethash n h) :function))))
'''

    def test_closure_complete_when_every_call_is_extracted_runtime_or_cl(self):
        out = run_lisp(self.CLOSURE + "(show (fe-check-closure *blocks* (rt 'xl-car)))")
        self.assertEqual(out.strip(), 'NIL')

    def test_removing_a_runtime_entry_is_refused_by_name(self):
        out = run_lisp(self.CLOSURE + "(show (fe-check-closure *blocks* (rt)))")
        self.assertIn('raw:ACL2::G references function ACL2::XL-CAR', out)

    def test_removing_an_extracted_def_is_refused_by_name(self):
        out = run_lisp(self.CLOSURE + "(show (fe-check-closure (list (car *blocks*)) (rt 'xl-car)))")
        self.assertIn('raw:ACL2::G references function ACL2::F', out)


# The *1* forms below are what ACL2 8.7's oneify-cltl-code returns (printed by the live harness further down, from
# the local ACL2 launcher): a compliant function, a compliant function of two arguments, an :ideal one
# (runtime symbol-class test), a :program one, and a compliant one whose guard is T.
STAR1_FIXTURES = r"""
(defpackage "ACL2_*1*_ACL2" (:use))
(defpackage "ACL2_*1*_COMMON-LISP" (:use))
(defvar *cap* '(acl2_*1*_acl2::cap (x)
   (when (not (eq (f-get-global 'guard-checking-on *the-live-state*) :none))
     (cond ((natp x) (return-from acl2_*1*_acl2::cap (cap x)))
           ((f-get-global 'guard-checking-on *the-live-state*)
            (throw-raw-ev-fncall (list 'ev-fncall-guard-er 'cap (list x) '(natp x) '(nil) nil)))))
   (labels ((acl2_*1*_acl2::cap (x)
              (if (acl2_*1*_acl2::zp x) '0
                  (acl2_*1*_acl2::binary-+ '1 (acl2_*1*_acl2::cap (acl2_*1*_acl2::binary-+ '-1 x))))))
     (acl2_*1*_acl2::cap x))))
(defvar *ideal* '(acl2_*1*_acl2::idl (x)
   (when (eq (symbol-class 'idl (w *the-live-state*)) :common-lisp-compliant)
     (return-from acl2_*1*_acl2::idl (idl x)))
   (labels ((acl2_*1*_acl2::idl (x)
              (if (consp x) (acl2_*1*_acl2::binary-+ '1 (acl2_*1*_acl2::idl (acl2_*1*_common-lisp::cdr x))) '0)))
     (acl2_*1*_acl2::idl x))))
(defvar *program* '(acl2_*1*_acl2::prg (x)
   (cond ((or (member-eq (f-get-global 'guard-checking-on *the-live-state*) '(:none :all))
              (f-get-global 'safe-mode *the-live-state*))
          (return-from acl2_*1*_acl2::prg (if (consp x) (acl2_*1*_acl2::binary-+ '1 (acl2_*1*_acl2::prg (acl2_*1*_common-lisp::cdr x))) '0))))
   (prg x)))
(defvar *guard-t* '(acl2_*1*_acl2::gt (x) (gt x)))
(defun star1-names (o)
  (let ((fns (make-hash-table :test 'eq)) (vars (make-hash-table :test 'eq)) (out nil))
    (fe-calls (fe-walkable (cons 'defun o)) fns vars)
    (maphash (lambda (s v) (declare (ignore v)) (when (fe-star1-p s) (push (symbol-name s) out))) fns)
    (sort out #'string<)))
"""


@unittest.skipUnless(SBCL, 'SBCL required')
class StarOneTrimTests(unittest.TestCase):
    """fe-star1-trim and its premise check, on *1* forms as ACL2 8.7 oneifies them (the live differential against
    the real oneify is StarOneTrimLiveTests)."""

    def lisp(self, body):
        return run_lisp(STAR1_FIXTURES + body)

    def test_trim_removes_exactly_the_labels_form_and_its_callee_star1_edges(self):
        out = self.lisp("""
(show (star1-names *cap*))
(show (star1-names (fe-star1-trim 'cap *cap*)))
(show (equal (butlast (fe-star1-trim 'cap *cap*)) (butlast *cap*)))
(show (car (last (fe-star1-trim 'cap *cap*))))""")
        lines = out.strip().splitlines()
        self.assertIn('ZP', lines[0])
        self.assertIn('BINARY-+', lines[0])
        self.assertEqual(lines[1], 'NIL')
        self.assertEqual(lines[2], 'T')
        self.assertEqual(lines[3], "(XL-STAR1-LOGIC-PATH-DROPPED 'CAP)")

    def test_trim_applies_only_to_the_compliant_shape(self):
        out = self.lisp("""
(show (list (eq (fe-star1-trim 'idl *ideal*) *ideal*)
            (eq (fe-star1-trim 'prg *program*) *program*)
            (eq (fe-star1-trim 'gt *guard-t*) *guard-t*)))""")
        self.assertEqual(out.strip(), '(T T T)')

    def test_a_compliant_form_without_its_guard_violation_clause_is_not_trimmed(self):
        out = self.lisp("""
(let ((bad (subst nil '(throw-raw-ev-fncall (list 'ev-fncall-guard-er 'cap (list x) '(natp x) '(nil) nil)) *cap* :test #'equal)))
  (show (eq (fe-star1-trim 'cap bad) bad)))
(let ((bad (subst '(acl2_*1*_acl2::cap x) '(return-from acl2_*1*_acl2::cap (cap x)) *cap* :test #'equal)))
  (show (eq (fe-star1-trim 'cap bad) bad)))""")
        self.assertEqual(out.split(), ['T', 'T'])

    def test_compliant_predicate_is_logic_mode_and_the_worlds_symbol_class(self):
        out = self.lisp("""
(defvar *fe-w* nil)
(defun symbol-class (f w) (declare (ignore w)) (get f 'cls))
(setf (get 'cap 'cls) :common-lisp-compliant (get 'idl 'cls) :ideal (get 'prg 'cls) :program)
(show (list (fe-star1-compliant-p 'cap :logic) (fe-star1-compliant-p 'idl :logic)
            (fe-star1-compliant-p 'prg :program) (fe-star1-compliant-p 'cap :program)))""")
        self.assertEqual(out.strip(), '(T NIL NIL NIL)')

    PREMISE = r"""
(defvar *the-live-state* nil)
(defvar *gc* t) (defvar *safe* nil)
(defun global-symbol (s) (intern (symbol-name s) (or (find-package "ACL2_GLOBAL_ACL2") (make-package "ACL2_GLOBAL_ACL2" :use nil))))
(defun f-get-global (s st) (declare (ignore st)) (if (eq s 'guard-checking-on) *gc* *safe*))
(defun premise-result (units)
  (handler-case (progn (fe-check-star1-premise units) :ok) (error (c) (princ-to-string c))))
(defvar *cell* (global-symbol 'guard-checking-on))
"""

    def test_premise_accepts_reads_and_locals_named_safe_mode(self):
        out = self.lisp(self.PREMISE + """
(show (premise-result (list (cons "raw:ACL2::A" (list `(defun a (safe-mode) (let ((safe-mode 1)) (let nil (declare (special ,*cell*)) ,*cell*)))))
                            (cons "raw:ACL2::B" (list '(defun b () (quote (and safe-mode guard-checking-on))))))))""")
        self.assertEqual(out.strip(), 'OK')

    def test_premise_refuses_a_unit_that_binds_assigns_or_names_the_cell(self):
        for form in ("`(defun w () (let ((,*cell* nil)) 1))", "`(defun w () (setq ,*cell* nil))",
                     "`(defun w () (set ',*cell* nil))", "`(defun w () (f-put-global 'guard-checking-on nil state))",
                     "`(defun w () (put-global 'safe-mode t state))",
                     "`(defun w (syms) (progv syms '(nil) 1))",
                     "`(let ((,*cell* nil)) 1)"):
            out = self.lisp(self.PREMISE + '(show (premise-result (list (cons "raw:ACL2::OK" (list \'(defun ok () 1))) (cons "raw:ACL2::W" (list %s)))))' % form)
            self.assertIn('unit raw:ACL2::W', out, form)
            self.assertNotIn('unit raw:ACL2::OK', out, form)

    def test_premise_refuses_codex_review_witness_a_raw_helper_that_sets_a_computed_symbol(self):
        # REVIEW1.md section 3 (live-review.lsp): both units passed the scan before computed writes were refused.
        out = self.lisp(self.PREMISE + """
(let ((units (list (cons "raw:ACL2::R4-INDIRECT-SET"
                         (list (fe-expand-def '(r4-indirect-set (name value) (set (global-symbol name) value)))))
                   (cons "raw:ACL2::R4-ENTER"
                         (list (fe-expand-def '(r4-enter () (r4-indirect-set 'guard-checking-on nil))))))))
  (show (premise-result units)))""")
        self.assertIn('unit raw:ACL2::R4-INDIRECT-SET', out)
        self.assertIn('COMPUTED-WRITE', out)

    def test_premise_refuses_each_computed_write_form_and_a_computed_setter_key(self):
        for form in ("(set (global-symbol k) 1)", "(setf (symbol-value k) 1)", "(makunbound k)",
                     "(setf (sb-ext:symbol-global-value k) 1)", "(f-put-global k 1 st)", "(put-global k 1 st)"):
            out = self.lisp(self.PREMISE + '(show (premise-result (list (cons "raw:ACL2::W" (list (fe-expand-def \'(w (k st) %s)))))))' % form)
            self.assertIn('unit raw:ACL2::W', out, form)

    def test_premise_does_not_mistake_a_variable_named_set_for_a_call(self):
        out = self.lisp(self.PREMISE + """
(show (premise-result (list (cons "raw:ACL2::OK" (list (fe-expand-def '(ok (x) (let ((set (car x))) (set-foo set))))
                                                        (fe-expand-def '(ok2 (set) (flet ((g (set) set)) (g set)))))))))""")
        self.assertEqual(out.strip(), 'OK')

    def test_named_exceptions_match_only_their_unit_and_their_kind(self):
        out = self.lisp(self.PREMISE + """
(defvar *flush* (fe-expand-def '(memoize-flush1 (s) (set (the symbol s) nil))))
(show (premise-result (list (cons "raw:ACL2::MEMOIZE-FLUSH1" (list *flush*)))))
(show (search "unit raw:ACL2::OTHER" (premise-result (list (cons "raw:ACL2::OTHER" (list *flush*))))))
(show (search "unit raw:ACL2::MEMOIZE-FLUSH1" (premise-result (list (cons "raw:ACL2::MEMOIZE-FLUSH1"
        (list (fe-expand-def (list 'memoize-flush1 '(s) (list 'setq *cell* nil)))))))))
(show (search "unit raw:ACL2::MEMOIZE-FLUSH1" (premise-result (list (cons "raw:ACL2::MEMOIZE-FLUSH1"
        (list (fe-expand-def (list 'memoize-flush1 '(s) (list 'let (list (list *cell* nil)) 1)))))))))
(show (premise-result (list (cons "star1:ACL2::PUT-GLOBAL" (list (fe-expand-def '(put-global (k v st) (f-put-global k v st))))))))
(show (search "unit raw:ACL2::PUT-GLOBAL" (premise-result (list (cons "raw:ACL2::PUT-GLOBAL" (list (fe-expand-def '(put-global (k v st) (f-put-global k v st)))))))))""")
        lines = out.split('\n')
        lines = [l for l in lines if l.strip()]
        self.assertEqual(lines[0], 'OK')
        self.assertNotEqual(lines[1], 'NIL')
        self.assertNotEqual(lines[3], 'NIL')
        self.assertEqual(lines[4], 'OK')
        self.assertNotEqual(lines[5], 'NIL')

    def test_premise_refuses_a_session_that_is_not_guard_checking_t_and_safe_mode_nil(self):
        out = self.lisp(self.PREMISE + '(setq *gc* nil) (show (premise-result nil)) (setq *gc* t *safe* t) (show (premise-result nil))')
        first, second = out.strip().splitlines()
        self.assertIn('guard-checking-on is NIL', first.upper().replace('GUARD-CHECKING-ON IS', 'guard-checking-on is'))
        self.assertIn('safe-mode', second.lower())


LIVE_HARNESS = r"""
(set-ld-prompt nil state)
(defun cap (x) (declare (xargs :guard (natp x))) (if (zp x) 0 (+ 1 (cap (- x 1)))))
(defun two (x y) (declare (xargs :guard (and (natp x) (true-listp y)))) (+ x (len y)))
(defun mb (x) (declare (xargs :guard (natp x))) (mbe :logic (+ 1 x) :exec (1+ x)))
(defun idl (x) (if (consp x) (+ 1 (idl (cdr x))) 0))
(defun prg (x) (declare (xargs :mode :program)) (if (consp x) (+ 1 (prg (cdr x))) 0))
(defun gt (x) (declare (xargs :guard t)) (if (consp x) 1 0))
(defstobj st (fld :type integer :initially 0))
(defun sget (st) (declare (xargs :stobjs st :guard (natp (fld st)))) (+ 1 (fld st)))
:q
(load "FORMS")
(in-package "ACL2")
(fe-index-world)
(defun xl-star1-logic-path-dropped (fn) (throw 'trap (list :trap fn)))
(defun squeeze (string)
  (with-output-to-string (o)
    (let ((space nil))
      (loop for c across string
            do (if (member c '(#\Space #\Newline #\Tab)) (setq space t)
                 (progn (when space (write-char #\Space o) (setq space nil)) (write-char c o)))))))
(defun outcome (thunk)
  "(:value v), (:trap f), or (:error condition-text printed-text): the guard violation is the text ACL2 prints."
  (let* ((printed (make-string-output-stream))
         (co (get *standard-co* *open-output-channel-key*))
         (r (unwind-protect
                (progn (setf (get *standard-co* *open-output-channel-key*) printed)
                       (catch 'trap
                         (catch 'raw-ev-fncall
                           (let ((*standard-output* printed) (*error-output* printed))
                             (handler-case (list :value (funcall thunk))
                               (error (c) (list :error (princ-to-string c))))))))
              (setf (get *standard-co* *open-output-channel-key*) co))))
    (if (eq (car r) :error)
        (list :error (squeeze (get-output-stream-string printed)) (squeeze (cadr r)))
      r)))
(defun drop-gc-clause (x)
  "The mutant: the guard-violation clause of the early exit removed."
  (cond ((atom x) x)
        ((and (eq (car x) 'cond) (some (lambda (c) (equal (car c) '(f-get-global 'guard-checking-on *the-live-state*))) (cdr x)))
         (cons 'cond (remove-if (lambda (c) (equal (car c) '(f-get-global 'guard-checking-on *the-live-state*))) (cdr x))))
        (t (cons (drop-gc-clause (car x)) (drop-gc-clause (cdr x))))))
(defun star1-of (f)
  (let* ((e (gethash f *fe-defs*)))
    (oneify-cltl-code (car e) (caddr e) (if (consp (cadr e)) (cdr (cadr e)) nil) (w *the-live-state*))))
(defun install (o) (eval (cons 'defun o)) (symbol-function (car o)))
(defun live-st () (cdr (assoc 'st *user-stobj-alist*)))
(defun cases (f)
  (case f
    (cap '(((3) "ok") ((-1) "bad") ((nil) "bad")))
    (two '(((2 (a b)) "ok") ((2 7) "bad") ((-1 nil) "bad")))
    (mb '(((4) "ok") ((-2) "bad")))
    (sget (list (list (list (live-st)) "ok") (list (list (list 5)) "nonlive-ok")))))
(dolist (f '(idl prg gt))
  (let ((o (star1-of f)))
    (format t "~%R UNCHANGED ~a ~a~%" f (eq o (fe-star1-trim f o)))))
(dolist (f '(cap two mb sget))
  (let* ((o (star1-of f)) (star1 (car o)) (orig (symbol-function star1))
         (trim (install (fe-star1-trim f o)))
         (mutant (install (drop-gc-clause (fe-star1-trim f o)))))
    (format t "~%R COMPLIANT ~a ~a SHAPE ~a~%" f (fe-star1-compliant-p f :logic) (fe-star1-trimmable-shape-p f o))
    (setf (symbol-function star1) orig)
    (dolist (gc '(t :all nil :none))
      (dolist (c (cases f))
        (when (eq f 'sget) (update-fld 0 (live-st)))
        (let ((row nil))
          (dolist (v (list (cons :orig orig) (cons :trim trim) (cons :mutant mutant)))
            (f-put-global 'guard-checking-on gc *the-live-state*)
            (push (cons (car v) (outcome (lambda () (apply (cdr v) (car c))))) row))
          (format t "~%R ROW ~a ~s ~a~%" f gc (cadr c))
          (dolist (r (reverse row)) (let ((*print-pretty* nil)) (format t "~%R OUT ~a ~s~%" (car r) (cdr r)))))))))
(f-put-global 'guard-checking-on t *the-live-state*)
"""


def local_acl2():
    launcher = os.environ.get('FN_ACL2') or str(Path.home() / 'tools/acl2-fn/acl2-literal-4g-tls64k')
    return launcher if os.access(launcher, os.X_OK) else None


@unittest.skipUnless(local_acl2(), 'a local ACL2 launcher is required (FN_ACL2)')
class StarOneTrimLiveTests(unittest.TestCase):
    """S1 against the real oneify: each toy function is oneified by ACL2 8.7 in the local image, the trimmed form is
    installed over the real *1* function, and the two run side by side under guard-checking-on T, :all, NIL and :none."""

    @classmethod
    def setUpClass(cls):
        with tempfile.TemporaryDirectory() as directory:
            script = Path(directory) / 'harness.lsp'
            script.write_text(LIVE_HARNESS.replace('FORMS', str(FORMS)))
            run = subprocess.run(['timeout', '600', local_acl2()], input=script.read_text(), cwd=ROOT,
                                 capture_output=True, text=True, timeout=700)
        cls.output = run.stdout
        cls.unchanged, cls.compliant, cls.rows = {}, {}, []
        for line in run.stdout.splitlines():
            if line.startswith('R UNCHANGED'):
                _, _, f, same = line.split()
                cls.unchanged[f] = same
            elif line.startswith('R COMPLIANT'):
                parts = line.split()
                cls.compliant[parts[2]] = (parts[3], parts[5])
            elif line.startswith('R ROW'):
                _, _, f, gc, kind = line.split(None, 4)
                cls.rows.append({'f': f, 'gc': gc, 'kind': kind.strip(), 'out': {}})
            elif line.startswith('R OUT'):
                _, _, variant, rest = line.split(None, 3)
                cls.rows[-1]['out'][variant] = rest.strip()

    def rows_for(self, gcs, kinds=None):
        return [r for r in self.rows if r['gc'] in gcs and (kinds is None or r['kind'] in kinds)]

    def test_harness_ran(self):
        self.assertEqual(sorted(self.compliant), ['CAP', 'MB', 'SGET', 'TWO'], self.output[-2000:])
        self.assertTrue(self.rows, self.output[-2000:])

    def test_only_compliant_functions_with_the_recognised_shape_are_trimmed(self):
        for f, (compliant, shape) in self.compliant.items():
            self.assertEqual((compliant, shape), ('T', 'T'), f)
        self.assertEqual(self.unchanged, {'IDL': 'T', 'PRG': 'T', 'GT': 'T'})

    def test_guard_checking_t_and_all_agree_with_oneify_on_values_and_on_the_guard_violation(self):
        rows = self.rows_for({'T', ':ALL'}, {'ok', 'bad'})
        self.assertGreaterEqual(len(rows), 14)
        for r in rows:
            self.assertEqual(r['out']['TRIM'], r['out']['ORIG'], r)
        bad = [r for r in rows if r['kind'] == 'bad']
        self.assertTrue(all(':ERROR' in r['out']['ORIG'] and 'guard' in r['out']['ORIG'] for r in bad))

    def test_guard_checking_nil_keeps_the_raw_value_and_traps_by_name_where_oneify_took_the_logic_path(self):
        for r in self.rows_for({'NIL'}, {'ok'}):
            self.assertEqual(r['out']['TRIM'], r['out']['ORIG'], r)
        for r in self.rows_for({'NIL'}, {'bad'}):
            self.assertEqual(r['out']['TRIM'], '(:TRAP %s)' % r['f'], r)
            self.assertTrue(r['out']['ORIG'].startswith('(:VALUE'), r)

    def test_guard_checking_none_always_traps_by_name(self):
        rows = self.rows_for({':NONE'}, {'ok', 'bad'})
        self.assertTrue(rows)
        for r in rows:
            self.assertEqual(r['out']['TRIM'], '(:TRAP %s)' % r['f'], r)

    def test_a_stobj_argument_that_is_not_live_traps_by_name(self):
        rows = self.rows_for({'T'}, {'nonlive-ok'})
        self.assertEqual(len(rows), 1)
        self.assertEqual(rows[0]['out']['TRIM'], '(:TRAP SGET)')
        self.assertTrue(rows[0]['out']['ORIG'].startswith('(:VALUE'), rows[0])

    def test_mutant_that_drops_the_guard_violation_clause_is_caught_by_the_agreement_check(self):
        rows = self.rows_for({'T', ':ALL'}, {'ok', 'bad'})
        mismatching = [r for r in rows if r['out']['MUTANT'] != r['out']['ORIG']]
        self.assertTrue(mismatching, 'the agreement check cannot see the dropped guard-violation clause')
        self.assertTrue(all(r['kind'] == 'bad' for r in mismatching))
        self.assertTrue(all(r['out']['TRIM'] == r['out']['ORIG'] for r in mismatching))


@unittest.skipUnless(os.environ.get('FN_EXTRACT_FORMS_WORLD'), 'an extraction world image is required')
class FormsWorldTests(unittest.TestCase):
    """Against the real world: run on hbox with FN_EXTRACT_FORMS_WORLD (a world launcher) and
    FN_EXTRACT_FORMS_OUT (an export directory made by xt-fe-export with world key FN_EXTRACT_FORMS_KEY)."""

    def verify(self, out_dir):
        world = os.environ['FN_EXTRACT_FORMS_WORLD']
        key = os.environ['FN_EXTRACT_FORMS_KEY']
        script = ('(ld "tools/extract/frontend.lisp")\n:q\n(load "tools/extract/forms-export.lisp")\n(in-package "ACL2")\n'
                  '(handler-case (xt-verify-defs "%s" "%s" "tools/extract/clruntime.lisp" "%s")\n'
                  '  (error (e) (format t "~&VERIFY-ERROR ~a~%%" e)))\n(sb-ext:exit)\n'
                  % (out_dir, os.environ.get('FN_EXTRACT_FORMS_SRC', '/tank/fn/acl2-8.7'), key))
        run = subprocess.run(['timeout', '900', world], input=script, capture_output=True, text=True, cwd=ROOT)
        return run.stdout

    def mutated(self, edit):
        source = Path(os.environ['FN_EXTRACT_FORMS_OUT'])
        copy = Path(tempfile.mkdtemp())
        self.addCleanup(shutil.rmtree, copy, True)
        for name in ('defs.lisp', 'manifest.tsv'):
            shutil.copy(source / name, copy / name)
        edit(copy)
        return self.verify(str(copy))

    def test_unmutated_defs_verify(self):
        self.assertIn('XT-VERIFY-DEFS OK', self.verify(os.environ['FN_EXTRACT_FORMS_OUT']))

    def test_one_unit_edited_is_refused_by_name(self):
        def edit(copy):
            text = (copy / 'defs.lisp').read_text('latin-1')
            head = ';;;; UNIT raw:ACL2::FN-ZC-OWED\n'
            self.assertTrue(head in text)
            at = text.index(head) + len(head)
            text = text[:at] + text[at:].replace('COMMON-LISP:DEFUN', 'COMMON-LISP:DEFMACRO', 1)
            (copy / 'defs.lisp').write_text(text, 'latin-1')
        out = self.mutated(edit)
        self.assertIn('unit raw:ACL2::FN-ZC-OWED', out)

    def test_manifest_bound_to_another_world_is_refused(self):
        def edit(copy):
            text = (copy / 'manifest.tsv').read_text('latin-1')
            (copy / 'manifest.tsv').write_text(text.replace('#world_key\t', '#world_key\tOTHER', 1), 'latin-1')
        self.assertIn('manifest is bound to world OTHER', self.mutated(edit))


if __name__ == '__main__':
    unittest.main()
