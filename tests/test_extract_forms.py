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

    def test_canonical_text_renames_generated_names_only(self):
        out = run_lisp('''
(let ((g1 (make-symbol "G77")) (g2 (make-symbol "G5")))
  (show (fe-text (list 'f g1 g2 g1 'ONEIFY4581 'T107 'T109 'real)))
  (show (fe-text (list 'f (make-symbol "A") (make-symbol "B") nil 'ONEIFY12 'T3 'T4 'real))))''')
        first, second = out.strip().split('\n')
        self.assertEqual(first, '(ACL2::F #1=#:G1 #:G2 #1# ACL2::ONEIFY3 ACL2::XTGT4 ACL2::XTGT5 COMMON-LISP:REAL)')
        self.assertEqual(second, '(ACL2::F #:G1 #:G2 COMMON-LISP:NIL ACL2::ONEIFY3 ACL2::XTGT4 ACL2::XTGT5 COMMON-LISP:REAL)')

    # -- X1 teeth: a manifest over synthetic units; the world's derivation is the REDERIVE table --------
    SETUP = '''
(defvar *units* (list (cons "raw:ACL2::F" (format nil ";;;; UNIT raw:ACL2::F~%(DEFUN F (X) (CAR X))~%"))
                      (cons "star1:ACL2::F" (format nil ";;;; UNIT star1:ACL2::F~%(DEFUN ACL2_*1*_ACL2::F (X) (IF (CONSP X) (F X) (ERROR \\"guard\\")))~%"))
                      (cons "raw:ACL2::G" (format nil ";;;; UNIT raw:ACL2::G~%(DEFUN G (X) (F X))~%"))))
(defun manifest (units key)
  (format nil "#world_key~c~a~%#roots~c1~%~{~a~%~}" #\\Tab key #\\Tab
          (mapcar (lambda (u) (format nil "~a~c~a~c~a" (car u) #\\Tab (fe-sha256-hex (cdr u)) #\\Tab "world:defuns")) units)))
(defun defs (units) (format nil "~{~a~}" (mapcar #'cdr units)))
(defun world-of (units) (lambda (id) (cdr (assoc id units :test #'string=))))
(defun swap (units id from to)
  (mapcar (lambda (u) (if (string= (car u) id)
                          (cons id (let ((p (search from (cdr u)))) (concatenate 'string (subseq (cdr u) 0 p) to (subseq (cdr u) (+ p (length from))))))
                          u)) units))
(defun refusals (m d w) (fe-verify-core m d w "WORLD1"))
(defun mentions (rs id) (and rs (every (lambda (r) (search id r)) rs) t))
'''

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
            head = ';;;; UNIT raw:ACL2::FN-OCTETS-LEN\n'
            self.assertIn(head, text)
            at = text.index(head) + len(head)
            text = text[:at] + text[at:].replace('COMMON-LISP:DEFUN', 'COMMON-LISP:DEFMACRO', 1)
            (copy / 'defs.lisp').write_text(text, 'latin-1')
        out = self.mutated(edit)
        self.assertIn('unit raw:ACL2::FN-OCTETS-LEN', out)

    def test_manifest_bound_to_another_world_is_refused(self):
        def edit(copy):
            text = (copy / 'manifest.tsv').read_text('latin-1')
            (copy / 'manifest.tsv').write_text(text.replace('#world_key\t', '#world_key\tOTHER', 1), 'latin-1')
        self.assertIn('manifest is bound to world OTHER', self.mutated(edit))


if __name__ == '__main__':
    unittest.main()
