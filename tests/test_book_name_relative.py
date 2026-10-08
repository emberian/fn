"""Exercise the actual world-dump consumers through the pooled ACL2 wrapper."""
import os
from pathlib import Path
import shutil
import subprocess
import sys
import unittest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "tools"))
import acl2_slots


@unittest.skipUnless(shutil.which(acl2_slots.configured_acl2()), "no ACL2 launcher")
class BookNameDumpTests(unittest.TestCase):
    def run_acl2(self, script):
        # The wrapper owns a shared slot; no private pool for this real prover.
        return subprocess.run(
            [sys.executable, str(ROOT / "tools/acl2"), "--timeout", "90",
             "--label", "book-name-dump-tests"],
            input=script, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
            cwd=ROOT, timeout=100, env={**os.environ, "FN_ACL2_SLOT_WAIT": "15"})

    def test_raw_measurement_without_a_certified_fn_world(self):
        result = self.run_acl2(r'''
:q
(handler-case
 (progn
  (assert (not (fboundp 'book-name-relative)))
  (load "tools/runtime_image/closure.lisp")
  (assert (equal (ri-book-string '(:fn . "books/a.lisp")) "books/a.lisp"))
  (format t "~%FN-BOOK-NAME-RAW-PASS~%")
  (sb-ext:exit :code 0))
 (error (e) (format t "~%FN-BOOK-NAME-RAW-ERROR: ~a~%" e)
            (sb-ext:exit :code 1)))
''')
        self.assertEqual(result.returncode, 0, result.stdout[-10000:])
        self.assertIn("FN-BOOK-NAME-RAW-PASS", result.stdout)

    def test_project_and_absolute_names_agree_in_all_dump_consumers(self):
        script = r'''
(ld "tools/coverage_dump.lisp")
:q
(handler-case
 (progn
  (load "tools/runtime_image/closure.lisp")
  (load "tools/image_anatomy/ia-anatomy.lisp")
  (let* ((projects (project-dir-alist (w *the-live-state*)))
         (root (cdr (assoc :fn projects)))
         (relative "books/assumptions-recovery.lisp")
         (absolute (concatenate 'string root relative))
         (project (cons :fn relative)))
    (assert (equal (cov-book-string project projects) relative))
    (assert (equal (cov-book-string absolute projects) relative))
    (assert (equal (ri-book-string project) relative))
    (assert (equal (ri-book-string absolute) relative))
    (assert (equal (ia-book-class project) "fn-books"))
    (assert (equal (ia-book-class absolute) "fn-books"))
    (assert (equal (cov-book-string '(:system . "books/a.lisp") projects)
                   ":system/books/a.lisp"))
    (assert (equal (ri-book-string '(:system . "books/a.lisp"))
                   ":system/books/a.lisp"))
    (assert (equal (ia-book-class '(:system . "books/a.lisp")) "community-books"))
    (assert (equal (ia-book-class '(:other . "books/a.lisp")) "other-book")))
  (format t "~%FN-BOOK-NAME-DUMPS-PASS~%")
  (sb-ext:exit :code 0))
 (error (e) (format t "~%FN-BOOK-NAME-DUMPS-ERROR: ~a~%" e)
            (sb-ext:exit :code 1)))
'''
        result = self.run_acl2(script)
        self.assertEqual(result.returncode, 0, result.stdout[-10000:])
        self.assertNotIn("ACL2 Error", result.stdout)
        self.assertIn("FN-BOOK-NAME-DUMPS-PASS", result.stdout)


if __name__ == "__main__":
    unittest.main()
