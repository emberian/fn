"""tools/extract/clruntime.lisp's fast alists: hons-get/hons-acons/
make-fast-alist/fast-alist-free over a hash table give the logical answer
(hons-assoc-equal over the alist) on every version, old ones included."""
import shutil
import subprocess
import tempfile
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
RUNTIME = ROOT / "tools" / "extract" / "clruntime.lisp"

DRIVER = r"""
(defpackage "ACL2" (:use "COMMON-LISP"))
(defpackage "ACL2_INVISIBLE" (:use))
(handler-bind ((warning #'muffle-warning))
  (load (compile-file "%(runtime)s" :output-file "%(fasl)s")))
(in-package "ACL2")
(defun logic-get (key alist)            ; hons-assoc-equal, ACL2's logic
  (cond ((atom alist) nil)
        ((and (consp (car alist)) (equal key (caar alist))) (car alist))
        (t (logic-get key (cdr alist)))))
(defun key (n) (map 'list #'char-code (format nil "<m~d@example.org>" n)))
(defvar *bad* 0)
(defun check (label key alist)
  (unless (eq (hons-get key alist) (logic-get key alist))
    (incf *bad*) (format t "MISMATCH ~a ~s~%%" label key)))
;; random operations over several live versions
(let ((*random-state* (sb-ext:seed-random-state 7))
      (versions (list nil)))
  (dotimes (i 4000)
    (let* ((base (nth (random (length versions)) versions))
           (k (key (random 300)))
           (op (random 10)))
      (cond ((< op 6) (push (hons-acons k i base) versions))
            ((= op 6) (make-fast-alist base))
            ((= op 7) (fast-alist-free base))
            (t (check "get" k base)))))
  (dolist (v versions) (dotimes (j 20) (check "final" (key j) v))))
;; a slow alist (never fast) and shadowed keys: the first binding wins
(let ((slow (list (cons (key 1) :a) 'junk (cons (key 1) :b) (cons (key 2) :c))))
  (check "slow" (key 1) slow)
  (make-fast-alist slow)
  (check "made" (key 1) slow) (check "made2" (key 2) slow))
;; the measurement: 25k distinct keys, then 25k lookups
(let ((n 25000) (fast nil) (walk nil))
  (let ((start (get-internal-real-time)))
    (dotimes (i n) (setq fast (hons-acons (key i) i fast)))
    (dotimes (i n) (unless (eql (cdr (hons-get (key i) fast)) i) (incf *bad*)))
    (format t "FAST ~,3f s~%%" (/ (- (get-internal-real-time) start) internal-time-units-per-second)))
  (setq walk (copy-list fast))
  (let ((start (get-internal-real-time)))
    (dotimes (i n) (unless (eql (cdr (logic-get (key i) walk)) i) (incf *bad*)))
    (format t "WALK ~,3f s~%%" (/ (- (get-internal-real-time) start) internal-time-units-per-second))))
(format t "BAD ~d~%%" *bad*)
"""


@unittest.skipUnless(shutil.which("sbcl"), "no sbcl")
class FastAlistTests(unittest.TestCase):
    def test_every_version_answers_as_the_logic_and_lookups_are_hashed(self):
        with tempfile.TemporaryDirectory() as directory:
            driver = Path(directory) / "driver.lisp"
            driver.write_text(DRIVER % {"runtime": RUNTIME,
                                        "fasl": Path(directory) / "clruntime.fasl"})
            done = subprocess.run(["sbcl", "--script", str(driver)], capture_output=True,
                                  text=True, timeout=600)
        out = done.stdout
        self.assertEqual(done.returncode, 0, done.stderr[-2000:])
        self.assertIn("BAD 0", out, out[-2000:])
        fast = float(out.split("FAST ")[1].split()[0])
        walk = float(out.split("WALK ")[1].split()[0])
        print(f"\n25k keys: hashed build+lookup {fast:.3f} s, walked lookup {walk:.3f} s")
        self.assertLess(fast, walk)


if __name__ == "__main__":
    unittest.main()
