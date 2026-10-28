(in-package "ACL2")
(include-book "../books/owed")
(include-book "std/testing/must-fail" :dir :system)

(defun fn2-owed-sample-positive () (and (natp 1) (<= 0 1)))
(defun fn2-owed-sample-negative () (and (not (natp -1)) (not (<= 0 -1))))
(local
 (defthm-owed fn2-owed-sample (x)
  (implies (natp x) (<= 0 x))
  :teeth (fn2-owed-sample-positive fn2-owed-sample-negative)
  :doc "Translation/registration fixture; not a theorem."))
(fn2-assert-owed-teeth fn2-owed-sample)
(assert-event (not (getpropc 'fn2-owed-sample 'theorem nil (w state))))

(must-fail
 (defthm-owed fn2-owed-prose (x) (equal x x) :teeth "not executable")
 :expected :hard :with-output-off nil :check-expansion t)
(local
 (defthm-owed fn2-owed-missing (x) (equal x x)
   :teeth (fn2-owed-no-such-evaluator)))
(must-fail (fn2-assert-owed-teeth fn2-owed-missing)
 :expected :any :with-output-off nil)
(defun fn2-owed-false-tooth () nil)
(local
 (defthm-owed fn2-owed-false (x) (equal x x)
   :teeth (fn2-owed-false-tooth)))
(must-fail (fn2-assert-owed-teeth fn2-owed-false)
 :with-output-off nil)
(value-triple (cw "OWED UNIT: prose, missing evaluator, false evaluator refused PASS~%"))
