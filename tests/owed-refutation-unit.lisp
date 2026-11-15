(in-package "ACL2")
(include-book "../books/owed-report")
(include-book "std/testing/must-fail" :dir :system)

(defun fn2-refutation-positive () (natp 0))
(defun fn2-refutation-negative () (not (natp -1)))
(defthm-owed fn2-refutation-original (x) (natp x)
 :teeth (fn2-refutation-positive fn2-refutation-negative)
 :doc "False universal fixture; its stronger guarded replacement is distinct.")
(defthm-owed fn2-refutation-other (x) (natp x)
 :teeth (fn2-refutation-positive fn2-refutation-negative))
(defthm fn2-refutation-guarded (implies (integerp x) (integerp x)) :rule-classes nil)
(defthm fn2-refutation-ground (not (fn2-refutation-original$owed -1))
 :hints (("Goal" :in-theory (enable fn2-refutation-original$owed))) :rule-classes nil)
(defthm fn2-refutation-wrong-subject (not (fn2-refutation-other$owed -1))
 :hints (("Goal" :in-theory (enable fn2-refutation-other$owed))) :rule-classes nil)
(defthm fn2-refutation-open (not (fn2-refutation-original$owed (- (1+ (nfix x)))) )
 :hints (("Goal" :in-theory (enable fn2-refutation-original$owed))) :rule-classes nil)
(must-fail (defsquare-refuted fn2-refutation-original fn2-refutation-guarded fn2-refutation-guarded) :expected :any)
(must-fail (defsquare-refuted fn2-refutation-original fn2-refutation-wrong-subject fn2-refutation-guarded) :expected :any)
(must-fail (defsquare-refuted fn2-refutation-original fn2-refutation-open fn2-refutation-guarded) :expected :any)
(must-fail (defsquare-refuted fn2-refutation-original fn2-refutation-ground fn2-refutation-missing) :expected :any)
(defsquare-refuted fn2-refutation-original fn2-refutation-ground fn2-refutation-guarded)
(assert-event
 (let* ((row (fn2-decl-row '(:square fn2-refutation-original) (w state)))
        (rows (list (cons 'fn2-refutation-original row))))
   (and (equal (fn2-decl-get :proof row)
               '(:refuted fn2-refutation-ground fn2-refutation-guarded))
        (member-eq 'fn2-refutation-original (fn2-owed-names (w state)))
        (equal (fn2-square-counts rows) '(1 1 0 0))
        (equal (fn2-square-owed-rows rows) rows)
        (not (fn2-owed-proved-rows rows)))))
; Direct table updates obey the same guard; no refutation->proof laundering.
(must-fail
 (make-event
  (value `(table fn2-squares 'fn2-refutation-original
    ',(fn2-decl-set :proof '(:proved fn2-refutation-ground)
       (fn2-decl-row '(:square fn2-refutation-original) (w state))))))
 :expected :any)
; A malformed negation cannot smuggle the right subject with the wrong arity.
(assert-event
 (not (fn2-square-refutedp '(:refuted fn2-refutation-ground fn2-refutation-guarded)
                          'fn2-refutation-original$owed '(x y) (w state))))
