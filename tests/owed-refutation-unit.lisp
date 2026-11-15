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

; Same body/formals cannot redirect an established key to a different subject.
(make-event
 (value `(defconst *fn2-refutation-original-row*
           ',(fn2-decl-row '(:square fn2-refutation-original) (w state)))))
(defmacro fn2-refutation-retarget (proof)
 `(make-event
   (value `(table fn2-squares 'fn2-refutation-original
     ',(fn2-decl-set :statement 'fn2-refutation-other$owed
        (fn2-decl-set :proof ',proof *fn2-refutation-original-row*))))))
(must-fail (fn2-refutation-retarget
            (:refuted fn2-refutation-wrong-subject fn2-refutation-guarded)) :expected :any)
(must-fail (fn2-refutation-retarget (:owed)) :expected :any)
; Test the identity predicate separately with a nominal :proved status: this
; must fail at identity, independently of proof checking.
(assert-event
 (not (fn2-square-identity-boundp 'fn2-refutation-original
       (fn2-decl-set :statement 'fn2-refutation-other$owed
        (fn2-decl-set :proof '(:proved fn2-refutation-guarded) *fn2-refutation-original-row*))
       (w state))))
(must-fail
 (make-event
  (value `(table fn2-squares 'fn2-refutation-original
    ',(fn2-decl-set :statement nil
       (fn2-decl-set :vars nil
        (fn2-decl-set :translated nil
         (fn2-decl-set :formula nil
          (fn2-decl-set :checks nil
           (fn2-decl-set :proof '(:owed) *fn2-refutation-original-row*)))))))))
 :expected :any)
(must-fail
 (make-event
  (value `(table fn2-squares 'fn2-refutation-original
    ',(fn2-decl-set :formula '(integerp x) *fn2-refutation-original-row*))))
 :expected :any)
; Clearing the table cannot clear the admitted declaration identity. The
; composite attempt must refuse whether TABLE itself rejects CLEAR or not.
(must-fail
 (progn (table fn2-squares nil nil :clear)
        (fn2-refutation-retarget (:owed)))
 :expected :any)
; Status-independent identity also refuses altered variables and translation.
(assert-event
 (and
  (not (fn2-square-identity-boundp 'fn2-refutation-original
         (fn2-decl-set :vars '(y) *fn2-refutation-original-row*) (w state)))
  (not (fn2-square-identity-boundp 'fn2-refutation-original
         (fn2-decl-set :translated ''t *fn2-refutation-original-row*) (w state)))))

; First binding is legitimate, and custom statement names are supported.
(table fn2-squares 'fn2-refutation-custom
 '(:schema :assertion :proof (:owed) :checks nil))
(defun-nx fn2-custom-claim-statement (x) (natp x))
(make-event
 (value (fn2-decl-finish '(:square fn2-refutation-custom)
          '(:schema :assertion :statement fn2-custom-claim-statement :vars (x)
            :formula (natp x) :teeth (fn2-refutation-positive fn2-refutation-negative)
            :proof (:owed) :checks nil :doc "Custom first binding fixture.")
          nil nil "tests/owed-refutation-unit" (w state))))
(assert-event
 (fn2-square-rowp 'fn2-refutation-custom
   (fn2-decl-row '(:square fn2-refutation-custom) (w state)) (w state)))
; Author replay preserves refutation evidence, and an identical declaration
; identity constant is an ACL2 redundant event rather than a new claim.
(defthm-owed fn2-refutation-original (x) (natp x)
 :teeth (fn2-refutation-positive fn2-refutation-negative)
 :doc "False universal fixture; its stronger guarded replacement is distinct.")
(make-event
 (value (fn2-decl-finish '(:square fn2-refutation-custom)
          '(:schema :assertion :statement fn2-custom-claim-statement :vars (x)
            :formula (natp x) :teeth (fn2-refutation-positive fn2-refutation-negative)
            :proof (:owed) :checks nil :doc "Custom first binding fixture.")
          nil nil "tests/owed-refutation-unit" (w state))))
(assert-event
 (equal (fn2-decl-get :proof
          (fn2-decl-row '(:square fn2-refutation-original) (w state)))
        '(:refuted fn2-refutation-ground fn2-refutation-guarded)))
; Evidence/check/doc metadata updates preserve identity.
(make-event
 (value `(table fn2-squares 'fn2-refutation-original
   ',(fn2-decl-set :doc "Updated diagnostic text; original identity unchanged."
      (fn2-decl-set :evidence '(:fixture t) *fn2-refutation-original-row*)))))
