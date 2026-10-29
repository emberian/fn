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

; All store controls are local: FN2-OWED-SAMPLE never enters the export.
(local
 (encapsulate ()
  (defconst *fn2-square-check*
    '(:contract fn2-unit-contract :revision "fixture" :profile :tiny
      :domain (:x 1) :horizon 1 :unit :call :reached 1 :exercised 1
      :verdict :pass :location "fn2/tests/owed-unit.lisp"))
  (make-event
   (value `(table fn2-squares 'fn2-owed-sample
             ',(fn2-decl-set :checks (list *fn2-square-check*)
                 (fn2-decl-row '(:square fn2-owed-sample) (w state))))))
  (assert-event
   (and (member-eq 'fn2-owed-sample (fn2-owed-names (w state)))
        (equal (fn2-decl-get :checks (fn2-decl-row '(:square fn2-owed-sample) (w state)))
               (list *fn2-square-check*))
        (equal (fn2-square-counts
                (list (cons 'fn2-owed-sample (fn2-decl-row '(:square fn2-owed-sample) (w state)))))
               '(1 1 0 1))))
  (defthm fn2-square-right (implies (natp x) (<= 0 x)) :rule-classes nil)
  (defthm fn2-square-wrong (equal (car (cons x y)) x) :rule-classes nil)
  (defmacro fn2-square-test-proof (proof)
    `(make-event
      (value `(table fn2-squares 'fn2-owed-sample
                ',(fn2-decl-set :proof ',proof
                    (fn2-decl-row '(:square fn2-owed-sample) (w state)))))))
  (must-fail (fn2-square-test-proof (:proved fn2-square-wrong)) :expected :any)
  (must-fail (fn2-square-test-proof (:proved fn2-square-absent)) :expected :any)
  (must-fail (fn2-square-test-proof (:checked)) :expected :any)
  (fn2-square-test-proof (:proved fn2-square-right))
  (assert-event (not (member-eq 'fn2-owed-sample (fn2-owed-names (w state)))))
  (defthm fn2-square-wrapper (fn2-owed-sample$owed x)
    :hints (("Goal" :in-theory (enable fn2-owed-sample$owed))) :rule-classes nil)
  (fn2-square-test-proof (:proved fn2-square-wrapper))
  (assert-event
   (equal (fn2-square-counts
           (list (cons 'fn2-owed-sample (fn2-decl-row '(:square fn2-owed-sample) (w state)))))
          '(1 1 1 1)))
  ; Identical author replay preserves independently accumulated proof/evidence.
  (defthm-owed fn2-owed-sample (x)
    (implies (natp x) (<= 0 x))
    :teeth (fn2-owed-sample-positive fn2-owed-sample-negative)
    :doc "Translation/registration fixture; not a theorem.")
  (assert-event
   (let ((row (fn2-decl-row '(:square fn2-owed-sample) (w state))))
     (and (equal (fn2-decl-get :proof row) '(:proved fn2-square-wrapper))
          (equal (fn2-decl-get :checks row) (list *fn2-square-check*))
          (eq (fn2-decl-get :schema row) :assertion))))
  (assert-event (not (fn2-square-checksp '((:verdict :pass)))))
  (make-event
   (value `(table fn2-squares 'fn2-owed-sample
             ',(fn2-decl-set :teeth
                 '(:positive fn2-owed-sample-positive :negative fn2-owed-sample-negative)
                 (fn2-decl-row '(:square fn2-owed-sample) (w state))))))
  (fn2-assert-owed-teeth fn2-owed-sample)
  ; Shared syntax is allowed for refinement, but semantic claims must name
  ; both independent judgment and the shared-handler mutation control.
  (must-fail
   (defthm-owed fn2-square-shared-bad (x) (natp x) :schema :invariant
     :shared ((:machine fn2-example)) :teeth (fn2-owed-sample-positive))
   :expected :any)
  (must-fail
   (defthm-owed fn2-square-shared-bad2 (x) (natp x) :schema :invariant
     :shared ((:machine fn2-example)) :contract (:independent fn2-unit-contract)
     :teeth (fn2-owed-sample-positive)) :expected :any)
  (defthm-owed fn2-square-shared-good (x) (natp x) :schema :invariant
    :shared ((:machine fn2-example)) :contract (:independent fn2-unit-contract)
    :shared-handler-mutation fn2-unit-mutation :teeth (fn2-owed-sample-positive))
  (defthm-owed fn2-square-representation (x) (natp x) :schema :g1 :claim :representation
    :shared ((:columns fn2-example)) :teeth (fn2-owed-sample-positive) :layer :b)
  (assert-event
   (equal (fn2-decl-get :layer (fn2-decl-row '(:square fn2-square-representation) (w state))) :b))
  (table fn2-squares 'fn2-square-unbound
    '(:schema :bound :owner (:correspondence fn2-unit) :case-source :executor-cases
      :proof (:owed) :statement nil :translated nil :checks nil))
  (assert-event
   (equal (fn2-square-counts
           (list (cons 'fn2-square-unbound (fn2-decl-row '(:square fn2-square-unbound) (w state)))))
          '(1 0 0 0)))
  (assert-event (not (fn2-square-coveredp
                      (list (fn2-decl-set :verdict :fail *fn2-square-check*)
                            (fn2-decl-set :exercised 0 *fn2-square-check*)))))))
