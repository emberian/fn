; Inner account boundary; the configured-node/identity issuer is a separate
; composition prerequisite. Node and identity labels below are fixture inputs.
(in-package "ACL2")
(include-book "consumer-account-config-commit-tests") ; its fixtures are used by non-local events

(defconst *caeft-event* '(:consumer-authority 0 1 0 (:authority-begin (65) 0 1 7)))
(defconst *caeft-produced*
 (list (fn-stxk-initial-context 1) :same-fields :carried :none nil nil))
(defconst *caeft-before*
 (fn-capr-state :actual-node-input (fn-stxk-initial-context 0) :prior-fields
                 *acjt-initial* *acjt-metadata* nil
                 (list :ok *acjt-initial* :committed-root 17) nil
                 :withdrawals :visible :verdicts 7 0 nil
                 (list *caeft-event*) :config-source))

;@mutation-witness actual-preparation-never-publishes-before-typed-C
(assert-event
 (and (equal (fn-cp-nth 0 *acjt-final*) :ok)
      (equal (fn-cp-nth 3 *acjt-final*) (fn-cp-nth 3 (fn-cp-nth 0 *acjt-prepared*)))
      (equal (fn-cfg-generation (fn-cp-nth 6 *acjt-final*)) 8)
      (equal (fn-cp-nth 1 (fn-cp-nth 6 (fn-cp-nth 1 *acjt-final*))) 1)
      (equal (fn-cp-nth 3 (fn-cp-nth 2 *acjt-final*)) (list *cadt-b*))))

