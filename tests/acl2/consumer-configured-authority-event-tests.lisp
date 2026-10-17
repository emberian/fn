; UNHOOKED cert-roots (2026-10-02): out of the Makefile certify roots -- it depends on the FNCE consumer-authority / remote-consumer event kinds stage 0 reverted from the wire-event grammar (814763fdf; planning/design-store-representation-2026-10-01.md section 4). The code stays; it returns with that grammar.
; AUTHORED composition tests; actual source admission is still pending.
; Metadata/source labels below are test fixtures, never runtime readiness.
(in-package "ACL2")
(include-book "../../books/consumer-configured-control-event")
(local (include-book "consumer-account-config-commit-tests"))

(defconst *caet-event* '(:consumer-authority 0 1 0 (:authority-begin (65) 0 1 7)))
(defconst *caet-cn* (fn-cnode-initial *bcpt-base*))
(defconst *caet-next* (fn-cpr-apply-event *caet-cn* *caet-event*))
(defconst *caet-produced*
 (list (fn-replay-identity-step (fn-stxk-initial-context 0) *caet-event*)
       :same-identity-fields :carried :none nil nil))
(defconst *caet-before*
 (fn-capr-state *caet-cn* (fn-stxk-initial-context 0) :old-fields
                 *acjt-initial* *acjt-metadata* nil
                 (list :ok *acjt-initial* :previous-root 0) nil
                 :borrowed-withdrawals :borrowed-visible :borrowed-verdicts
                 7 0 '(:remaining-config) (list *caet-event*) :same-config-source))

