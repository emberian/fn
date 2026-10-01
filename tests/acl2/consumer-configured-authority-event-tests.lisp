; AUTHORED composition tests; actual source admission is still pending.
; Metadata/source labels below are test fixtures, never runtime readiness.
(in-package "ACL2")
(include-book "../../books/consumer-configured-authority-event")
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
(defconst *caet-one*
 (fn-cape-authority-after-node *caet-before* *caet-produced* *caet-next* nil))

;@mutation-witness actual-authority-node-account-decision-retained-once
(assert-event
 (let* ((after (fn-cp-nth 1 *caet-one*)) (full (fn-cp-nth 2 *caet-one*)))
  (and (fn-cnode-statep *caet-cn*) (fn-store-event-p *caet-event*)
       (fn-cnode-statep *caet-next*)
       (equal (fn-cp-nth 0 *caet-one*) :advanced) (equal (len full) 7)
       (equal full (fn-acj-stage *acjt-initial* *acjt-metadata* nil
                                 *bcpt-base* *caet-event* 0 nil))
       (equal (fn-cp-nth 1 after) *caet-next*)
       (equal (fn-cp-nth 2 after) (fn-cp-nth 0 *caet-produced*))
       (equal (fn-cp-nth 3 after) :same-identity-fields)
       (equal (fn-cp-nth 4 after) (fn-cp-nth 1 full))
       (equal (fn-cp-nth 5 after) (fn-cp-nth 4 full))
       (equal (fn-cp-nth 6 after) (fn-cp-nth 6 full))
       (equal (fn-cp-nth 8 after) 0) (equal (fn-cp-nth 12 after) 7)
       (equal (fn-cp-nth 13 after) 1) (null (fn-cp-nth 15 after))
       (equal (fn-cp-nth 9 after) :borrowed-withdrawals)
       (equal (fn-cp-nth 10 after) :borrowed-visible)
       (equal (fn-cp-nth 11 after) :borrowed-verdicts)
       (equal (fn-cp-nth 7 after)
              (list :ok (fn-cp-nth 1 full) :previous-root 0)))))

; On this actual neutral producer path, the optimized companion retains the
; COMPLETE generic callback result. This literal is not a universal theorem.
;@mutation-witness authority-complete-generic-callback-result-agreement
(assert-event
 (equal *caet-one*
  (fn-cape-step (fn-cp-nth 1
    (fn-cape-after-node *caet-before* *caet-produced* *caet-next* nil nil
                       nil :same-source 1 1)))))

;@corrupted-state authority-rejects-identity-effects-before-account-mutation
(assert-event
 (and (equal (fn-cape-authority-after-node *caet-before*
                 (update-nth 3 :verdict *caet-produced*) *caet-next* nil)
              (list :unavailable *caet-before* :authority-identity-effect))
      (equal (fn-cape-authority-after-node *caet-before*
                 (update-nth 2 :unavailable *caet-produced*) *caet-next* nil)
              (list :unavailable *caet-before* :identity-carries))))

; The source sequence is a captured actual E coordinate, never C generation.
;@corrupted-state authority-sequence-mismatch-preserves-original-state
(assert-event
 (equal (fn-cape-authority-after-node (update-nth 13 7 *caet-before*)
           *caet-produced* *caet-next* nil)
        (fn-capr-fault (update-nth 13 7 *caet-before*) :event-sequence)))
