; Composition refuter: the SAME existing live record producer determines C
; sequence/generation. This coordinate fixture does not establish the pending
; authority/config/source invariant or a whole durable transaction.
(in-package "ACL2")
(include-book "../../books/owner-config")
(include-book "consumer-account-config-commit-tests") ; its fixtures are used by non-local events

(defconst *acolt-owner*
 (fn-ocfg-make (fn-own-start (fn-sn-initial '("fn.test") 8) 1)
               *bcpt-base* nil nil))
(defconst *acolt-produced*
 (fn-ocfg-reconfig-record *acolt-owner* *acjt-marker*))
;@mutation-witness existing-live-c-builder-pairs-typed-account-commit
(assert-event
 (and (equal (fn-cfg-record-sequence *acolt-produced*)
              (fn-cfg-record-sequence *acjt-record*))
      (equal (fn-cfg-record-generation *acolt-produced*)
             (fn-cfg-record-generation *acjt-record*))
      (equal (fn-cfg-record-sequence *acolt-produced*) 7)
      (equal (fn-cfg-record-generation *acolt-produced*) 8)
      (equal (fn-cfg-record-txid *acolt-produced*)
             (fn-state-next-txid
              (fn-node-acceptance
               (fn-sn-node (fn-own-store (fn-ocfg-owner *acolt-owner*))))))
      (equal (fn-cp-nth 0 *acjt-final*) :ok)))
