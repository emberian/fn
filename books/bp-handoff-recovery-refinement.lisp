; Structural recovery output check, not a cited keystone.
; The actual producer preservation and encoded trajectory carry the boundary.
(in-package "ACL2")
(include-book "bp-node-foundation")

(defthm fn-bpnf-recover-fnbs-ready-installs-typed-handoffs-by-definition
  (let ((answer (fn-bpnf-recover-fnbs-step
                 st new-epoch base-records sequence-ready replay-result)))
    (implies
     (equal (car (car (fn-bpnf-answer-effects answer))) :restart-ready)
     (fn-bphs-handoffs-p (fn-bpnf-handoffs (fn-bpnf-answer-state answer)))))
  :hints (("Goal" :do-not-induct t
    :in-theory (union-theories
      '(fn-bpnf-recover-fnbs-step fn-bpnf-answer fn-bpnf-answer-effects
        fn-bpnf-answer-state fn-bpnf-handoffs fn-bpnf-state-with-arrival
        fn-bpn-nth fn-cbor-ag-car fn-cbor-ag-cdr
        cons car cdr consp equal not nth nfix zp natp
        binary-+ < integerp car-cons cdr-cons)
      (theory 'minimal-theory))))
  :rule-classes nil)
