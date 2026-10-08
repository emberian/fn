; Guard closure for the exact outbound BP interpreter.  This book can use
; preservation facts from the dependent invariant book without making the
; executable machine depend on its own proof layer.
(in-package "ACL2")
(include-book "bp-node-machine-invariants")
(include-book "bp-node-foundation")

(verify-guards fn-bpn-eventp)
(verify-guards fn-bpn-machine-eventp)
(verify-guards fn-bpn-existing-sequence
  :hints (("Goal" :in-theory
           (disable fn-bpn-machine-statep fn-bpn-machine-recordp))))

(verify-guards fn-bpn-replay-records
  :hints (("Goal"
           :use ((:instance fn-bpn-apply-record-preserves-machine-statep
                            (record (car records)))
                 (:instance fn-bpn-next-token-of-applicable-record
                            (record (car records))))
           :in-theory (disable fn-bpn-machine-statep
                               fn-bpn-machine-recordp
                               fn-bpn-record-applicablep
                               fn-bpn-apply-record-preserves-machine-statep
                               fn-bpn-next-token-of-applicable-record))))

(defthm fn-bpn-replay-result-true-list-for-guard
  (true-listp (fn-bpn-replay-records st records))
  :hints (("Goal" :induct (fn-bpn-replay-records st records)
           :in-theory (enable fn-bpn-replay-records))))

(defthm fn-bpn-restart-replay-statep-for-guard
  (implies
   (and (fn-bpn-machine-statep base)
        (null (fn-bpn-machine-state-pending base))
        (true-listp records)
        (fn-bpn-restart-seed-fitsp
         base (fn-bpn-machine-state-next-token base) records))
   (fn-bpn-machine-statep (nth 1 (fn-bpn-replay-records base records))))
  :hints (("Goal"
           :use ((:instance fn-bpn-replay-records-preserves-machine-invariant
                            (st base))
                 (:instance fn-bpn-machine-invariant-components
                            (st (nth 1 (fn-bpn-replay-records base records)))))
           :in-theory (union-theories
                       '(fn-bpn-machine-invariantp fn-bpn-restart-seed-fitsp)
                       (disable fn-bpn-machine-statep fn-bpn-replay-records
                                fn-bpn-replay-records-preserves-machine-invariant)))))

(verify-guards fn-bpn-restart-replay-step
  :hints (("Goal"
           :use (fn-bpn-restart-replay-statep-for-guard
                 (:instance fn-bpn-replay-result-true-list-for-guard (st base)))
           :in-theory
           (union-theories
            '(fn-bpn-restart-seed-fitsp)
            (disable fn-bpn-machine-statep fn-bpn-machine-recordp
                     fn-bpn-machine-invariantp
                     fn-bpn-restart-replay-statep-for-guard
                     fn-bpn-replay-result-true-list-for-guard
                     fn-bpn-replay-records)))))

(verify-guards fn-bpn-restart-step-from
  :hints (("Goal"
           :use ((:instance fn-bpn-seeded-machine-state-accessors
                            (config (fn-bpn-machine-state-config st))
                            (max-jobs (fn-bpn-machine-state-max-jobs st))
                            (max-octets (fn-bpn-machine-state-max-octets st))))
           :in-theory
           (union-theories
            '(fn-bpn-restart-seed-fitsp)
            (disable fn-bpn-machine-statep fn-bpn-machine-recordp
                     fn-bpn-seeded-machine-state-accessors
                     fn-bpn-seeded-machine-state)))))

(verify-guards fn-bpn-restart-step
  :hints (("Goal"
           :in-theory (disable fn-bpn-machine-statep))))
(verify-guards fn-bpn-dispatch
  :hints (("Goal" :in-theory
           (disable fn-bpn-machine-statep fn-bpn-machine-recordp))))

(verify-guards fn-bpn-step
  :hints (("Goal" :in-theory
           (disable fn-bpn-machine-statep fn-bpn-machine-recordp))))

(verify-guards fn-bpnf-all-heldp)
(verify-guards fn-bpnf-recovery-heldp-fast)

; The one-pass recovery check is the recursive one (bp-catalog): a suffix's
; row count and octet total never exceed the whole list's, so checking the
; bounds once at the head decides every level's.
(defthm fn-bpnf-recovery-heldp-fast-is-logic
  (equal (fn-bpnf-recovery-heldp-fast held max-held max-octets)
         (fn-bpnf-recovery-heldp held max-held max-octets))
  :hints (("Goal" :induct (fn-bpnf-all-heldp held)
           :in-theory (e/d (fn-bpnf-recovery-heldp fn-bpnf-recovery-heldp-fast
                            fn-bpnf-all-heldp fn-bpnf-held-octets)
                           (fn-bpnf-heldp)))))

(verify-guards fn-bpnf-recovery-heldp
  :hints (("Goal" :in-theory (e/d (fn-bpnf-recovery-heldp-fast-is-logic)
                                  (fn-bpnf-recovery-heldp-fast)))))

; The restart step's guard is the caller's hypotheses verbatim; opening the
; replay loop under it reached the wildmat decoder and took 11 s.
(verify-guards fn-bpnf-recover-fnbs-step
  :hints (("Goal" :in-theory
           (disable fn-bpn-machine-statep fn-bpn-machine-recordp
                    fn-bpn-replay-records))))

(verify-guards fn-bpnf-step
  :hints (("Goal" :in-theory
           (disable fn-bpn-machine-statep fn-bpn-machine-recordp))))
