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

(defthm fn-bpn-restart-base-invariant-for-guard
  (implies
   (fn-bpn-machine-statep st)
   (fn-bpn-machine-invariantp
    (fn-bpn-initial-machine-state
     (fn-bpn-machine-state-config st)
     (fn-bpn-machine-state-max-jobs st)
     (fn-bpn-machine-state-max-octets st))))
  :hints (("Goal"
           :use ((:instance fn-bpn-machine-statep-components)
                 (:instance fn-bpn-initial-machine-state-has-invariant
                  (config (fn-bpn-machine-state-config st))
                  (max-jobs (fn-bpn-machine-state-max-jobs st))
                  (max-octets (fn-bpn-machine-state-max-octets st))))
           :in-theory
           (disable fn-bpn-machine-statep fn-bpn-machine-invariantp
                    fn-bpn-initial-machine-state-has-invariant))))

(defthm fn-bpn-restart-replay-statep-for-guard
  (implies
   (and (fn-bpn-machine-statep st)
        (true-listp records)
        (<= (len records) *fn-bpn-machine-max-records*))
   (fn-bpn-machine-statep
    (nth 1
         (fn-bpn-replay-records
          (fn-bpn-initial-machine-state
           (fn-bpn-machine-state-config st)
           (fn-bpn-machine-state-max-jobs st)
           (fn-bpn-machine-state-max-octets st))
          records))))
  :hints (("Goal"
           :use ((:instance fn-bpn-restart-base-invariant-for-guard)
                 (:instance fn-bpn-replay-records-preserves-machine-invariant
                  (st (fn-bpn-initial-machine-state
                       (fn-bpn-machine-state-config st)
                       (fn-bpn-machine-state-max-jobs st)
                       (fn-bpn-machine-state-max-octets st))))
                 (:instance fn-bpn-next-token-of-initial-machine-state
                  (config (fn-bpn-machine-state-config st))
                  (max-jobs (fn-bpn-machine-state-max-jobs st))
                  (max-octets (fn-bpn-machine-state-max-octets st))))
           :in-theory
           (disable fn-bpn-machine-statep fn-bpn-machine-invariantp
                    fn-bpn-restart-base-invariant-for-guard
                    fn-bpn-replay-records-preserves-machine-invariant
                    fn-bpn-initial-machine-state))))

(verify-guards fn-bpn-restart-step
  :hints (("Goal"
           :use (fn-bpn-restart-base-invariant-for-guard
                 fn-bpn-restart-replay-statep-for-guard
                 (:instance fn-bpn-replay-result-true-list-for-guard
                  (st (fn-bpn-initial-machine-state
                       (fn-bpn-machine-state-config st)
                       (fn-bpn-machine-state-max-jobs st)
                       (fn-bpn-machine-state-max-octets st))))
                 (:instance fn-bpn-next-token-of-initial-machine-state
                  (config (fn-bpn-machine-state-config st))
                  (max-jobs (fn-bpn-machine-state-max-jobs st))
                  (max-octets (fn-bpn-machine-state-max-octets st))))
           :in-theory
           (disable fn-bpn-machine-statep fn-bpn-machine-recordp
                    fn-bpn-machine-invariantp
                    fn-bpn-restart-base-invariant-for-guard
                    fn-bpn-restart-replay-statep-for-guard
                    fn-bpn-replay-result-true-list-for-guard
                    fn-bpn-replay-records fn-bpn-initial-machine-state))))
(verify-guards fn-bpn-dispatch
  :hints (("Goal" :in-theory
           (disable fn-bpn-machine-statep fn-bpn-machine-recordp))))

(verify-guards fn-bpn-step
  :hints (("Goal" :in-theory
           (disable fn-bpn-machine-statep fn-bpn-machine-recordp))))

(verify-guards fn-bpnf-recovery-heldp)

(verify-guards fn-bpnf-recover-fnbs-step
  :hints (("Goal" :in-theory
           (disable fn-bpn-machine-statep fn-bpn-machine-recordp))))

(verify-guards fn-bpnf-step
  :hints (("Goal" :in-theory
           (disable fn-bpn-machine-statep fn-bpn-machine-recordp))))
