; Byte observation to the recovery-only fn-bpnf-step event.  The event is
; built by ACL2 from final-name/frame octets; no host replay-value assembly.
(in-package "ACL2")
(include-book "bp-fnbs-replay")

(defthm fn-bpnf-replay-ready-frontier-bounded
  (implies (equal (car (fn-bpnf-replay-rows rows max-held max-octets))
                  :ready)
           (<= (fn-bpnf-held-arrival-frontier
                (cadr (fn-bpnf-replay-rows rows max-held max-octets)))
               (1+ *fn-frame-max-nat*)))
  :hints (("Goal" :do-not-induct t
           :in-theory (enable fn-bpnf-replay-rows))))

(defthm fn-bpnf-recover-fault-bytes-keep-state
  (implies
   (not (equal
         (car (fn-bpnf-replay-rows
               rows
               (fn-bpn-machine-state-max-jobs (fn-bpnf-base st))
               (fn-bpn-machine-state-max-octets (fn-bpnf-base st))))
         :ready))
   (equal
    (fn-bpnf-answer-state
     (fn-bpnf-step st
                    (fn-bpnf-recover-event st new-epoch
                                            base-records sequence-ready rows)))
    st))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-bpnf-recover-event fn-bpnf-step
                            fn-bpnf-recover-fnbs-step)
                           (fn-bpnf-replay-rows fn-bpn-restart-step
                            fn-bpnf-recovery-heldp)))))

(defthm fn-bpnf-recover-ready-bytes-install-held
  (implies
   (and (equal
         (fn-bpnf-replay-rows
          rows
          (fn-bpn-machine-state-max-jobs (fn-bpnf-base st))
          (fn-bpn-machine-state-max-octets (fn-bpnf-base st)))
         (list :ready held prior))
        (or (null prior)
            (and (consp prior) (natp (car prior)) (natp (cdr prior))))
        (fn-frame-natp new-epoch)
        (natp (fn-bpnf-epoch st))
        (< (fn-bpnf-epoch st) new-epoch)
        (or (null prior) (< (car prior) new-epoch))
        (fn-bpnf-recovery-heldp
         held
         (fn-bpn-machine-state-max-jobs
          (fn-bpn-answer-state
           (fn-bpn-restart-step (fn-bpnf-base st)
                                base-records sequence-ready)))
         (fn-bpn-machine-state-max-octets
          (fn-bpn-answer-state
           (fn-bpn-restart-step (fn-bpnf-base st)
                                base-records sequence-ready))))
        (equal
         (car (fn-bpn-answer-effects
               (fn-bpn-restart-step (fn-bpnf-base st)
                                    base-records sequence-ready)))
         (list :restart-ready
               (len (fn-bpn-machine-state-jobs
                     (fn-bpn-answer-state
                      (fn-bpn-restart-step (fn-bpnf-base st)
                                           base-records sequence-ready)))))))
   (let ((recovered
          (fn-bpnf-answer-state
           (fn-bpnf-step st
                          (fn-bpnf-recover-event st new-epoch
                                                  base-records sequence-ready
                                                  rows)))))
     (and (equal (fn-bpnf-held-list recovered) held)
          (equal (fn-bpnf-epoch recovered) new-epoch)
          (equal (fn-bpnf-next-op recovered) 0)
          (null (fn-bpnf-issued recovered)))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-bpnf-replay-ready-frontier-bounded
                            (max-held
                             (fn-bpn-machine-state-max-jobs
                              (fn-bpnf-base st)))
                            (max-octets
                             (fn-bpn-machine-state-max-octets
                              (fn-bpnf-base st)))))
           :in-theory (e/d (fn-bpnf-recover-event fn-bpnf-step
                            fn-bpnf-recover-fnbs-step)
                           (fn-bpnf-replay-rows fn-bpn-restart-step
                            fn-bpnf-recovery-heldp)))))
