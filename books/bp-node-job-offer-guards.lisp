; Guard closure for the job-offer entry the native BP service calls.
; The opened machine shape is carried by the service, not revalidated here.
(in-package "ACL2")
(include-book "bp-node-job-offer")
(include-book "bp-node-progress-guards")

; This recognizer uses the progress guard closure, so verify it here.
(verify-guards fn-bpnj-host-eventp)

(verify-guards fn-bpnj-start-job
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-bpn-state-field-types-for-guard (st base)))
           :in-theory (disable fn-bpn-machine-statep fn-bpn-machine-recordp
                               fn-bpn-state-field-types-for-guard))))

(local
 (defthm fn-bpnj-receipt-contact-peer-for-guard
   (implies (fn-bpnp-receipt-contact-event st peer) (fn-bpp-eidp peer))
   :hints (("Goal" :in-theory
            (union-theories (theory 'minimal-theory)
                            '(fn-bpnp-receipt-contact-event))))))

(local
 (defthm fn-bpnj-open-base-statep-for-guard
   (implies (and (fn-bpn-machine-statep base) (fn-bpp-eidp peer))
            (fn-bpn-machine-statep (fn-bpnj-open-base base peer)))
   :hints (("Goal"
            :use ((:instance fn-bpn-contact-state-with-preserves-statep-for-guard
                   (st base)
                   (contacts (fn-bpn-open-contact peer
                              (fn-bpn-machine-state-contacts base))))
                  (:instance fn-bpn-machine-statep-components (st base))
                  (:instance fn-bpn-open-contact-preserves-contact-listp
                   (contacts (fn-bpn-machine-state-contacts base))))
            :in-theory (union-theories (theory 'minimal-theory)
                                       '(fn-bpnj-open-base))))))

(verify-guards fn-bpnj-contact-job-step
  :hints (("Goal"
           :use ((:instance fn-bpnj-receipt-contact-peer-for-guard)
                 (:instance fn-bpnj-open-base-statep-for-guard
                  (base (fn-bpnf-base st))))
           :in-theory (theory 'minimal-theory))))

(local
 (defthm fn-bpnj-attempt-token-key-for-guard
   (implies (and (fn-bpn-machine-statep (fn-bpnf-base st))
                 (natp (fn-bpnj-attempt-token st key)))
            (fn-bpn-keyp key))
   :hints (("Goal" :do-not-induct t
            :use ((:instance fn-bpn-machine-statep-components
                   (st (fn-bpnf-base st)))
                  (:instance fn-bpn-find-job-is-a-job
                   (jobs (fn-bpn-machine-state-jobs (fn-bpnf-base st))))
                  (:instance fn-bpn-key-of-found-job
                   (jobs (fn-bpn-machine-state-jobs (fn-bpnf-base st))))
                  (:instance fn-bpn-job-key-is-typed
                   (job (fn-bpn-find-job key
                         (fn-bpn-machine-state-jobs (fn-bpnf-base st))))))
            :in-theory (union-theories (theory 'minimal-theory)
                                       '(fn-bpnj-attempt-token natp))))))

(verify-guards fn-bpnj-result-step
  :hints (("Goal"
           :use ((:instance fn-bpnj-attempt-token-key-for-guard)
                 (:instance fn-bpnj-result-event-is-a-served-event))
           :in-theory (theory 'minimal-theory))))

(verify-guards fn-bpnj-step
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-bpnj-host-event-delegated-is-a-served-event))
           :in-theory (disable fn-bpn-machine-statep fn-bpn-machine-recordp
                               fn-bpnp-host-eventp fn-bpnj-host-eventp
                               fn-bpnj-contact-job-step fn-bpnj-result-step
                               fn-bpnj-unnamed-result-p fn-bpnf-held-list
                               fn-bpnp-sessions))))
