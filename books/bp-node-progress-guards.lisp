; Guard closure for the exact BP service progress caller.  The state premise
; is carried from open; no whole-state recognizer runs inside a served step.
(in-package "ACL2")
(include-book "bp-report-guards")
(include-book "bp-node-progress")
(include-book "bp-node-forward-lower-guards")
(include-book "bp-fnbs-conflict-invariants")

(verify-guards fn-bpnp-attempt-values)
(verify-guards fn-bpnp-result-values)
(verify-guards fn-bpnp-forward-frame-with)
(verify-guards fn-bpnp-attempt-frame)
(verify-guards fn-bpnp-result-frame)
(verify-guards fn-bpnp-deferral-values)
(verify-guards fn-bpnp-deferral-frame)
(verify-guards fn-bpnp-deferral-from-values)

(verify-guards fn-bpnp-routep)
(verify-guards fn-bpnp-single-peer-routes)
(verify-guards fn-bpnp-routesp)
(verify-guards fn-bpnp-route-peer)
(verify-guards fn-bpnp-waits)
(verify-guards fn-bpnp-used)
(verify-guards fn-bpnp-debt)
(verify-guards fn-bpnp-with-credit)
(verify-guards fn-bpnp-with-waits)
(verify-guards fn-bpnp-sessions)
(verify-guards fn-bpnp-pending-image)
(verify-guards fn-bpnp-with-runtime)
(verify-guards fn-bpnp-with-issued)
(verify-guards fn-bpnp-session)
(verify-guards fn-bpnp-sessionp)
(verify-guards fn-bpnp-session-listp)
(verify-guards fn-bpnp-remove-peer-session)
(verify-guards fn-bpnp-open-session)
(verify-guards fn-bpnp-session-currentp)
(verify-guards fn-bpnp-find-session)
(verify-guards fn-bpnp-has-forward-pendingp)
(verify-guards fn-bpnp-tcpcl-outcome)
(verify-guards fn-bpnp-wait-for)
(verify-guards fn-bpnp-remove-wait)
(verify-guards fn-bpnp-prune-waits)
(verify-guards fn-bpnp-wait-key)
(verify-guards fn-bpnp-primary)
(verify-guards fn-bpnp-payload)
;; The obligation needs only the clock-time and primary-field shapes.  In
;; the ambient theory every true-listp/fragment/report rule backchains on the
;; held primary, which cost 20 s and 6.4 million steps for no useful rewrite.
(verify-guards fn-bpnp-held-expiry
  :hints (("Goal" :in-theory
           (union-theories
            (theory 'minimal-theory)
            '(fn-clock-timep natp fn-bpp-lifetime fn-bpp-creation-time
              (:type-prescription fn-clock-age-anchorp)
              (:type-prescription fn-clock-observationp)
              (:executable-counterpart fn-clock-age-anchorp)
              (:compound-recognizer natp-compound-recognizer))))))
(verify-guards fn-bpnp-local-class)
(verify-guards fn-bpnp-live-pendingp)
(verify-guards fn-bpnp-blockedp)
(verify-guards fn-bpnp-credit-blockedp)
(verify-guards fn-bpnp-busy-count)
(verify-guards fn-bpnp-busy-strandedp)
(verify-guards fn-bpnp-busy-blockedp)
(verify-guards fn-bpnp-first-busy-stranded)
(verify-guards fn-bpnp-busy-stranded-effects)
(verify-guards fn-bpnp-oldest-eligible-with-credit)
(verify-guards fn-bpnp-oldest-eligible)
(verify-guards fn-bpnp-oldest-uncertain-local)
(verify-guards fn-bpnp-delivery-view)
(verify-guards fn-bpnp-dispatched-held)
(verify-guards fn-bpnp-dispatch-matches-heldp)
(verify-guards fn-bpnp-replace-dispatched)
(verify-guards fn-bpnp-dispatch-apply)
;; The helper's premise is the base state; its remaining obligations are
;; the list shape of the two apply answers, stated here with the appliers
;; closed.
(local
 (defthm fn-bpnp-family-apply-consp-for-guard
   (consp (fn-bpnf-family-apply st record expected-arrival))
   :rule-classes :type-prescription
   :hints (("Goal" :do-not-induct t
            :in-theory (union-theories '(fn-bpnf-family-apply)
                                       (theory 'minimal-theory))))))
(local
 (defthm fn-bpnp-family-apply-at-consp-for-guard
   (consp (fn-bpnf-family-apply-at st record expected-arrival))
   :rule-classes :type-prescription
   :hints (("Goal" :do-not-induct t
            :in-theory (union-theories
                        '(fn-bpnf-family-apply-at
                          fn-bpnp-family-apply-consp-for-guard)
                        (theory 'minimal-theory))))))
(local
 (defthm fn-bpnp-dispatch-apply-consp-for-guard
   (consp (fn-bpnp-dispatch-apply record held))
   :rule-classes :type-prescription
   :hints (("Goal" :do-not-induct t
            :in-theory (union-theories '(fn-bpnp-dispatch-apply)
                                       (theory 'minimal-theory))))))
(verify-guards fn-bpnp-issued-debt-delta
  :hints (("Goal" :do-not-induct t
           :in-theory (disable fn-bpnf-family-apply-at fn-bpnp-dispatch-apply
                               fn-bpn-machine-statep))))
(verify-guards fn-bpnp-received-publicationp)
(verify-guards fn-bpnp-credit-refusal)
(verify-guards fn-bpnp-credit-proposal-kind)
(verify-guards fn-bpnp-publication-fault-effect)
(verify-guards fn-bpnp-transit-dispatch-step)
(verify-guards fn-bpnp-progress-step)
(verify-guards fn-bpnp-dispatch-persist-step)
(verify-guards fn-bpnp-forward-mru-waitp)
(verify-guards fn-bpnp-forward-candidatep)
(verify-guards fn-bpnp-first-stranded)
(verify-guards fn-bpnp-stranded-effects)
;; A ready forwarding image carries the bundle it encoded.
(local
 (defthm fn-bpnp-forward-image-ready-bundlep-for-guard
   (implies (equal (car (fn-bpnp-forward-image h node observation)) :ready)
            (fn-bpb-bundlep (fn-bpn-nth 2 (fn-bpnp-forward-image
                                           h node observation))))
   :hints (("Goal" :do-not-induct t
            :in-theory (e/d (fn-bpnp-forward-image)
                            (fn-bpb-bundlep fn-bpnp-forward-blocks
                             fn-bpb-make-bundle fn-bpb-encode
                             fn-bpnp-forward-anchor fn-bpah-held-expiry
                             fn-bpp-previous-nodep fn-clock-observationp
                             fn-cbor-octet-listp fn-bpnf-held-bundle
                             fn-bpf-fragment-listp-is-a-true-list
                             fn-cp-idp-true-listp
                             fn-nntp-response-text-true-listp
                             fn-bpn-report-bounded-append-suffix
                             fn-bpf-fragment-listp-car-and-cdr
                             fn-bpf-fragmentp-fields))))
   :rule-classes nil))
(verify-guards fn-bpnp-forward-scan
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-bpnp-forward-image-ready-bundlep-for-guard
                            (h (car ordered))))
           :in-theory (disable fn-bpnp-forward-candidatep
                               fn-bpnp-forward-mru-waitp
                               fn-bpnp-credit-blockedp
                               fn-bpnp-forward-image fn-bpb-bundlep))))
(verify-guards fn-bpnp-start-one
  :hints (("Goal" :do-not-induct t
           :in-theory (disable fn-bpnp-forward-scan fn-bpnp-stranded-effects
                               fn-bpn-machine-statep
                               fn-bpb-bundlep fn-bpnf-heldp))))
(verify-guards fn-bpnp-routed-start
  :hints (("Goal" :do-not-induct t
           :in-theory (disable fn-bpnp-forward-scan fn-bpnp-start-one
                               fn-bprt-offer-decision fn-bpaj-eid-text
                               fn-bpnp-primary fn-bpn-machine-statep
                               fn-bpb-bundlep fn-bpnf-heldp))))
(verify-guards fn-bpnp-attempt-persist-step)
(verify-guards fn-bpnp-find-attempt)
(verify-guards fn-bpnp-forward-result-propose-step)
(verify-guards fn-bpnp-forward-result-persist-step)
(verify-guards fn-bpnp-resume-refusal)
(verify-guards fn-bpnp-resume-record)
(verify-guards fn-bpnp-operator-resume-step)
(verify-guards fn-bpnp-clock-domain-evidencep)
(verify-guards fn-bpnp-domain-recover-eventp)
(verify-guards fn-bpnp-clock-domain-admitsp)
(verify-guards fn-bpnp-clock-domain-reason)
(verify-guards fn-bpnp-clock-domain-fence)
(verify-guards fn-bpnp-conflict-held)
(verify-guards fn-bpnp-with-next-issued)
(verify-guards fn-bpnp-conflict-refusal)
(verify-guards fn-bpnp-conflict-propose-step)
(verify-guards fn-bpnp-conflict-persist-step)
(verify-guards fn-bpnp-busy-eventp)
(local
 (defthm fn-bpnp-budget-backoff-is-a-natural
   (natp (fn-bpnp-budget-backoff b))
   :rule-classes :type-prescription
   :hints (("Goal" :in-theory (enable fn-bpnp-budget-backoff fn-bpnp-budgetsp
                                      fn-frame-natp)))))
(verify-guards fn-bpnp-busy-wait
  :hints (("Goal" :in-theory (disable fn-bpnp-budget-backoff
                                      fn-bpnp-budget-retries))))
(verify-guards fn-bpnp-busy-delivery-step
  :hints (("Goal" :in-theory (disable fn-bpf-fragment-listp-is-a-true-list
                                      fn-cp-idp-true-listp
                                      fn-nntp-response-text-true-listp
                                      fn-bpn-report-bounded-append-suffix
                                      fn-bpf-fragment-listp-car-and-cdr
                                      fn-bpf-fragmentp-fields))))
(verify-guards fn-bpnp-deferral-effects)
;; The durable arm writes the applied held list into a cleared-issued
;; state; its guard needs only that the state is a list and that the apply
;; answers a list.  The obligation is closed in the minimal theory.
(local
 (defthm fn-bpnpg-true-listp-of-with-issued
   (true-listp (fn-bpnp-with-issued st i))
   :hints (("Goal" :in-theory (union-theories
                               '(fn-bpnp-with-issued fn-bpnp-with-runtime
                                 fn-bpnp-with-credit fn-bpnf-with-issued
                                 fn-bpnf-state-with-arrival true-listp-update-nth
                                 true-listp car-cons cdr-cons (:e true-listp))
                               (theory 'minimal-theory))))))
(verify-guards fn-bpnp-deferral-persist-step
  :hints (("Goal" :do-not-induct t
           :in-theory (union-theories
                       '(fn-bpnpg-true-listp-of-with-issued
                         (:type-prescription fn-bpnp-deferral-apply)
                         (:type-prescription nfix))
                       (theory 'minimal-theory)))))
(verify-guards fn-bpnp-busy-resume-step)
(verify-guards fn-bpnr-checkpoint-of-statep)
(verify-guards fn-bpnp-rotation-quiescentp)
(verify-guards fn-bpnp-rotate-step)
(verify-guards fn-bpnp-rotation-persist-step)
(verify-guards fn-bpnp-session-via)
(verify-guards fn-bpnp-session-base-length)
(verify-guards fn-bpnp-host-eventp)
(verify-guards fn-bpnp-preserve-runtime-answer)
;; The proposal state keeps the base it was given whenever it carries an
;; issued row, so a credit proposal's delta is computed over a base that the
;; served step's own premise already covers.  Each step's lemma opens only
;; that step, in the minimal theory, with the lower steps' lemmas.
(local
 (encapsulate
  ()
  (defun fn-bpnp-keeps-base-p (st ans)
    (declare (xargs :guard t))
    (let ((inner (fn-bpnf-answer-state ans)))
      (or (not (fn-bpnf-issued inner))
          (equal (fn-bpnf-base inner) (fn-bpnf-base st)))))
  (defthm fn-bpnp-state-accessors
    (and (equal (fn-bpnf-base (fn-bpnf-state-with-arrival b h o ho c i w e n a)) b)
         (equal (fn-bpnf-issued (fn-bpnf-state-with-arrival b h o ho c i w e n a)) i)
         (equal (fn-bpnf-answer-state (fn-bpnf-answer s effects)) s)
         (equal (fn-bpnf-base (fn-bpnf-with-issued st i)) (fn-bpnf-base st))
         (equal (fn-bpnf-issued (fn-bpnf-with-issued st i)) i)
         (equal (fn-bpnf-issued (fn-bpnf-with-base st b)) (fn-bpnf-issued st)))
    :hints (("Goal" :in-theory (disable fn-bpf-fragment-listp-is-a-true-list
                                        fn-cp-idp-true-listp
                                        fn-nntp-response-text-true-listp
                                        fn-bpn-report-bounded-append-suffix
                                        fn-bpf-fragment-listp-car-and-cdr
                                        fn-bpf-fragmentp-fields))))
  (local (in-theory (disable fn-bpnf-base fn-bpnf-issued fn-bpnf-answer-state
                      fn-bpnf-answer fn-bpnf-state-with-arrival
                      fn-bpnf-with-issued fn-bpnf-with-base)))
  (defthm fn-bpnp-keeps-base-of-answer-self
    (fn-bpnp-keeps-base-p st (fn-bpnf-answer st effects))
    :hints (("Goal" :in-theory (enable fn-bpnp-keeps-base-p))))
  (defthm fn-bpnp-keeps-base-of-with-issued
    (fn-bpnp-keeps-base-p st (fn-bpnf-answer (fn-bpnf-with-issued st i) effects))
    :hints (("Goal" :in-theory (enable fn-bpnp-keeps-base-p))))
  (defthm fn-bpnp-keeps-base-of-rebuilt
    (fn-bpnp-keeps-base-p st (fn-bpnf-answer (fn-bpnf-state-with-arrival (fn-bpnf-base st) h o ho c i w e n a) effects))
    :hints (("Goal" :in-theory (enable fn-bpnp-keeps-base-p))))
  (defthm fn-bpnp-keeps-base-of-cleared
    (fn-bpnp-keeps-base-p st (fn-bpnf-answer (fn-bpnf-state-with-arrival b h o ho c nil w e n a) effects))
    :hints (("Goal" :in-theory (enable fn-bpnp-keeps-base-p))))
  (local (in-theory (disable fn-bpnp-keeps-base-p)))
  (deftheory fn-bpnp-keep-theory
    '(fn-bpnp-keeps-base-of-answer-self fn-bpnp-keeps-base-of-with-issued
      fn-bpnp-keeps-base-of-rebuilt fn-bpnp-keeps-base-of-cleared))
  (defthm fn-bpnp-deliver-step-keeps-base
    (fn-bpnp-keeps-base-p st (fn-bpah-deliver-step st key node))
    :hints (("Goal" :do-not-induct t
             :in-theory (union-theories '(fn-bpah-deliver-step)
                          (union-theories (theory 'fn-bpnp-keep-theory) (theory 'minimal-theory))))))
  (defthm fn-bpnp-keeps-base-of-with-base
    (implies (not (fn-bpnf-issued st))
             (fn-bpnp-keeps-base-p st (fn-bpnf-answer (fn-bpnf-with-base st b) effects)))
    :hints (("Goal" :in-theory (enable fn-bpnp-keeps-base-p))))
  (deftheory fn-bpnp-keep-all
    (union-theories
     '(fn-bpnp-keeps-base-of-answer-self fn-bpnp-keeps-base-of-with-issued
       fn-bpnp-keeps-base-of-rebuilt fn-bpnp-keeps-base-of-cleared
       fn-bpnp-keeps-base-of-with-base
       fn-bpnp-deliver-step-keeps-base)
     (theory 'minimal-theory))
    )
  (defthm fn-bpnp-deliver-result-step-keeps-base
    (fn-bpnp-keeps-base-p st (fn-bpah-deliver-result-step st epoch marker-id key status detail))
    :hints (("Goal" :do-not-induct t
             :in-theory (union-theories '(fn-bpah-deliver-result-step) (theory 'fn-bpnp-keep-all)))))
  (defthm fn-bpnp-persist-delivery-step-keeps-base
    (fn-bpnp-keeps-base-p st (fn-bpah-persist-delivery-step st epoch operation-id result))
    :hints (("Goal" :do-not-induct t
             :in-theory (union-theories '(fn-bpah-persist-delivery-step) (theory 'fn-bpnp-keep-all)))))
  (defthm fn-bpnp-recover-fnbs-step-keeps-base
    (fn-bpnp-keeps-base-p st (fn-bpnf-recover-fnbs-step st new-epoch base-records sequence-ready replay-result))
    :hints (("Goal" :do-not-induct t
             :in-theory (union-theories '(fn-bpnf-recover-fnbs-step) (theory 'fn-bpnp-keep-all)))))
  (defthm fn-bpnp-foundation-step-keeps-base
    (fn-bpnp-keeps-base-p st (fn-bpnf-step st event))
    :hints (("Goal" :do-not-induct t
             :in-theory (union-theories '(fn-bpnf-step fn-bpnp-deliver-result-step-keeps-base
                                          fn-bpnp-persist-delivery-step-keeps-base
                                          fn-bpnp-recover-fnbs-step-keeps-base)
                                        (theory 'fn-bpnp-keep-all)))))
  (defthm fn-bpnp-family-propose-step-keeps-base
    (fn-bpnp-keeps-base-p st (fn-bpnf-family-propose-step st anchor-arrival observation))
    :hints (("Goal" :do-not-induct t
             :in-theory (union-theories '(fn-bpnf-family-propose-step) (theory 'fn-bpnp-keep-all)))))
  (defthm fn-bpnp-family-persist-step-keeps-base
    (fn-bpnp-keeps-base-p st (fn-bpnf-family-persist-step st epoch op result))
    :hints (("Goal" :do-not-induct t
             :in-theory (union-theories '(fn-bpnf-family-persist-step) (theory 'fn-bpnp-keep-all)))))
  (defthm fn-bpnp-fragment-step-keeps-base
    (fn-bpnp-keeps-base-p st (fn-bpnf-fragment-step st event))
    :hints (("Goal" :do-not-induct t
             :in-theory (union-theories '(fn-bpnf-fragment-step
                                          fn-bpnp-foundation-step-keeps-base
                                          fn-bpnp-family-propose-step-keeps-base
                                          fn-bpnp-family-persist-step-keeps-base)
                                        (theory 'fn-bpnp-keep-all)))))
  (defthm fn-bpnp-delete-propose-step-keeps-base
    (fn-bpnp-keeps-base-p st (fn-bpn-report-delete-propose-step st obs enabled))
    :hints (("Goal" :do-not-induct t
             :in-theory (union-theories '(fn-bpn-report-delete-propose-step) (theory 'fn-bpnp-keep-all)))))
  (defthm fn-bpnp-delete-persist-step-keeps-base
    (fn-bpnp-keeps-base-p st (fn-bpn-report-delete-persist-step st epoch op result))
    :hints (("Goal" :do-not-induct t
             :in-theory (union-theories '(fn-bpn-report-delete-persist-step) (theory 'fn-bpnp-keep-all)))))
  (defthm fn-bpnp-report-step-keeps-base
    (fn-bpnp-keeps-base-p st (fn-bpn-report-step st event))
    :hints (("Goal" :do-not-induct t
             :in-theory (union-theories '(fn-bpn-report-step
                                          fn-bpnp-fragment-step-keeps-base
                                          fn-bpnp-delete-propose-step-keeps-base
                                          fn-bpnp-delete-persist-step-keeps-base)
                                        (theory 'fn-bpnp-keep-all)))))
  (defthm fn-bpnp-queue-step-keeps-base
    (fn-bpnp-keeps-base-p st (fn-bpn-report-queue-step st arrival sequence route observation))
    :hints (("Goal" :do-not-induct t
             :in-theory (union-theories '(fn-bpn-report-queue-step) (theory 'fn-bpnp-keep-all)))))
  (defthm fn-bpnp-report-author-step-keeps-base
    (fn-bpnp-keeps-base-p st (fn-bpn-report-author-step st event))
    :hints (("Goal" :do-not-induct t
             :in-theory (union-theories '(fn-bpn-report-author-step
                                          fn-bpnp-report-step-keeps-base
                                          fn-bpnp-queue-step-keeps-base)
                                        (theory 'fn-bpnp-keep-all)))))
  (defthm fn-bpnp-proposal-base-statep-for-guard
    (implies (and (fn-bpn-machine-statep (fn-bpnf-base st))
                  (fn-bpnf-issued
                   (fn-bpnf-answer-state (fn-bpn-report-author-step st event))))
             (fn-bpn-machine-statep
              (fn-bpnf-base
               (fn-bpnf-answer-state (fn-bpn-report-author-step st event)))))
    :rule-classes nil
    :hints (("Goal" :use fn-bpnp-report-author-step-keeps-base
             :in-theory (union-theories '(fn-bpnp-keeps-base-p)
                                        (theory 'minimal-theory)))))))
(verify-guards fn-bpnp-delegate-with-credit
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-bpnp-proposal-base-statep-for-guard))
           :in-theory (disable fn-bpn-report-author-step fn-bpn-machine-statep
                               fn-bpn-machine-eventp
                               fn-bpnp-issued-debt-delta
                               fn-bpnp-credit-refusal
                               fn-bpnd-admitp fn-bpnd-debt
                               fn-bpnf-operation-matchp
                               fn-bpnp-received-publicationp
                               fn-bpnp-publication-fault-effect
                               fn-bpnp-with-credit fn-bpnp-with-waits
                               fn-bpnf-with-issued fn-bpnf-operation
                               fn-bpnf-answer
                               fn-bpn-nth-is-nth-on-true-lists
                               fn-bpf-fragment-listp-is-a-true-list
                               fn-bpf-fragment-listp fn-bpf-fragmentp fn-cp-idp
                               fn-bpn-report-bounded-append-suffix))))
;; The carried session table supplies the resumed session's MRU; a session
;; event's MRU is a bounded field of the admitted host event.
(local
 (encapsulate
  ()
  (local
   (defthm fn-bpnp-session-mru-natp-for-guard
     (implies (fn-bpnp-sessionp x) (natp (fn-bpn-nth 3 x)))
     :hints (("Goal" :in-theory (union-theories '(fn-bpnp-sessionp fn-frame-natp)
                                                (theory 'minimal-theory))))))
  (defthm fn-bpnp-found-session-mru-for-guard
    (implies (and (fn-bpnp-session-listp sessions)
                  (fn-bpnp-find-session sessions peer session))
             (natp (fn-bpn-nth 3 (fn-bpnp-find-session sessions peer session))))
    :rule-classes nil
    :hints (("Goal" :induct (fn-bpnp-find-session sessions peer session)
             :expand ((fn-bpnp-session-listp sessions))
             :in-theory (union-theories '(fn-bpnp-find-session fn-bpnp-session-listp
                                          fn-bpnp-session-mru-natp-for-guard)
                                        (theory 'minimal-theory)))))))
(local
 (defthm fn-bpnp-session-event-mru-for-guard
   (implies (and (fn-bpnp-host-eventp event)
                 (equal (fn-cbor-ag-car event) :session))
            (natp (fn-bpn-nth 4 event)))
   :rule-classes nil
   :hints (("Goal" :do-not-induct t
            :in-theory (e/d (fn-bpnp-host-eventp fn-frame-natp)
                            (fn-bpp-eidp fn-bpnp-session-idp
                             fn-clock-observationp fn-bpnf-host-eventp
                             fn-bpnp-routesp fn-bprt-viap
                             fn-bpf-fragment-listp-is-a-true-list
                             fn-cp-idp-true-listp
                             fn-nntp-response-text-true-listp
                             fn-bpn-report-bounded-append-suffix
                             fn-bpf-fragment-listp-car-and-cdr
                             fn-bpf-fragmentp-fields))))))
(local
 (defthm fn-bpnp-delegate-event-guard
   (implies (and (fn-bpnp-host-eventp event)
                 (not (equal (fn-cbor-ag-car event) :progress)))
            (and (or (not (equal (fn-cbor-ag-car event) :base))
                     (fn-bpn-machine-eventp (fn-bpn-nth 1 event)))
                 (or (not (equal (fn-cbor-ag-car event) :recover-fnbs))
                     (and (true-listp (fn-bpn-nth 2 event))
                          (<= (len (fn-bpn-nth 2 event))
                              *fn-bpn-machine-max-records*)))))
   :hints (("Goal" :do-not-induct t
            :in-theory (e/d (fn-bpnp-host-eventp fn-bpnf-host-eventp)
                            (fn-bpn-machine-eventp fn-bpb-bundlep
                             fn-bpp-blockp fn-bpn-nth-is-nth-on-true-lists
                             fn-bpf-fragment-listp-is-a-true-list
                             fn-bpf-fragment-listp fn-bpf-fragmentp fn-cp-idp))))
   :rule-classes nil))
(local
 (defthm fn-bpnp-held-list-of-with-runtime-for-guard
   (equal (fn-bpnf-held-list (fn-bpnp-with-runtime st sessions pending-image))
          (fn-bpnf-held-list st))
   :hints (("Goal" :in-theory (e/d (fn-bpnp-with-runtime fn-bpnf-held-list)
                                   (fn-bpf-fragment-listp-is-a-true-list
                                    fn-cp-idp-true-listp
                                    fn-nntp-response-text-true-listp
                                    fn-bpn-report-bounded-append-suffix
                                    fn-bpf-fragment-listp-car-and-cdr
                                    fn-bpf-fragmentp-fields))))))
(verify-guards fn-bpnp-step
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-bpnp-delegate-event-guard)
                 (:instance fn-bpnp-session-event-mru-for-guard)
                 (:instance fn-bpnp-found-session-mru-for-guard
                            (sessions (fn-bpnp-sessions st))
                            (peer (fn-bpn-nth 1 event))
                            (session (fn-bpn-nth 2 event))))
           :in-theory (disable fn-bpnp-host-eventp fn-bpnf-host-eventp
                               fn-bpn-machine-eventp fn-bpn-machine-statep
                               fn-bpnp-session-listp fn-bpnp-find-session
                               fn-bpnp-start-one fn-bpnp-routed-start
                               fn-bpnp-delegate-with-credit
                               fn-bpn-nth-is-nth-on-true-lists
                               fn-bpf-fragment-listp-is-a-true-list
                               fn-bpf-fragment-listp fn-bpf-fragmentp fn-cp-idp
                               fn-bpn-report-bounded-append-suffix
                               fn-bpnp-with-runtime fn-bpnf-held-list))))
