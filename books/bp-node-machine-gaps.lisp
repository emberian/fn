; Keystones for the two machine transitions spec bp-node-machine 11.1
; named and the counterexample suite could not express: the boot-domain
; gate on recovery (N07) and the kind-14 conflict record (N11's other
; half).  Every theorem is over fn-bpnp-step, the function
; host/native/bp-service.lisp:172 calls.
(in-package "ACL2")
(include-book "bp-node-progress")
(include-book "bp-clock-domain")

(local
 (defthm bpgap-held-of-slot-writers
   (and (equal (fn-bpnf-held-list (fn-bpnp-with-runtime st s p))
               (fn-bpnf-held-list st))
        (equal (fn-bpnf-held-list (fn-bpnp-with-credit st u d))
               (fn-bpnf-held-list st))
        (equal (fn-bpnf-held-list (fn-bpnp-with-waits st w))
               (fn-bpnf-held-list st))
        (equal (fn-bpnf-issued (fn-bpnp-with-runtime st s p))
               (fn-bpnf-issued st))
        (equal (fn-bpnf-issued (fn-bpnp-with-credit st u d))
               (fn-bpnf-issued st))
        (equal (fn-bpnf-issued (fn-bpnp-with-waits st w))
               (fn-bpnf-issued st)))
   :hints (("Goal" :in-theory (enable fn-bpnp-with-runtime fn-bpnp-with-credit
                                      fn-bpnp-with-waits fn-bpnf-held-list
                                      fn-bpnf-issued fn-bpn-nth)))))

(local
 (defthm bpgap-with-issued-fields
   (and (equal (fn-bpnf-held-list (fn-bpnp-with-issued st x))
               (fn-bpnf-held-list st))
        (equal (fn-bpnf-issued (fn-bpnp-with-issued st x)) x)
        (equal (fn-bpnf-held-list (fn-bpnp-with-next-issued st x))
               (fn-bpnf-held-list st))
        (equal (fn-bpnf-issued (fn-bpnp-with-next-issued st x)) x))
   :hints (("Goal" :in-theory (e/d (fn-bpnp-with-issued fn-bpnf-with-issued
                                    fn-bpnp-with-next-issued
                                    fn-bpnf-state-with-arrival
                                    fn-bpnf-held-list fn-bpnf-issued
                                    fn-bpn-nth fn-bpnp-with-runtime
                                    fn-bpnp-with-credit fn-bpnp-with-waits)
                                   ())))))

(local
 (defthm bpgap-used-of-slot-writers
   (and (equal (fn-bpnp-used (fn-bpnp-with-waits st w)) (fn-bpnp-used st))
        (implies (true-listp st)
                 (equal (fn-bpnp-used (fn-bpnp-with-credit st u d)) u))
        (true-listp (fn-bpnp-with-issued st x)))
   :hints (("Goal" :in-theory (enable fn-bpnp-with-waits fn-bpnp-with-credit
                                      fn-bpnp-used fn-bpnp-with-issued
                                      fn-bpnp-with-runtime fn-bpnf-with-issued
                                      fn-bpnf-state-with-arrival fn-bpn-nth)))))

;; ---------------------------------------------------------------------
;; A fenced state (an uncertain issued operation) is inert to every event
;; except recovery; this is the top of fn-bpnp-step.
(local
 (defthm bpgap-uncertain-issued-is-inert
   (implies (and (equal (fn-bpn-nth 5 (fn-bpnf-issued st)) :uncertain)
                 (not (equal (fn-cbor-ag-car later) :recover-fnbs)))
            (equal (fn-bpnp-step st later) (fn-bpnf-answer st nil)))
   :hints (("Goal" :do-not-induct t
            :expand ((fn-bpnp-step st later))
            :in-theory (theory 'minimal-theory)))))

(local
 (defthm bpgap-domain-event-is-fenced
   (implies (and (fn-bpnp-domain-recover-eventp event)
                 (not (fn-bpnp-clock-domain-admitsp event)))
            (equal (fn-bpnp-step st event)
                   (fn-bpnp-clock-domain-fence st (fn-bpn-nth 6 event))))
   :hints (("Goal" :do-not-induct t
            :expand ((fn-bpnp-step st event))
            :in-theory (union-theories '(fn-bpnp-domain-recover-eventp)
                                       (theory 'minimal-theory))))))

(local
 (defthm bpgap-fence-fields
   (let ((ans (fn-bpnp-clock-domain-fence st plan)))
     (and (equal (fn-bpnf-answer-effects ans)
                 (list (list :restart-fault :clock-domain
                             (fn-bpnp-clock-domain-reason plan))))
          (equal (fn-bpnf-held-list (fn-bpnf-answer-state ans))
                 (fn-bpnf-held-list st))
          (equal (fn-bpn-nth 5 (fn-bpnf-issued (fn-bpnf-answer-state ans)))
                 :uncertain)))
   :hints (("Goal" :do-not-induct t
            :in-theory (e/d (fn-bpnp-clock-domain-fence fn-bpnf-answer
                             fn-bpnf-answer-state fn-bpnf-answer-effects
                             fn-bpnf-operation fn-bpn-nth)
                            (fn-bpnp-with-issued fn-bpnp-clock-domain-reason
                             fn-bpnf-held-list fn-bpnf-issued
                             fn-bpnf-epoch fn-bpnf-next-op))))))

;; N07.  KEYSTONE (fence).  A recovery event whose boot-domain decision is
;; not :same (nor :initialize with nothing retained) installs no replay and
;; compares no retained anchor: the step answers one :restart-fault naming
;; the decision's reason, keeps every held row, and leaves a state in which
;; every later event other than a recovery is inert.
(defthm fn-bpnp-step-domain-disagreement-fences
  (implies (and (fn-bpnp-domain-recover-eventp event)
                (not (fn-bpnp-clock-domain-admitsp event)))
           (let* ((ans (fn-bpnp-step st event))
                  (st2 (fn-bpnf-answer-state ans)))
             (and (equal (fn-bpnf-answer-effects ans)
                         (list (list :restart-fault :clock-domain
                                     (fn-bpnp-clock-domain-reason
                                      (fn-bpn-nth 6 event)))))
                  (equal (fn-bpnf-held-list st2) (fn-bpnf-held-list st))
                  (implies (not (equal (fn-cbor-ag-car later) :recover-fnbs))
                           (equal (fn-bpnp-step st2 later)
                                  (fn-bpnf-answer st2 nil))))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use ((:instance bpgap-domain-event-is-fenced)
                 (:instance bpgap-fence-fields (plan (fn-bpn-nth 6 event)))
                 (:instance bpgap-uncertain-issued-is-inert
                            (st (fn-bpnf-answer-state
                                 (fn-bpnp-clock-domain-fence
                                  st (fn-bpn-nth 6 event))))))
           :in-theory (theory 'minimal-theory))))

(local
 (defthm bpgap-domain-fence-answer
   (implies (and (fn-bpnp-domain-recover-eventp event)
                 (not (fn-bpnp-clock-domain-admitsp event)))
            (equal (fn-bpnf-answer-effects (fn-bpnp-step st event))
                   (list (list :restart-fault :clock-domain
                               (fn-bpnp-clock-domain-reason
                                (fn-bpn-nth 6 event))))))
   :hints (("Goal" :use fn-bpnp-step-domain-disagreement-fences
            :in-theory (theory 'minimal-theory)))))

(local
 (defthm bpgap-admitted-plan-is-same-boot-or-fresh
   (implies (and (equal (fn-bpn-nth 6 event)
                        (fn-bpnf-clock-domain-plan
                         saved present observed legacy-evidence
                         lock-owned final-absent))
                 (fn-bpnp-clock-domain-admitsp event))
            (or (and present
                     (fn-bpcd-unframe saved)
                     (equal (fn-bpcd-unframe saved)
                            (fn-bpcd-observed-id observed)))
                (and (not present) (not legacy-evidence)
                     lock-owned final-absent
                     (fn-bpcd-observed-id observed)
                     (null (fn-bpn-nth 2 event))
                     (equal (fn-bpn-nth 5 event) 0))))
   :rule-classes nil
   :hints (("Goal" :do-not-induct t
            :in-theory (union-theories
                        '(fn-bpnp-clock-domain-admitsp fn-bpnf-clock-domain-plan
                          fn-cbor-ag-car fn-bpn-nth car-cons cdr-cons
                          (:e fn-bpn-nth) (:e equal) (:e car) (:e consp))
                        (theory 'minimal-theory))))))

;; N07.  KEYSTONE (soundness of a ready recovery).  When the host passes the
;; decision of fn-bpnf-clock-domain-plan over its observations, a recovery
;; through fn-bpnp-step that answers :restart-ready happened either in the
;; boot the durable clock-domain record names (the saved record decodes and
;; equals this boot's observed ID) or at the domain's first initialization,
;; with no legacy evidence, no base records and no received row retained.
(defthm fn-bpnp-step-ready-recovery-is-same-boot
  (implies (and (fn-bpnp-domain-recover-eventp event)
                (equal (fn-bpn-nth 6 event)
                       (fn-bpnf-clock-domain-plan
                        saved present observed legacy-evidence
                        lock-owned final-absent))
                (equal (car (car (fn-bpnf-answer-effects
                                  (fn-bpnp-step st event))))
                       :restart-ready))
           (or (and present
                    (fn-bpcd-unframe saved)
                    (equal (fn-bpcd-unframe saved)
                           (fn-bpcd-observed-id observed)))
               (and (not present) (not legacy-evidence)
                    lock-owned final-absent
                    (fn-bpcd-observed-id observed)
                    (null (fn-bpn-nth 2 event))
                    (equal (fn-bpn-nth 5 event) 0))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :cases ((fn-bpnp-clock-domain-admitsp event))
           :use ((:instance bpgap-admitted-plan-is-same-boot-or-fresh)
                 (:instance bpgap-domain-fence-answer))
           :in-theory (union-theories '(car-cons (:e equal) (:e car))
                                      (theory 'minimal-theory)))))

;; N07 on the actual startup decision: a restart whose saved domain and
;; observed boot ID both decode and differ is fenced with reason
;; :different-boot before any retained anchor is compared.
(defthm fn-bpnp-step-different-boot-fences
  (implies (and (fn-bpnp-domain-recover-eventp event)
                (equal (fn-bpn-nth 6 event)
                       (fn-bpnf-clock-domain-plan
                        saved present observed legacy-evidence
                        lock-owned final-absent))
                present
                (fn-bpcd-unframe saved)
                (fn-bpcd-observed-id observed)
                (not (equal (fn-bpcd-unframe saved)
                            (fn-bpcd-observed-id observed))))
           (equal (fn-bpnf-answer-effects (fn-bpnp-step st event))
                  '((:restart-fault :clock-domain :different-boot))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-bpnf-clock-domain-different-boot-fences)
                 (:instance bpgap-domain-fence-answer))
           :in-theory (union-theories
                       '(fn-bpnp-clock-domain-admitsp
                         (:e fn-bpnp-clock-domain-reason)
                         (:e fn-cbor-ag-car) (:e fn-bpn-nth) (:e equal))
                       (theory 'minimal-theory)))))

;; ---------------------------------------------------------------------
;; N11 lemmas: the conflict arm is reached exactly under the keystone's
;; hypotheses, and the arm's answer.
(local
 (defthm bpgap-conflict-arm-is-taken
   (implies (and (equal (fn-cbor-ag-car event) :receive-bundle)
                 (not (fn-bpnf-issued st))
                 (fn-bpnp-conflict-held st event))
            (equal (fn-bpnp-step st event)
                   (fn-bpnp-conflict-propose-step
                    st event (fn-bpnp-conflict-held st event))))
   :hints (("Goal" :do-not-induct t
            :expand ((fn-bpnp-step st event))
            :in-theory (union-theories '(fn-bpnp-domain-recover-eventp
                                         (:e fn-bpn-nth) (:e equal))
                                       (theory 'minimal-theory))))))

(local
 (defthm bpgap-conflict-held-under-hypotheses
   (implies (and (fn-bpnp-host-eventp event)
                (equal (fn-cbor-ag-car event) :receive-bundle)
                (not (fn-bpnf-issued st))
                (not (fn-bpah-delivery-uncertainp st))
                (fn-frame-natp (fn-bpnf-epoch st))
                (fn-frame-natp (fn-bpnf-next-op st))
                (fn-frame-natp (fn-bpnf-next-arrival st))
                (< (fn-bpnf-next-op st) *fn-frame-max-nat*)
                (equal (fn-bpn-nth 2 event) (fn-bpb-encode (fn-bpn-nth 1 event)))
                (equal (fn-bpnf-receive-decision (fn-bpnf-held-list st)
                                                 (fn-bpn-nth 3 event)
                                                 (fn-bpn-nth 1 event))
                       :identity-conflict))
            (and (fn-bpnp-conflict-held st event)
                 (equal (fn-bpnp-conflict-held st event)
                   (fn-bpnf-find-held
                    (fn-bpnf-held-key (fn-bpnf-ingress-principal (fn-bpn-nth 3 event))
                                      (fn-bpb-bundle-id (fn-bpn-nth 1 event)))
                    (fn-bpnf-held-list st)))))
   :rule-classes nil
   :hints (("Goal" :do-not-induct t
            :in-theory (e/d (fn-bpnp-conflict-held fn-bpnp-host-eventp
                             fn-bpnf-host-eventp fn-bpnf-receive-decision
                             fn-frame-natp)
                            (fn-bpnf-find-held fn-bpb-bundlep fn-bpb-encode
                             fn-bpnf-cl-ingressp fn-clock-observationp
                             fn-bpnf-immutable fn-bpnf-held-key
                             fn-bpnf-ingress-principal fn-bpb-bundle-id
                             fn-cbor-octet-listp fn-cbor-at-mostp
                             fn-bpah-delivery-uncertainp))))))

(local
 (defthm bpgap-conflict-propose-fields
   (let* ((ans (fn-bpnp-conflict-propose-step st event h))
          (ingress (fn-bpn-nth 3 event))
          (record (fn-bpnf-conflict-of (fn-bpnf-epoch st) (fn-bpnf-next-op st)
                                       h ingress (fn-bpn-nth 2 event))))
     (and (equal (fn-bpnf-held-list (fn-bpnf-answer-state ans))
                 (fn-bpnf-held-list st))
          (if (and (fn-bpnf-conflict-recordp record)
                   (not (equal (fn-bpnf-conflict-frame record) :bad))
                   (fn-bpnd-admitp (fn-bpnp-used st) (fn-bpnp-debt st)
                                   *fn-bpnp-control-margin* 0 :spend))
              (and (equal (fn-bpnf-answer-effects ans)
                          (list (list :persist-conflict (fn-bpnf-epoch st)
                                      (fn-bpnf-next-op st) record)))
                   (equal (fn-bpnf-issued (fn-bpnf-answer-state ans))
                          (fn-bpnf-operation
                           (fn-bpnf-epoch st) (fn-bpnf-next-op st)
                           :conflict (list record ingress) :pending)))
            (equal (fn-bpnf-answer-effects ans)
                   (list (list :receive-answer ingress :identity-conflict))))))
   :hints (("Goal" :do-not-induct t
            :in-theory (e/d (fn-bpnp-conflict-propose-step
                             fn-bpnp-conflict-refusal
                             fn-bpnf-answer fn-bpnf-answer-state
                             fn-bpnf-answer-effects fn-bpn-nth)
                            (fn-bpnp-with-next-issued fn-bpnf-conflict-of
                             fn-bpnf-conflict-recordp fn-bpnf-conflict-frame
                             fn-bpnd-admitp fn-bpnf-operation))))))

;; ---------------------------------------------------------------------
;; N11.  KEYSTONE (a conflicting reception is refused, never dropped or
;; replaced).  A host-admitted reception whose exact wire names a live held
;; identity with a different immutable projection keeps every held row and
;; answers either the refusal to its ingress at once or, exactly when the
;; kind-14 record is well formed and the journal's credit admits one more
;; final at zero debt, the proposal of that record naming the held row, the
;; ingress and the carrier's content id, with the operation issued.
(defthm fn-bpnp-step-identity-conflict-is-refused-or-recorded
  (implies (and (fn-bpnp-host-eventp event)
                (equal (fn-cbor-ag-car event) :receive-bundle)
                (not (fn-bpnf-issued st))
                (not (fn-bpah-delivery-uncertainp st))
                (fn-frame-natp (fn-bpnf-epoch st))
                (fn-frame-natp (fn-bpnf-next-op st))
                (fn-frame-natp (fn-bpnf-next-arrival st))
                (< (fn-bpnf-next-op st) *fn-frame-max-nat*)
                (equal (fn-bpn-nth 2 event) (fn-bpb-encode (fn-bpn-nth 1 event)))
                (equal (fn-bpnf-receive-decision (fn-bpnf-held-list st)
                                                 (fn-bpn-nth 3 event)
                                                 (fn-bpn-nth 1 event))
                       :identity-conflict))
           (let* ((ans (fn-bpnp-step st event))
                  (st2 (fn-bpnf-answer-state ans))
                  (ingress (fn-bpn-nth 3 event))
                  (h (fn-bpnf-find-held
                      (fn-bpnf-held-key (fn-bpnf-ingress-principal ingress)
                                        (fn-bpb-bundle-id (fn-bpn-nth 1 event)))
                      (fn-bpnf-held-list st)))
                  (record (fn-bpnf-conflict-of
                           (fn-bpnf-epoch st) (fn-bpnf-next-op st) h ingress
                           (fn-bpn-nth 2 event))))
             (and (equal (fn-bpnf-held-list st2) (fn-bpnf-held-list st))
                  (if (and (fn-bpnf-conflict-recordp record)
                           (not (equal (fn-bpnf-conflict-frame record) :bad))
                           (fn-bpnd-admitp (fn-bpnp-used st) (fn-bpnp-debt st)
                                           *fn-bpnp-control-margin* 0 :spend))
                      (and (equal (fn-bpnf-answer-effects ans)
                                  (list (list :persist-conflict
                                              (fn-bpnf-epoch st)
                                              (fn-bpnf-next-op st) record)))
                           (equal (fn-bpnf-issued st2)
                                  (fn-bpnf-operation
                                   (fn-bpnf-epoch st) (fn-bpnf-next-op st)
                                   :conflict (list record ingress) :pending)))
                    (equal (fn-bpnf-answer-effects ans)
                           (list (list :receive-answer ingress
                                       :identity-conflict)))))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use ((:instance bpgap-conflict-arm-is-taken)
                 (:instance bpgap-conflict-held-under-hypotheses)
                 (:instance bpgap-conflict-propose-fields
                            (h (fn-bpnf-find-held
                                (fn-bpnf-held-key
                                 (fn-bpnf-ingress-principal (fn-bpn-nth 3 event))
                                 (fn-bpb-bundle-id (fn-bpn-nth 1 event)))
                                (fn-bpnf-held-list st)))))
           :in-theory (theory 'minimal-theory))))

;; The persist-result arm for a pending kind-14 operation, and its answer.
(local
 (defthm bpgap-conflict-persist-arm-is-taken
   (implies (and (equal (fn-bpn-nth 3 (fn-bpnf-issued st)) :conflict)
                 (equal (fn-bpn-nth 5 (fn-bpnf-issued st)) :pending))
            (equal (fn-bpnp-step st (list :persist-result epoch op result))
                   (fn-bpnp-conflict-persist-step st epoch op result)))
   :hints (("Goal" :do-not-induct t
            :expand ((fn-bpnp-step st (list :persist-result epoch op result)))
            :in-theory (union-theories '(fn-bpnp-domain-recover-eventp
                                         fn-cbor-ag-car fn-bpn-nth
                                         car-cons cdr-cons
                                         (:e fn-bpn-nth) (:e equal))
                                       (theory 'minimal-theory))))))

;; N11.  KEYSTONE (the record's publication outcome answers the refusal).
;; Whatever the kind-14 publication's outcome, the matching persist result
;; answers the recorded ingress exactly the refusal, keeps every held row,
;; clears the operation after a durable or refused publication, and fences
;; after any other; a durable record consumes one final of credit.
(defthm fn-bpnp-step-conflict-publication-answers-refusal
  (implies (and (equal (fn-bpn-nth 3 (fn-bpnf-issued st)) :conflict)
                (equal (fn-bpn-nth 5 (fn-bpnf-issued st)) :pending)
                (fn-bpnf-operation-matchp (fn-bpnf-issued st) epoch op)
                (equal event (list :persist-result epoch op result)))
           (let* ((ans (fn-bpnp-step st event))
                  (st2 (fn-bpnf-answer-state ans)))
             (and (equal (fn-bpnf-answer-effects ans)
                         (list (list :receive-answer
                                     (fn-bpn-nth 1 (fn-bpn-nth 4 (fn-bpnf-issued st)))
                                     :identity-conflict)))
                  (equal (fn-bpnf-held-list st2) (fn-bpnf-held-list st))
                  (if (member-equal result '(:durable :refused))
                      (null (fn-bpnf-issued st2))
                    (equal (fn-bpn-nth 5 (fn-bpnf-issued st2)) :uncertain))
                  (implies (equal result :durable)
                           (equal (fn-bpnp-used st2)
                                  (1+ (nfix (fn-bpnp-used st))))))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use ((:instance bpgap-conflict-persist-arm-is-taken))
           :in-theory (e/d (fn-bpnp-conflict-persist-step
                            fn-bpnp-conflict-refusal
                            fn-bpnp-domain-recover-eventp fn-bpnp-conflict-held
                            fn-bpnf-answer fn-bpnf-answer-state
                            fn-bpnf-answer-effects fn-bpnf-operation)
                           (fn-bpnp-step fn-bpnp-with-issued
                            fn-bpnp-with-credit fn-bpnp-with-waits
                            bpgap-conflict-persist-arm-is-taken)))))
