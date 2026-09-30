; PKT-064: unrelated volatile waits survive forwarding publication. The
; host subject is fn-bpnj-step, called by fnn-bps-foundation-step. Recovery
; and uncertainty remain separate transitions, with their existing policy.
(in-package "ACL2")
(include-book "bp-node-job-offer")

(local
 (defthm fn-bpnw-nth-past-length
   (implies (<= (len st) (nfix n))
            (equal (nth n st) nil))
   :hints (("Goal" :induct (nth n st)
            :in-theory (union-theories
                        '(nth len (:type-prescription len) nfix zp natp car-cons cdr-cons
                          (:e binary-+) (:e <) (:e equal))
                        (theory 'minimal-theory))))))

(local
 (defthm fn-bpnw-waits-of-writers
   (and (equal (fn-bpnp-waits (fn-bpnp-with-credit st used debt))
               (fn-bpnp-waits st))
        (equal (fn-bpnp-waits (fn-bpnp-with-runtime st sessions image))
               (fn-bpnp-waits st))
        (implies (true-listp st)
                 (equal (fn-bpnp-waits (fn-bpnp-with-waits st waits)) waits)))
   :hints (("Goal" :in-theory (enable fn-bpn-nth)))))

(local
 (defthm fn-bpnw-constructor-is-a-true-list
   (and (true-listp (fn-bpnf-state-with-arrival b h o d c i w e n a))
        (true-listp (fn-bpnp-with-issued st issued)))
   :hints (("Goal" :in-theory (enable fn-bpnp-with-issued
                                      fn-bpnf-with-issued)))))

(local
 (defthm fn-bpnw-result-proposal-keeps-waits
   (equal (fn-bpnp-waits
           (fn-bpnf-answer-state
            (fn-bpnp-forward-result-propose-step st ae ao session outcome obs)))
          (fn-bpnp-waits st))
   :hints (("Goal" :do-not-induct t
            :in-theory (union-theories
                        '(fn-bpnp-forward-result-propose-step
                          fn-bpnf-answer fn-bpnf-answer-state
                          fn-bpn-nth fn-cbor-ag-car fn-cbor-ag-cdr (:e natp) fn-bpnw-waits-of-writers
                          fn-bpnw-constructor-is-a-true-list
                          car-cons cdr-cons (:e zp) (:e binary-+) (:e equal))
                        (theory 'minimal-theory))))))

; KEYSTONE PRF-1116. Includes stale/rejected proposals: no antecedent, and
; no assumption that persistence has completed or that there is only one row.
(defthm fn-bpnj-forward-result-proposal-preserves-waits
  (equal (fn-bpnp-waits
          (fn-bpnf-answer-state
           (fn-bpnj-step st (list :forward-result ae ao session outcome obs))))
         (fn-bpnp-waits st))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-bpnj-step-delegates-every-other-event
                            (event (list :forward-result ae ao session outcome obs)))
                 (:instance fn-bpnw-result-proposal-keeps-waits))
           :in-theory (union-theories
                       '(fn-bpnp-step fn-bpnj-unnamed-result-p
                         fn-bpnp-domain-recover-eventp fn-bpnp-conflict-held
                         fn-bpnf-answer fn-bpnf-answer-state
                         fn-bpnw-result-proposal-keeps-waits
                         fn-bpn-nth fn-cbor-ag-car fn-cbor-ag-cdr (:e natp) car-cons cdr-cons
                         (:e zp) (:e binary-+) (:e equal))
                       (theory 'minimal-theory)))))

(local
 (defthm fn-bpnw-forward-refusal-keeps-waits-and-class
   (implies
    (member-equal (fn-bpn-nth 3 (fn-bpnf-issued st)) '(:attempt :forward-result))
    (let ((answer
           (if (equal (fn-bpn-nth 3 (fn-bpnf-issued st)) :attempt)
               (fn-bpnp-attempt-persist-step st epoch op :refused)
             (fn-bpnp-forward-result-persist-step st epoch op :refused))))
      (and (equal (fn-bpnp-waits (fn-bpnf-answer-state answer)) (fn-bpnp-waits st))
           (iff (equal (fn-bpnf-answer-effects answer) '((:forward-answer :refused)))
                (and (fn-bpnf-operation-matchp (fn-bpnf-issued st) epoch op)
                     (equal (fn-bpn-nth 5 (fn-bpnf-issued st)) :pending))))))
   :hints (("Goal" :do-not-induct t
            :in-theory (union-theories
                        '(fn-bpnp-attempt-persist-step
                          fn-bpnp-forward-result-persist-step member-equal
                          fn-bpnf-answer fn-bpnf-answer-state fn-bpnf-answer-effects
                          fn-bpn-nth fn-cbor-ag-car fn-cbor-ag-cdr (:e natp) fn-bpnw-waits-of-writers
                          fn-bpnw-constructor-is-a-true-list
                          car-cons cdr-cons (:e zp) (:e binary-+) (:e equal))
                        (theory 'minimal-theory))))))

; KEYSTONE PRF-1116. A refused kind-8/9 publication preserves every wait;
; only the matching pending callback reports refusal. A stale callback does
; not manufacture a refusal, and an uncertain operation remains fenced.
(defthm fn-bpnj-forward-publication-refusal-preserves-waits-and-class
  (implies
   (member-equal (fn-bpn-nth 3 (fn-bpnf-issued st)) '(:attempt :forward-result))
   (let ((answer (fn-bpnj-step st (list :persist-result epoch op :refused))))
     (and (equal (fn-bpnp-waits (fn-bpnf-answer-state answer)) (fn-bpnp-waits st))
          (iff (equal (fn-bpnf-answer-effects answer) '((:forward-answer :refused)))
               (and (fn-bpnf-operation-matchp (fn-bpnf-issued st) epoch op)
                    (equal (fn-bpn-nth 5 (fn-bpnf-issued st)) :pending))))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-bpnj-step-delegates-every-other-event
                            (event (list :persist-result epoch op :refused)))
                 (:instance fn-bpnw-forward-refusal-keeps-waits-and-class))
           :in-theory (union-theories
                       '(fn-bpnp-step fn-bpnj-unnamed-result-p member-equal
                         fn-bpnp-domain-recover-eventp fn-bpnp-conflict-held
                         fn-bpnf-answer fn-bpnf-answer-state fn-bpnf-answer-effects
                         fn-bpnw-forward-refusal-keeps-waits-and-class
                         fn-bpn-nth fn-cbor-ag-car fn-cbor-ag-cdr (:e natp) car-cons cdr-cons
                         (:e zp) (:e binary-+) (:e equal))
                       (theory 'minimal-theory)))))

; The dispatch callback preserves waits unless it reports uncertainty. A
; durable apply failure remains uncertain and deliberately drops waits.
(local
 (defthm fn-bpnw-dispatch-known-keeps-waits
   (implies
    (not (equal (fn-bpn-nth 1
                       (car (fn-bpnf-answer-effects
                             (fn-bpnp-dispatch-persist-step st epoch op result))))
                     :uncertain))
    (equal (fn-bpnp-waits
            (fn-bpnf-answer-state
             (fn-bpnp-dispatch-persist-step st epoch op result)))
           (fn-bpnp-waits st)))
   :hints (("Goal" :do-not-induct t
            :in-theory (union-theories
                         '(fn-bpnp-dispatch-persist-step fn-bpnf-with-issued member-equal
                           fn-bpnf-answer fn-bpnf-answer-state fn-bpnf-answer-effects
                           fn-bpnw-waits-of-writers fn-bpnw-constructor-is-a-true-list
                           fn-bpn-nth fn-cbor-ag-car fn-cbor-ag-cdr (:e natp)
                           car-cons cdr-cons (:e zp) (:e binary-+) (:e equal))
                         (theory 'minimal-theory))))))

(defthm fn-bpnj-dispatch-known-publication-preserves-waits
  (implies
   (and (equal (fn-bpn-nth 3 (fn-bpnf-issued st)) :dispatch)
        (not (equal (fn-bpn-nth 1
                      (car (fn-bpnf-answer-effects
                            (fn-bpnj-step st (list :persist-result epoch op result)))))
                    :uncertain)))
   (equal (fn-bpnp-waits
           (fn-bpnf-answer-state
            (fn-bpnj-step st (list :persist-result epoch op result))))
          (fn-bpnp-waits st)))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-bpnj-step-delegates-every-other-event
                            (event (list :persist-result epoch op result)))
                 (:instance fn-bpnw-dispatch-known-keeps-waits))
           :in-theory (union-theories
                        '(fn-bpnp-step fn-bpnj-unnamed-result-p member-equal
                          fn-bpnp-domain-recover-eventp fn-bpnp-conflict-held
                          fn-bpnp-preserve-runtime-answer
                          fn-bpnf-answer fn-bpnf-answer-state fn-bpnf-answer-effects
                          fn-bpnw-waits-of-writers
                          fn-bpn-nth fn-cbor-ag-car fn-cbor-ag-cdr (:e natp)
                          car-cons cdr-cons (:e zp) (:e binary-+) (:e equal))
                        (theory 'minimal-theory)))))

(local
 (defthm fn-bpnw-transit-dispatch-proposal-keeps-waits
   (implies
    (equal (fn-bpn-nth 0 (car (fn-bpnf-answer-effects
                              (fn-bpnp-transit-dispatch-step st h peer node))))
           :persist-dispatch)
    (equal (fn-bpnp-waits
            (fn-bpnf-answer-state (fn-bpnp-transit-dispatch-step st h peer node)))
           (fn-bpnp-waits st)))
   :hints (("Goal" :do-not-induct t
            :in-theory (union-theories
                         '(fn-bpnp-transit-dispatch-step fn-bpnf-answer
                           fn-bpnf-answer-state fn-bpnf-answer-effects
                           fn-bpnw-waits-of-writers fn-bpnw-constructor-is-a-true-list
                           fn-bpn-nth fn-cbor-ag-car fn-cbor-ag-cdr (:e natp)
                           car-cons cdr-cons (:e zp) (:e binary-+) (:e equal))
                         (theory 'minimal-theory))))))

(local
 (defthm fn-bpnw-progress-dispatch-proposal-keeps-pruned-waits
   (implies
    (and (true-listp st)
    (equal (fn-bpn-nth 0 (car (fn-bpnf-answer-effects
                             (fn-bpnp-progress-step st node obs routes generation budget))))
           :persist-dispatch))
    (equal (fn-bpnp-waits
            (fn-bpnf-answer-state
             (fn-bpnp-progress-step st node obs routes generation budget)))
           (fn-bpnp-prune-waits (fn-bpnp-waits st) (fn-bpnf-held-list st))))
   :hints (("Goal" :do-not-induct t
            :in-theory (union-theories
                         '(fn-bpnp-progress-step fn-bpnp-transit-dispatch-step
                           fn-bpah-deliver-step fn-bpnf-answer
                           fn-bpnf-answer-state fn-bpnf-answer-effects
                           fn-bpnw-transit-dispatch-proposal-keeps-waits
                           fn-bpnw-waits-of-writers fn-bpnw-constructor-is-a-true-list
                           fn-bpn-nth fn-cbor-ag-car fn-cbor-ag-cdr (:e natp)
                           car-cons cdr-cons (:e zp) (:e binary-+) (:e equal))
                         (theory 'minimal-theory))))))

(defthm fn-bpnj-progress-dispatch-preserves-pruned-waits
  (implies
   (and (true-listp st)
        (equal (fn-bpn-nth 0
                (car (fn-bpnf-answer-effects
                      (fn-bpnj-step st (list :progress node obs routes generation)))))
               :persist-dispatch))
   (equal (fn-bpnp-waits
           (fn-bpnf-answer-state
            (fn-bpnj-step st (list :progress node obs routes generation))))
          (fn-bpnp-prune-waits (fn-bpnp-waits st) (fn-bpnf-held-list st))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-bpnj-step-delegates-every-other-event
                            (event (list :progress node obs routes generation)))
                 (:instance fn-bpnw-progress-dispatch-proposal-keeps-pruned-waits
                            (budget (fn-bpnp-budget-retries
                                     (fn-bpnp-event-budgets
                                      (list :progress node obs routes generation) 5)))))
           :in-theory (union-theories
                        '(fn-bpnp-step fn-bpnj-unnamed-result-p
                          fn-bpnp-domain-recover-eventp fn-bpnp-conflict-held
                          fn-bpnf-answer fn-bpnf-answer-state fn-bpnf-answer-effects
                          fn-bpnw-waits-of-writers
                          fn-bpn-nth fn-cbor-ag-car fn-cbor-ag-cdr (:e natp)
                          car-cons cdr-cons (:e zp) (:e binary-+) (:e equal))
                        (theory 'minimal-theory)))))
