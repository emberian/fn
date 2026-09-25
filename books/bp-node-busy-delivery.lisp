; BP-R17: a delivery the application answers busy is deferred at the node
; (spec bp-node-machine 4.2, the (:after m) wait; 11.1 BP-R17).  Every
; theorem is over fn-bpnp-step, the function host/native/bp-service.lisp
; fnn-bps-foundation-step calls; host/native/bp-node.lisp
; fnn-bpnode-dispatch-one issues the seven-field busy event.
(in-package "ACL2")
(include-book "bp-node-progress")

(local
 (defthm bpbusy-step-is-busy-step
   (implies (fn-bpnp-busy-eventp event)
            (equal (fn-bpnp-step st event)
                   (if (equal (fn-bpn-nth 5 (fn-bpnf-issued st)) :uncertain)
                       (fn-bpnf-answer st nil)
                     (fn-bpnp-busy-delivery-step
                      st (fn-bpn-nth 1 event) (fn-bpn-nth 2 event)
                      (fn-bpn-nth 3 event) (fn-bpn-nth 6 event)))))
   :hints (("Goal" :do-not-induct t
            :expand ((fn-bpnp-step st event))
            :in-theory (union-theories
                        '(fn-bpnp-busy-eventp fn-bpnp-domain-recover-eventp
                          fn-cbor-ag-car car-cons (:e equal))
                        (theory 'minimal-theory))))))

;; Slot facts: fn-bpn-nth is nth on a natural index; the writers are
;; update-nth, so nth-update-nth decides each slot.
(local
 (defthm bpbusy-nth-is-nth
   (implies (natp n)
            (equal (fn-bpn-nth n xs) (nth n xs)))
   :hints (("Goal" :induct (fn-bpn-nth n xs)
            :in-theory (enable fn-bpn-nth nth fn-cbor-ag-car)))))

(local
 (defthm bpbusy-slots-of-deferral
   (let ((st2 (update-nth 11 w (update-nth 7 nil st))))
     (and (equal (fn-bpnf-held-list st2) (fn-bpnf-held-list st))
          (equal (fn-bpnf-handoffs st2) (fn-bpnf-handoffs st))
          (equal (fn-bpnf-outcomes st2) (fn-bpnf-outcomes st))
          (equal (fn-bpnf-issued st2) (fn-bpnf-issued st))
          (equal (fn-bpnf-base st2) (fn-bpnf-base st))
          (equal (fn-bpnf-epoch st2) (fn-bpnf-epoch st))
          (equal (fn-bpnf-next-op st2) (fn-bpnf-next-op st))
          (equal (fn-bpnf-next-arrival st2) (fn-bpnf-next-arrival st))
          (equal (fn-bpnp-used st2) (fn-bpnp-used st))
          (equal (fn-bpnp-debt st2) (fn-bpnp-debt st))
          (equal (fn-bpnp-sessions st2) (fn-bpnp-sessions st))
          (equal (fn-bpnf-waits st2) nil)
          (equal (fn-bpnp-waits st2) w)))
   :hints (("Goal" :in-theory (union-theories
                               '(fn-bpnf-held-list fn-bpnf-handoffs
                                 fn-bpnf-outcomes fn-bpnf-issued fn-bpnf-base
                                 fn-bpnf-epoch fn-bpnf-next-op
                                 fn-bpnf-next-arrival fn-bpnp-used
                                 fn-bpnp-debt fn-bpnp-sessions fn-bpnf-waits
                                 fn-bpnp-waits bpbusy-nth-is-nth
                                 nth-update-nth (:e natp) (:e nfix) (:e equal))
                               (theory 'minimal-theory))))))

;; KEYSTONE (BP-R17).  The owner's busy answer to the delivery the marker
;; names neither releases nor refuses: the step proposes no record, the
;; held row, its handoffs and outcomes, the issued slot, the base, the
;; frontiers, journal credit and sessions are unchanged, and the state
;; differs from ST only in the cleared marker (slot 7) and the key's
;; deferral wait (slot 11).  The one effect is the deferral, or at the
;; kind-8 retry bound the stranded report; never a :refused or
;; :uncertain answer.
(defthm fn-bpnp-step-busy-delivery-defers
  (implies (and (fn-bpnp-busy-eventp event)
                (true-listp st)
                (equal (fn-bpnf-waits st)
                       (list :delivery (fn-bpn-nth 1 event)
                             (fn-bpn-nth 2 event) (fn-bpn-nth 3 event)))
                (equal (fn-bpnf-epoch st) (fn-bpn-nth 1 event))
                (null (fn-bpnf-issued st)))
           (let* ((ans (fn-bpnp-step st event))
                  (st2 (fn-bpnf-answer-state ans))
                  (key (fn-bpn-nth 3 event))
                  (wait (fn-bpnp-busy-wait key (fn-bpnp-waits st)
                                           (fn-bpn-nth 6 event)))
                  (n (fn-bpn-nth 3 wait)))
             (and (equal st2
                         (update-nth 11 (cons wait (fn-bpnp-remove-wait
                                                    key (fn-bpnp-waits st)))
                                     (update-nth 7 nil st)))
                  (equal (fn-bpnf-held-list st2) (fn-bpnf-held-list st))
                  (equal (fn-bpnf-handoffs st2) (fn-bpnf-handoffs st))
                  (equal (fn-bpnf-outcomes st2) (fn-bpnf-outcomes st))
                  (null (fn-bpnf-issued st2))
                  (null (fn-bpnf-waits st2))
                  (equal (fn-bpnf-next-op st2) (fn-bpnf-next-op st))
                  (equal (fn-bpnp-used st2) (fn-bpnp-used st))
                  (equal (fn-bpnf-answer-effects ans)
                         (list (if (<= *fn-bpnp-max-forward-retries* n)
                                   (list :delivery-stranded key n)
                                 (list :delivery-deferred key n
                                       (fn-bpn-nth 4 wait))))))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use ((:instance bpbusy-step-is-busy-step)
                 (:instance bpbusy-slots-of-deferral
                            (w (cons (fn-bpnp-busy-wait
                                      (fn-bpn-nth 3 event) (fn-bpnp-waits st)
                                      (fn-bpn-nth 6 event))
                                     (fn-bpnp-remove-wait
                                      (fn-bpn-nth 3 event)
                                      (fn-bpnp-waits st))))))
           :in-theory (union-theories
                       '(fn-bpnp-busy-delivery-step fn-bpnf-answer
                         fn-bpnf-answer-state fn-bpnf-answer-effects
                         bpbusy-nth-is-nth nth car-cons cdr-cons
                         (:e natp) (:e zp) (:e fn-bpn-nth) (:e equal)
                         (:e <) (:e binary-+))
                       (theory 'minimal-theory)))))

;; The deferral ends.  A row whose deferral wait is under the kind-8 retry
;; bound is not held back by it at any observation whose monotonic reading
;; reaches the wait's m, so class 3 offers it again (the positive trace in
;; bp-node-counterexamples-tests runs the redelivery through fn-bpnp-step).
(defthm fn-bpnp-busy-deferral-ends-at-its-reading
  (implies (and (equal (fn-bpnp-wait-for (fn-bpnp-wait-key h) waits)
                       (list :bpnp-wait key :busy n m))
                (natp n) (natp m)
                (< n *fn-bpnp-max-forward-retries*)
                (fn-clock-observationp obs)
                (<= m (fn-clock-monotonic obs)))
           (not (fn-bpnp-busy-blockedp h waits obs)))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (union-theories
                       '(fn-bpnp-busy-blockedp bpbusy-nth-is-nth nth
                         car-cons cdr-cons nfix natp-compound-recognizer
                         (:e natp) (:e zp) (:e equal) (:e binary-+)
                         (:e fn-bpn-nth) (:e nfix) (:e <)
                         fn-clock-observationp fn-clock-timep natp)
                       (theory 'minimal-theory)))))

(local
 (defthm bpbusy-selection-is-not-busy-blocked
   (let ((r (fn-bpnp-oldest-eligible-with-credit
             held node obs routes generation waits free selected)))
     (implies (not (equal r selected))
              (not (fn-bpnp-busy-blockedp r waits obs))))
   :hints (("Goal" :induct (fn-bpnp-oldest-eligible-with-credit
                            held node obs routes generation waits free
                            selected)
            :in-theory (union-theories
                        '(fn-bpnp-oldest-eligible-with-credit)
                        (theory 'minimal-theory))))))

;; A stranded row stays held and is never the progress selection: at the
;; retry bound its deferral holds it back at every observation, until
;; recovery clears the volatile wait.
(defthm fn-bpnp-busy-stranded-row-is-not-offered
  (implies (and (equal (fn-bpnp-wait-for (fn-bpnp-wait-key h) waits)
                       (list :bpnp-wait key :busy n m))
                (natp n)
                (<= *fn-bpnp-max-forward-retries* n)
                h)
           (not (equal (fn-bpnp-oldest-eligible-with-credit
                        held node obs routes generation waits free nil)
                       h)))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use ((:instance bpbusy-selection-is-not-busy-blocked
                            (selected nil)))
           :in-theory (union-theories
                       '(fn-bpnp-busy-blockedp bpbusy-nth-is-nth nth
                         car-cons cdr-cons nfix
                         natp natp-compound-recognizer
                         (:e natp) (:e zp) (:e equal) (:e fn-bpn-nth)
                         (:e nfix) (:e <))
                       (theory 'minimal-theory)))))
