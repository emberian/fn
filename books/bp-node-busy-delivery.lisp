; BP-R17: a delivery the application answers busy is deferred at the node
; (spec bp-node-machine 4.2, the (:after m) wait; 11.1 BP-R17).  Every
; theorem is over fn-bpnp-step, the function host/native/bp-service.lisp
; fnn-bps-foundation-step calls; host/native/bp-node.lisp
; fnn-bpnode-dispatch-one issues the busy event with the node's budgets.
; Since 2026-09-25 (lane bp-budgets-receipts) the busy count is durable: the
; answer proposes a kind 20, its live persist arm and ordered replay apply
; it through one function, and the budgets are the operator's.
(in-package "ACL2")
(include-book "bp-node-progress")
(include-book "bp-fnbs-family-replay")

(local
 (defthm bpbusy-step-is-busy-step
   (implies (fn-bpnp-busy-eventp event)
            (equal (fn-bpnp-step st event)
                   (if (equal (fn-bpn-nth 5 (fn-bpnf-issued st)) :uncertain)
                       (fn-bpnf-answer st nil)
                     (fn-bpnp-busy-delivery-step
                      st (fn-bpn-nth 1 event) (fn-bpn-nth 2 event)
                      (fn-bpn-nth 3 event) (fn-bpn-nth 6 event)
                      (fn-bpnp-event-budgets event 7)))))
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

(local
 (defthm bpbusy-step-is-deferral-persist
   (implies (and (equal (fn-cbor-ag-car event) :persist-result)
                 (equal (fn-bpn-nth 3 (fn-bpnf-issued st)) :deferral))
            (equal (fn-bpnp-step st event)
                   (if (equal (fn-bpn-nth 5 (fn-bpnf-issued st)) :uncertain)
                       (fn-bpnf-answer st nil)
                     (fn-bpnp-deferral-persist-step
                      st (fn-bpn-nth 1 event) (fn-bpn-nth 2 event)
                      (fn-bpn-nth 3 event)))))
   :hints (("Goal" :do-not-induct t
            :expand ((fn-bpnp-step st event))
            :in-theory (union-theories
                        '(fn-bpnp-domain-recover-eventp (:e equal))
                        (theory 'minimal-theory))))))

;; KEYSTONE (BP-R17, durable count).  The owner's busy answer to the
;; delivery the marker names proposes exactly the kind 20 that counts it:
;; the row's arrival and primary identity, at the current epoch and next
;; operation, with count one more than the row's durable count.  Nothing
;; else moves the count: the held rows are unchanged until the record is
;; durable, and the marker is cleared.  Without journal credit the answer
;; is the credit wait instead, and nothing is issued.
(defthm fn-bpnp-step-busy-delivery-proposes-its-count
  (implies (and (fn-bpnp-busy-eventp event)
                (true-listp st)
                (equal (fn-bpnf-waits st)
                       (list :delivery (fn-bpn-nth 1 event)
                             (fn-bpn-nth 2 event) (fn-bpn-nth 3 event)))
                (equal (fn-bpnf-epoch st) (fn-bpn-nth 1 event))
                (null (fn-bpnf-issued st)))
           (let* ((ans (fn-bpnp-step st event))
                  (st2 (fn-bpnf-answer-state ans))
                  (h (fn-bpnf-find-held (fn-bpn-nth 3 event)
                                        (fn-bpnf-held-list st)))
                  (r (fn-bpnp-deferral-record
                      (fn-bpnf-epoch st) (fn-bpnf-next-op st)
                      (fn-bpn-nth 3 h) (fn-bpah-held-primary-identity h)
                      (1+ (fn-bpnp-busy-count h)))))
             (and (equal (fn-bpnf-held-list st2) (fn-bpnf-held-list st))
                  (null (fn-bpnf-waits st2))
                  (if (equal (fn-bpnf-answer-effects ans)
                             (list (list :persist-deferral (fn-bpnf-epoch st)
                                         (fn-bpnf-next-op st) r)))
                      (equal (fn-bpnf-issued st2)
                             (fn-bpnf-operation (fn-bpnf-epoch st)
                                                (fn-bpnf-next-op st)
                                                :deferral r :pending))
                    (and (null (fn-bpnf-issued st2))
                         (equal (car (car (fn-bpnf-answer-effects ans)))
                                :progress-wait))))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use ((:instance bpbusy-step-is-busy-step))
           :in-theory (e/d (fn-bpnp-busy-delivery-step fn-bpnp-with-next-issued
                            fn-bpnf-answer fn-bpnf-answer-state
                            fn-bpnf-answer-effects bpbusy-nth-is-nth)
                           (fn-bpnp-step fn-bpnp-busy-eventp
                            fn-bpnp-deferral-frame fn-bpnd-admitp
                            fn-bpnp-deferral-recordp fn-bpnp-busy-wait
                            fn-bpnf-find-held fn-bpah-held-primary-identity
                            fn-bpnd-free fn-bpnp-remove-wait)))))

;; The durable persist arm applies the kind 20 by fn-bpnp-deferral-apply,
;; the function ordered replay calls on the same record.
(defthm fn-bpnp-step-deferral-durable-applies-the-replay-function
  (implies (and (equal (fn-bpn-nth 3 (fn-bpnf-issued st)) :deferral)
                (equal (fn-bpn-nth 5 (fn-bpnf-issued st)) :pending)
                (fn-bpnf-operation-matchp (fn-bpnf-issued st) e op)
                (true-listp st)
                (equal (car (fn-bpnp-deferral-apply
                             (fn-bpn-nth 4 (fn-bpnf-issued st))
                             (fn-bpnf-held-list st)))
                       :ready))
           (equal (fn-bpnf-held-list
                   (fn-bpnf-answer-state
                    (fn-bpnp-step st (list :persist-result e op :durable))))
                  (fn-bpn-nth 1 (fn-bpnp-deferral-apply
                                 (fn-bpn-nth 4 (fn-bpnf-issued st))
                                 (fn-bpnf-held-list st)))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use ((:instance bpbusy-step-is-deferral-persist
                            (event (list :persist-result e op :durable))))
           :in-theory (e/d (fn-bpnp-deferral-persist-step
                            fn-bpnf-answer fn-bpnf-answer-state
                            fn-bpnf-held-list fn-bpnp-with-waits
                            fn-bpnp-with-credit bpbusy-nth-is-nth)
                           (fn-bpnp-step fn-bpnp-deferral-apply
                            fn-bpnp-with-issued fn-bpnf-find-arrival
                            fn-bpnp-wait-for fn-bpnp-remove-wait
                            fn-bpnp-deferral-effects)))))

;; Ordered replay over a journal extended by one row is the replay of the
;; journal continued by that row.
(local
 (defthm bpbusy-replay-append-one
   (implies (and (true-listp rows)
                 (equal (car (fn-bpnf-family-replay-rows-aux
                              rows base held handoffs prior next-arrival))
                        :ready))
            (equal (fn-bpnf-family-replay-rows-aux
                    (append rows (list row))
                    base held handoffs prior next-arrival)
                   (let ((r (fn-bpnf-family-replay-rows-aux
                             rows base held handoffs prior next-arrival)))
                     (fn-bpnf-family-replay-rows-aux
                      (list row) base (fn-bpn-nth 1 r) (fn-bpn-nth 2 r)
                      (fn-bpn-nth 3 r) (fn-bpn-nth 4 r)))))
   :hints (("Goal" :induct (fn-bpnf-family-replay-rows-aux
                            rows base held handoffs prior next-arrival)
            :in-theory (e/d (bpbusy-nth-is-nth)
                            (fn-bpnf-family-replay-row-record
                             fn-bpnf-stored-record-name
                             fn-bpnf-replay-pair-afterp
                             fn-bpah-apply-delivery fn-bpnf-family-apply-at
                             fn-bpn-report-apply-delete fn-bpnp-dispatch-apply
                             fn-bpnp-attempt-apply fn-bpnp-forward-result-apply
                             fn-bpnf-conflict-apply fn-bpnp-deferral-apply
                             fn-bpnf-receive-decision fn-bpnf-held-octets
                             fn-bpnf-state))))))

;; KEYSTONE (the count survives recovery).  Let ROWS be the durable
;; journal the live state's held rows replay from, and ROW the journal row
;; the live node wrote for its pending kind 20 R.  Then the held rows the
;; live durable persist arm leaves are exactly the held rows ordered replay
;; of ROWS then ROW computes, so every row's busy count after recovery
;; (fn-bpnp-host-recovery-installs-the-durable-replay installs the replay's
;; held rows exactly) is the count the live node held: a restart gives a
;; stranded row no fresh tries.  The subject pair is fn-bpnp-step (called by
;; fnn-bps-foundation-step) and fn-bpnf-family-replay-rows (called by
;; fn-bpnf-family-recover-auto-event, host/native/bp-service.lisp).
(defthm fn-bpnp-busy-count-after-recovery-is-the-live-count
  (implies (and (true-listp rows)
                (true-listp st)
                (equal (fn-bpnf-family-replay-rows rows base)
                       (list :ready (fn-bpnf-held-list st) handoffs prior
                             next-arrival))
                (equal (fn-bpn-nth 3 (fn-bpnf-issued st)) :deferral)
                (equal (fn-bpn-nth 5 (fn-bpnf-issued st)) :pending)
                (fn-bpnf-operation-matchp (fn-bpnf-issued st) e op)
                (equal (fn-bpnf-family-replay-row-record row)
                       (fn-bpn-nth 4 (fn-bpnf-issued st)))
                (equal (car (fn-bpn-nth 4 (fn-bpnf-issued st))) :bpnf-deferred)
                (equal (car row) (fn-bpnf-stored-record-name e op))
                (equal (fn-bpn-nth 1 (fn-bpn-nth 4 (fn-bpnf-issued st))) e)
                (equal (fn-bpn-nth 2 (fn-bpn-nth 4 (fn-bpnf-issued st))) op)
                (fn-bpnf-replay-pair-afterp e op prior)
                (equal (car (fn-bpnp-deferral-apply
                             (fn-bpn-nth 4 (fn-bpnf-issued st))
                             (fn-bpnf-held-list st)))
                       :ready))
           (equal (fn-bpnf-held-list
                   (fn-bpnf-answer-state
                    (fn-bpnp-step st (list :persist-result e op :durable))))
                  (fn-bpn-nth 1 (fn-bpnf-family-replay-rows
                                 (append rows (list row)) base))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-bpnp-step-deferral-durable-applies-the-replay-function)
                 (:instance bpbusy-replay-append-one
                            (held nil) (handoffs nil) (prior nil)
                            (next-arrival 0)))
           :expand ((fn-bpnf-family-replay-rows-aux
                     (list row) base (fn-bpnf-held-list st) handoffs prior
                     next-arrival)
                    (fn-bpnf-family-replay-rows-aux
                     nil base
                     (fn-bpn-nth 1 (fn-bpnp-deferral-apply
                                    (fn-bpn-nth 4 (fn-bpnf-issued st))
                                    (fn-bpnf-held-list st)))
                     handoffs (cons e op) next-arrival))
           :in-theory (e/d (fn-bpnf-family-replay-rows bpbusy-nth-is-nth)
                           (fn-bpnp-step fn-bpnf-family-replay-rows-aux
                            fn-bpnf-family-replay-row-record
                            fn-bpnf-stored-record-name fn-bpnf-replay-pair-afterp
                            fn-bpnp-deferral-apply)))))

;; The deferral ends.  A row not stranded under the configured budget is
;; not held back by its wait at any observation whose monotonic reading
;; reaches the wait's m.
(defthm fn-bpnp-busy-deferral-ends-at-its-reading
  (implies (and (equal (fn-bpnp-wait-for (fn-bpnp-wait-key h) waits)
                       (list :bpnp-wait key :busy m b))
                (natp m)
                (not (fn-bpnp-busy-strandedp h budget))
                (fn-clock-observationp obs)
                (<= m (fn-clock-monotonic obs)))
           (not (fn-bpnp-busy-blockedp h waits obs budget)))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-bpnp-busy-blockedp bpbusy-nth-is-nth)
                           (fn-bpnp-busy-strandedp)))))

(local
 (defthm bpbusy-selection-is-not-busy-blocked
   (let ((r (fn-bpnp-oldest-eligible-with-credit
             held node obs routes generation waits free budget selected)))
     (implies (not (equal r selected))
              (not (fn-bpnp-busy-blockedp r waits obs budget))))
   :hints (("Goal" :induct (fn-bpnp-oldest-eligible-with-credit
                            held node obs routes generation waits free budget
                            selected)
            :in-theory (union-theories
                        '(fn-bpnp-oldest-eligible-with-credit)
                        (theory 'minimal-theory))))))

;; A row stranded under the configured budget is never the progress
;; selection (the function fn-bpnp-progress-step calls), at any
;; observation: only the operator's kind-20 resume changes its count.
(defthm fn-bpnp-busy-stranded-row-is-not-offered
  (implies (and (fn-bpnp-busy-strandedp h budget) h)
           (not (equal (fn-bpnp-oldest-eligible-with-credit
                        held node obs routes generation waits free budget nil)
                       h)))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use ((:instance bpbusy-selection-is-not-busy-blocked
                            (selected nil)))
           :in-theory (e/d (fn-bpnp-busy-blockedp)
                           (fn-bpnp-busy-strandedp
                            fn-bpnp-oldest-eligible-with-credit)))))

(local
 (defthm bpbusy-first-stranded-is-stranded
   (let ((r (fn-bpnp-first-busy-stranded held budget selected)))
     (implies (and r (not (equal r selected)))
              (fn-bpnp-busy-strandedp r budget)))
   :hints (("Goal" :induct (fn-bpnp-first-busy-stranded held budget selected)
            :in-theory (e/d (fn-bpnp-first-busy-stranded)
                            (fn-bpnp-busy-strandedp))))))

(local
 (defthm bpbusy-first-stranded-found
   (implies (and (member-equal h held)
                 (fn-bpnp-busy-strandedp h budget))
            (fn-bpnp-first-busy-stranded held budget selected))
   :hints (("Goal" :induct (fn-bpnp-first-busy-stranded held budget selected)
            :in-theory (e/d (fn-bpnp-first-busy-stranded)
                            (fn-bpnp-busy-strandedp))))))

;; KEYSTONE (the stranded report repeats).  On a progress event that
;; selects no row to deliver or forward and finds no uncertain local row,
;; if any held row is stranded under the configured budget the answer is
;; the report of the oldest stranded row, with its durable count; the held
;; rows are unchanged.  So the report is made on every such tick until the
;; operator resumes the row (fnn-bpnode-dispatch-one prints it each tick).
(defthm fn-bpnp-progress-reports-a-stranded-row
  (let* ((held (fn-bpnf-held-list st))
         (waits (fn-bpnp-prune-waits (fn-bpnp-waits st) held))
         (ans (fn-bpnp-progress-step st node obs routes generation budget)))
    (implies (and (not (fn-bpnf-issued st)) (not (fn-bpnf-waits st))
                  (not (fn-bpn-machine-state-fenced (fn-bpnf-base st)))
                  (fn-bpp-eidp node) (fn-clock-observationp obs)
                  (fn-bpnp-routesp routes)
                  (<= (len routes) *fn-bpnp-max-routes*)
                  (fn-frame-natp generation)
                  (not (fn-bpnp-oldest-eligible-with-credit
                        held node obs routes generation waits
                        (fn-bpnd-free (fn-bpnp-used st) (fn-bpnp-debt st)
                                      *fn-bpnp-control-margin*)
                        budget nil))
                  (not (fn-bpnp-oldest-uncertain-local
                        held node obs generation waits budget nil))
                  (member-equal h held)
                  (fn-bpnp-busy-strandedp h budget))
             (let ((s (fn-bpnp-first-busy-stranded held budget nil)))
               (and (fn-bpnp-busy-strandedp s budget)
                    (equal (fn-bpnf-answer-effects ans)
                           (list (list :delivery-stranded
                                       (fn-bpnp-wait-key s)
                                       (fn-bpnp-busy-count s))))
                    (equal (fn-bpnf-held-list (fn-bpnf-answer-state ans))
                           held)))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use ((:instance bpbusy-first-stranded-is-stranded
                            (held (fn-bpnf-held-list st)) (selected nil))
                 (:instance bpbusy-first-stranded-found
                            (held (fn-bpnf-held-list st)) (selected nil)))
           :in-theory (e/d (fn-bpnp-progress-step fn-bpnp-busy-stranded-effects
                            fn-bpnf-answer fn-bpnf-answer-state
                            fn-bpnf-answer-effects fn-bpnp-with-waits
                            fn-bpnf-held-list bpbusy-nth-is-nth)
                           (fn-bpnp-oldest-eligible-with-credit
                            fn-bpnp-oldest-uncertain-local
                            fn-bpnp-first-busy-stranded fn-bpnp-busy-strandedp
                            fn-bpnp-prune-waits fn-bpnd-free
                            fn-bpnp-routesp fn-bpp-eidp
                            fn-clock-observationp)))))
