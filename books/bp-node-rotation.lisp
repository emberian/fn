; Rotation of the BP lifecycle journal (spec bp-node-machine 3.6, slice E,
; trace N16): recovery from a held-row checkpoint, and its two keystones.
;
; The host (host/native/bp-service.lisp fnn-bps-open) reads the selection
; file named by fn-bpnr-selection-name, asks fn-bpnr-selection-plan what it
; means, enumerates the generation directory the plan names, and passes the
; plan and that directory's ordered received finals to
; fn-bpnr-recover-auto-event.  The event it returns goes to fn-bpnp-step,
; exactly as the event of fn-bpnf-family-recover-auto-event did before.
;
; With a checkpoint the record limit of the received namespace
; (*fn-bpnf-received-max-records*) bounds the work of one replay: the
; suffix of one generation, plus one checkpoint decode bounded by the
; profile (fn-bpnr-read-bound, fn-bpnr-depth-budget).  It no longer bounds
; the data the journal can carry over its lifetime, because a rotation
; starts a generation whose record count is zero (D27).
(in-package "ACL2")
(include-book "bp-fnbs-family-replay")
(include-book "bp-node-progress")
(include-book "bp-node-rotation-codec")
(set-verify-guards-eagerness 0)

; What the selected file means.  No file: generation 0, no checkpoint.
; A file that does not decode: damaged, recovery fences.
(defun fn-bpnr-selection-plan (present octets budget)
  (declare (xargs :guard t))
  (if (not present)
      (list :none)
    (let ((ck (fn-bpnr-checkpoint-decode octets budget)))
      (if ck (list :selected ck) (list :damaged)))))

(defun fn-bpnr-plan-checkpoint (plan)
  (declare (xargs :guard t))
  (if (equal (fn-cbor-ag-car plan) :selected) (fn-bpn-nth 1 plan) nil))

(defun fn-bpnr-plan-generation (plan)
  (declare (xargs :guard t))
  (if (equal (fn-cbor-ag-car plan) :selected)
      (fn-bpnr-checkpoint-generation (fn-bpn-nth 1 plan))
    0))

(defun fn-bpnr-plan-directory (plan)
  (declare (xargs :guard t :verify-guards nil))
  (fn-bpnr-generation-directory (fn-bpnr-plan-generation plan)))

; The replay of one generation's rows from its checkpoint.  Without a
; checkpoint it is exactly fn-bpnf-family-replay-rows.
(defun fn-bpnr-replay-from (ck rows base)
  (declare (xargs :guard t))
  (if (fn-bpnr-checkpointp ck)
      (fn-bpnf-family-replay-rows-aux
       rows base (fn-bpnr-checkpoint-held ck) (fn-bpnr-checkpoint-handoffs ck)
       (fn-bpnr-checkpoint-prior ck) (fn-bpnr-checkpoint-next-arrival ck))
    (fn-bpnf-family-replay-rows rows base)))

; The recovery event the host passes to fn-bpnp-step at open.  The epoch
; rule and the event shape are fn-bpnf-family-recover-auto-event's; the row
; count is the current generation's, which is what rotation resets.
(defun fn-bpnr-recover-auto-event (st base-records sequence-ready rows plan)
  (declare (xargs :guard t))
  (let* ((replay (if (equal (fn-cbor-ag-car plan) :damaged)
                     (list :fault :generation-authority)
                   (fn-bpnr-replay-from (fn-bpnr-plan-checkpoint plan)
                                        rows (fn-bpnf-base st))))
         (prior (fn-bpn-nth 3 replay))
         (new-epoch (1+ (max (nfix (fn-bpnf-epoch st))
                             (nfix (and (consp prior) (car prior)))))))
    (list :recover-fnbs new-epoch base-records sequence-ready replay
          (len rows))))

; The checkpoint of a replay result, and of the recovery event the host
; holds after open (the value `bp-node checkpoint' passes to :rotate).
(defun fn-bpnr-checkpoint-of-replay (generation replay covered)
  (declare (xargs :guard t))
  (fn-bpnr-checkpoint generation (fn-bpn-nth 1 replay) (fn-bpn-nth 2 replay)
                      (fn-bpn-nth 3 replay) (fn-bpn-nth 4 replay) covered))

(defun fn-bpnr-checkpoint-of-event (event generation)
  (declare (xargs :guard t))
  (fn-bpnr-checkpoint-of-replay generation (fn-bpn-nth 4 event)
                                (fn-bpn-nth 5 event)))

; The clock-domain gate's retained evidence (N07): a selected or damaged
; checkpoint is retained evidence, so a missing domain record next to it
; never initializes a fresh domain.
(defun fn-bpnr-clock-domain-evidence (namespace-plan sequence-present plan)
  (declare (xargs :guard t))
  (or (fn-bpnf-clock-domain-legacy-evidence namespace-plan sequence-present)
      (not (equal (fn-cbor-ag-car plan) :none))))

; ---------------------------------------------------------------------------
; The fold composes: replaying a prefix and then a suffix from the prefix's
; accumulator is replaying their concatenation.  First one row, then any
; prefix by an induction that carries the accumulator.

(defthm fn-bpnr-family-replay-aux-cons
  (implies (syntaxp (not (equal rest ''nil)))
           (equal (fn-bpnf-family-replay-rows-aux
                   (cons row rest) base held handoffs prior next-arrival)
                  (let ((r (fn-bpnf-family-replay-rows-aux
                            (list row) base held handoffs prior next-arrival)))
                    (if (equal (car r) :ready)
                        (fn-bpnf-family-replay-rows-aux
                         rest base (fn-bpn-nth 1 r) (fn-bpn-nth 2 r)
                         (fn-bpn-nth 3 r) (fn-bpn-nth 4 r))
                      r))))
  :hints (("Goal" :do-not-induct t
           :do-not '(generalize fertilize eliminate-destructors)
           :expand ((fn-bpnf-family-replay-rows-aux
                     (cons row rest) base held handoffs prior next-arrival)
                    (fn-bpnf-family-replay-rows-aux
                     (list row) base held handoffs prior next-arrival)
                    (:free (h ho p na)
                           (fn-bpnf-family-replay-rows-aux nil base h ho p na)))
           :in-theory (disable fn-bpnf-family-replay-rows-aux
                               fn-bpnf-family-replay-row-record
                               fn-bpnf-stored-record-name
                               fn-bpnf-replay-pair-afterp
                               fn-bpnf-receive-decision
                               fn-bpah-apply-delivery fn-bpnf-family-apply-at
                               fn-bpn-report-apply-delete fn-bpnp-dispatch-apply
                               fn-bpnp-attempt-apply fn-bpnp-forward-result-apply
                               fn-bpnf-conflict-apply fn-bpnf-state
                               fn-bpnf-held-octets fn-bpn-machine-state-max-jobs
                               fn-bpn-machine-state-max-octets
                               fn-bpnf-held-bundle))))

(local
 (defun fn-bpnr-append-induct (prefix base held handoffs prior next-arrival)
   (if (atom prefix) (list base held handoffs prior next-arrival)
     (let ((r (fn-bpnf-family-replay-rows-aux
               (list (car prefix)) base held handoffs prior next-arrival)))
       (fn-bpnr-append-induct (cdr prefix) base (fn-bpn-nth 1 r) (fn-bpn-nth 2 r)
                              (fn-bpn-nth 3 r) (fn-bpn-nth 4 r))))))

(defthm fn-bpnr-family-replay-aux-append
  (implies (true-listp prefix)
           (equal (fn-bpnf-family-replay-rows-aux
                   (append prefix suffix) base held handoffs prior next-arrival)
                  (let ((r (fn-bpnf-family-replay-rows-aux
                            prefix base held handoffs prior next-arrival)))
                    (if (equal (car r) :ready)
                        (fn-bpnf-family-replay-rows-aux
                         suffix base (fn-bpn-nth 1 r) (fn-bpn-nth 2 r)
                         (fn-bpn-nth 3 r) (fn-bpn-nth 4 r))
                      r))))
  :hints (("Goal" :induct (fn-bpnr-append-induct
                           prefix base held handoffs prior next-arrival)
           :do-not '(generalize fertilize eliminate-destructors)
           :in-theory (disable fn-bpnf-family-replay-rows-aux
                               fn-bpnr-family-replay-aux-cons))
          ("Subgoal *1/2"
           :use ((:instance fn-bpnr-family-replay-aux-cons
                            (row (car prefix)) (rest (cdr prefix)))
                 (:instance fn-bpnr-family-replay-aux-cons
                            (row (car prefix))
                            (rest (append (cdr prefix) suffix)))))
          ("Subgoal *1/1"
           :expand ((fn-bpnf-family-replay-rows-aux
                     nil base held handoffs prior next-arrival)))))

; ---------------------------------------------------------------------------
; KEYSTONE (recovery from a checkpoint).  Take any recovery authority the
; host can act on (no checkpoint, or a selected one) and the rows of its
; generation, whose replay is ready.  Write the checkpoint of that replay at
; a new generation.  Then recovery from the new checkpoint and any later
; rows is exactly recovery from the old authority over the old rows followed
; by the later ones: the same replay result, hence the same held rows,
; handoffs, operation frontier, arrival frontier and epoch.  Only the row
; count differs, and it is the new generation's own count: that is the
; reset.  With plan0 = (:none) the right side is replay of the whole
; history (fn-bpnr-recover-without-checkpoint-is-family-recover).
(defthm fn-bpnr-replay-from-checkpoint-chains
  (implies (and (true-listp rows0)
                (equal (car (fn-bpnr-replay-from ck0 rows0 base)) :ready)
                (fn-bpnr-checkpointp ck1)
                (equal ck1 (fn-bpnr-checkpoint-of-replay
                            generation (fn-bpnr-replay-from ck0 rows0 base)
                            covered)))
           (equal (fn-bpnr-replay-from ck1 suffix base)
                  (fn-bpnr-replay-from ck0 (append rows0 suffix) base)))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-bpnf-family-replay-rows)
                           (fn-bpnf-family-replay-rows-aux
                            fn-bpnr-checkpointp)))))

(defthm fn-bpnr-recover-without-checkpoint-is-family-recover
  (equal (fn-bpnr-recover-auto-event st base-records sequence-ready rows
                                     '(:none))
         (fn-bpnf-family-recover-auto-event st base-records sequence-ready
                                            rows))
  :hints (("Goal" :in-theory (disable fn-bpnf-family-replay-rows))))

(defthm fn-bpnr-recover-from-checkpoint-equals-full-recover
  (implies (and (true-listp rows0)
                (not (equal (car plan0) :damaged))
                (equal (car (fn-bpnr-replay-from
                             (fn-bpnr-plan-checkpoint plan0) rows0
                             (fn-bpnf-base st)))
                       :ready)
                (equal ck1 (fn-bpnr-checkpoint-of-replay
                            generation
                            (fn-bpnr-replay-from
                             (fn-bpnr-plan-checkpoint plan0) rows0
                             (fn-bpnf-base st))
                            covered))
                (fn-bpnr-checkpoint-octets ck1 budget))
           (equal (fn-bpnr-recover-auto-event
                   st base-records sequence-ready suffix
                   (fn-bpnr-selection-plan
                    t (fn-bpnr-checkpoint-octets ck1 budget) budget))
                  (update-nth 5 (len suffix)
                              (fn-bpnr-recover-auto-event
                               st base-records sequence-ready
                               (append rows0 suffix) plan0))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-bpnr-replay-from-checkpoint-chains
                            (ck0 (fn-bpnr-plan-checkpoint plan0))
                            (base (fn-bpnf-base st)))
                 (:instance fn-bpnr-checkpoint-decode-of-octets
                            (ck ck1)))
           :in-theory (disable fn-bpnr-replay-from fn-bpnr-checkpoint-octets
                               fn-bpnr-checkpoint-decode
                               fn-bpnr-checkpoint-of-replay
                               fn-bpnr-replay-from-checkpoint-chains
                               fn-bpnr-checkpoint-decode-of-octets))))

; ---------------------------------------------------------------------------
; KEYSTONE (process death during the rotation program).  The host publishes
; the new selection file with the Store's marker program
; (host/native/bp-node.lisp fnnr-bp-publish-selection, driven by
; fn-cpp-marker-driver-action/-step/-outcome, the same driver
; host/native/checkpoint.lisp fnn-marker-replace uses): stage and file
; barrier, rename over the final name, directory barrier.  The rename is the
; only step that changes the visible selection, and it is atomic (old or
; new).  So a kill in any phase leaves the old file visible, and from the
; phase in which the rename may have been issued, either file.  The program
; writes no record into the new generation's directory before the
; selection is durable, so recovery under the new file reads no rows.
(defun fn-bpnr-replace-issuedp (phase)
  (declare (xargs :guard t))
  (if (member-equal phase '(:marker-data-durable :marker-attempted :idle
                            :fenced-marker))
      t nil))

(defun fn-bpnr-crash-visible (phase old new choice)
  (declare (xargs :guard t))
  (if (and (fn-bpnr-replace-issuedp phase) (equal choice :new)) new old))

(defthm fn-bpnr-rotation-crash-recovers-old-or-new
  (implies (and (true-listp rows0)
                (equal plan0 (fn-bpnr-selection-plan (and old t) old budget))
                (not (equal (car plan0) :damaged))
                (equal (car (fn-bpnr-replay-from
                             (fn-bpnr-plan-checkpoint plan0) rows0
                             (fn-bpnf-base st)))
                       :ready)
                (equal ck1 (fn-bpnr-checkpoint-of-replay
                            generation
                            (fn-bpnr-replay-from
                             (fn-bpnr-plan-checkpoint plan0) rows0
                             (fn-bpnf-base st))
                            covered))
                (equal new (fn-bpnr-checkpoint-octets ck1 budget))
                new)
           (let* ((visible (fn-bpnr-crash-visible phase old new choice))
                  (plan (fn-bpnr-selection-plan (and visible t) visible
                                                budget)))
             (and (or (equal visible old) (equal visible new))
                  (implies (not (fn-bpnr-replace-issuedp phase))
                           (equal visible old))
                  (implies (equal visible old) (equal plan plan0))
                  (implies (equal visible new)
                           (equal (fn-bpnr-recover-auto-event
                                   st base-records sequence-ready nil plan)
                                  (update-nth 0 :recover-fnbs
                                   (update-nth 5 0
                                    (fn-bpnr-recover-auto-event
                                     st base-records sequence-ready rows0
                                     plan0))))))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-bpnr-recover-from-checkpoint-equals-full-recover
                            (suffix nil)))
           :in-theory (disable fn-bpnr-recover-auto-event fn-bpnr-selection-plan
                               fn-bpnr-replay-from fn-bpnr-checkpoint-octets
                               fn-bpnr-checkpoint-of-replay
                               fn-bpnr-recover-from-checkpoint-equals-full-recover))))

; ---------------------------------------------------------------------------
; The machine's rotation transition, through fn-bpnp-step (the function
; host/native/bp-service.lisp fnn-bps-foundation-step calls; the host
; issues :rotate at bp-node.lisp fnn-command-bp-node-checkpoint and the
; publication's answer at bp-service.lisp fnn-bps-drive-effects
; :persist-checkpoint).

;; KEYSTONE.  A rotation is proposed only for the machine's own durable
;; projection, from a quiescent recovered state.
(defthm fn-bpnp-step-rotate-proposes-only-own-projection
  (implies (equal (car (car (fn-bpnf-answer-effects
                             (fn-bpnp-step st (list :rotate generation ck)))))
                  :persist-checkpoint)
           (and (fn-bpnr-checkpoint-of-statep ck st generation)
                (fn-bpnp-rotation-quiescentp st)
                (fn-bpnr-checkpoint-octets
                 ck (fn-bpnr-depth-budget
                     (fn-bpn-machine-state-max-jobs (fn-bpnf-base st))))))
  :hints (("Goal" :do-not-induct t
           :in-theory (union-theories
                       '(fn-bpnp-step fn-bpnp-rotate-step
                         fn-bpnp-domain-recover-eventp fn-bpnf-answer
                         fn-bpnf-answer-effects fn-cbor-ag-car
                         (:e fn-bpn-nth) fn-bpn-nth car-cons cdr-cons
                         (:e equal) (:e car) (:e cdr) (:e consp) (:e len)
                         (:e true-listp))
                       (theory 'minimal-theory)))))

;; KEYSTONE.  The record count changes on a checkpoint publication's answer
;; only when that answer is :durable for the issued operation, and then it
;; is zero: the new generation starts empty.  :rotate itself never changes it.
(defthm fn-bpnp-step-rotation-resets-credit-only-on-durable
  (implies (and (equal (fn-bpn-nth 3 (fn-bpnf-issued st)) :checkpoint)
                (equal (fn-cbor-ag-car event) :persist-result)
                (not (equal (fn-bpnp-used
                             (fn-bpnf-answer-state (fn-bpnp-step st event)))
                            (fn-bpnp-used st))))
           (and (equal (fn-bpn-nth 3 event) :durable)
                (equal (fn-bpn-nth 5 (fn-bpnf-issued st)) :pending)
                (fn-bpnf-operation-matchp (fn-bpnf-issued st)
                                          (fn-bpn-nth 1 event)
                                          (fn-bpn-nth 2 event))
                (equal (fn-bpnp-used
                        (fn-bpnf-answer-state (fn-bpnp-step st event)))
                       0)))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-bpnp-step fn-bpnp-rotation-persist-step
                            fn-bpnp-domain-recover-eventp fn-bpnp-used)
                           (fn-bpnp-rotate-step fn-bpnp-clock-domain-fence
                            fn-bpnp-conflict-persist-step
                            fn-bpnp-busy-delivery-step fn-bpnp-conflict-held
                            fn-bpnp-conflict-propose-step fn-bpnp-start-one
                            fn-bpnp-operator-resume-step
                            fn-bpnp-forward-result-propose-step
                            fn-bpnp-progress-step fn-bpnp-dispatch-persist-step
                            fn-bpnp-attempt-persist-step
                            fn-bpnp-forward-result-persist-step
                            fn-bpnp-delegate-with-credit
                            fn-bpnp-preserve-runtime-answer
                            fn-bpnf-operation-matchp)))))

(defthm fn-bpnp-step-rotate-keeps-credit
  (equal (fn-bpnp-used (fn-bpnf-answer-state
                        (fn-bpnp-step st (list :rotate generation ck))))
         (fn-bpnp-used st))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-bpnp-step fn-bpnp-rotate-step
                            fn-bpnp-domain-recover-eventp fn-bpnp-used)
                           (fn-bpnp-clock-domain-fence
                            fn-bpnr-checkpoint-of-statep
                            fn-bpnp-rotation-quiescentp
                            fn-bpnr-checkpoint-octets)))))
