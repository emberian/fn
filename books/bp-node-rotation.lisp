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
(include-book "bp-fnbs-replay-append")
(include-book "bp-node-progress")
(include-book "bp-node-rotation-codec")
(include-book "bp-clock-domain")
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

(defthm fn-bpnr-checkpoint-octets-names-a-checkpoint
  (implies (fn-bpnr-checkpoint-octets ck budget)
           (and (fn-bpnr-checkpointp ck) ck))
  :rule-classes nil
  :hints (("Goal" :in-theory '(fn-bpnr-checkpoint-octets fn-bpnr-checkpointp))))
(defthm fn-bpnr-selection-plan-of-octets
  (implies (fn-bpnr-checkpoint-octets ck budget)
           (equal (fn-bpnr-selection-plan t (fn-bpnr-checkpoint-octets ck budget)
                                          budget)
                  (list :selected ck)))
  :hints (("Goal" :use (fn-bpnr-checkpoint-decode-of-octets
                        fn-bpnr-checkpoint-octets-names-a-checkpoint)
           :in-theory '(fn-bpnr-selection-plan))))
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
                 (:instance fn-bpnr-checkpoint-octets-names-a-checkpoint
                            (ck ck1)))
           :in-theory (union-theories
                       '(fn-bpnr-recover-auto-event fn-bpnr-plan-checkpoint
                         fn-bpnr-selection-plan-of-octets
                         update-nth car-cons cdr-cons fn-cbor-ag-car
                         (:e zp) (:e equal) (:e car) (:e cdr) (:e consp)
                         (:e fn-cbor-ag-car) (:e fn-bpn-nth) (:e nfix) (:e binary-+) len fn-bpn-nth (:e natp) (:e not) (:e unary--))
                       (theory 'minimal-theory)))))

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
                                  (update-nth 5 0
                                   (fn-bpnr-recover-auto-event
                                    st base-records sequence-ready rows0
                                    plan0)))))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-bpnr-recover-from-checkpoint-equals-full-recover
                            (suffix nil))
                 (:instance fn-bpnr-selection-plan-of-octets (ck ck1)))
           :in-theory (union-theories
                       '(fn-bpnr-crash-visible append-to-nil (:e len)
                         (:e fn-bpnr-replace-issuedp))
                       (theory 'minimal-theory)))))

; ---------------------------------------------------------------------------
; The machine's rotation arms.  fn-bpnp-step dispatches (:rotate g ck) to
; fn-bpnp-rotate-step and a :persist-result whose issued operation is a
; :checkpoint to fn-bpnp-rotation-persist-step, after its uncertainty fence
; and clock-domain arm (books/bp-node-progress.lisp).  The theorems below
; are stated over the arms; the N16 trace in
; tests/acl2/bp-node-counterexamples-tests.lisp drives them through
; fn-bpnp-step.  A theorem equating the arms to fn-bpnp-step on these
; events is open (the step's case split does not return in a minute).

;; KEYSTONE.  A rotation is proposed only for the machine's own durable
;; projection, from a quiescent recovered state, with a file that fits the
;; profile's read bound.
(defthm fn-bpnp-rotate-step-proposes-only-own-projection
  (implies (equal (car (car (fn-bpnf-answer-effects
                             (fn-bpnp-rotate-step st generation ck))))
                  :persist-checkpoint)
           (and (fn-bpnr-checkpoint-of-statep ck st generation)
                (fn-bpnp-rotation-quiescentp st)
                (fn-bpnr-checkpoint-octets
                 ck (fn-bpnr-depth-budget
                     (fn-bpn-machine-state-max-jobs (fn-bpnf-base st))))))
  :hints (("Goal" :do-not-induct t
           :in-theory '(fn-bpnp-rotate-step fn-bpnf-answer
                        fn-bpnf-answer-effects fn-bpn-nth car-cons cdr-cons
                        (:e zp) (:e natp) (:e not) (:e binary-+)
                        (:e fn-cbor-ag-car) (:e fn-bpn-nth) (:e equal)
                        (:e car) (:e cdr) fn-cbor-ag-car))))

;; The credit reset (only a :durable answer for the issued, pending
;; checkpoint operation sets the count to zero) is exercised by the N16
;; teeth in tests/acl2/bp-node-counterexamples-tests.lisp; its theorem is
;; open (the default theory takes 36 s, over the per-book budget).
