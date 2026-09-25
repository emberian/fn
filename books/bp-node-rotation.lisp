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
                            fn-bpnr-checkpointp
                            ;; fn-bpn-nth-is-nth-on-true-lists applies to the
                            ;; checkpoint's own conses; these rules only
                            ;; backchain its true-listp hypothesis through the
                            ;; held rows' recognizers (4.3 s -> 0.1 s).
                            fn-bpf-fragment-listp-is-a-true-list
                            fn-cp-idp-true-listp
                            fn-nntp-response-text-true-listp
                            fn-bpn-report-bounded-append-suffix
                            fn-bpf-fragment-listp-car-and-cdr
                            fn-bpf-fragmentp-fields)))))

(defthm fn-bpnr-recover-without-checkpoint-is-family-recover
  (equal (fn-bpnr-recover-auto-event st base-records sequence-ready rows
                                     '(:none))
         (fn-bpnf-family-recover-auto-event st base-records sequence-ready
                                            rows))
  :hints (("Goal" :in-theory (disable fn-bpnf-family-replay-rows
                                      fn-bpf-fragment-listp-is-a-true-list
                                      fn-cp-idp-true-listp
                                      fn-nntp-response-text-true-listp
                                      fn-bpn-report-bounded-append-suffix
                                      fn-bpf-fragment-listp-car-and-cdr
                                      fn-bpf-fragmentp-fields))))

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
(defthm fn-bpnr-recover-from-projection-equals-full-recover
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
; N16-F1.  The lemma above is about the projection ck1, whose operation
; frontier is the replay's: a reopen from it takes the rotating epoch again,
; and the first new operation is the rotation's own id.  The rotation
; publishes fn-bpnr-rotation-checkpoint instead (fn-bpnp-rotate-step's
; effect, written by host/native/bp-service.lisp fnn-bps-publish-generation):
; the frontier is (E . 0), E the epoch the recovery event names (field 1),
; the epoch of the state that rotates.

; Rows whose first record comes after PRIOR: what replay from a checkpoint
; admits first.  Rows written after the reopen are in a later epoch.
(defun fn-bpnr-rows-start-after (rows prior)
  (declare (xargs :guard t))
  (if (atom rows)
      t
    (let ((record (fn-bpnf-family-replay-row-record (car rows))))
      (fn-bpnf-replay-pair-afterp (fn-bpn-nth 1 record) (fn-bpn-nth 2 record)
                                  prior))))

(defthm fn-bpnr-replay-aux-prior-irrelevant
  (implies (and (consp rows)
                (fn-bpnr-rows-start-after rows p)
                (fn-bpnr-rows-start-after rows q))
           (equal (fn-bpnf-family-replay-rows-aux rows base held handoffs p
                                                  next-arrival)
                  (fn-bpnf-family-replay-rows-aux rows base held handoffs q
                                                  next-arrival)))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :expand ((fn-bpnf-family-replay-rows-aux rows base held handoffs p
                                                    next-arrival)
                    (fn-bpnf-family-replay-rows-aux rows base held handoffs q
                                                    next-arrival))
           :in-theory (union-theories '(fn-bpnr-rows-start-after)
                                      (theory 'minimal-theory)))))

(defthm fn-bpnr-rotation-checkpoint-is-a-checkpoint
  (implies (and (fn-bpnr-checkpointp ck) (natp e))
           (fn-bpnr-checkpointp (fn-bpnr-rotation-checkpoint ck e)))
  :hints (("Goal" :do-not-induct t
           :in-theory (union-theories
                       '(fn-bpnr-checkpointp fn-bpnr-rotation-checkpoint
                         fn-bpnr-checkpoint fn-bpnr-checkpoint-generation
                         fn-bpnr-checkpoint-held fn-bpnr-checkpoint-handoffs
                         fn-bpnr-checkpoint-next-arrival fn-bpnr-checkpoint-covered
                         fn-bpn-nth-is-nth-on-true-lists
                         nth len true-listp car-cons cdr-cons
                         (:e natp) (:e zp) (:e binary-+) (:e unary--) (:e len)
                         (:e nth) (:e equal) (:e <))
                       (theory 'minimal-theory)))))

(defthm fn-bpnr-rotation-checkpoint-fields
  (and (equal (fn-bpnr-checkpoint-held (fn-bpnr-rotation-checkpoint ck e))
              (fn-bpnr-checkpoint-held ck))
       (equal (fn-bpnr-checkpoint-handoffs (fn-bpnr-rotation-checkpoint ck e))
              (fn-bpnr-checkpoint-handoffs ck))
       (equal (fn-bpnr-checkpoint-prior (fn-bpnr-rotation-checkpoint ck e))
              (cons e 0))
       (equal (fn-bpnr-checkpoint-next-arrival (fn-bpnr-rotation-checkpoint ck e))
              (fn-bpnr-checkpoint-next-arrival ck)))
  :hints (("Goal" :in-theory (union-theories
                              '(fn-bpnr-rotation-checkpoint fn-bpnr-checkpoint
                                fn-bpnr-checkpoint-held fn-bpnr-checkpoint-handoffs
                                fn-bpnr-checkpoint-prior
                                fn-bpnr-checkpoint-next-arrival fn-bpn-nth fn-cbor-ag-car
                                car-cons cdr-cons (:e zp) (:e natp) (:e not)
                                (:e binary-+))
                              (theory 'minimal-theory)))))

(defthm fn-bpnr-replay-from-rotation-checkpoint
  (implies (and (fn-bpnr-checkpointp ck) (natp e))
           (equal (fn-bpnr-replay-from (fn-bpnr-rotation-checkpoint ck e)
                                       rows base)
                  (fn-bpnf-family-replay-rows-aux
                   rows base (fn-bpnr-checkpoint-held ck)
                   (fn-bpnr-checkpoint-handoffs ck) (cons e 0)
                   (fn-bpnr-checkpoint-next-arrival ck))))
  :hints (("Goal" :do-not-induct t
           :in-theory (union-theories
                       '(fn-bpnr-replay-from
                         fn-bpnr-rotation-checkpoint-is-a-checkpoint
                         fn-bpnr-rotation-checkpoint-fields)
                       (theory 'minimal-theory)))))

(defthm fn-bpnr-replay-aux-of-nil
  (equal (fn-bpnf-family-replay-rows-aux nil base held handoffs prior
                                         next-arrival)
         (list :ready held handoffs prior next-arrival))
  :hints (("Goal" :expand ((fn-bpnf-family-replay-rows-aux
                            nil base held handoffs prior next-arrival))
           :in-theory (theory 'minimal-theory))))

(defthm fn-bpnr-replay-from-rotation-checkpoint-nil
  (implies (and (fn-bpnr-checkpointp ck) (natp e))
           (equal (fn-bpnr-replay-from (fn-bpnr-rotation-checkpoint ck e)
                                       nil base)
                  (update-nth 3 (cons e 0) (fn-bpnr-replay-from ck nil base))))
  :hints (("Goal" :do-not-induct t
           :in-theory (union-theories
                       '(fn-bpnr-replay-from-rotation-checkpoint
                         fn-bpnr-replay-from fn-bpnr-replay-aux-of-nil
                         update-nth car-cons cdr-cons (:e zp) (:e natp)
                         (:e binary-+) (:e unary--))
                       (theory 'minimal-theory)))))

(defthm fn-bpnr-rows-start-after-earlier-prior
  (implies (and (fn-bpnr-rows-start-after rows (cons e 0))
                (natp e)
                (or (null p)
                    (and (consp p) (natp (car p)) (< (car p) e))))
           (fn-bpnr-rows-start-after rows p))
  :hints (("Goal" :in-theory (union-theories
                              '(fn-bpnr-rows-start-after
                                fn-bpnf-replay-pair-afterp car-cons cdr-cons)
                              (theory 'ground-zero)))))

(defthm fn-bpnr-replay-from-rotation-checkpoint-later-rows
  (implies (and (fn-bpnr-checkpointp ck) (natp e) (consp rows)
                (fn-bpnr-rows-start-after rows (cons e 0))
                (fn-bpnr-rows-start-after rows (fn-bpnr-checkpoint-prior ck)))
           (equal (fn-bpnr-replay-from (fn-bpnr-rotation-checkpoint ck e)
                                       rows base)
                  (fn-bpnr-replay-from ck rows base)))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-bpnr-replay-aux-prior-irrelevant
                            (held (fn-bpnr-checkpoint-held ck))
                            (handoffs (fn-bpnr-checkpoint-handoffs ck))
                            (p (cons e 0))
                            (q (fn-bpnr-checkpoint-prior ck))
                            (next-arrival (fn-bpnr-checkpoint-next-arrival ck))))
           :in-theory (union-theories
                       '(fn-bpnr-replay-from-rotation-checkpoint
                         fn-bpnr-replay-from)
                       (theory 'minimal-theory)))))

(defthm fn-bpnr-reopen-from-rotation-checkpoint
  (implies (and (fn-bpnr-checkpointp ck1) (natp e)
                (fn-bpnr-checkpoint-octets (fn-bpnr-rotation-checkpoint ck1 e)
                                           budget))
           (equal (fn-bpnr-recover-auto-event
                   st base-records sequence-ready suffix
                   (fn-bpnr-selection-plan
                    t (fn-bpnr-checkpoint-octets
                       (fn-bpnr-rotation-checkpoint ck1 e) budget)
                    budget))
                  (fn-bpnr-recover-auto-event
                   st base-records sequence-ready suffix
                   (list :selected (fn-bpnr-rotation-checkpoint ck1 e)))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-bpnr-selection-plan-of-octets
                            (ck (fn-bpnr-rotation-checkpoint ck1 e))))
           :in-theory (theory 'minimal-theory))))

(defthm fn-bpnr-reopen-after-rotation-names-a-later-epoch
  (implies (and (fn-bpnr-checkpointp ck1) (natp e)
                (<= (nfix (fn-bpnf-epoch st)) e))
           (equal (fn-bpnr-recover-auto-event
                   st base-records sequence-ready nil
                   (list :selected (fn-bpnr-rotation-checkpoint ck1 e)))
                  (list :recover-fnbs (1+ e) base-records sequence-ready
                        (update-nth 3 (cons e 0)
                                    (fn-bpnr-replay-from ck1 nil
                                                         (fn-bpnf-base st)))
                        0)))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (union-theories
                       '(fn-bpnr-recover-auto-event fn-bpnr-plan-checkpoint
                         fn-bpnr-replay-from-rotation-checkpoint-nil
                         fn-bpnr-replay-from fn-bpnr-replay-aux-of-nil
                         fn-cbor-ag-car fn-bpn-nth update-nth max nfix
                         car-cons cdr-cons (:e len) (:e zp) (:e natp) (:e equal)
                         (:e binary-+) (:e unary--) (:e not) (:e fn-bpn-nth)
                         (:e fn-cbor-ag-car))
                       (theory 'ground-zero)))))

(defthm fn-bpnr-recover-event-epoch-bounds
  (let ((e (fn-bpn-nth 1 (fn-bpnr-recover-auto-event
                          st base-records sequence-ready rows plan)))
        (prior (fn-bpn-nth 3 (fn-bpnr-replay-from (fn-bpnr-plan-checkpoint plan)
                                                  rows (fn-bpnf-base st)))))
    (implies (not (equal (car plan) :damaged))
             (and (natp e)
                  (<= (nfix (fn-bpnf-epoch st)) e)
                  (implies (and (consp prior) (natp (car prior)))
                           (< (car prior) e)))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (union-theories
                       '(fn-bpnr-recover-auto-event fn-cbor-ag-car fn-bpn-nth
                         max nfix car-cons cdr-cons (:e zp) (:e natp)
                         (:e binary-+) (:e unary--) (:e not) (:e equal))
                       (theory 'ground-zero)))))

(defthm fn-bpnr-checkpoint-of-replay-prior
  (equal (fn-bpnr-checkpoint-prior (fn-bpnr-checkpoint-of-replay g replay c))
         (fn-bpn-nth 3 replay))
  :hints (("Goal" :in-theory (union-theories
                              '(fn-bpnr-checkpoint-prior fn-bpnr-checkpoint-of-replay
                                fn-bpnr-checkpoint fn-bpn-nth fn-cbor-ag-car
                                car-cons cdr-cons (:e zp) (:e natp) (:e not)
                                (:e binary-+))
                              (theory 'minimal-theory)))))

(defthm fn-bpnr-recover-event-replay
  (implies (not (equal (car plan) :damaged))
           (and (equal (fn-bpn-nth 4 (fn-bpnr-recover-auto-event
                                      st base-records sequence-ready rows plan))
                       (fn-bpnr-replay-from (fn-bpnr-plan-checkpoint plan)
                                            rows (fn-bpnf-base st)))
                (equal (fn-bpnr-recover-auto-event
                        st base-records sequence-ready rows plan)
                       (list :recover-fnbs
                             (fn-bpn-nth 1 (fn-bpnr-recover-auto-event
                                            st base-records sequence-ready rows
                                            plan))
                             base-records sequence-ready
                             (fn-bpnr-replay-from (fn-bpnr-plan-checkpoint plan)
                                                  rows (fn-bpnf-base st))
                             (len rows)))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (union-theories
                       '(fn-bpnr-recover-auto-event fn-cbor-ag-car fn-bpn-nth
                         car-cons cdr-cons (:e zp) (:e natp) (:e not)
                         (:e binary-+) (:e unary--) (:e equal))
                       (theory 'minimal-theory)))))

(defthm fn-bpnr-recover-event-shape
  (implies (not (equal (car plan) :damaged))
           (equal (fn-bpnr-recover-auto-event st base-records sequence-ready
                                              rows plan)
                  (let* ((replay (fn-bpnr-replay-from
                                  (fn-bpnr-plan-checkpoint plan) rows
                                  (fn-bpnf-base st)))
                         (prior (fn-bpn-nth 3 replay)))
                    (list :recover-fnbs
                          (1+ (max (nfix (fn-bpnf-epoch st))
                                   (nfix (and (consp prior) (car prior)))))
                          base-records sequence-ready replay (len rows)))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (union-theories
                       '(fn-bpnr-recover-auto-event fn-cbor-ag-car)
                       (theory 'minimal-theory)))))

(defthm fn-bpnr-reopen-over-later-rows
  (implies (and (true-listp rows0)
                (equal (car (fn-bpnr-replay-from ck0 rows0 base)) :ready)
                (equal ck1 (fn-bpnr-checkpoint-of-replay
                            generation (fn-bpnr-replay-from ck0 rows0 base)
                            covered))
                (fn-bpnr-checkpointp ck1)
                (natp e)
                (or (null (fn-bpnr-checkpoint-prior ck1))
                    (< (car (fn-bpnr-checkpoint-prior ck1)) e))
                (consp suffix)
                (fn-bpnr-rows-start-after suffix (cons e 0)))
           (equal (fn-bpnr-replay-from (fn-bpnr-rotation-checkpoint ck1 e)
                                       suffix base)
                  (fn-bpnr-replay-from ck0 (append rows0 suffix) base)))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-bpnr-replay-from-checkpoint-chains)
                 (:instance fn-bpnr-rows-start-after-earlier-prior
                            (rows suffix) (p (fn-bpnr-checkpoint-prior ck1)))
                 (:instance fn-bpnr-replay-from-rotation-checkpoint-later-rows
                            (ck ck1) (rows suffix)))
           :in-theory (union-theories
                       '(fn-bpnr-checkpointp fn-bpnr-checkpoint-prior
                         fn-bpn-nth-is-nth-on-true-lists (:e natp))
                       (theory 'ground-zero)))))

(defthm fn-bpnr-plan-checkpoint-of-selected
  (equal (fn-bpnr-plan-checkpoint (list :selected ck)) ck)
  :hints (("Goal" :in-theory '(fn-bpnr-plan-checkpoint fn-cbor-ag-car fn-bpn-nth
                               car-cons cdr-cons (:e zp) (:e natp) (:e not)
                               (:e binary-+) (:e equal)))))

(defthm fn-bpnr-reopen-event-over-later-rows
  (implies (and (not (equal (car plan0) :damaged))
                (true-listp rows0)
                (equal (car (fn-bpnr-replay-from (fn-bpnr-plan-checkpoint plan0)
                                                 rows0 (fn-bpnf-base st)))
                       :ready)
                (equal ck1 (fn-bpnr-checkpoint-of-replay
                            generation
                            (fn-bpnr-replay-from (fn-bpnr-plan-checkpoint plan0)
                                                 rows0 (fn-bpnf-base st))
                            covered))
                (fn-bpnr-checkpointp ck1)
                (natp e)
                (or (null (fn-bpnr-checkpoint-prior ck1))
                    (< (car (fn-bpnr-checkpoint-prior ck1)) e))
                (consp suffix)
                (fn-bpnr-rows-start-after suffix (cons e 0)))
           (equal (fn-bpnr-recover-auto-event
                   st base-records sequence-ready suffix
                   (list :selected (fn-bpnr-rotation-checkpoint ck1 e)))
                  (update-nth 5 (len suffix)
                              (fn-bpnr-recover-auto-event
                               st base-records sequence-ready
                               (append rows0 suffix) plan0))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-bpnr-recover-event-shape
                            (rows (append rows0 suffix)) (plan plan0))
                 (:instance fn-bpnr-recover-event-shape
                            (rows suffix)
                            (plan (list :selected
                                        (fn-bpnr-rotation-checkpoint ck1 e))))
                 (:instance fn-bpnr-reopen-over-later-rows
                            (ck0 (fn-bpnr-plan-checkpoint plan0))
                            (base (fn-bpnf-base st))))
           :in-theory (union-theories
                       '(fn-bpnr-plan-checkpoint-of-selected
                         update-nth car-cons cdr-cons (:e zp) (:e natp) (:e not)
                         (:e binary-+) (:e unary--) (:e equal) (:e car))
                       (theory 'minimal-theory)))))

(defthm fn-bpnr-checkpoint-prior-shape
  (implies (fn-bpnr-checkpointp ck)
           (or (null (fn-bpnr-checkpoint-prior ck))
               (and (consp (fn-bpnr-checkpoint-prior ck))
                    (natp (car (fn-bpnr-checkpoint-prior ck))))))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories
                              '(fn-bpnr-checkpointp fn-bpnr-checkpoint-prior
                                fn-bpn-nth-is-nth-on-true-lists (:e natp))
                              (theory 'ground-zero)))))

(defthm fn-bpnr-projection-prior-precedes-event-epoch
  (implies (and (not (equal (car plan0) :damaged))
                (equal ck1 (fn-bpnr-checkpoint-of-replay
                            generation
                            (fn-bpnr-replay-from (fn-bpnr-plan-checkpoint plan0)
                                                 rows0 (fn-bpnf-base st))
                            covered))
                (fn-bpnr-checkpointp ck1))
           (or (null (fn-bpnr-checkpoint-prior ck1))
               (< (car (fn-bpnr-checkpoint-prior ck1))
                  (fn-bpn-nth 1 (fn-bpnr-recover-auto-event
                                 st base-records sequence-ready rows0 plan0)))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-bpnr-recover-event-epoch-bounds
                            (rows rows0) (plan plan0))
                 (:instance fn-bpnr-checkpoint-prior-shape (ck ck1)))
           :in-theory (union-theories
                       '(fn-bpnr-checkpoint-of-replay-prior)
                       (theory 'minimal-theory)))))

(defthm fn-bpnr-reopen-event-right-after-rotation
  (implies (and (true-listp rows0)
                (equal (car (fn-bpnr-replay-from (fn-bpnr-plan-checkpoint plan0)
                                                 rows0 (fn-bpnf-base st)))
                       :ready)
                (equal ck1 (fn-bpnr-checkpoint-of-replay
                            generation
                            (fn-bpnr-replay-from (fn-bpnr-plan-checkpoint plan0)
                                                 rows0 (fn-bpnf-base st))
                            covered))
                (fn-bpnr-checkpointp ck1)
                (natp e)
                (<= (nfix (fn-bpnf-epoch st)) e))
           (equal (fn-bpnr-recover-auto-event
                   st base-records sequence-ready nil
                   (list :selected (fn-bpnr-rotation-checkpoint ck1 e)))
                  (list :recover-fnbs (1+ e) base-records sequence-ready
                        (update-nth 3 (cons e 0)
                                    (fn-bpnr-replay-from
                                     (fn-bpnr-plan-checkpoint plan0) rows0
                                     (fn-bpnf-base st)))
                        0)))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-bpnr-replay-from-checkpoint-chains
                            (ck0 (fn-bpnr-plan-checkpoint plan0))
                            (base (fn-bpnf-base st)) (suffix nil))
                 (:instance fn-bpnr-reopen-after-rotation-names-a-later-epoch))
           :in-theory (union-theories '(append-to-nil)
                                      (theory 'minimal-theory)))))

;; KEYSTONE (N16-F1 repaired).  Same authority, rows and projection ck1 as
;; fn-bpnr-recover-from-projection-equals-full-recover, E the epoch field of
;; the recovery event over them, and the file of the checkpoint the rotation
;; publishes, (fn-bpnr-rotation-checkpoint ck1 E).  (1) The reopen right
;; after the rotation (the new generation holds no row) names epoch E + 1,
;; so the first operation after it, (E+1 . 0), is not the rotation's
;; (E . 0); its replay is the old one with the operation frontier (E . 0)
;; and its row count is 0.  (2) Over later rows that start after (E . 0)
;; (the rows written after the reopen), recovery equals recovery over plan0
;; and the concatenated rows with the row count set to the later rows'
;; count.
(defthm fn-bpnr-recover-from-checkpoint-equals-full-recover
  (let* ((full (fn-bpnr-recover-auto-event st base-records sequence-ready
                                           rows0 plan0))
         (e (fn-bpn-nth 1 full))
         (rck (fn-bpnr-rotation-checkpoint ck1 e))
         (reopen (fn-bpnr-recover-auto-event
                  st base-records sequence-ready suffix
                  (fn-bpnr-selection-plan
                   t (fn-bpnr-checkpoint-octets rck budget) budget))))
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
                  (fn-bpnr-checkpointp ck1)
                  (fn-bpnr-checkpoint-octets rck budget)
                  (fn-bpnr-rows-start-after suffix (cons e 0)))
             (and (implies (null suffix)
                           (equal reopen
                                  (list :recover-fnbs (1+ e) base-records
                                        sequence-ready
                                        (update-nth 3 (cons e 0)
                                                    (fn-bpn-nth 4 full))
                                        0)))
                  (implies (consp suffix)
                           (equal reopen
                                  (update-nth 5 (len suffix)
                                              (fn-bpnr-recover-auto-event
                                               st base-records sequence-ready
                                               (append rows0 suffix)
                                               plan0)))))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-bpnr-recover-event-epoch-bounds
                            (rows rows0) (plan plan0))
                 (:instance fn-bpnr-recover-event-replay
                            (rows rows0) (plan plan0))
                 (:instance fn-bpnr-projection-prior-precedes-event-epoch)
                 (:instance fn-bpnr-reopen-from-rotation-checkpoint
                            (e (fn-bpn-nth 1 (fn-bpnr-recover-auto-event
                                              st base-records sequence-ready
                                              rows0 plan0))))
                 (:instance fn-bpnr-reopen-event-right-after-rotation
                            (e (fn-bpn-nth 1 (fn-bpnr-recover-auto-event
                                              st base-records sequence-ready
                                              rows0 plan0))))
                 (:instance fn-bpnr-reopen-event-over-later-rows
                            (e (fn-bpn-nth 1 (fn-bpnr-recover-auto-event
                                              st base-records sequence-ready
                                              rows0 plan0)))))
           :in-theory (theory 'minimal-theory))))

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
  (let ((e (fn-bpn-nth 1 (fn-bpnr-recover-auto-event
                          st base-records sequence-ready rows0 plan0))))
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
                  (fn-bpnr-checkpointp ck1)
                  (equal new (fn-bpnr-checkpoint-octets
                              (fn-bpnr-rotation-checkpoint ck1 e) budget))
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
                                    (list :recover-fnbs (1+ e) base-records
                                          sequence-ready
                                          (update-nth
                                           3 (cons e 0)
                                           (fn-bpn-nth
                                            4 (fn-bpnr-recover-auto-event
                                               st base-records sequence-ready
                                               rows0 plan0)))
                                          0)))))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-bpnr-recover-from-checkpoint-equals-full-recover
                            (suffix nil)))
           :in-theory (union-theories
                       '(fn-bpnr-crash-visible fn-bpnr-rows-start-after
                         (:e fn-bpnr-replace-issuedp) (:e consp) (:e atom))
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
;; projection, from a quiescent recovered state; the checkpoint the effect
;; carries (the one the host writes) is that projection with the rotation's
;; own operation id as its frontier (N16-F1), and its file exists.
(defthm fn-bpnp-rotate-step-proposes-only-own-projection
  (implies (equal (car (car (fn-bpnf-answer-effects
                             (fn-bpnp-rotate-step st generation ck))))
                  :persist-checkpoint)
           (and (fn-bpnr-checkpoint-of-statep ck st generation)
                (fn-bpnp-rotation-quiescentp st)
                (equal (fn-bpn-nth 4 (car (fn-bpnf-answer-effects
                                           (fn-bpnp-rotate-step st generation ck))))
                       (fn-bpnr-rotation-checkpoint ck (fn-bpnf-epoch st)))
                (fn-bpnr-checkpoint-octets
                 (fn-bpnr-rotation-checkpoint ck (fn-bpnf-epoch st))
                 (fn-bpnr-depth-budget
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
