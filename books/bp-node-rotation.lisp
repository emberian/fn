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
; accumulator is replaying their concatenation.

(local
 (defthm fn-bpnr-car-append
   (implies (consp p) (equal (car (append p s)) (car p)))))
(local
 (defthm fn-bpnr-cdr-append
   (implies (consp p) (equal (cdr (append p s)) (append (cdr p) s)))))

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
  :hints (("Goal" :induct (fn-bpnf-family-replay-rows-aux
                           prefix base held handoffs prior next-arrival)
           :expand ((:free (s) (fn-bpnf-family-replay-rows-aux
                                (append prefix s) base held handoffs prior
                                next-arrival))
                    (fn-bpnf-family-replay-rows-aux
                     prefix base held handoffs prior next-arrival))
           :in-theory (disable fn-bpnf-family-replay-row-record
                               fn-bpnf-stored-record-name
                               fn-bpnf-replay-pair-afterp
                               fn-bpnf-receive-decision
                               fn-bpah-apply-delivery fn-bpnf-family-apply-at
                               fn-bpn-report-apply-delete fn-bpnp-dispatch-apply
                               fn-bpnp-attempt-apply fn-bpnp-forward-result-apply
                               fn-bpnf-conflict-apply fn-bpnf-state
                               fn-bpnf-held-octets fn-bpn-machine-state-max-jobs
                               fn-bpn-machine-state-max-octets))))
