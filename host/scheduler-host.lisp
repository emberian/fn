; Program-mode bridge: the scheduler's decisions reach the host.
;
; Every decision below is `books/scheduler''s.  This file marshals a global and
; nothing else: it does not choose a work, does not test admissibility, does
; not decide expiry and does not build a decision record.  `fn-sched-tick-step'
; is the modeled composition of the three entry points the host calls in
; sequence (`fn-sched-selection', the journal's durable attempt, and
; `fn-sched-take'); `fn-sched-tick-step-is-select-drive-take' in
; books/scheduler-invariants.lisp is the equation between them.
(in-package "ACL2")
(include-book "../books/scheduler")
(include-book "../books/records") ; fn-record-string-octets

(defun fn-sched-host-install (config next-tx state)
 (declare (xargs :stobjs state :mode :program))
 (if (not (fn-sched-configp config))
     (value :fault)
   (let ((state (f-put-global 'fn-sched-state
                              (fn-sched-initial-state config next-tx) state)))
    (value :ready))))

(defun fn-sched-host-get (state)
 (declare (xargs :stobjs state :mode :program))
 (value (f-get-global 'fn-sched-state state)))

(defun fn-sched-host-generation (state)
 (declare (xargs :stobjs state :mode :program))
 (value (fn-sched-generation (f-get-global 'fn-sched-state state))))

(defun fn-sched-host-next-tx (state)
 (declare (xargs :stobjs state :mode :program))
 (value (fn-sched-next-tx (f-get-global 'fn-sched-state state))))

(defun fn-sched-host-retries (state)
 (declare (xargs :stobjs state :mode :program))
 (value (fn-sched-retries (f-get-global 'fn-sched-state state))))

; One non-tick observation.  ACL2 refuses a malformed event by leaving the
; state alone, and the host learns nothing it did not already know.
(defun fn-sched-host-observe (event state)
 (declare (xargs :stobjs state :mode :program))
 (if (not (fn-sched-eventp event))
     (value :fault)
   (let* ((wf (f-get-global 'fn-workflow-state state))
          (r (fn-sched-step (f-get-global 'fn-sched-state state) wf event)))
    (let ((state (f-put-global 'fn-sched-state (fn-sched-result-ss r) state)))
     (value :ready)))))

; Admissibility and selection.  `:none' is a decision too: no contact is open,
; the retry budget is spent, or nothing eligible is queued.
(defun fn-sched-host-admissiblep (state)
 (declare (xargs :stobjs state :mode :program))
 (value (if (fn-sched-admissiblep (f-get-global 'fn-sched-state state)) t nil)))

(defun fn-sched-host-selection (state)
 (declare (xargs :stobjs state :mode :program))
 (let ((selected (fn-sched-selection (f-get-global 'fn-sched-state state)
                                     (f-get-global 'fn-workflow-state state))))
  (value (if (consp selected) (fn-sched-item-work-id selected) :none))))

(defun fn-sched-host-reason (state)
 (declare (xargs :stobjs state :mode :program))
 (value (fn-sched-selection-reason (f-get-global 'fn-sched-state state)
                                   (f-get-global 'fn-workflow-state state))))

(defun fn-sched-host-passes (work-id state)
 (declare (xargs :stobjs state :mode :program))
 (let ((item (fn-sched-find work-id
                            (fn-sched-queue (f-get-global 'fn-sched-state state)))))
  (value (if (consp item) (fn-sched-item-passes item) :none))))

; The durable decision record for the work the scheduler just selected, as the
; protected octets of one FNSC frame.  The host appends the A-CRYPTO trailer
; over exactly these octets, as it does for FNST, FNWF, FNRJ and FNBI.
(defun fn-sched-host-decision-octets (work-id attempt-id state)
 (declare (xargs :stobjs state :mode :program))
 (let* ((ss (f-get-global 'fn-sched-state state))
        (wf (f-get-global 'fn-workflow-state state))
        (item (fn-sched-find work-id (fn-sched-queue ss)))
        (contact (fn-sched-open-contact ss)))
  (if (or (not (consp item)) (not (fn-sched-contactp contact)))
      (value :bad)
    (value (fn-sched-decision-protected
            (fn-sched-decision
             (fn-sched-generation ss) (nfix (fn-sched-tick ss))
             ; `:text' fields are octet lists (`fn-frame-textp',
             ; books/frame-fields.lisp).  The state keeps the peer and the ids
             ; as strings; this is the one place the representation is
             ; converted, and the codec is not touched.
             (fn-record-string-octets (fn-sched-contact-peer contact))
             (fn-record-string-octets work-id)
             (fn-record-string-octets attempt-id)
             (nfix (fn-bp-work-next-generation
                    (fn-bp-find-work work-id (fn-bp-state-works wf))))
             (fn-sched-selection-reason ss wf)
             (nfix (fn-sched-item-passes item))))))))

; Commit one contact tick.  The host calls this only after the journal's
; durable attempt reported that ACL2 granted the submit permission
; (`fn-workflow-take-submit'); a refused attempt is committed as a pass, which
; charges no retry.
(defun fn-sched-host-commit (work-id attempt-id state)
 (declare (xargs :stobjs state :mode :program))
 (let* ((ss (f-get-global 'fn-sched-state state))
        (wf (f-get-global 'fn-workflow-state state))
        (item (fn-sched-find work-id (fn-sched-queue ss))))
  (if (not (consp item))
      (value :fault)
    (let* ((decisions (fn-sched-record-decision ss wf item attempt-id))
           (next (fn-sched-with-decisions (fn-sched-take ss wf item) decisions))
           (state (f-put-global 'fn-sched-state next state)))
     (value :ready)))))

(defun fn-sched-host-pass (state)
 (declare (xargs :stobjs state :mode :program))
 (let* ((ss (f-get-global 'fn-sched-state state))
        (wf (f-get-global 'fn-workflow-state state))
        (next (if (fn-sched-admissiblep ss)
                  (fn-sched-pass-over ss wf)
                (fn-sched-with-tick ss)))
        (state (f-put-global 'fn-sched-state next state)))
  (value :ready)))

(defun fn-sched-host-decision-count (state)
 (declare (xargs :stobjs state :mode :program))
 (value (len (fn-sched-decisions (f-get-global 'fn-sched-state state)))))

(defun fn-sched-host-queue-ids (state)
 (declare (xargs :stobjs state :mode :program))
 (value (fn-sched-queue (f-get-global 'fn-sched-state state))))
