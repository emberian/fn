; fn: mutable replacement phases for the authoritative FNAN anchor record.
;
; This is intentionally not the immutable journal publisher.  One final name
; is replaced after ACL2 accepts a newer anchor.  The host asks this machine
; for every action and records :replace-issued before entering rename(2), so a
; death after namespace mutation but before its result has a model phase.

(in-package "ACL2")

(defun fn-anchor-rp-start ()
  (declare (xargs :guard t))
  :stage-pending)

(defun fn-anchor-rp-recover-start (presentp)
  (declare (xargs :guard t))
  (if presentp :recover-file :recover-directory))

(defun fn-anchor-rp-action (phase)
  (declare (xargs :guard t))
  (cond ((equal phase :stage-pending) :stage-and-file-barrier)
        ((equal phase :data-durable) :issue-replace)
        ((equal phase :replace-issued) :observe-replace)
        ((equal phase :replace-visible) :directory-barrier)
        ((equal phase :recover-file) :recovery-file-barrier)
        ((equal phase :recover-directory) :recovery-directory-barrier)
        (t :done)))

(defun fn-anchor-rp-resultp (x)
  (declare (xargs :guard t))
  (or (equal x :ok) (equal x :known-fail) (equal x :uncertain)))

(defun fn-anchor-rp-event-value (event)
  (declare (xargs :guard t))
  (mbe :logic (car (cdr event))
       :exec (if (and (consp event) (consp (cdr event)))
                 (car (cdr event))
               nil)))

(defun fn-anchor-rp-step (phase event)
  (declare (xargs :guard t))
  (cond
   ((equal phase :stage-pending)
    (if (and (consp event) (equal (car event) :stage-result)
             (fn-anchor-rp-resultp (fn-anchor-rp-event-value event)))
        (cond ((equal (fn-anchor-rp-event-value event) :ok) :data-durable)
              ((equal (fn-anchor-rp-event-value event) :known-fail) :known-fail)
              (t :fenced))
      phase))
   ((equal phase :data-durable)
    (if (equal event :replace-issued) :replace-issued phase))
   ((equal phase :replace-issued)
    (if (and (consp event) (equal (car event) :replace-result)
             (fn-anchor-rp-resultp (fn-anchor-rp-event-value event)))
        (if (equal (fn-anchor-rp-event-value event) :ok) :replace-visible :fenced)
      phase))
   ((equal phase :replace-visible)
    (if (and (consp event) (equal (car event) :directory-result)
             (fn-anchor-rp-resultp (fn-anchor-rp-event-value event)))
        (if (equal (fn-anchor-rp-event-value event) :ok) :durable :fenced)
      phase))
   ((equal phase :recover-file)
    (if (and (consp event) (equal (car event) :recovery-file-result)
             (fn-anchor-rp-resultp (fn-anchor-rp-event-value event)))
        (if (equal (fn-anchor-rp-event-value event) :ok) :recover-directory :fenced)
      phase))
   ((equal phase :recover-directory)
    (if (and (consp event) (equal (car event) :recovery-directory-result)
             (fn-anchor-rp-resultp (fn-anchor-rp-event-value event)))
        (if (equal (fn-anchor-rp-event-value event) :ok) :recovered :fenced)
      phase))
   (t phase)))

(defun fn-anchor-rp-outcome (phase)
  (declare (xargs :guard t))
  (cond ((equal phase :durable) :durable)
        ((equal phase :recovered) :recovered)
        ((equal phase :known-fail) :fault)
        ((equal phase :fenced) :uncertain)
        (t :pending)))

; KEYSTONES on the exact step the native host calls.  A one-step transition
; can introduce a terminal success only from its final barrier phase and its
; explicit successful barrier observation.
(defthm fn-anchor-rp-step-is-durable-only-after-directory-barrier
  (implies (and (not (equal phase :durable))
                (equal (fn-anchor-rp-step phase event) :durable))
           (and (equal phase :replace-visible)
                (consp event)
                (equal (car event) :directory-result)
                (equal (fn-anchor-rp-event-value event) :ok)))
  :rule-classes nil)

(defthm fn-anchor-rp-step-is-recovered-only-after-directory-barrier
  (implies (and (not (equal phase :recovered))
                (equal (fn-anchor-rp-step phase event) :recovered))
           (and (equal phase :recover-directory)
                (consp event)
                (equal (car event) :recovery-directory-result)
                (equal (fn-anchor-rp-event-value event) :ok)))
  :rule-classes nil)

(defun fn-anchor-rp-trace (phase events)
  (declare (xargs :guard t))
  (if (atom events)
      phase
    (fn-anchor-rp-trace (fn-anchor-rp-step phase (car events))
                        (cdr events))))

(defun fn-anchor-rp-has-directory-okp (events)
  (declare (xargs :guard t))
  (if (atom events)
      nil
    (or (and (consp (car events))
             (equal (car (car events)) :directory-result)
             (equal (fn-anchor-rp-event-value (car events)) :ok))
        (fn-anchor-rp-has-directory-okp (cdr events)))))

; General induction fact: only a directory-result event can introduce the
; durable phase.  Keeping PHASE explicit gives the induction hypothesis the
; strength needed after the stage and replace transitions.
(local
 (defthm fn-anchor-rp-trace-introduces-durable
   (implies (and (not (equal phase :durable))
                 (equal (fn-anchor-rp-trace phase events) :durable))
            (fn-anchor-rp-has-directory-okp events))))

; The host calls fn-anchor-rp-step itself.  Over any finite event trace from
; the publication start, durable is unreachable without an observed final
; directory barrier.  In particular :replace-issued and :replace-visible are
; not accepted outcomes.
(defthm fn-anchor-rp-durable-trace-has-directory-barrier
  (implies (equal (fn-anchor-rp-trace (fn-anchor-rp-start) events) :durable)
           (fn-anchor-rp-has-directory-okp events))
  :hints (("Goal" :use ((:instance fn-anchor-rp-trace-introduces-durable
                                   (phase (fn-anchor-rp-start)))))))

(defun fn-anchor-rp-has-recovery-directory-okp (events)
  (declare (xargs :guard t))
  (if (atom events)
      nil
    (or (and (consp (car events))
             (equal (car (car events)) :recovery-directory-result)
             (equal (fn-anchor-rp-event-value (car events)) :ok))
        (fn-anchor-rp-has-recovery-directory-okp (cdr events)))))

(local
 (defthm fn-anchor-rp-trace-introduces-recovered
   (implies (and (not (equal phase :recovered))
                 (equal (fn-anchor-rp-trace phase events) :recovered))
            (fn-anchor-rp-has-recovery-directory-okp events))))

(defthm fn-anchor-rp-recovered-trace-has-directory-barrier
  (implies (equal (fn-anchor-rp-trace
                   (fn-anchor-rp-recover-start presentp) events)
                  :recovered)
           (fn-anchor-rp-has-recovery-directory-okp events))
  :hints (("Goal" :use ((:instance fn-anchor-rp-trace-introduces-recovered
                                   (phase (fn-anchor-rp-recover-start
                                           presentp)))))))

(in-theory (disable (:d fn-anchor-rp-start)
                    (:d fn-anchor-rp-recover-start)
                    (:d fn-anchor-rp-action)
                    (:d fn-anchor-rp-resultp)
                    (:d fn-anchor-rp-event-value)
                    (:d fn-anchor-rp-step)
                    (:d fn-anchor-rp-outcome)
                    (:d fn-anchor-rp-trace)
                    (:d fn-anchor-rp-has-directory-okp)
                    (:d fn-anchor-rp-has-recovery-directory-okp)))
