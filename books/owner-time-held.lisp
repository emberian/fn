; fn: the held commit's entries over the owner's scheduler value (ruling 19,
; item LOCK-R2-COMMIT-INLINE-LOG-IO; C's host split asked for these).
;
; The host holds only the gate's value S (books/owner-time-model.lisp: OCP,
; the disk, the clock and, while a caller holds a submission behind the
; batch in flight, the HELD slot).  These are the host's calls for the held
; commit; each is books/owner-commit-held.lisp's step or wake on the phase,
; next and held S carries, and each is the time model's own entry when
; nothing is held, so the committer's path is unchanged.
;   fn-otm-held-event      quantum 1's START and quantum 2's :fenced/:failed
;                          and :completed (fn-och-step), (mv ACTION S').
;   fn-otm-held-committer-wake   the committer's wake (fn-och-committer-wake).
;   fn-otm-held-caller-wake      the held caller's wake (fn-och-caller-wake).
(in-package "ACL2")
(include-book "owner-time-model")
(include-book "owner-commit-held")

(defun fn-otm-phase-of (s)
  (declare (xargs :guard t))
  (fn-ocs-phase (fn-ocp-ocs (fn-otm-ocp s))))

(defun fn-otm-next-of (s)
  (declare (xargs :guard t))
  (fn-ocp-open-next (fn-otm-ocp s)))

; The value after a held step: the step's phase and next into OCP, the pick's
; state, the passes, the disk and the clock kept, HELD as the step leaves it.
(defun fn-otm-with-step (s phase next held)
  (declare (xargs :guard t))
  (let* ((ocp (fn-otm-ocp s))
         (ocs (fn-ocp-ocs ocp))
         (ocp2 (fn-ocp-make (fn-ocs-make (fn-ocs-ocm ocs) phase (fn-ocs-lasti ocs))
                            next (fn-ocp-passes ocp))))
    (if held
        (list ocp2 (fn-otm-disk s) (fn-otm-clock s) t)
      (fn-otm-make ocp2 (fn-otm-disk s) (fn-otm-clock s)))))

(defun fn-otm-held-event (s event)
  (declare (xargs :guard t))
  (mv-let (action phase next held)
    (fn-och-step (fn-otm-phase-of s) (fn-otm-next-of s) (fn-otm-held s) event)
    (mv action (fn-otm-with-step s phase next held))))

(defun fn-otm-held-committer-wake (s returned queued w)
  (declare (xargs :guard t))
  (let ((ocp (fn-otm-ocp s)))
    (fn-och-committer-wake (fn-otm-phase-of s) (fn-otm-next-of s) (fn-otm-held s)
                           (if returned t nil) (if queued t nil)
                           (and (fn-ocp-excluded-waits-p w)
                                (<= *fn-ocp-pass-bound* (fn-ocp-passes ocp))))))

(defun fn-otm-held-caller-wake (s returned)
  (declare (xargs :guard t))
  (fn-och-caller-wake (fn-otm-phase-of s) (fn-otm-held s) (if returned t nil)))

; -----------------------------------------------------------------------------
; KEYSTONE.  The lifted entries are owner-commit-held's on S's projection:
; the action, phase, next and held of fn-otm-held-event are fn-och-step's.
(defthm fn-otm-held-event-is-the-held-step
  (let ((r (fn-och-step (fn-otm-phase-of s) (fn-otm-next-of s) (fn-otm-held s) event))
        (s2 (mv-nth 1 (fn-otm-held-event s event))))
    (and (equal (mv-nth 0 (fn-otm-held-event s event)) (mv-nth 0 r))
         (equal (fn-otm-phase-of s2)
                (if (fn-ocs-in-flight-p (mv-nth 1 r)) (mv-nth 1 r) :idle))
         (equal (fn-otm-next-of s2) (if (mv-nth 2 r) t nil))
         (equal (fn-otm-held s2) (if (mv-nth 3 r) t nil))
         (equal (fn-otm-disk s2) (fn-otm-disk s))
         (equal (fn-otm-clock s2) (fn-otm-clock s)))))

; KEYSTONE.  With nothing held and no held event, the held event IS the time
; model's commit event (S0 over the value).
(defthm fn-otm-held-event-without-a-held-batch-is-the-commit-event
  (implies (and (not (fn-otm-held s))
                (not (member-equal event '(:started-held :started-none-held))))
           (equal (fn-otm-held-event s event) (fn-otm-commit-event s event)))
  :hints (("Goal" :in-theory (enable fn-otm-commit-event fn-ocp-commit-event))))

; KEYSTONE.  The wakes over the value: with nothing held the committer's is
; the time model's; with a batch held the committer waits and the caller
; collects exactly when the syncer returned in flight.
(defthm fn-otm-held-wakes
  (and (implies (not (fn-otm-held s))
                (and (equal (fn-otm-held-committer-wake s returned queued w)
                            (fn-otm-committer-wake s returned queued w))
                     (equal (fn-otm-held-caller-wake s returned) :wait)))
       (implies (fn-otm-held s)
                (equal (fn-otm-held-committer-wake s returned queued w) :wait))
       (iff (equal (fn-otm-held-caller-wake s returned) :collect)
            (and (fn-otm-held s) (fn-ocs-in-flight-p (fn-otm-phase-of s)) returned)))
  :hints (("Goal" :in-theory (enable fn-otm-committer-wake fn-ocp-committer-wake))))

;; KEYSTONE.  The gate's other entries keep the held slot: between the
; caller's two quanta nothing but the held events sets or clears it.
(defthm fn-otm-next-keeps-held
  (equal (fn-otm-held (mv-nth 1 (fn-otm-next s w))) (fn-otm-held s))
  :hints (("Goal" :in-theory (union-theories '(fn-otm-next fn-otm-of-keep)
                                             (theory 'minimal-theory)))))

(defthm fn-otm-observe-keeps-held
  (equal (fn-otm-held (fn-otm-observe s class hold-ms wait-ms)) (fn-otm-held s))
  :hints (("Goal" :in-theory (union-theories '(fn-otm-observe fn-otm-of-keep)
                                             (theory 'minimal-theory)))))

(defthm fn-otm-disk-event-keeps-held
  (equal (fn-otm-held (mv-nth 1 (fn-otm-disk-event s kind reading arg))) (fn-otm-held s))
  :hints (("Goal" :in-theory (union-theories '(fn-otm-disk-event fn-otm-of-keep)
                                             (theory 'minimal-theory)))))

(defthm fn-otm-commit-event-keeps-held
  (equal (fn-otm-held (mv-nth 1 (fn-otm-commit-event s event))) (fn-otm-held s))
  :hints (("Goal" :in-theory (union-theories '(fn-otm-commit-event fn-otm-of-keep)
                                             (theory 'minimal-theory)))))

; The committer's START over the value (C6's gap 1): refused while a batch is
; held or in flight; the committer's path when nothing is held is unchanged.
(defun fn-otm-committer-may-start (s)
  (declare (xargs :guard t))
  (fn-och-committer-may-start (fn-otm-phase-of s) (fn-otm-held s)))

(defthm fn-otm-committer-may-start-is-the-held-rule
  (and (implies (fn-otm-held s) (not (fn-otm-committer-may-start s)))
       (implies (not (fn-otm-held s))
                (iff (fn-otm-committer-may-start s)
                     (not (fn-ocs-in-flight-p (fn-otm-phase-of s)))))))


; KEYSTONE.  The held caller's answer over the host's own quantum-2 sequence
; (host/native/owner.lisp fnn-owner-held-complete): the batch's word
; (:fenced or :failed) through fn-otm-held-event, then :completed, or
; :completed-stopping when that step was :complete and the owner is stopping,
; then fn-och-caller-answer of the action.  For the batch quantum 1 left held
; at :staged it is the held outcome of S7 (fn-och-held-caller-answer): the
; submission is taken exactly when the job ran every phase and the owner is
; not stopping.
(defthm fn-otm-held-quantum-2-answers-the-held-outcome
  (implies (and (fn-otm-held s)
                (equal (fn-otm-phase-of s) :staged)
                (member-equal word '(:fenced :failed)))
           (mv-let (step s2) (fn-otm-held-event s word)
             (equal (fn-och-caller-answer
                     (mv-nth 0 (fn-otm-held-event
                                s2 (if (and (equal step :complete) stopping)
                                       :completed-stopping
                                     :completed))))
                    (fn-och-held-outcome (if (equal word :fenced) :done :uncertain)
                                         stopping))))
  :hints (("Goal"
           :in-theory (e/d (fn-oqw-outcome-of-final)
                           (fn-otm-held-event fn-otm-phase-of fn-otm-next-of fn-otm-held
                            fn-otm-with-step fn-otm-disk fn-otm-clock))
           :use ((:instance fn-otm-held-event-is-the-held-step (event word))
                 (:instance fn-otm-held-event-is-the-held-step
                            (s (mv-nth 1 (fn-otm-held-event s word)))
                            (event :completed))
                 (:instance fn-otm-held-event-is-the-held-step
                            (s (mv-nth 1 (fn-otm-held-event s word)))
                            (event :completed-stopping))))))
