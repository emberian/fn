; Observed-file recovery model for the FNBS creation-sequence frontier.
;
; This model follows host/native/bp.lisp:132-170.  It calls the same ACL2 host
; wrappers used at lines 148-165, and it models only observations obtainable
; from the final pathname.  No rename-completed or directory-barrier bit is
; remembered across a restart.  `confirmed' is a ghost frontier justified by
; the parent-directory and sequence-directory fsync assumptions; it is not a
; second counter used by the native host.

(in-package "ACL2")
(include-book "bp-node-records")
(local (include-book "arithmetic/top" :dir :system))

; Observations correspond to the OCTETS/PRESENTP inputs handed to
; fn-bpn-host-sequence-recover.  FRESHP is supplied by the namespace event.
(defun fn-bpn-sf-observationp (x)
  (declare (xargs :guard t))
  (or (equal x :absent) (equal x :malformed)
      (and (true-listp x) (equal (len x) 2) (equal (car x) :valid)
           (fn-bpn-sequence-frontierp (cadr x)))))

(defun fn-bpn-sf-validp (x)
  (declare (xargs :guard t))
  (and (true-listp x) (equal (len x) 2) (equal (car x) :valid)
       (fn-bpn-sequence-frontierp (cadr x))))

(defun fn-bpn-sf-observed-frontier (x)
  (declare (xargs :guard (fn-bpn-sf-validp x)))
  (cadr x))

(defthm fn-bpn-sf-valid-recordp
  (implies (fn-bpn-sf-validp observation)
           (fn-bpn-sequence-recordp
            (fn-bpn-sequence-record (fn-bpn-sf-observed-frontier observation))))
  :hints (("Goal" :in-theory (enable fn-bpn-sf-validp
                                      fn-bpn-sf-observed-frontier
                                      fn-bpn-sequence-record
                                      fn-bpn-sequence-recordp))))

; The model delegates to the exact core functions selected by the thin host
; wrappers in host/bp-node-host.lisp:88-118.  The named bridge theorems below
; keep the modeled subject fn-bpn-sequence-{recover,reserve}, rather than a
; sibling allocator.
(defun fn-bpn-sf-host-recover (observation freshp)
  (declare (xargs :guard (fn-bpn-sf-observationp observation)
                  :guard-hints
                  (("Goal" :use
                    ((:instance fn-bpn-sequence-record-frame-octet-listp
                                (record (fn-bpn-sequence-record
                                         (fn-bpn-sf-observed-frontier
                                          observation))))
                     (:instance fn-bpn-sf-valid-recordp))))))
  (cond ((equal observation :absent)
         (fn-bpn-sequence-recover nil nil freshp))
        ((equal observation :malformed)
         (fn-bpn-sequence-recover '(0) t freshp))
        (t (fn-bpn-sequence-recover
            (fn-bpn-sequence-record-frame
             (fn-bpn-sequence-record (fn-bpn-sf-observed-frontier observation)))
            t freshp))))

(defun fn-bpn-sf-host-reserve (frontier)
  (declare (xargs :guard (fn-bpn-sequence-frontierp frontier)))
  (fn-bpn-sequence-reserve frontier))

; (tag root-parent sequence-parent fresh observed ready frontier confirmed
;      pending returned-rev fenced staged)
(defun fn-bpn-sf-state (root sequence fresh observed ready frontier confirmed
                         pending returned fenced staged)
  (declare (xargs :guard t))
  (list :bpn-sequence-fidelity root sequence fresh observed ready frontier
        confirmed pending returned fenced staged))

(defun fn-bpn-sf-nth (n s)
  (declare (xargs :guard t))
  (if (and (natp n) (true-listp s)) (nth n s) nil))
(defun fn-bpn-sf-rootp (s) (declare (xargs :guard t)) (fn-bpn-sf-nth 1 s))
(defun fn-bpn-sf-sequencep (s) (declare (xargs :guard t)) (fn-bpn-sf-nth 2 s))
(defun fn-bpn-sf-freshp (s) (declare (xargs :guard t)) (fn-bpn-sf-nth 3 s))
(defun fn-bpn-sf-observed (s) (declare (xargs :guard t)) (fn-bpn-sf-nth 4 s))
(defun fn-bpn-sf-readyp (s) (declare (xargs :guard t)) (fn-bpn-sf-nth 5 s))
(defun fn-bpn-sf-frontier (s) (declare (xargs :guard t)) (fn-bpn-sf-nth 6 s))
(defun fn-bpn-sf-confirmed (s) (declare (xargs :guard t)) (fn-bpn-sf-nth 7 s))
(defun fn-bpn-sf-pending (s) (declare (xargs :guard t)) (fn-bpn-sf-nth 8 s))
(defun fn-bpn-sf-returned (s) (declare (xargs :guard t)) (fn-bpn-sf-nth 9 s))
(defun fn-bpn-sf-fencedp (s) (declare (xargs :guard t)) (fn-bpn-sf-nth 10 s))
(defun fn-bpn-sf-stagedp (s) (declare (xargs :guard t)) (fn-bpn-sf-nth 11 s))

(defun fn-bpn-sf-statep (s)
  (declare (xargs :guard t))
  (and (true-listp s) (equal (len s) 12)
       (equal (car s) :bpn-sequence-fidelity)
       (booleanp (fn-bpn-sf-rootp s)) (booleanp (fn-bpn-sf-sequencep s))
       (booleanp (fn-bpn-sf-freshp s))
       (fn-bpn-sf-observationp (fn-bpn-sf-observed s))
       (booleanp (fn-bpn-sf-readyp s))
       (fn-bpn-sequence-frontierp (fn-bpn-sf-frontier s))
       (fn-bpn-sequence-frontierp (fn-bpn-sf-confirmed s))
       (or (null (fn-bpn-sf-pending s))
           (fn-bpn-sequence-frontierp (fn-bpn-sf-pending s)))
       (true-listp (fn-bpn-sf-returned s))
       (booleanp (fn-bpn-sf-fencedp s)) (booleanp (fn-bpn-sf-stagedp s))))

(defun fn-bpn-sf-initial ()
  (declare (xargs :guard t))
  (fn-bpn-sf-state nil nil nil :absent nil 0 0 nil nil nil nil))

(defun fn-bpn-sf-returned-belowp (xs n)
  (declare (xargs :guard t))
  (if (not (rationalp n)) nil
    (if (consp xs) (and (natp (car xs)) (< (car xs) n)
                        (fn-bpn-sf-returned-belowp (cdr xs) n))
      (null xs))))

; PENDING is the value extracted by the host's reservation accessor.  This
; invariant contains exactly the facts needed for return nonreuse; state shape
; is proved separately so the transition proof does not repeatedly expand the
; twelve-field recognizer.
(defun fn-bpn-sf-nonreusep (s)
  (declare (xargs :guard (fn-bpn-sf-statep s)))
  (and (no-duplicatesp-equal (fn-bpn-sf-returned s))
       (fn-bpn-sf-returned-belowp (fn-bpn-sf-returned s)
                                   (fn-bpn-sf-confirmed s))
       (implies (and (fn-bpn-sf-readyp s) (null (fn-bpn-sf-pending s)))
                (<= (nfix (fn-bpn-sf-confirmed s))
                    (nfix (fn-bpn-sf-frontier s))))
       (implies (fn-bpn-sf-pending s)
                (and (fn-bpn-sf-readyp s)
                     (fn-bpn-sf-stagedp s)
                     (<= (nfix (fn-bpn-sf-confirmed s))
                         (+ 1 (nfix (fn-bpn-sf-pending s))))
                     (not (member-equal (fn-bpn-sf-pending s)
                                        (fn-bpn-sf-returned s)))))))

(defun fn-bpn-sf-safep (s)
  (declare (xargs :guard t))
  (and (fn-bpn-sf-statep s) (fn-bpn-sf-nonreusep s)))

; Physical correspondence, stated on the actual recovery result: whenever
; recovery is willing to continue, the recovered frontier cannot precede the
; last directory-barrier-confirmed frontier.  Thus a missing old namespace or
; malformed record is admissible precisely because core fences it; a freshly
; absent namespace after a confirmed return would recover zero and violate
; this predicate.  This is the parent/directory-fsync assumption with no claim
; about raw device behavior hidden in the model.
(defun fn-bpn-sf-observation-admissiblep (s observation)
  (declare (xargs :guard (and (fn-bpn-sf-statep s)
                              (fn-bpn-sf-observationp observation))))
  (let ((answer (fn-bpn-sf-host-recover observation
                                          (fn-bpn-sf-freshp s))))
    (or (not (fn-bpn-sequence-recovery-readyp answer))
        (<= (fn-bpn-sf-confirmed s)
            (nfix (cadr answer))))))

(defun fn-bpn-sf-recover-eventp (event)
  (declare (xargs :guard t))
  (and (true-listp event) (equal (len event) 2)
       (equal (car event) :recover)
       (fn-bpn-sf-observationp (cadr event))))

(defun fn-bpn-sf-event-admissiblep (s event)
  (declare (xargs :guard (fn-bpn-sf-statep s)))
  (if (fn-bpn-sf-recover-eventp event)
      (fn-bpn-sf-observation-admissiblep s (cadr event))
    t))

(defun fn-bpn-sf-crash (s)
  (declare (xargs :guard (fn-bpn-sf-statep s)))
  (fn-bpn-sf-state nil nil nil (fn-bpn-sf-observed s) nil
                   (fn-bpn-sf-confirmed s) (fn-bpn-sf-confirmed s)
                   nil (fn-bpn-sf-returned s) nil nil))

(defun fn-bpn-sf-recover-observation (s observation)
  (declare (xargs :guard (and (fn-bpn-sf-statep s)
                              (fn-bpn-sf-observationp observation))))
  (if (and (fn-bpn-sf-rootp s) (fn-bpn-sf-sequencep s))
      (let ((answer (fn-bpn-sf-host-recover observation
                                             (fn-bpn-sf-freshp s))))
        (if (fn-bpn-sequence-recovery-readyp answer)
            (fn-bpn-sf-state t t (fn-bpn-sf-freshp s) observation t
                             (fn-bpn-sequence-recovery-frontier answer)
                             (fn-bpn-sf-confirmed s) nil
                             (fn-bpn-sf-returned s) nil nil)
          (fn-bpn-sf-state t t (fn-bpn-sf-freshp s) observation nil
                           (fn-bpn-sf-confirmed s) (fn-bpn-sf-confirmed s)
                           nil (fn-bpn-sf-returned s) t nil)))
    s))

; EVENT transcribes fnn-bp-reserve-sequence.  A staged residue has no recovery
; meaning.  :RETURN is native line 165 after the sequence-directory barrier.
(defun fn-bpn-sf-step (s event)
  (declare (xargs :guard (fn-bpn-sf-statep s)))
  (cond
   ((or (equal event :process-death) (equal event :power-loss))
    (fn-bpn-sf-crash s))
   ((fn-bpn-sf-fencedp s) s)
   ((equal event :root-parent-barrier)
    (fn-bpn-sf-state t (fn-bpn-sf-sequencep s) (fn-bpn-sf-freshp s)
                     (fn-bpn-sf-observed s) (fn-bpn-sf-readyp s)
                     (fn-bpn-sf-frontier s) (fn-bpn-sf-confirmed s)
                     (fn-bpn-sf-pending s) (fn-bpn-sf-returned s) nil
                     (fn-bpn-sf-stagedp s)))
   ((or (equal event :sequence-parent-new)
        (equal event :sequence-parent-old))
    (if (fn-bpn-sf-rootp s)
        (fn-bpn-sf-state t t (equal event :sequence-parent-new)
                         (fn-bpn-sf-observed s) (fn-bpn-sf-readyp s)
                         (fn-bpn-sf-frontier s) (fn-bpn-sf-confirmed s)
                         (fn-bpn-sf-pending s) (fn-bpn-sf-returned s) nil
                         (fn-bpn-sf-stagedp s))
      s))
   ((fn-bpn-sf-recover-eventp event)
    (fn-bpn-sf-recover-observation s (cadr event)))
   ((equal event :stage-durable)
    (if (and (fn-bpn-sf-rootp s) (fn-bpn-sf-sequencep s)
             (fn-bpn-sf-readyp s) (null (fn-bpn-sf-pending s))
             (< (fn-bpn-sf-frontier s) *fn-bpc-max-uint*)
             (fn-bpn-sequence-reservationp
              (fn-bpn-sf-host-reserve (fn-bpn-sf-frontier s))))
        (fn-bpn-sf-state t t (fn-bpn-sf-freshp s)
                         (fn-bpn-sf-observed s) t (fn-bpn-sf-frontier s)
                         (fn-bpn-sf-confirmed s)
                         (fn-bpn-sequence-reservation-sequence
                          (fn-bpn-sf-host-reserve (fn-bpn-sf-frontier s)))
                         (fn-bpn-sf-returned s) nil t)
      s))
   ((equal event :frontier-name-published)
    (if (and (fn-bpn-sf-stagedp s) (fn-bpn-sf-pending s)
             (< (fn-bpn-sf-pending s) *fn-bpc-max-uint*))
        (fn-bpn-sf-state (fn-bpn-sf-rootp s) (fn-bpn-sf-sequencep s)
                         (fn-bpn-sf-freshp s)
                         (list :valid (+ 1 (fn-bpn-sf-pending s))) t
                         (fn-bpn-sf-frontier s) (fn-bpn-sf-confirmed s)
                         (fn-bpn-sf-pending s) (fn-bpn-sf-returned s) nil t)
      s))
   ((equal event :sequence-directory-barrier)
    (if (and (fn-bpn-sf-stagedp s) (fn-bpn-sf-pending s)
             (fn-bpn-sf-validp (fn-bpn-sf-observed s))
             (equal (fn-bpn-sf-observed-frontier (fn-bpn-sf-observed s))
                    (+ 1 (fn-bpn-sf-pending s))))
        (fn-bpn-sf-state (fn-bpn-sf-rootp s) (fn-bpn-sf-sequencep s)
                         (fn-bpn-sf-freshp s) (fn-bpn-sf-observed s) t
                         (fn-bpn-sf-frontier s)
                         (fn-bpn-sf-observed-frontier (fn-bpn-sf-observed s))
                         (fn-bpn-sf-pending s) (fn-bpn-sf-returned s) nil t)
      s))
   ((equal event :return)
    (if (and (fn-bpn-sf-pending s)
             (equal (fn-bpn-sf-confirmed s) (+ 1 (fn-bpn-sf-pending s))))
        (fn-bpn-sf-state (fn-bpn-sf-rootp s) (fn-bpn-sf-sequencep s)
                         (fn-bpn-sf-freshp s) (fn-bpn-sf-observed s) nil
                         (fn-bpn-sf-confirmed s) (fn-bpn-sf-confirmed s) nil
                         (cons (fn-bpn-sf-pending s)
                               (fn-bpn-sf-returned s))
                         nil nil)
      s))
   (t s)))

(defun fn-bpn-sf-trace (s events)
  (declare (xargs :guard (and (fn-bpn-sf-statep s) (true-listp events))
                  :measure (len events)
                  :verify-guards nil))
  (if (consp events)
      (fn-bpn-sf-trace (fn-bpn-sf-step s (car events)) (cdr events))
    s))

(defun fn-bpn-sf-trace-admissiblep (s events)
  (declare (xargs :guard (and (fn-bpn-sf-statep s) (true-listp events))
                  :measure (len events)
                  :verify-guards nil))
  (if (consp events)
      (and (fn-bpn-sf-event-admissiblep s (car events))
           (fn-bpn-sf-trace-admissiblep
            (fn-bpn-sf-step s (car events)) (cdr events)))
    t))

; Named bridges from this model to both called host wrappers and core subjects.
(defthm fn-bpn-sf-host-reserve-is-core-reserve
  (implies (fn-bpn-sequence-frontierp frontier)
           (equal (fn-bpn-sf-host-reserve frontier)
                  (fn-bpn-sequence-reserve frontier)))
  :hints (("Goal" :in-theory (enable fn-bpn-sf-host-reserve))))

(defthm fn-bpn-sf-host-reserve-result
  (implies (and (fn-bpn-sequence-frontierp frontier)
                (< frontier *fn-bpc-max-uint*))
           (and (fn-bpn-sequence-reservationp
                 (fn-bpn-sf-host-reserve frontier))
                (equal (fn-bpn-sequence-reservation-sequence
                        (fn-bpn-sf-host-reserve frontier))
                       frontier)))
  :hints (("Goal" :use
           ((:instance fn-bpn-sequence-reserve-advances-frontier))
           :in-theory (enable fn-bpn-sf-host-reserve))))

(defthm fn-bpn-sf-host-recover-is-core-recover
  (implies (fn-bpn-sf-observationp observation)
           (equal (fn-bpn-sf-host-recover observation freshp)
                  (cond ((equal observation :absent)
                         (fn-bpn-sequence-recover nil nil freshp))
                        ((equal observation :malformed)
                         (fn-bpn-sequence-recover '(0) t freshp))
                        (t (fn-bpn-sequence-recover
                            (fn-bpn-sequence-record-frame
                             (fn-bpn-sequence-record
                              (fn-bpn-sf-observed-frontier observation)))
                            t freshp)))))
  :hints (("Goal" :in-theory (enable fn-bpn-sf-host-recover))))

(defthm fn-bpn-sf-returned-below-not-member
  (implies (and (fn-bpn-sf-returned-belowp xs bound)
                (natp n) (<= bound n))
           (not (member-equal n xs)))
  :hints (("Goal" :induct (fn-bpn-sf-returned-belowp xs bound)
           :in-theory (enable fn-bpn-sf-returned-belowp))))

(defthm fn-bpn-sf-returned-below-weaken
  (implies (and (fn-bpn-sf-returned-belowp xs n)
                (natp n) (natp m) (<= n m))
           (fn-bpn-sf-returned-belowp xs m))
  :hints (("Goal" :induct (fn-bpn-sf-returned-belowp xs n)
           :in-theory (enable fn-bpn-sf-returned-belowp))))

(defthm fn-bpn-sf-returned-below-cons
  (implies (and (fn-bpn-sf-returned-belowp xs (+ 1 n))
                (natp n) (not (member-equal n xs)))
           (fn-bpn-sf-returned-belowp (cons n xs) (+ 1 n)))
  :hints (("Goal" :in-theory (enable fn-bpn-sf-returned-belowp))))

(defthm fn-bpn-sf-step-preserves-statep
  (implies (fn-bpn-sf-statep s)
           (fn-bpn-sf-statep (fn-bpn-sf-step s event)))
  :hints (("Goal" :in-theory (enable fn-bpn-sf-step fn-bpn-sf-statep
                                      fn-bpn-sf-crash
                                      fn-bpn-sf-recover-observation
                                      fn-bpn-sf-host-reserve
                                      fn-bpn-sequence-recovery-readyp
                                      fn-bpn-sequence-reservationp))))

(local
 (defthm fn-bpn-sf-crash-preserves-nonreuse
   (implies (and (fn-bpn-sf-statep s) (fn-bpn-sf-nonreusep s))
            (and (fn-bpn-sf-nonreusep
                  (fn-bpn-sf-step s :process-death))
                 (fn-bpn-sf-nonreusep
                  (fn-bpn-sf-step s :power-loss))))
   :hints (("Goal" :in-theory
            (enable fn-bpn-sf-step fn-bpn-sf-crash
                    fn-bpn-sf-nonreusep fn-bpn-sf-statep)))))

(local
 (defthm fn-bpn-sf-parent-steps-preserve-nonreuse
   (implies (and (fn-bpn-sf-statep s) (fn-bpn-sf-nonreusep s))
            (and (fn-bpn-sf-nonreusep
                  (fn-bpn-sf-step s :root-parent-barrier))
                 (fn-bpn-sf-nonreusep
                  (fn-bpn-sf-step s :sequence-parent-new))
                 (fn-bpn-sf-nonreusep
                  (fn-bpn-sf-step s :sequence-parent-old))))
   :hints (("Goal" :in-theory
            (enable fn-bpn-sf-step fn-bpn-sf-nonreusep
                    fn-bpn-sf-statep)))))

(local
 (defthm fn-bpn-sf-recover-step-preserves-nonreuse
   (implies (and (fn-bpn-sf-statep s)
                 (fn-bpn-sf-nonreusep s)
                 (fn-bpn-sf-observationp observation)
                 (fn-bpn-sf-observation-admissiblep s observation))
            (fn-bpn-sf-nonreusep
             (fn-bpn-sf-step s (list :recover observation))))
   :hints (("Goal" :in-theory
            (enable fn-bpn-sf-step fn-bpn-sf-recover-eventp
                    fn-bpn-sf-recover-observation fn-bpn-sf-nonreusep
                    fn-bpn-sf-observation-admissiblep
                    fn-bpn-sequence-recovery-readyp fn-bpn-sf-statep)))))

(local
 (defthm fn-bpn-sf-stage-step-preserves-nonreuse
   (implies (and (fn-bpn-sf-statep s) (fn-bpn-sf-nonreusep s))
            (fn-bpn-sf-nonreusep (fn-bpn-sf-step s :stage-durable)))
   :hints (("Goal" :use
            ((:instance fn-bpn-sf-host-reserve-result
                        (frontier (fn-bpn-sf-frontier s)))
             (:instance fn-bpn-sf-returned-below-not-member
                        (xs (fn-bpn-sf-returned s))
                        (bound (fn-bpn-sf-confirmed s))
                        (n (fn-bpn-sf-frontier s))))
            :in-theory
            (enable fn-bpn-sf-step fn-bpn-sf-nonreusep fn-bpn-sf-statep
                    fn-bpn-sf-host-reserve
                    fn-bpn-sequence-reservationp)))))

(local
 (defthm fn-bpn-sf-name-step-preserves-nonreuse
   (implies (and (fn-bpn-sf-statep s) (fn-bpn-sf-nonreusep s))
            (fn-bpn-sf-nonreusep
             (fn-bpn-sf-step s :frontier-name-published)))
   :hints (("Goal" :in-theory
            (enable fn-bpn-sf-step fn-bpn-sf-nonreusep
                    fn-bpn-sf-statep)))))

(local
 (defthm fn-bpn-sf-directory-step-preserves-nonreuse
   (implies (and (fn-bpn-sf-statep s) (fn-bpn-sf-nonreusep s))
            (fn-bpn-sf-nonreusep
             (fn-bpn-sf-step s :sequence-directory-barrier)))
   :hints (("Goal" :use
            ((:instance fn-bpn-sf-returned-below-weaken
                        (xs (fn-bpn-sf-returned s))
                        (n (fn-bpn-sf-confirmed s))
                        (m (+ 1 (fn-bpn-sf-pending s)))))
            :in-theory
            (enable fn-bpn-sf-step fn-bpn-sf-nonreusep
                    fn-bpn-sf-statep fn-bpn-sf-returned-belowp)))))

(local
 (defthm fn-bpn-sf-return-step-preserves-nonreuse
   (implies (and (fn-bpn-sf-statep s) (fn-bpn-sf-nonreusep s))
            (fn-bpn-sf-nonreusep (fn-bpn-sf-step s :return)))
   :hints (("Goal" :in-theory
            (enable fn-bpn-sf-step fn-bpn-sf-nonreusep
                    fn-bpn-sf-statep fn-bpn-sf-returned-belowp)))))

(defthm fn-bpn-sf-step-preserves-nonreuse
  (implies (and (fn-bpn-sf-statep s)
                (fn-bpn-sf-nonreusep s)
                (fn-bpn-sf-event-admissiblep s event))
           (fn-bpn-sf-nonreusep (fn-bpn-sf-step s event)))
  :hints (("Goal"
           :cases ((equal event :process-death)
                   (equal event :power-loss)
                   (equal event :root-parent-barrier)
                   (equal event :sequence-parent-new)
                   (equal event :sequence-parent-old)
                   (fn-bpn-sf-recover-eventp event)
                   (equal event :stage-durable)
                   (equal event :frontier-name-published)
                   (equal event :sequence-directory-barrier)
                   (equal event :return))
           :in-theory (enable fn-bpn-sf-step
                              fn-bpn-sf-event-admissiblep
                              fn-bpn-sf-recover-eventp))))

(defthm fn-bpn-sf-step-preserves-safety
  (implies (and (fn-bpn-sf-safep s)
                (fn-bpn-sf-event-admissiblep s event))
           (fn-bpn-sf-safep (fn-bpn-sf-step s event)))
  :hints (("Goal" :use (fn-bpn-sf-step-preserves-statep
                         fn-bpn-sf-step-preserves-nonreuse)
           :in-theory '(fn-bpn-sf-safep))))

(defthm fn-bpn-sf-trace-preserves-statep
  (implies (fn-bpn-sf-statep s)
           (fn-bpn-sf-statep (fn-bpn-sf-trace s events)))
  :hints (("Goal" :induct (fn-bpn-sf-trace s events)
           :in-theory (e/d (fn-bpn-sf-trace)
                           (fn-bpn-sf-statep fn-bpn-sf-step)))))

(verify-guards fn-bpn-sf-trace
  :hints (("Goal" :use ((:instance fn-bpn-sf-step-preserves-statep
                                    (event (car events))))
           :in-theory (disable fn-bpn-sf-statep fn-bpn-sf-step))))

(verify-guards fn-bpn-sf-trace-admissiblep
  :hints (("Goal" :use ((:instance fn-bpn-sf-step-preserves-statep
                                    (event (car events))))
           :in-theory (disable fn-bpn-sf-statep fn-bpn-sf-step))))

(defthm fn-bpn-sf-trace-preserves-safety
  (implies (and (fn-bpn-sf-safep s)
                (fn-bpn-sf-trace-admissiblep s events))
           (fn-bpn-sf-safep (fn-bpn-sf-trace s events)))
  :hints (("Goal" :induct (fn-bpn-sf-trace-admissiblep s events)
           :in-theory (e/d (fn-bpn-sf-trace
                             fn-bpn-sf-trace-admissiblep)
                           (fn-bpn-sf-safep fn-bpn-sf-step)))))

(defthm fn-bpn-sf-initial-safe
  (fn-bpn-sf-safep (fn-bpn-sf-initial))
  :hints (("Goal" :in-theory (enable fn-bpn-sf-initial fn-bpn-sf-safep
                                      fn-bpn-sf-statep
                                      fn-bpn-sf-returned-belowp))))

(defthm fn-bpn-sf-safety-implies-returned-unique
  (implies (fn-bpn-sf-safep s)
           (no-duplicatesp-equal (fn-bpn-sf-returned s)))
  :hints (("Goal" :in-theory '(fn-bpn-sf-safep
                                fn-bpn-sf-nonreusep))))

; Keystone: every finite physically admissible trace of the native allocator
; returns pairwise distinct creation sequences.
(defthm fn-bpn-sf-admissible-trace-returned-sequences-unique
  (implies (fn-bpn-sf-trace-admissiblep (fn-bpn-sf-initial) events)
           (no-duplicatesp-equal
            (fn-bpn-sf-returned
             (fn-bpn-sf-trace (fn-bpn-sf-initial) events))))
  :hints (("Goal" :use
           (fn-bpn-sf-initial-safe
            (:instance fn-bpn-sf-trace-preserves-safety
                       (s (fn-bpn-sf-initial)))
            (:instance fn-bpn-sf-safety-implies-returned-unique
                       (s (fn-bpn-sf-trace
                           (fn-bpn-sf-initial) events))))
           :in-theory nil)))

(deftheory fn-bpn-sequence-fidelity-vocabulary
  '((:d fn-bpn-sf-state) (:d fn-bpn-sf-statep)
    (:d fn-bpn-sf-nonreusep) (:d fn-bpn-sf-safep)
    (:d fn-bpn-sf-crash) (:d fn-bpn-sf-recover-observation)
    (:d fn-bpn-sf-step) (:d fn-bpn-sf-trace)
    (:d fn-bpn-sf-trace-admissiblep)))

(in-theory (disable fn-bpn-sequence-fidelity-vocabulary))
