; Explicit persistence cuts for the FNBS creation-sequence frontier.
;
; `bp-node-records' decides the successor record.  This book models the host
; cuts between that decision and bundle authoring: journal-root parent barrier,
; sequence-namespace parent barrier, staged file durability, final-name
; publication, sequence-directory barrier, and authoring.  It deliberately
; makes no statement about a device unless its directory barriers hold.

(in-package "ACL2")
(include-book "bp-node-records")
(local (include-book "arithmetic/top" :dir :system))

; (tag root-parent sequence-parent stage name directory frontier pending
;      authored-rev fenced)
(defun fn-bpn-sp-state (root sequence stage name directory frontier pending
                         authored fenced)
  (declare (xargs :guard t))
  (list :bpn-sequence-persistence root sequence stage name directory frontier
        pending authored fenced))

(defun fn-bpn-sp-rootp (s) (declare (xargs :guard t))
  (if (true-listp s) (nth 1 s) nil))
(defun fn-bpn-sp-sequencep (s) (declare (xargs :guard t))
  (if (true-listp s) (nth 2 s) nil))
(defun fn-bpn-sp-stagep (s) (declare (xargs :guard t))
  (if (true-listp s) (nth 3 s) nil))
(defun fn-bpn-sp-namep (s) (declare (xargs :guard t))
  (if (true-listp s) (nth 4 s) nil))
(defun fn-bpn-sp-directoryp (s) (declare (xargs :guard t))
  (if (true-listp s) (nth 5 s) nil))
(defun fn-bpn-sp-frontier (s) (declare (xargs :guard t))
  (if (true-listp s) (nth 6 s) nil))
(defun fn-bpn-sp-pending (s) (declare (xargs :guard t))
  (if (true-listp s) (nth 7 s) nil))
(defun fn-bpn-sp-authored (s) (declare (xargs :guard t))
  (if (true-listp s) (nth 8 s) nil))
(defun fn-bpn-sp-fencedp (s) (declare (xargs :guard t))
  (if (true-listp s) (nth 9 s) nil))

(defun fn-bpn-sp-statep (s)
  (declare (xargs :guard t))
  (and (true-listp s) (equal (len s) 10)
       (equal (car s) :bpn-sequence-persistence)
       (booleanp (fn-bpn-sp-rootp s))
       (booleanp (fn-bpn-sp-sequencep s))
       (booleanp (fn-bpn-sp-stagep s))
       (booleanp (fn-bpn-sp-namep s))
       (booleanp (fn-bpn-sp-directoryp s))
       (fn-bpn-sequence-frontierp (fn-bpn-sp-frontier s))
       (or (null (fn-bpn-sp-pending s))
           (fn-bpn-sequence-frontierp (fn-bpn-sp-pending s)))
       (true-listp (fn-bpn-sp-authored s))
       (booleanp (fn-bpn-sp-fencedp s))))

(defun fn-bpn-sp-initial ()
  (declare (xargs :guard t))
  (fn-bpn-sp-state nil nil nil nil nil 0 nil nil nil))

(defun fn-bpn-sp-authors-belowp (xs bound)
  (declare (xargs :guard t))
  (if (not (rationalp bound)) nil
    (if (consp xs)
        (and (natp (car xs)) (< (car xs) bound)
             (fn-bpn-sp-authors-belowp (cdr xs) bound))
      (null xs))))

(defun fn-bpn-sp-safep (s)
  (declare (xargs :guard t))
  (and (fn-bpn-sp-statep s)
       (no-duplicatesp-equal (fn-bpn-sp-authored s))
       (fn-bpn-sp-authors-belowp (fn-bpn-sp-authored s)
                                  (fn-bpn-sp-frontier s))
       (or (null (fn-bpn-sp-pending s))
           (and (fn-bpn-sp-authors-belowp (fn-bpn-sp-authored s)
                                           (fn-bpn-sp-pending s))
                ;; The successor written at the final directory barrier must
                ;; still be in the FNBS u64/time domain.
                (< (fn-bpn-sp-pending s) *fn-bpc-max-uint*)))
       (implies (fn-bpn-sp-directoryp s)
                (and (fn-bpn-sp-namep s) (fn-bpn-sp-stagep s)
                     (fn-bpn-sequence-frontierp (fn-bpn-sp-pending s))
                     (equal (fn-bpn-sp-frontier s)
                            (+ 1 (fn-bpn-sp-pending s)))))))

(defun fn-bpn-sp-effect (s)
  (declare (xargs :guard t))
  (if (and (fn-bpn-sp-stagep s) (fn-bpn-sp-namep s)
           (fn-bpn-sp-directoryp s) (fn-bpn-sp-pending s))
      (list :authored (fn-bpn-sp-pending s))
    nil))

; A process restart and a power loss have different operational causes.  Both
; are deliberately projected to only the cuts the host has durably reported:
; an unbarriered staged/name state fences; a directory-barriered successor is
; retained but any pending bundle is abandoned.  The latter projection relies
; on the filesystem's directory-fsync persistence assumption.
(defun fn-bpn-sp-recover (s)
  (declare (xargs :guard (fn-bpn-sp-statep s)))
  (cond
   ((fn-bpn-sp-directoryp s)
    (fn-bpn-sp-state nil nil nil nil nil (fn-bpn-sp-frontier s) nil
                     (fn-bpn-sp-authored s) nil))
   ((or (fn-bpn-sp-stagep s) (fn-bpn-sp-namep s))
    (fn-bpn-sp-state nil nil nil nil nil (fn-bpn-sp-frontier s) nil
                     (fn-bpn-sp-authored s) t))
   (t
    (fn-bpn-sp-state nil nil nil nil nil (fn-bpn-sp-frontier s) nil
                     (fn-bpn-sp-authored s) nil))))

(defun fn-bpn-sp-process-restart (s)
  (declare (xargs :guard (fn-bpn-sp-statep s)))
  (fn-bpn-sp-recover s))

(defun fn-bpn-sp-power-loss (s)
  (declare (xargs :guard (fn-bpn-sp-statep s)))
  (fn-bpn-sp-recover s))

; EVENT names a host observation/cut.  Failed barriers, malformed recovery
; and a crash before the directory barrier cannot create an author effect.
(defun fn-bpn-sp-step (s event)
  (declare (xargs :guard (fn-bpn-sp-statep s)))
  (cond
   ((equal event :process-restart) (fn-bpn-sp-process-restart s))
   ((equal event :power-loss) (fn-bpn-sp-power-loss s))
   ((fn-bpn-sp-fencedp s) s)
   ((equal event :root-parent-barrier)
    (fn-bpn-sp-state t (fn-bpn-sp-sequencep s) (fn-bpn-sp-stagep s)
                     (fn-bpn-sp-namep s) (fn-bpn-sp-directoryp s)
                     (fn-bpn-sp-frontier s) (fn-bpn-sp-pending s)
                     (fn-bpn-sp-authored s) nil))
   ((equal event :sequence-parent-barrier)
    (if (fn-bpn-sp-rootp s)
        (fn-bpn-sp-state t t (fn-bpn-sp-stagep s) (fn-bpn-sp-namep s)
                         (fn-bpn-sp-directoryp s) (fn-bpn-sp-frontier s)
                         (fn-bpn-sp-pending s) (fn-bpn-sp-authored s) nil)
      s))
   ((equal event :stage-durable)
    (if (and (fn-bpn-sp-rootp s) (fn-bpn-sp-sequencep s)
             (not (fn-bpn-sp-stagep s)) (not (fn-bpn-sp-pending s))
             (< (fn-bpn-sp-frontier s) *fn-bpc-max-uint*))
        (fn-bpn-sp-state t t t nil nil (fn-bpn-sp-frontier s)
                         (fn-bpn-sp-frontier s) (fn-bpn-sp-authored s) nil)
      s))
   ((equal event :frontier-name-published)
    (if (fn-bpn-sp-stagep s)
        (fn-bpn-sp-state (fn-bpn-sp-rootp s) (fn-bpn-sp-sequencep s) t t nil
                         (fn-bpn-sp-frontier s) (fn-bpn-sp-pending s)
                         (fn-bpn-sp-authored s) nil)
      s))
   ((equal event :sequence-directory-barrier)
    (if (and (fn-bpn-sp-stagep s) (fn-bpn-sp-namep s)
             (fn-bpn-sp-pending s)
             (< (fn-bpn-sp-pending s) *fn-bpc-max-uint*))
        (fn-bpn-sp-state (fn-bpn-sp-rootp s) (fn-bpn-sp-sequencep s) t t t
                         (+ 1 (fn-bpn-sp-pending s)) (fn-bpn-sp-pending s)
                         (fn-bpn-sp-authored s) nil)
      s))
   ((equal event :author)
    (if (and (fn-bpn-sp-rootp s) (fn-bpn-sp-sequencep s)
             (fn-bpn-sp-directoryp s) (fn-bpn-sp-pending s))
        (fn-bpn-sp-state t t nil nil nil (fn-bpn-sp-frontier s) nil
                         (cons (fn-bpn-sp-pending s) (fn-bpn-sp-authored s)) nil)
      s))
   (t s)))

(defun fn-bpn-sp-trace (s events)
  (declare (xargs :guard (and (fn-bpn-sp-statep s) (true-listp events))
                  :verify-guards nil))
  (if (consp events)
      (fn-bpn-sp-trace (fn-bpn-sp-step s (car events)) (cdr events))
    s))

(defthm fn-bpn-sp-authors-below-not-member
  (implies (fn-bpn-sp-authors-belowp xs bound)
           (not (member-equal bound xs)))
  :hints (("Goal" :induct (fn-bpn-sp-authors-belowp xs bound)
           :in-theory (enable fn-bpn-sp-authors-belowp))))

(defthm fn-bpn-sp-authors-below-successor
  (implies (and (fn-bpn-sp-authors-belowp xs n) (natp n))
           (fn-bpn-sp-authors-belowp (cons n xs) (+ 1 n)))
  :hints (("Goal" :induct (fn-bpn-sp-authors-belowp xs n)
           :in-theory (enable fn-bpn-sp-authors-belowp))))

(defthm fn-bpn-sp-authors-below-weaken
  (implies (and (fn-bpn-sp-authors-belowp xs n) (natp n))
           (fn-bpn-sp-authors-belowp xs (+ 1 n)))
  :hints (("Goal" :induct (fn-bpn-sp-authors-belowp xs n)
           :in-theory (enable fn-bpn-sp-authors-belowp))))

(defthm fn-bpn-sp-step-preserves-safety
  (implies (fn-bpn-sp-safep s)
           (fn-bpn-sp-safep (fn-bpn-sp-step s event)))
  :hints (("Goal" :use ((:instance fn-bpn-sp-authors-below-weaken
                                     (xs (fn-bpn-sp-authored s))
                                     (n (fn-bpn-sp-pending s))))
           :in-theory (enable fn-bpn-sp-step fn-bpn-sp-safep
                                      fn-bpn-sp-statep fn-bpn-sp-effect
                                      fn-bpn-sp-process-restart
                                      fn-bpn-sp-power-loss fn-bpn-sp-recover))))

(defthm fn-bpn-sp-step-preserves-statep
  (implies (fn-bpn-sp-statep s)
           (fn-bpn-sp-statep (fn-bpn-sp-step s event)))
  :hints (("Goal" :in-theory (enable fn-bpn-sp-step fn-bpn-sp-statep
                                      fn-bpn-sp-process-restart
                                      fn-bpn-sp-power-loss fn-bpn-sp-recover))))

(defthm fn-bpn-sp-trace-preserves-statep
  (implies (and (fn-bpn-sp-statep s) (true-listp events))
           (fn-bpn-sp-statep (fn-bpn-sp-trace s events)))
  :hints (("Goal" :induct (fn-bpn-sp-trace s events)
           :in-theory (e/d (fn-bpn-sp-trace)
                           (fn-bpn-sp-statep fn-bpn-sp-step
                            fn-bpn-sp-recover fn-bpn-sp-process-restart
                            fn-bpn-sp-power-loss)))))

(verify-guards fn-bpn-sp-trace
  :hints (("Goal" :use ((:instance fn-bpn-sp-step-preserves-statep
                                    (event (car events))))
           :in-theory (disable fn-bpn-sp-statep fn-bpn-sp-step))))

(defthm fn-bpn-sp-trace-preserves-safety
  (implies (and (fn-bpn-sp-safep s) (true-listp events))
           (fn-bpn-sp-safep (fn-bpn-sp-trace s events)))
  :hints (("Goal" :induct (fn-bpn-sp-trace s events)
           :in-theory (e/d (fn-bpn-sp-trace)
                           (fn-bpn-sp-safep fn-bpn-sp-step
                            fn-bpn-sp-statep fn-bpn-sp-recover
                            fn-bpn-sp-process-restart
                            fn-bpn-sp-power-loss)))))

(defthm fn-bpn-sp-initial-safe
  (fn-bpn-sp-safep (fn-bpn-sp-initial))
  :hints (("Goal" :in-theory (enable fn-bpn-sp-initial fn-bpn-sp-safep
                                      fn-bpn-sp-statep
                                      fn-bpn-sp-authors-belowp))))

(defthm fn-bpn-sp-safety-implies-authored-unique
  (implies (fn-bpn-sp-safep s)
           (no-duplicatesp-equal (fn-bpn-sp-authored s)))
  :hints (("Goal" :in-theory (enable fn-bpn-sp-safep))))

; Keystone: all author effects in a safe trace name distinct sequences.  The
; theorem is intentionally about the host-cut model, not about disk hardware.
(defthm fn-bpn-sp-trace-authored-sequences-unique
  (implies (true-listp events)
           (no-duplicatesp-equal
            (fn-bpn-sp-authored (fn-bpn-sp-trace (fn-bpn-sp-initial) events))))
  :hints (("Goal" :use (fn-bpn-sp-initial-safe
                          (:instance fn-bpn-sp-trace-preserves-safety
                                     (s (fn-bpn-sp-initial)))
                          (:instance fn-bpn-sp-safety-implies-authored-unique
                                     (s (fn-bpn-sp-trace
                                         (fn-bpn-sp-initial) events))))
           :in-theory (disable fn-bpn-sp-safep fn-bpn-sp-initial
                               fn-bpn-sp-trace fn-bpn-sp-step
                            fn-bpn-sp-statep fn-bpn-sp-recover
                            fn-bpn-sp-process-restart
                            fn-bpn-sp-power-loss))))

(deftheory fn-bpn-sequence-persistence-vocabulary
  '((:d fn-bpn-sp-state) (:d fn-bpn-sp-statep) (:d fn-bpn-sp-safep)
    (:d fn-bpn-sp-recover) (:d fn-bpn-sp-process-restart)
    (:d fn-bpn-sp-power-loss) (:d fn-bpn-sp-step) (:d fn-bpn-sp-trace)))

(in-theory (disable fn-bpn-sequence-persistence-vocabulary))
