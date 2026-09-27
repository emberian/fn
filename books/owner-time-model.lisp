; fn: the disk as an adversarial environment -- the barrier's deadline, the
; disk's mode and the owner's answers relative to it (lane time-model,
; 2026-09-27, slice 1 of planning/design-time-model-2026-09-27.md; PRF-308).
;
; books/owner-commit-pipeline.lisp runs a batch's barrier (append and
; fdatasync) in the syncer thread with the owner released; its completion is
; already an EVENT the committer reports (:fenced / :failed).  Nothing bounded
; how long that event may take: a stalled device kept the batch in flight
; for as long as it liked, every new POST joined the queue behind it, and
; nothing told anyone why.  This book adds the other half of "a completion is
; an event": the completion that does not come.
;
;   - Time is a recorded event (design section 3.7).  The host appends
;     clock events -- each disk event carries one monotonic reading in
;     milliseconds, taken under the gate mutex (host/native/owner.lisp
;     fnn-owner-disk-event) -- and ACL2 records it in the value (kept
;     monotone; a reading below it is counted by name, :clock-regressed).
;     Every decision here reads the RECORDED time; nothing reads a clock and
;     the host compares no times.
;   - The barrier is a request with a deadline D (the live configuration's
;     `barrier-deadline-ms' limit, default 5,000 ms: fn-otm-deadline-of-
;     limit).  Its issue, the committer's clock events while it waits (at
;     the deadline, then at the cadence) and its completion are events on
;     the DISK part of the scheduler's value.
;   - A barrier pending for D or longer puts the disk in mode :slow.  A
;     timeout is not a failure: the batch stays in flight, its members keep
;     waiting for their replies (the durability keystones of
;     owner-commit-steps are untouched: nothing here produces a :complete),
;     and only a failed completion is the recovery event, as before.
;   - While :slow, a new served POST is refused try-later (nothing stored,
;     nothing prepared: fn-otm-disk-admit answers :shed; the host sheds it
;     with fn-own-outcome's :refused outcome and this book's reason line),
;     and health and status carry the disk line (fn-otm-disk-line).  The
;     completion event is the recovery: no operator action.
;
; The scheduler's value is (OCP DISK CLOCK): OCP books/owner-commit-pipeline.lisp's,
; whose pick, fold and commit steps are used unchanged (fn-otm-next-is-ocp-
; next, fn-otm-commit-event-is-ocp-commit-event), so every keystone of the
; scheduler books holds of the host's calls as it did.
(in-package "ACL2")
(include-book "owner-commit-pipeline")

; -----------------------------------------------------------------------------
; The deadline: an operator profile field (D27: admission policy belongs to
; the profile), the live configuration's `barrier-deadline-ms' limit row,
; read like `log-batch-records' (books/owner-log-route.lisp fn-olr-bmax).  An
; absent or zero row is this default (PKT-845 (a)).

(defconst *fn-otm-deadline-default-ms* 5000)

(defun fn-otm-deadline-of-limit (n)
  (declare (xargs :guard t))
  (if (posp n) n *fn-otm-deadline-default-ms*))

; -----------------------------------------------------------------------------
; The disk's observed state: (PENDING SINCE DEADLINE SLOW LAST MAXL EPISODES)
;   PENDING   a barrier was issued and its completion has not been reported
;   SINCE     the reading at its issue
;   DEADLINE  its deadline in milliseconds (positive)
;   SLOW      the mode :slow was entered for it (a tick past the deadline)
;   LAST      the latency of the last completed barrier
;   MAXL      the largest completed latency
;   EPISODES  how many barriers went past their deadline

(defun fn-otm-nth-nat (i d)
  (declare (xargs :guard (natp i)))
  (nfix (nth i (if (true-listp d) d nil))))

(defun fn-otm-disk-make (pending since deadline slow last maxl episodes)
  (declare (xargs :guard t))
  (list (if pending t nil) (nfix since) (fn-otm-deadline-of-limit deadline)
        (if slow t nil) (nfix last) (nfix maxl) (nfix episodes)))

(defun fn-otm-disk-pending (d)
  (declare (xargs :guard t))
  (if (and (true-listp d) (car d)) t nil))
(defun fn-otm-disk-since (d) (declare (xargs :guard t)) (fn-otm-nth-nat 1 d))
(defun fn-otm-disk-deadline (d)
  (declare (xargs :guard t))
  (fn-otm-deadline-of-limit (fn-otm-nth-nat 2 d)))
(defun fn-otm-disk-slow (d)
  (declare (xargs :guard t))
  (if (and (true-listp d) (nth 3 d)) t nil))
(defun fn-otm-disk-last (d) (declare (xargs :guard t)) (fn-otm-nth-nat 4 d))
(defun fn-otm-disk-max (d) (declare (xargs :guard t)) (fn-otm-nth-nat 5 d))
(defun fn-otm-disk-episodes (d) (declare (xargs :guard t)) (fn-otm-nth-nat 6 d))

(defun fn-otm-disk-init ()
  (declare (xargs :guard t))
  (fn-otm-disk-make nil 0 0 nil 0 0 0))

; How long the pending barrier has waited at NOW (0 with none pending, and 0
; for a reading before its issue: the clock is monotonic, a smaller reading
; is the host's defect and never makes the disk slow).
(defun fn-otm-disk-elapsed (d now)
  (declare (xargs :guard t))
  (if (and (fn-otm-disk-pending d) (< (fn-otm-disk-since d) (nfix now)))
      (- (nfix now) (fn-otm-disk-since d))
    0))

(defun fn-otm-disk-overdue-p (d now)
  (declare (xargs :guard t))
  (and (fn-otm-disk-pending d)
       (<= (fn-otm-disk-deadline d) (fn-otm-disk-elapsed d now))))

; The disk's mode at NOW.  :slow exactly when a barrier is pending past its
; deadline; it depends on the reading, not on whether the committer's tick
; has run yet, so a POST's admission and a health render agree at every
; reading (fn-otm-shed-iff-slow).
(defun fn-otm-disk-mode (d now)
  (declare (xargs :guard t))
  (if (fn-otm-disk-overdue-p d now) :slow :ok))

; A served POST's admission: :shed (refused try-later, nothing stored) while
; the disk is slow, :admit otherwise.
(defun fn-otm-disk-admit (d now)
  (declare (xargs :guard t))
  (if (eq (fn-otm-disk-mode d now) :slow) :shed :admit))

; The events at the recorded time NOW.  Each answers (mv WORD D'):
;   issue   (:issued) the barrier was handed to the syncer at NOW with the
;           configured DEADLINE; (:fault) one was already pending (the
;           pipeline has at most one batch in flight)
;   tick    a clock event recorded NOW: (:became-slow) the first time past
;           the pending barrier's deadline, else (:none)
;   return  the syncer's completion was observed at NOW: (:recovered) after
;           a slow episode, (:returned) otherwise, (:fault) with none pending

(defun fn-otm-disk-issue (d now deadline)
  (declare (xargs :guard t))
  (if (fn-otm-disk-pending d)
      (mv :fault d)
    (mv :issued (fn-otm-disk-make t now deadline nil (fn-otm-disk-last d)
                                  (fn-otm-disk-max d) (fn-otm-disk-episodes d)))))

(defun fn-otm-disk-tick (d now)
  (declare (xargs :guard t))
  (if (and (fn-otm-disk-overdue-p d now) (not (fn-otm-disk-slow d)))
      (mv :became-slow
          (fn-otm-disk-make t (fn-otm-disk-since d) (fn-otm-disk-deadline d) t
                            (fn-otm-disk-last d) (fn-otm-disk-max d)
                            (+ 1 (fn-otm-disk-episodes d))))
    (mv :none d)))

(defun fn-otm-disk-return (d now)
  (declare (xargs :guard t))
  (if (fn-otm-disk-pending d)
      (let ((latency (fn-otm-disk-elapsed d now)))
        (mv (if (or (fn-otm-disk-slow d) (fn-otm-disk-overdue-p d now))
                :recovered
              :returned)
            (fn-otm-disk-make nil 0 (fn-otm-disk-deadline d) nil latency
                              (max latency (fn-otm-disk-max d))
                              (if (and (fn-otm-disk-overdue-p d now)
                                       (not (fn-otm-disk-slow d)))
                                  (+ 1 (fn-otm-disk-episodes d))
                                (fn-otm-disk-episodes d)))))
    (mv :fault d)))

; The clock-event cadence while a barrier is pending past its deadline
; (design section 3.7; the profile field `clock-event-ms' is slice 2's).
(defconst *fn-otm-clock-cadence-ms* 1000)

; The committer's timed wait for the syncer: the milliseconds until the
; pending barrier's deadline (at least 1), then the cadence; nil (wait for
; the completion's notification alone) when none is pending.  At its expiry
; the committer appends a clock event.
(defun fn-otm-disk-wait-ms (d now)
  (declare (xargs :guard t))
  (if (fn-otm-disk-pending d)
      (if (fn-otm-disk-overdue-p d now)
          *fn-otm-clock-cadence-ms*
        (max 1 (- (fn-otm-disk-deadline d) (fn-otm-disk-elapsed d now))))
    nil))

; -----------------------------------------------------------------------------
; What the operator and the poster read.

;; health and status: one line, a tag that names the mode and its figures.
(defun fn-otm-disk-tag (d now)
  (declare (xargs :guard t))
  (if (fn-otm-disk-overdue-p d now)
      (fn-osch-text "disk slow: barrier ")
    (fn-osch-text "disk ok:")))

(defun fn-otm-disk-body (d now)
  (declare (xargs :guard t))
  (if (fn-otm-disk-overdue-p d now)
      (append (fn-osch-decimal (fn-otm-disk-elapsed d now))
              (fn-osch-text " ms pending")
              (fn-osch-kv "deadline-ms" (fn-otm-disk-deadline d))
              (fn-osch-kv "slow-episodes" (fn-otm-disk-episodes d))
              (fn-osch-text " posts=try-later")
              (list 10))
    (append (fn-osch-kv "pending-ms" (fn-otm-disk-elapsed d now))
            (fn-osch-kv "last-barrier-ms" (fn-otm-disk-last d))
            (fn-osch-kv "max-barrier-ms" (fn-otm-disk-max d))
            (fn-osch-kv "deadline-ms" (fn-otm-disk-deadline d))
            (fn-osch-kv "slow-episodes" (fn-otm-disk-episodes d))
            (list 10))))

(defun fn-otm-disk-line (d now)
  (declare (xargs :guard t))
  (append (fn-otm-disk-tag d now) (fn-otm-disk-body d now)))

; The service log's line for an event word the host reports (nil: none).
(defun fn-otm-disk-log-line (word d now)
  (declare (xargs :guard t))
  (cond ((eq word :became-slow)
         (append (fn-osch-text "disk slow: a barrier has waited ")
                 (fn-osch-decimal (fn-otm-disk-elapsed d now))
                 (fn-osch-text " ms (deadline ")
                 (fn-osch-decimal (fn-otm-disk-deadline d))
                 (fn-osch-text " ms); new posts are refused try-later until it completes")))
        ((eq word :recovered)
         (append (fn-osch-text "disk recovered: the barrier completed after ")
                 (fn-osch-decimal (fn-otm-disk-last d))
                 (fn-osch-text " ms")))
        (t nil)))

; The shed POST's reply: RFC 3977 section 6.3.1's subsequent refusal (441;
; 436 is IHAVE's code, section 6.3.2), with the reason.  Nothing was stored.
(defun fn-otm-shed-line (d now)
  (declare (xargs :guard t))
  (append (fn-osch-text "441 posting failed; the disk is slow (a write has waited ")
          (fn-osch-decimal (fn-otm-disk-elapsed d now))
          (fn-osch-text " ms, deadline ")
          (fn-osch-decimal (fn-otm-disk-deadline d))
          (fn-osch-text " ms): nothing was stored, try again later")
          (list 13 10)))

; -----------------------------------------------------------------------------
; The scheduler's value: (OCP DISK CLOCK).  CLOCK is the recorded time
; (design section 3.7): (NOW REGRESSIONS), NOW the largest reading the host
; appended, REGRESSIONS how many readings came in below it.  Every disk
; decision reads NOW; no entry below takes the environment's time.

(defun fn-otm-ocp (s)
  (declare (xargs :guard t))
  (if (consp s) (car s) nil))

(defun fn-otm-disk (s)
  (declare (xargs :guard t))
  (if (and (consp s) (consp (cdr s))) (cadr s) (fn-otm-disk-init)))

(defun fn-otm-clock (s)
  (declare (xargs :guard t))
  (if (and (consp s) (consp (cdr s)) (consp (cddr s))) (caddr s) nil))

(defun fn-otm-now (s)
  (declare (xargs :guard t))
  (let ((c (fn-otm-clock s))) (if (consp c) (nfix (car c)) 0)))

(defun fn-otm-regressions (s)
  (declare (xargs :guard t))
  (let ((c (fn-otm-clock s))) (if (and (consp c) (consp (cdr c))) (nfix (cadr c)) 0)))

(defun fn-otm-make (ocp d clock)
  (declare (xargs :guard t))
  (list ocp d clock))

(defun fn-otm-init ()
  (declare (xargs :guard t))
  (fn-otm-make (fn-ocp-init) (fn-otm-disk-init) (list 0 0)))

; The host's entries.  The four the gate and the committer already made are
; the pipeline's over OCP, the disk and the clock kept.
(defun fn-otm-next (s w)
  (declare (xargs :guard t))
  (mv-let (class ocp) (fn-ocp-next (fn-otm-ocp s) w)
    (mv class (fn-otm-make ocp (fn-otm-disk s) (fn-otm-clock s)))))

(defun fn-otm-observe (s class hold-ms wait-ms)
  (declare (xargs :guard t))
  (fn-otm-make (fn-ocp-observe (fn-otm-ocp s) class hold-ms wait-ms) (fn-otm-disk s)
               (fn-otm-clock s)))

(defun fn-otm-commit-event (s event)
  (declare (xargs :guard t))
  (mv-let (action ocp) (fn-ocp-commit-event (fn-otm-ocp s) event)
    (mv action (fn-otm-make ocp (fn-otm-disk s) (fn-otm-clock s)))))

(defun fn-otm-committer-wake (s returned queued)
  (declare (xargs :guard t))
  (fn-ocp-committer-wake (fn-otm-ocp s) returned queued))

; Recording a reading: kept monotone; a reading below the recorded time is
; counted by name (:clock-regressed) and moves nothing back.
(defun fn-otm-record-clock (s reading)
  (declare (xargs :guard t))
  (if (< (nfix reading) (fn-otm-now s))
      (mv :clock-regressed
          (fn-otm-make (fn-otm-ocp s) (fn-otm-disk s)
                       (list (fn-otm-now s) (+ 1 (fn-otm-regressions s)))))
    (mv :recorded
        (fn-otm-make (fn-otm-ocp s) (fn-otm-disk s)
                     (list (nfix reading) (fn-otm-regressions s))))))

; The disk's events, over the whole value.  Each carries the host's READING,
; recorded first; the event then applies at the recorded time.  KIND :clock
; (a clock event: the committer's cadence, or on demand before a decision;
; :became-slow the first time the pending barrier is past its deadline),
; :issue (DEADLINE the configured limit) or :return.  Answers (mv WORD S').
(defun fn-otm-disk-event (s kind reading deadline)
  (declare (xargs :guard t))
  (mv-let (cw s1) (fn-otm-record-clock s reading)
    (let ((d (fn-otm-disk s1)) (now (fn-otm-now s1)))
      (mv-let (word d2)
        (cond ((eq kind :clock) (fn-otm-disk-tick d now))
              ((eq kind :issue) (fn-otm-disk-issue d now deadline))
              ((eq kind :return) (fn-otm-disk-return d now))
              (t (mv :fault d)))
        (mv (if (and (eq word :none) (eq cw :clock-regressed)) :clock-regressed word)
            (fn-otm-make (fn-otm-ocp s1) d2 (fn-otm-clock s1)))))))

(defun fn-otm-admit-post (s)
  (declare (xargs :guard t))
  (fn-otm-disk-admit (fn-otm-disk s) (fn-otm-now s)))

(defun fn-otm-wait-ms (s)
  (declare (xargs :guard t))
  (fn-otm-disk-wait-ms (fn-otm-disk s) (fn-otm-now s)))

(defun fn-otm-log-line (s word)
  (declare (xargs :guard t))
  (fn-otm-disk-log-line word (fn-otm-disk s) (fn-otm-now s)))

(defun fn-otm-shed-reply (s)
  (declare (xargs :guard t))
  (fn-otm-shed-line (fn-otm-disk s) (fn-otm-now s)))

; health's lines and status's, at the recorded time (the host appends a
; clock event on demand before the render).
(defun fn-otm-disk-lines (s)
  (declare (xargs :guard t))
  (append (fn-otm-disk-line (fn-otm-disk s) (fn-otm-now s))
          (if (posp (fn-otm-regressions s))
              (append (fn-osch-text "clock regressed:")
                      (fn-osch-kv "readings" (fn-otm-regressions s))
                      (list 10))
            nil)))

(defun fn-otm-health-lines (s)
  (declare (xargs :guard t))
  (append (fn-ocp-health-lines (fn-otm-ocp s)) (fn-otm-disk-lines s)))

;; =============================================================================
;; Theorems.  The disk's record through its accessors, never reopened.

(defthm fn-otm-disk-pending-of-make
  (equal (fn-otm-disk-pending (fn-otm-disk-make p since dl slow last maxl ep)) (if p t nil)))

(defthm fn-otm-disk-since-of-make
  (equal (fn-otm-disk-since (fn-otm-disk-make p since dl slow last maxl ep)) (nfix since)))

(defthm fn-otm-disk-deadline-of-make
  (equal (fn-otm-disk-deadline (fn-otm-disk-make p since dl slow last maxl ep)) (fn-otm-deadline-of-limit dl)))

(defthm fn-otm-disk-slow-of-make
  (equal (fn-otm-disk-slow (fn-otm-disk-make p since dl slow last maxl ep)) (if slow t nil)))

(defthm fn-otm-disk-last-of-make
  (equal (fn-otm-disk-last (fn-otm-disk-make p since dl slow last maxl ep)) (nfix last)))

(defthm fn-otm-disk-max-of-make
  (equal (fn-otm-disk-max (fn-otm-disk-make p since dl slow last maxl ep)) (nfix maxl)))

(defthm fn-otm-disk-episodes-of-make
  (equal (fn-otm-disk-episodes (fn-otm-disk-make p since dl slow last maxl ep)) (nfix ep)))

(defthm fn-otm-deadline-of-limit-of-deadline
  (equal (fn-otm-deadline-of-limit (fn-otm-disk-deadline d)) (fn-otm-disk-deadline d)))

(defthm fn-otm-disk-deadline-posp
  (posp (fn-otm-disk-deadline d))
  :rule-classes :type-prescription)

(defthm fn-otm-deadline-of-limit-posp
  (posp (fn-otm-deadline-of-limit n))
  :rule-classes :type-prescription)

(defthm fn-otm-disk-since-natp
  (natp (fn-otm-disk-since d))
  :rule-classes :type-prescription)

(defthm fn-otm-of-make
  (and (equal (fn-otm-ocp (fn-otm-make ocp d c)) ocp)
       (equal (fn-otm-disk (fn-otm-make ocp d c)) d)
       (equal (fn-otm-clock (fn-otm-make ocp d c)) c)))

(defthm fn-otm-now-of-list
  (and (equal (fn-otm-now (fn-otm-make ocp d (list n r))) (nfix n))
       (equal (fn-otm-regressions (fn-otm-make ocp d (list n r))) (nfix r))))

(defthm fn-otm-now-natp
  (natp (fn-otm-now s))
  :rule-classes :type-prescription)

(local (in-theory (disable fn-otm-disk-make fn-otm-disk-pending fn-otm-disk-since
                           fn-otm-disk-deadline fn-otm-disk-slow fn-otm-disk-last
                           fn-otm-disk-max fn-otm-disk-episodes fn-otm-deadline-of-limit
                           fn-otm-make fn-otm-ocp fn-otm-disk fn-otm-clock fn-otm-now
                           fn-otm-regressions
                           fn-ocp-next fn-ocp-commit-event fn-ocp-observe
                           fn-osch-text fn-osch-decimal fn-osch-kv)))

;; The pipeline's keystones carry over.
(defthm fn-otm-next-is-ocp-next
  (and (equal (mv-nth 0 (fn-otm-next s w)) (mv-nth 0 (fn-ocp-next (fn-otm-ocp s) w)))
       (equal (fn-otm-ocp (mv-nth 1 (fn-otm-next s w)))
              (mv-nth 1 (fn-ocp-next (fn-otm-ocp s) w)))
       (equal (fn-otm-disk (mv-nth 1 (fn-otm-next s w))) (fn-otm-disk s))
       (equal (fn-otm-clock (mv-nth 1 (fn-otm-next s w))) (fn-otm-clock s))))

(defthm fn-otm-commit-event-is-ocp-commit-event
  (and (equal (mv-nth 0 (fn-otm-commit-event s event))
              (mv-nth 0 (fn-ocp-commit-event (fn-otm-ocp s) event)))
       (equal (fn-otm-ocp (mv-nth 1 (fn-otm-commit-event s event)))
              (mv-nth 1 (fn-ocp-commit-event (fn-otm-ocp s) event)))
       (equal (fn-otm-disk (mv-nth 1 (fn-otm-commit-event s event))) (fn-otm-disk s))
       (equal (fn-otm-clock (mv-nth 1 (fn-otm-commit-event s event))) (fn-otm-clock s))))

(defthm fn-otm-observe-keeps-the-disk
  (and (equal (fn-otm-ocp (fn-otm-observe s class hold-ms wait-ms))
              (fn-ocp-observe (fn-otm-ocp s) class hold-ms wait-ms))
       (equal (fn-otm-disk (fn-otm-observe s class hold-ms wait-ms)) (fn-otm-disk s))
       (equal (fn-otm-clock (fn-otm-observe s class hold-ms wait-ms)) (fn-otm-clock s))))

;; KEYSTONE (the deadline never tells a member anything).  A disk event --
;; issue, tick, return, whatever NOW says -- leaves the pipeline's value
;; exactly as it was: no deadline produces a :complete, a :stop or a phase
;; change, so fn-ocs-members-told-only-after-the-barrier and
;; fn-ocp-complete-only-after-the-barrier hold of every run with deadlines.
;; The subject is fn-otm-disk-event, which host/native/owner.lisp
;; fnn-owner-disk-event calls from the committer.
(defthm fn-otm-disk-event-keeps-the-pipeline
  (equal (fn-otm-ocp (mv-nth 1 (fn-otm-disk-event s kind reading deadline)))
         (fn-otm-ocp s))
  :hints (("Goal" :in-theory (disable fn-otm-disk-issue fn-otm-disk-tick fn-otm-disk-return))))

;; The recorded time is monotone, and a reading below it is counted by name
;; and moves nothing back (design section 3.7).  The subject is
;; fn-otm-disk-event, every clock event the host appends.
(defthm fn-otm-recorded-time-is-monotone
  (let ((s2 (mv-nth 1 (fn-otm-disk-event s kind reading deadline))))
    (and (<= (fn-otm-now s) (fn-otm-now s2))
         (equal (fn-otm-now s2) (max (fn-otm-now s) (nfix reading)))
         (equal (fn-otm-regressions s2)
                (if (< (nfix reading) (fn-otm-now s))
                    (+ 1 (fn-otm-regressions s))
                  (fn-otm-regressions s)))))
  :hints (("Goal" :in-theory (disable fn-otm-disk-issue fn-otm-disk-tick fn-otm-disk-return))))

;; The disk event at a reading: the core step at the recorded time.
(defthm fn-otm-disk-event-unfolds
  (implies (<= (fn-otm-now s) (nfix reading))
           (and (equal (fn-otm-disk (mv-nth 1 (fn-otm-disk-event s kind reading deadline)))
                       (cond ((eq kind :clock)
                              (mv-nth 1 (fn-otm-disk-tick (fn-otm-disk s) (nfix reading))))
                             ((eq kind :issue)
                              (mv-nth 1 (fn-otm-disk-issue (fn-otm-disk s) (nfix reading) deadline)))
                             ((eq kind :return)
                              (mv-nth 1 (fn-otm-disk-return (fn-otm-disk s) (nfix reading))))
                             (t (fn-otm-disk s))))
                (equal (fn-otm-now (mv-nth 1 (fn-otm-disk-event s kind reading deadline)))
                       (nfix reading))
                (equal (mv-nth 0 (fn-otm-disk-event s kind reading deadline))
                       (cond ((eq kind :clock)
                              (mv-nth 0 (fn-otm-disk-tick (fn-otm-disk s) (nfix reading))))
                             ((eq kind :issue)
                              (mv-nth 0 (fn-otm-disk-issue (fn-otm-disk s) (nfix reading) deadline)))
                             ((eq kind :return)
                              (mv-nth 0 (fn-otm-disk-return (fn-otm-disk s) (nfix reading))))
                             (t :fault)))))
  :hints (("Goal" :in-theory (disable fn-otm-disk-issue fn-otm-disk-tick fn-otm-disk-return))))

;; -----------------------------------------------------------------------------
;; The disk machine.

(local (in-theory (disable fn-otm-disk-elapsed)))

(local
 (defthm fn-otm-disk-elapsed-when-pending
   (implies (and (fn-otm-disk-pending d) (natp now) (<= (fn-otm-disk-since d) now))
            (equal (fn-otm-disk-elapsed d now) (- now (fn-otm-disk-since d))))
   :hints (("Goal" :in-theory (enable fn-otm-disk-elapsed)))))

(local
 (defthm fn-otm-disk-elapsed-natp
   (natp (fn-otm-disk-elapsed d now))
   :rule-classes :type-prescription
   :hints (("Goal" :in-theory (enable fn-otm-disk-elapsed)))))

(local
 (defthm fn-otm-disk-elapsed-when-not-pending
   (implies (not (fn-otm-disk-pending d)) (equal (fn-otm-disk-elapsed d now) 0))
   :hints (("Goal" :in-theory (enable fn-otm-disk-elapsed)))))

;; A shed happens only while a barrier is pending past its deadline at the
;; recorded time.
(defthm fn-otm-shed-only-past-the-deadline
  (implies (equal (fn-otm-admit-post s) :shed)
           (and (fn-otm-disk-pending (fn-otm-disk s))
                (<= (fn-otm-disk-deadline (fn-otm-disk s))
                    (- (fn-otm-now s) (fn-otm-disk-since (fn-otm-disk s))))))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-otm-disk-elapsed))))

;; ... and always then: a pending barrier past its deadline sheds.
(defthm fn-otm-past-the-deadline-sheds
  (implies (and (fn-otm-disk-pending (fn-otm-disk s))
                (<= (+ (fn-otm-disk-since (fn-otm-disk s))
                       (fn-otm-disk-deadline (fn-otm-disk s)))
                    (fn-otm-now s)))
           (equal (fn-otm-admit-post s) :shed)))

;; The backpressure always has its reason on the page: a POST is shed
;; exactly when health and status, rendered from the same value, print the
;; disk-slow line.
(defun fn-otm-slow-line-p (line)
  (declare (xargs :guard t))
  (and (true-listp line)
       (<= 6 (len line))
       (equal (take 6 line) (fn-osch-chars-octets (coerce "disk s" 'list)))))

(local
 (defthm fn-otm-take-of-append
   (implies (and (true-listp a) (<= (nfix n) (len a)))
            (equal (take n (append a b)) (take n a)))))

(local
 (defthm fn-otm-disk-tag-cases
   (and (implies (fn-otm-disk-overdue-p d now)
                 (equal (fn-otm-disk-tag d now)
                        (fn-osch-chars-octets (coerce "disk slow: barrier " 'list))))
        (implies (not (fn-otm-disk-overdue-p d now))
                 (equal (fn-otm-disk-tag d now)
                        (fn-osch-chars-octets (coerce "disk ok:" 'list)))))
   :hints (("Goal" :in-theory (enable fn-osch-text)))))

(local
 (defthm fn-otm-disk-overdue-p-of-nfix
   (equal (fn-otm-disk-overdue-p d (nfix now)) (fn-otm-disk-overdue-p d now))
   :hints (("Goal" :in-theory (enable fn-otm-disk-elapsed)))))

(defthm fn-otm-shed-iff-slow
  (iff (equal (fn-otm-admit-post s) :shed)
       (fn-otm-slow-line-p (fn-otm-disk-lines s)))
  :hints (("Goal" :in-theory (disable fn-otm-disk-body fn-otm-disk-tag fn-otm-disk-overdue-p
                                      fn-osch-chars-octets)
           :cases ((fn-otm-disk-overdue-p (fn-otm-disk s) (fn-otm-now s))))))

;; Recovery needs no operator action: after the completion event the node
;; admits every POST, and no later clock event makes the disk slow again
;; until the next barrier is issued.
(defthm fn-otm-return-recovers
  (implies (fn-otm-disk-pending (fn-otm-disk s))
           (let ((s2 (mv-nth 1 (fn-otm-disk-event s :return reading deadline))))
             (and (equal (fn-otm-admit-post s2) :admit)
                  (not (fn-otm-disk-pending (fn-otm-disk s2)))
                  (member-equal (mv-nth 0 (fn-otm-disk-event s :return reading deadline))
                                '(:returned :recovered))))))

(defthm fn-otm-clock-event-never-issues
  (implies (not (fn-otm-disk-pending (fn-otm-disk s)))
           (let ((s2 (mv-nth 1 (fn-otm-disk-event s :clock reading deadline))))
             (and (not (fn-otm-disk-pending (fn-otm-disk s2)))
                  (equal (fn-otm-admit-post s2) :admit)))))

;; The completion's latency is recorded: the last barrier's latency is the
;; recorded completion time's distance from the recorded issue time.
(defthm fn-otm-return-records-the-latency
  (implies (and (fn-otm-disk-pending (fn-otm-disk s)) (natp reading)
                (<= (fn-otm-now s) reading)
                (<= (fn-otm-disk-since (fn-otm-disk s)) reading))
           (equal (fn-otm-disk-last
                   (fn-otm-disk (mv-nth 1 (fn-otm-disk-event s :return reading deadline))))
                  (- reading (fn-otm-disk-since (fn-otm-disk s))))))

;; The committer's timed wait reaches the deadline: a clock event appended
;; WAIT-MS after the recorded time (or later) finds the barrier past its
;; deadline -- the POSTs after it are shed -- and enters :slow (once per
;; barrier: a disk already marked slow answers :none).
(defthm fn-otm-wait-reaches-the-deadline
  (implies (and (fn-otm-wait-ms s)
                (natp reading)
                (<= (fn-otm-disk-since (fn-otm-disk s)) (fn-otm-now s))
                (<= (+ (fn-otm-now s) (fn-otm-wait-ms s)) reading))
           (let ((s2 (mv-nth 1 (fn-otm-disk-event s :clock reading deadline))))
             (and (posp (fn-otm-wait-ms s))
                  (equal (fn-otm-admit-post s2) :shed)
                  (equal (mv-nth 0 (fn-otm-disk-event s :clock reading deadline))
                         (if (fn-otm-disk-slow (fn-otm-disk s)) :none :became-slow))))))

;; A barrier is issued only when none is pending (one in flight at a time),
;; and an issued barrier is pending from the recorded time of its issue.
(defthm fn-otm-issue-only-when-none-pending
  (iff (equal (mv-nth 0 (fn-otm-disk-event s :issue reading deadline)) :issued)
       (not (fn-otm-disk-pending (fn-otm-disk s)))))

(defthm fn-otm-issue-is-pending-and-admits
  (implies (and (not (fn-otm-disk-pending (fn-otm-disk s))) (natp reading)
                (<= (fn-otm-now s) reading))
           (let ((s2 (mv-nth 1 (fn-otm-disk-event s :issue reading deadline))))
             (and (fn-otm-disk-pending (fn-otm-disk s2))
                  (equal (fn-otm-disk-since (fn-otm-disk s2)) reading)
                  (equal (fn-otm-disk-deadline (fn-otm-disk s2))
                         (fn-otm-deadline-of-limit deadline))
                  (equal (fn-otm-admit-post s2) :admit)))))

; KEYSTONE (PRF-308): reads and status never wait for the barrier.
;
; The subject is the gate's pick, fn-otm-next (host/native/owner.lisp
; fnn-owner-gate-pick calls it at every release of the owner and every
; arrival at an idle one), and the committer's events, fn-otm-commit-event
; (fnn-owner-commit-event).  WS the successive pick observations while the
; batch's barrier is PENDING, each (W EVENT): W the waiting counts at the
; pick, EVENT what the commit reports if the pick is a :commit.  The
; hypotheses (fn-otm-barrier-walk-okp):
;   - a reader waits at every pick;
;   - the commit class waits only when the committer's wake is :start-next
;     (fn-ocp-committer-wake with the syncer NOT returned and a member
;     queued: host/native/owner.lisp fnn-owner-commit-pipeline enters the
;     gate as :commit during a barrier only then; its COMPLETE is entered
;     only after the syncer returned, which is where the walk ends).
; The event a :commit reports is any: the bound does not depend on what the
; START-NEXT found, and the durations of the barrier and of the device do
; not appear at all.
; Then before the reader is admitted only :inspect and :commit quanta run
; (no control, poster or transit), at most ONE of the :commit quanta is a
; START-NEXT that took members, and the :inspect quanta are at most one
; more than the :commit quanta.  So a read waits for at most 3 quanta plus
; one per START-NEXT that took nobody -- each an owner quantum with no I/O
; in it -- however long the disk takes.  The :inspect bound is
; fn-ocs-inspect-waits-at-most-one's (PRF-267), which holds of fn-otm-next
; by fn-otm-next-is-ocp-next.

;; The walk's parts: the class the gate picks for ITEM (W EVENT) at S, and
;; the value after that pick and, for a :commit, the commit's event.
(defun fn-otm-walk-class (s item)
  (declare (xargs :guard t))
  (mv-let (class s2) (fn-otm-next s (fn-ocs-item-w item))
    (declare (ignore s2))
    class))

(defun fn-otm-walk-next (s item)
  (declare (xargs :guard t))
  (mv-let (class s2) (fn-otm-next s (fn-ocs-item-w item))
    (if (eq class :commit)
        (mv-let (a s3) (fn-otm-commit-event s2 (fn-ocs-item-event item))
          (declare (ignore a))
          s3)
      s2)))

;; The quanta that run before the first :reader pick, each (CLASS . EVENT).
(defun fn-otm-barrier-walk (s ws)
  (declare (xargs :guard t :measure (len ws)))
  (if (consp ws)
      (let ((class (fn-otm-walk-class s (car ws))))
        (if (eq class :reader)
            nil
          (let ((rest (fn-otm-barrier-walk (fn-otm-walk-next s (car ws)) (cdr ws))))
            (if class
                (cons (cons class (fn-ocs-item-event (car ws))) rest)
              rest))))
    nil))

(defun fn-otm-barrier-walk-okp (s ws)
  (declare (xargs :guard t :measure (len ws)))
  (if (consp ws)
      (let ((w (fn-ocs-item-w (car ws))) (class (fn-otm-walk-class s (car ws))))
        (and (fn-ocs-reader-waits-p w)
             (implies (fn-ocs-commit-waits-p w)
                      (equal (fn-otm-committer-wake s nil t) :start-next))
             (or (eq class :reader)
                 (fn-otm-barrier-walk-okp (fn-otm-walk-next s (car ws)) (cdr ws)))))
    t))

;; Counts over the quanta.
(defun fn-otm-trace-count (class event trace)
  ;; EVENT nil counts every event of CLASS.
  (declare (xargs :guard t))
  (if (consp trace)
      (+ (if (and (consp (car trace)) (equal (caar trace) class)
                  (or (null event) (equal (cdar trace) event)))
             1 0)
         (fn-otm-trace-count class event (cdr trace)))
    0))

(defun fn-otm-trace-others (trace)
  (declare (xargs :guard t))
  (if (consp trace)
      (+ (if (and (consp (car trace)) (member-eq (caar trace) '(:inspect :commit))) 0 1)
         (fn-otm-trace-others (cdr trace)))
    0))

(defun fn-otm-walk-inspects (s ws)
  (declare (xargs :guard t))
  (fn-otm-trace-count :inspect nil (fn-otm-barrier-walk s ws)))
(defun fn-otm-walk-commits (s ws)
  (declare (xargs :guard t))
  (fn-otm-trace-count :commit nil (fn-otm-barrier-walk s ws)))
(defun fn-otm-walk-started (s ws)
  (declare (xargs :guard t))
  (fn-otm-trace-count :commit :next-started (fn-otm-barrier-walk s ws)))
(defun fn-otm-walk-others (s ws)
  (declare (xargs :guard t))
  (fn-otm-trace-others (fn-otm-barrier-walk s ws)))

;; The pipeline's phase, the inspect alternation and the next batch, read
;; through the whole value.
(defun fn-otm-phase (s)
  (declare (xargs :guard t))
  (fn-ocs-phase (fn-ocp-ocs (fn-otm-ocp s))))
(defun fn-otm-lasti (s)
  (declare (xargs :guard t))
  (fn-ocs-lasti (fn-ocp-ocs (fn-otm-ocp s))))
(defun fn-otm-open-next (s)
  (declare (xargs :guard t))
  (fn-ocp-open-next (fn-otm-ocp s)))

;; The barrier is pending: the batch is in flight and staged (its barrier's
;; word not yet reported).
(defun fn-otm-barrier-pending-p (s)
  (declare (xargs :guard t))
  (equal (fn-otm-phase s) :staged))

;; The pick and the commit event in flight, in the terms of the walk.
(local
 (defthm fn-otm-next-class-in-flight
   (implies (fn-ocs-in-flight-p (fn-otm-phase s))
            (equal (mv-nth 0 (fn-otm-next s w))
                   (cond ((and (fn-ocs-inspect-waits-p w)
                               (or (not (or (fn-ocs-commit-waits-p w) (fn-ocs-reader-waits-p w)))
                                   (not (fn-otm-lasti s))))
                          :inspect)
                         ((fn-ocs-commit-waits-p w) :commit)
                         ((fn-ocs-reader-waits-p w) :reader)
                         (t nil))))
   :hints (("Goal" :in-theory (e/d (fn-otm-next fn-ocp-next fn-ocs-next)
                                   (fn-ocs-inspect-waits-p fn-ocs-commit-waits-p
                                    fn-ocs-reader-waits-p fn-ocs-in-flight-p fn-ocs-phase
                                    fn-ocs-lasti fn-ocm-next))))))

(local
 (defthm fn-otm-next-state-in-flight
   (implies (fn-ocs-in-flight-p (fn-otm-phase s))
            (let ((s2 (mv-nth 1 (fn-otm-next s w))))
              (and (equal (fn-otm-phase s2) (fn-otm-phase s))
                   (equal (fn-otm-open-next s2) (fn-otm-open-next s))
                   (equal (fn-otm-lasti s2)
                          (if (mv-nth 0 (fn-otm-next s w))
                              (equal (mv-nth 0 (fn-otm-next s w)) :inspect)
                            (fn-otm-lasti s))))))
   :hints (("Goal" :in-theory (e/d (fn-otm-next fn-ocp-next fn-ocs-next fn-ocs-make)
                                   (fn-ocs-inspect-waits-p fn-ocs-commit-waits-p
                                    fn-ocs-reader-waits-p fn-ocm-next))))))

(local
 (defthm fn-otm-commit-event-next-in-flight
   (implies (equal (fn-otm-phase s) :staged)
            (let ((s2 (mv-nth 1 (fn-otm-commit-event s e))))
              (and (fn-ocs-in-flight-p (fn-otm-phase s2))
                   (equal (fn-otm-open-next s2)
                          (or (fn-otm-open-next s) (equal e :next-started)))
                   (equal (fn-otm-lasti s2) (fn-otm-lasti s)))))
   :hints (("Goal" :in-theory (enable fn-otm-commit-event fn-ocp-commit-event fn-ocp-commit-step
                                      fn-ocs-make fn-ocs-in-flight-p)))))

(local
 (defthm fn-otm-wake-start-next
   (equal (equal (fn-otm-committer-wake s nil t) :start-next)
          (and (equal (fn-otm-phase s) :staged) (not (fn-otm-open-next s))))
   :hints (("Goal" :in-theory (enable fn-otm-committer-wake fn-ocp-committer-wake fn-ocp-wake)))))

(local (in-theory (disable fn-otm-next fn-otm-commit-event fn-otm-committer-wake
                           fn-otm-next-is-ocp-next fn-otm-commit-event-is-ocp-commit-event
                           fn-ocp-next-is-ocs-next
                           fn-otm-phase fn-otm-lasti fn-otm-open-next fn-ocs-in-flight-p
                           fn-ocs-inspect-waits-p fn-ocs-commit-waits-p fn-ocs-reader-waits-p)))

;; One step of the walk, while the barrier is pending and a reader waits.
(defthm fn-otm-walk-step-facts
   (implies (and (fn-ocs-in-flight-p (fn-otm-phase s))
                 (fn-ocs-reader-waits-p (fn-ocs-item-w item))
                 (implies (fn-ocs-commit-waits-p (fn-ocs-item-w item))
                          (and (equal (fn-otm-phase s) :staged) (not (fn-otm-open-next s)))))
            (let ((c (fn-otm-walk-class s item)) (s2 (fn-otm-walk-next s item)))
              (and (member-equal c '(:inspect :commit :reader))
                   (implies (equal c :inspect) (not (fn-otm-lasti s)))
                   (implies (equal c :commit) (not (fn-otm-open-next s)))
                   (fn-ocs-in-flight-p (fn-otm-phase s2))
                   (equal (fn-otm-lasti s2) (equal c :inspect))
                   (equal (fn-otm-open-next s2)
                          (or (fn-otm-open-next s)
                              (and (equal c :commit)
                                   (equal (fn-ocs-item-event item) :next-started)))))))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-otm-walk-class fn-otm-walk-next fn-ocs-in-flight-p))))

(local (in-theory (disable fn-otm-walk-class fn-otm-walk-next)))

(local
 (defthm fn-otm-walk-okp-step
   (implies (and (consp ws) (fn-otm-barrier-walk-okp s ws))
            (and (fn-ocs-reader-waits-p (fn-ocs-item-w (car ws)))
                 (implies (fn-ocs-commit-waits-p (fn-ocs-item-w (car ws)))
                          (and (equal (fn-otm-phase s) :staged) (not (fn-otm-open-next s))))
                 (implies (not (equal (fn-otm-walk-class s (car ws)) :reader))
                          (fn-otm-barrier-walk-okp (fn-otm-walk-next s (car ws)) (cdr ws)))))))

(local (in-theory (disable fn-otm-barrier-walk-okp)))

(local
 (defthm fn-otm-walk-okp-facts
   (implies (and (consp ws) (fn-ocs-in-flight-p (fn-otm-phase s))
                 (fn-otm-barrier-walk-okp s ws))
            (and (fn-otm-walk-class s (car ws))
                 (implies (and (not (equal (fn-otm-walk-class s (car ws)) :inspect))
                               (not (equal (fn-otm-walk-class s (car ws)) :reader)))
                          (equal (fn-otm-walk-class s (car ws)) :commit))
                 (implies (equal (fn-otm-walk-class s (car ws)) :inspect)
                          (not (fn-otm-lasti s)))
                 (implies (equal (fn-otm-walk-class s (car ws)) :commit)
                          (not (fn-otm-open-next s)))
                 (fn-ocs-in-flight-p (fn-otm-phase (fn-otm-walk-next s (car ws))))
                 (equal (fn-otm-lasti (fn-otm-walk-next s (car ws)))
                        (equal (fn-otm-walk-class s (car ws)) :inspect))
                 (equal (fn-otm-open-next (fn-otm-walk-next s (car ws)))
                        (or (fn-otm-open-next s)
                            (and (equal (fn-otm-walk-class s (car ws)) :commit)
                                 (equal (fn-ocs-item-event (car ws)) :next-started))))
                 (implies (not (equal (fn-otm-walk-class s (car ws)) :reader))
                          (fn-otm-barrier-walk-okp (fn-otm-walk-next s (car ws)) (cdr ws)))))
   :hints (("Goal" :use ((:instance fn-otm-walk-step-facts (item (car ws)))
                         (:instance fn-otm-walk-okp-step))
            :in-theory (disable fn-otm-walk-okp-step)))))

(local
 (defthm fn-otm-walk-others-zero
   (implies (and (fn-ocs-in-flight-p (fn-otm-phase s)) (fn-otm-barrier-walk-okp s ws))
            (equal (fn-otm-trace-others (fn-otm-barrier-walk s ws)) 0))
   :hints (("Goal" :induct (fn-otm-barrier-walk s ws)))))

(local
 (defthm fn-otm-walk-started-bound
   (implies (and (fn-ocs-in-flight-p (fn-otm-phase s)) (fn-otm-barrier-walk-okp s ws))
            (<= (fn-otm-trace-count :commit :next-started (fn-otm-barrier-walk s ws))
                (if (fn-otm-open-next s) 0 1)))
   :rule-classes nil
   :hints (("Goal" :induct (fn-otm-barrier-walk s ws)))))

(local
 (defthm fn-otm-walk-inspect-bound
   (implies (and (fn-ocs-in-flight-p (fn-otm-phase s)) (fn-otm-barrier-walk-okp s ws))
            (<= (fn-otm-trace-count :inspect nil (fn-otm-barrier-walk s ws))
                (+ (fn-otm-trace-count :commit nil (fn-otm-barrier-walk s ws))
                   (if (fn-otm-lasti s) 0 1))))
   :rule-classes nil
   :hints (("Goal" :induct (fn-otm-barrier-walk s ws)))))

(defthm fn-otm-barrier-reader-bound
  ; KEYSTONE (PRF-308).  While the batch's barrier is pending and a reader
  ; waits at every pick (fn-otm-barrier-walk-okp), before the reader is
  ; admitted: no control, poster or transit quantum runs; at most one
  ; START-NEXT that took members runs; and the :inspect quanta are at most
  ; one more than the :commit quanta.  Nothing here depends on how long the
  ; barrier takes: the device's latency is not a quantity of the walk.
  (implies (and (fn-otm-barrier-pending-p s) (fn-otm-barrier-walk-okp s ws))
           (and (equal (fn-otm-walk-others s ws) 0)
                (<= (fn-otm-walk-started s ws) 1)
                (<= (fn-otm-walk-inspects s ws) (+ 1 (fn-otm-walk-commits s ws)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-ocs-in-flight-p)
           :use (fn-otm-walk-started-bound fn-otm-walk-inspect-bound))))

(in-theory (disable fn-otm-next fn-otm-observe fn-otm-commit-event fn-otm-committer-wake
                    fn-otm-disk-event fn-otm-admit-post fn-otm-wait-ms fn-otm-log-line
                    fn-otm-shed-reply fn-otm-health-lines fn-otm-disk-lines))
