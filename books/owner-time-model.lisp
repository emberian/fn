; fn: the disk as an adversarial environment -- the barrier's deadline, the
; disk's mode and the owner's answers relative to it (lane time-model,
; 2026-09-27, slice 1 of planning/design-time-model-2026-09-27.md; PRF-311).
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
; N3 of lane proto-determinism: the wall reading's validity (fn-otm-wall-reading).
(include-book "clock-wall-reading")


; -----------------------------------------------------------------------------
; The deadlines and the cadence: operator profile fields (D27: admission
; policy belongs to the profile), the live configuration's `:set-limit'
; rows, read like `log-batch-records' (books/owner-log-route.lisp
; fn-olr-bmax) and set by `policy set SLOT N' (books/native-admin.lisp).  An
; absent or zero row is the default (PKT-853 (a)):
;   barrier-deadline-ms  D: a barrier pending this long makes the disk :slow
;   barrier-stall-ms     H: pending this long, :stalled (slice 2; never below D)
;   clock-event-ms       the committer's clock-event cadence (slice 2)

(defconst *fn-otm-deadline-default-ms* 5000)
(defconst *fn-otm-stall-default-ms* 30000)
(defconst *fn-otm-cadence-default-ms* 1000)

(defun fn-otm-deadline-of-limit (n)
  (declare (xargs :guard t))
  (if (posp n) n *fn-otm-deadline-default-ms*))

(defun fn-otm-stall-of-limit (n)
  (declare (xargs :guard t))
  (if (posp n) n *fn-otm-stall-default-ms*))

(defun fn-otm-cadence-of-limit (n)
  (declare (xargs :guard t))
  (if (posp n) n *fn-otm-cadence-default-ms*))

; The limits an :issue carries, (D H C), each its row's value or its
; default, H raised to D when a profile sets it below (the stall deadline
; never precedes the slow one).  A bare number is D alone (slice 1's
; argument; H and C then their defaults).
(defun fn-otm-limits (arg)
  (declare (xargs :guard t))
  (let* ((d (fn-otm-deadline-of-limit (if (consp arg) (car arg) arg)))
         (h (fn-otm-stall-of-limit (if (and (consp arg) (consp (cdr arg))) (cadr arg) 0)))
         (c (fn-otm-cadence-of-limit
             (if (and (consp arg) (consp (cdr arg)) (consp (cddr arg))) (caddr arg) 0))))
    (list d (max d h) c)))

; -----------------------------------------------------------------------------
; The disk's observed state:
;   (PENDING SINCE DEADLINE SLOW LAST MAXL EPISODES STALL CADENCE STALLED STALLS)
;   PENDING   a barrier was issued and its completion has not been reported
;   SINCE     the recorded time of its issue
;   DEADLINE  D for it (positive)
;   SLOW      the mode :slow was entered for it (a clock event past D)
;   LAST      the latency of the last completed barrier
;   MAXL      the largest completed latency
;   EPISODES  how many barriers went past D
;   STALL     H for it (at least D)
;   CADENCE   the committer's clock-event cadence for it
;   STALLED   the mode :stalled was entered for it (a clock event past H:
;             its posters were told uncertain)
;   STALLS    how many barriers went past H

(defun fn-otm-nth-nat (i d)
  (declare (xargs :guard (natp i)))
  (nfix (nth i (if (true-listp d) d nil))))

(defun fn-otm-disk-make (pending since deadline slow last maxl episodes stall cadence
                                 stalled stalls)
  (declare (xargs :guard t))
  ;; The fields as given; every accessor normalizes what it reads.
  (list pending since deadline slow last maxl episodes stall cadence stalled stalls))

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
(defun fn-otm-disk-stall (d)
  (declare (xargs :guard t))
  (max (fn-otm-disk-deadline d) (fn-otm-stall-of-limit (fn-otm-nth-nat 7 d))))
(defun fn-otm-disk-cadence (d)
  (declare (xargs :guard t))
  (fn-otm-cadence-of-limit (fn-otm-nth-nat 8 d)))
(defun fn-otm-disk-stalled (d)
  (declare (xargs :guard t))
  (if (and (true-listp d) (nth 9 d)) t nil))
(defun fn-otm-disk-stalls (d) (declare (xargs :guard t)) (fn-otm-nth-nat 10 d))

(defun fn-otm-disk-init ()
  (declare (xargs :guard t))
  (fn-otm-disk-make nil 0 0 nil 0 0 0 0 0 nil 0))

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

(defun fn-otm-disk-stall-due-p (d now)
  (declare (xargs :guard t))
  (and (fn-otm-disk-pending d)
       (<= (fn-otm-disk-stall d) (fn-otm-disk-elapsed d now))))

; The disk's mode at NOW: :stalled past H, :slow past D, else :ok.  It
; depends on the reading, not on whether the committer's clock event has
; run yet, so a POST's admission and a health render agree at every
; reading (fn-otm-shed-iff-slow).
(defun fn-otm-disk-mode (d now)
  (declare (xargs :guard t))
  (cond ((fn-otm-disk-stall-due-p d now) :stalled)
        ((fn-otm-disk-overdue-p d now) :slow)
        (t :ok)))

; A write's admission (a served POST's, at its command and after its
; article; a mutating control request's): :shed (refused try-later,
; nothing stored) while the disk is :slow or :stalled, :admit otherwise.
(defun fn-otm-disk-admit (d now)
  (declare (xargs :guard t))
  (if (fn-otm-disk-overdue-p d now) :shed :admit))

; The events at the recorded time NOW.  Each answers (mv WORD D'):
;   issue   (:issued) the barrier was handed to the syncer at NOW with the
;           LIMITS (D H C); (:fault) one was already pending (the pipeline
;           has at most one batch in flight)
;   tick    a clock event recorded NOW: (:became-stalled) the first time
;           past the pending barrier's H -- the host then tells the batch's
;           posters uncertain -- (:became-slow) the first time past its D,
;           else (:none)
;   return  the syncer's completion was observed at NOW: (:recovered-from-
;           stall) after a stall, (:recovered) after a slow episode,
;           (:returned) otherwise, (:fault) with none pending

(defun fn-otm-disk-issue (d now limits)
  (declare (xargs :guard t))
  (if (fn-otm-disk-pending d)
      (mv :fault d)
    (let ((l (fn-otm-limits limits)))
      (mv :issued (fn-otm-disk-make t now (car l) nil (fn-otm-disk-last d)
                                    (fn-otm-disk-max d) (fn-otm-disk-episodes d)
                                    (cadr l) (caddr l) nil (fn-otm-disk-stalls d))))))

(defun fn-otm-disk-tick (d now)
  (declare (xargs :guard t))
  (cond ((and (fn-otm-disk-stall-due-p d now) (not (fn-otm-disk-stalled d)))
         (mv :became-stalled
             (fn-otm-disk-make t (fn-otm-disk-since d) (fn-otm-disk-deadline d) t
                               (fn-otm-disk-last d) (fn-otm-disk-max d)
                               (if (fn-otm-disk-slow d)
                                   (fn-otm-disk-episodes d)
                                 (+ 1 (fn-otm-disk-episodes d)))
                               (fn-otm-disk-stall d) (fn-otm-disk-cadence d) t
                               (+ 1 (fn-otm-disk-stalls d)))))
        ((and (fn-otm-disk-overdue-p d now) (not (fn-otm-disk-slow d)))
         (mv :became-slow
             (fn-otm-disk-make t (fn-otm-disk-since d) (fn-otm-disk-deadline d) t
                               (fn-otm-disk-last d) (fn-otm-disk-max d)
                               (+ 1 (fn-otm-disk-episodes d))
                               (fn-otm-disk-stall d) (fn-otm-disk-cadence d)
                               (fn-otm-disk-stalled d) (fn-otm-disk-stalls d))))
        (t (mv :none d))))

(defun fn-otm-disk-return (d now)
  (declare (xargs :guard t))
  (if (fn-otm-disk-pending d)
      (let ((latency (fn-otm-disk-elapsed d now)))
        (mv (cond ((fn-otm-disk-stalled d) :recovered-from-stall)
                  ((or (fn-otm-disk-slow d) (fn-otm-disk-overdue-p d now)) :recovered)
                  (t :returned))
            (fn-otm-disk-make nil 0 (fn-otm-disk-deadline d) nil latency
                              (max latency (fn-otm-disk-max d))
                              (if (and (fn-otm-disk-overdue-p d now)
                                       (not (fn-otm-disk-slow d)))
                                  (+ 1 (fn-otm-disk-episodes d))
                                (fn-otm-disk-episodes d))
                              (fn-otm-disk-stall d) (fn-otm-disk-cadence d) nil
                              (fn-otm-disk-stalls d))))
    (mv :fault d)))

; The committer's timed wait for the syncer: the milliseconds until the
; pending barrier's next boundary -- its D, then its H, each at least 1 --
; with at most the cadence between clock events once past D; the cadence
; past H; nil (wait for the completion's notification alone) when none is
; pending.  At its expiry, and at every other wake while a barrier is
; pending, the committer appends a clock event.  The wait never reaches
; past H (fn-otm-wait-stays-within-the-stall), which is what bounds the
; posters' answer (F4-W).
(defun fn-otm-disk-wait-ms (d now)
  (declare (xargs :guard t))
  (if (fn-otm-disk-pending d)
      (cond ((fn-otm-disk-stall-due-p d now) (fn-otm-disk-cadence d))
            ((fn-otm-disk-overdue-p d now)
             (max 1 (min (fn-otm-disk-cadence d)
                         (- (fn-otm-disk-stall d) (fn-otm-disk-elapsed d now)))))
            (t (max 1 (- (fn-otm-disk-deadline d) (fn-otm-disk-elapsed d now)))))
    nil))

; -----------------------------------------------------------------------------
; What the operator and the poster read.

;; health and status: one line, a tag that names the mode and its figures.
(defun fn-otm-disk-tag (d now)
  (declare (xargs :guard t))
  (cond ((fn-otm-disk-stall-due-p d now) (fn-osch-text "disk stalled: barrier "))
        ((fn-otm-disk-overdue-p d now) (fn-osch-text "disk slow: barrier "))
        (t (fn-osch-text "disk ok:"))))

(defun fn-otm-disk-body (d now)
  (declare (xargs :guard t))
  (if (fn-otm-disk-overdue-p d now)
      (append (fn-osch-decimal (fn-otm-disk-elapsed d now))
              (fn-osch-text " ms pending")
              (fn-osch-kv "deadline-ms" (fn-otm-disk-deadline d))
              (fn-osch-kv "stall-ms" (fn-otm-disk-stall d))
              (fn-osch-kv "slow-episodes" (fn-otm-disk-episodes d))
              (fn-osch-kv "stalls" (fn-otm-disk-stalls d))
              (fn-osch-text " posts=try-later")
              (if (fn-otm-disk-stall-due-p d now) (fn-osch-text " members=uncertain") nil)
              (list 10))
    (append (fn-osch-kv "pending-ms" (fn-otm-disk-elapsed d now))
            (fn-osch-kv "last-barrier-ms" (fn-otm-disk-last d))
            (fn-osch-kv "max-barrier-ms" (fn-otm-disk-max d))
            (fn-osch-kv "deadline-ms" (fn-otm-disk-deadline d))
            (fn-osch-kv "stall-ms" (fn-otm-disk-stall d))
            (fn-osch-kv "slow-episodes" (fn-otm-disk-episodes d))
            (fn-osch-kv "stalls" (fn-otm-disk-stalls d))
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
        ((eq word :became-stalled)
         (append (fn-osch-text "disk stalled: a barrier has waited ")
                 (fn-osch-decimal (fn-otm-disk-elapsed d now))
                 (fn-osch-text " ms (stall deadline ")
                 (fn-osch-decimal (fn-otm-disk-stall d))
                 (fn-osch-text " ms); its posters are told the outcome is uncertain: it may still complete")))
        ((eq word :recovered)
         (append (fn-osch-text "disk recovered: the barrier completed after ")
                 (fn-osch-decimal (fn-otm-disk-last d))
                 (fn-osch-text " ms")))
        ((eq word :recovered-from-stall)
         (append (fn-osch-text "disk recovered after a stall: the barrier completed after ")
                 (fn-osch-decimal (fn-otm-disk-last d))
                 (fn-osch-text " ms; the articles whose posters were told uncertain are stored")))
        (t nil)))

; The reason every try-later names: how long the write has waited and the
; deadline it passed.
(defun fn-otm-reason (d now)
  (declare (xargs :guard t))
  (append (fn-osch-text (if (fn-otm-disk-stall-due-p d now)
                            "the disk is stalled (a write has waited "
                          "the disk is slow (a write has waited "))
          (fn-osch-decimal (fn-otm-disk-elapsed d now))
          (fn-osch-text " ms, deadline ")
          (fn-osch-decimal (fn-otm-disk-deadline d))
          (fn-osch-text " ms)")))

; The shed POST's reply after its article: RFC 3977 section 6.3.1's
; subsequent refusal (441; 436 is IHAVE's code, section 6.3.2), with the
; reason.  Nothing was stored.
(defun fn-otm-shed-line (d now)
  (declare (xargs :guard t))
  (append (fn-osch-text "441 posting failed; ")
          (fn-otm-reason d now)
          (fn-osch-text ": nothing was stored, try again later")
          (list 13 10)))

; The POST command's reply while the disk sheds (slice 2): RFC 3977 section
; 6.3.1's initial refusal, 440, before the client sends the article.
(defun fn-otm-post-command-line (d now)
  (declare (xargs :guard t))
  (append (fn-osch-text "440 posting not permitted now; ")
          (fn-otm-reason d now)
          (fn-osch-text ", try again later")
          (list 13 10)))

; -----------------------------------------------------------------------------
; The scheduler's value: (OCP DISK CLOCK).  CLOCK is the recorded time
; (design section 3.7): (NOW REGRESSIONS JSEQ), NOW the largest reading the
; host appended, REGRESSIONS how many readings came in below it, JSEQ the
; decision journal's sequence number (every event the value takes is one
; journal entry).  Every disk decision reads NOW; no entry below takes the
; environment's time.

(defun fn-otm-ocp (s)
  (declare (xargs :guard t))
  (if (consp s) (car s) nil))

(defun fn-otm-disk (s)
  (declare (xargs :guard t))
  (if (and (consp s) (consp (cdr s))) (cadr s) (fn-otm-disk-init)))

(defun fn-otm-clock (s)
  (declare (xargs :guard t))
  (if (and (consp s) (consp (cdr s)) (consp (cddr s))) (caddr s) nil))

(defun fn-otm-c-now (c)
  (declare (xargs :guard t))
  (if (consp c) (nfix (car c)) 0))

(defun fn-otm-c-regressions (c)
  (declare (xargs :guard t))
  (if (and (consp c) (consp (cdr c))) (nfix (cadr c)) 0))

(defun fn-otm-c-jseq (c)
  (declare (xargs :guard t))
  (if (and (consp c) (consp (cdr c)) (consp (cddr c))) (nfix (caddr c)) 0))

(defun fn-otm-now (s)
  (declare (xargs :guard t))
  (fn-otm-c-now (fn-otm-clock s)))

(defun fn-otm-regressions (s)
  (declare (xargs :guard t))
  (fn-otm-c-regressions (fn-otm-clock s)))

(defun fn-otm-jseq (s)
  (declare (xargs :guard t))
  (fn-otm-c-jseq (fn-otm-clock s)))

(defun fn-otm-make (ocp d clock)
  (declare (xargs :guard t))
  (list ocp d clock))

(defun fn-otm-init ()
  (declare (xargs :guard t))
  (fn-otm-make (fn-ocp-init) (fn-otm-disk-init) (list 0 0 0)))

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

; The disk's events.  Each carries the host's READING, recorded first --
; kept monotone: a reading below the recorded time is counted by name
; (:clock-regressed) and moves nothing back -- and the event then applies at
; the recorded time; the journal sequence advances by one (the event is one
; entry).  KIND :clock (a clock event: the committer's, at each wake while
; a barrier is pending, or on demand before a decision), :served (a served
; read's clock reading, host/native/owner.lisp fnn-owner-advance-clock: a
; clock event whose ARG, the wall reading, the journal keeps for the
; owner's own clock), :issue (ARG the limits (D H C)) or :return.  The core
; reads the disk D and the clock C only: (mv WORD D' C').
(defun fn-otm-dc-event (d c kind reading arg)
  (declare (xargs :guard t))
  (let* ((r (nfix reading))
         (before (fn-otm-c-now c))
         (regressed (< r before))
         (now (if regressed before r))
         (c2 (list now
                   (if regressed (+ 1 (fn-otm-c-regressions c)) (fn-otm-c-regressions c))
                   (+ 1 (fn-otm-c-jseq c)))))
    (mv-let (word d2)
      (cond ((or (eq kind :clock) (eq kind :served)) (fn-otm-disk-tick d now))
            ((eq kind :issue) (fn-otm-disk-issue d now arg))
            ((eq kind :return) (fn-otm-disk-return d now))
            (t (mv :fault d)))
      (mv (if (and (eq word :none) regressed) :clock-regressed word) d2 c2))))

; Over the whole value: (mv WORD S'), the pipeline's value kept.
(defun fn-otm-disk-event (s kind reading arg)
  (declare (xargs :guard t))
  (mv-let (word d2 c2) (fn-otm-dc-event (fn-otm-disk s) (fn-otm-clock s) kind reading arg)
    (mv word (fn-otm-make (fn-otm-ocp s) d2 c2))))

(defun fn-otm-admit-post (s)
  (declare (xargs :guard t))
  (fn-otm-disk-admit (fn-otm-disk s) (fn-otm-now s)))

(defun fn-otm-mode (s)
  (declare (xargs :guard t))
  (fn-otm-disk-mode (fn-otm-disk s) (fn-otm-now s)))

(defun fn-otm-wait-ms (s)
  (declare (xargs :guard t))
  (fn-otm-disk-wait-ms (fn-otm-disk s) (fn-otm-now s)))

(defun fn-otm-log-line (s word)
  (declare (xargs :guard t))
  (fn-otm-disk-log-line word (fn-otm-disk s) (fn-otm-now s)))

(defun fn-otm-shed-reply (s)
  (declare (xargs :guard t))
  (fn-otm-shed-line (fn-otm-disk s) (fn-otm-now s)))

(defun fn-otm-post-command-reply (s)
  (declare (xargs :guard t))
  (fn-otm-post-command-line (fn-otm-disk s) (fn-otm-now s)))

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
  (equal (fn-otm-disk-pending (fn-otm-disk-make p since dl slow last maxl ep stall cad stalled stalls)) (if p t nil)))

(defthm fn-otm-disk-since-of-make
  (equal (fn-otm-disk-since (fn-otm-disk-make p since dl slow last maxl ep stall cad stalled stalls)) (nfix since)))

(defthm fn-otm-disk-deadline-of-make
  (equal (fn-otm-disk-deadline (fn-otm-disk-make p since dl slow last maxl ep stall cad stalled stalls)) (fn-otm-deadline-of-limit dl)))

(defthm fn-otm-disk-slow-of-make
  (equal (fn-otm-disk-slow (fn-otm-disk-make p since dl slow last maxl ep stall cad stalled stalls)) (if slow t nil)))

(defthm fn-otm-disk-last-of-make
  (equal (fn-otm-disk-last (fn-otm-disk-make p since dl slow last maxl ep stall cad stalled stalls)) (nfix last)))

(defthm fn-otm-disk-max-of-make
  (equal (fn-otm-disk-max (fn-otm-disk-make p since dl slow last maxl ep stall cad stalled stalls)) (nfix maxl)))

(defthm fn-otm-disk-episodes-of-make
  (equal (fn-otm-disk-episodes (fn-otm-disk-make p since dl slow last maxl ep stall cad stalled stalls)) (nfix ep)))

(defthm fn-otm-disk-stall-of-make
  (equal (fn-otm-disk-stall (fn-otm-disk-make p since dl slow last maxl ep stall cad stalled stalls)) (max (fn-otm-deadline-of-limit dl) (fn-otm-stall-of-limit (nfix stall)))))

(defthm fn-otm-disk-cadence-of-make
  (equal (fn-otm-disk-cadence (fn-otm-disk-make p since dl slow last maxl ep stall cad stalled stalls)) (fn-otm-cadence-of-limit cad)))

(defthm fn-otm-disk-stalled-of-make
  (equal (fn-otm-disk-stalled (fn-otm-disk-make p since dl slow last maxl ep stall cad stalled stalls)) (if stalled t nil)))

(defthm fn-otm-disk-stalls-of-make
  (equal (fn-otm-disk-stalls (fn-otm-disk-make p since dl slow last maxl ep stall cad stalled stalls)) (nfix stalls)))

(defthm fn-otm-deadline-of-limit-of-deadline
  (equal (fn-otm-deadline-of-limit (fn-otm-disk-deadline d)) (fn-otm-disk-deadline d)))

(defthm fn-otm-cadence-of-limit-of-cadence
  (equal (fn-otm-cadence-of-limit (fn-otm-disk-cadence d)) (fn-otm-disk-cadence d)))

(defthm fn-otm-disk-deadline-posp
  (posp (fn-otm-disk-deadline d))
  :rule-classes :type-prescription)

(defthm fn-otm-disk-cadence-posp
  (posp (fn-otm-disk-cadence d))
  :rule-classes :type-prescription)

(defthm fn-otm-disk-stall-posp
  (posp (fn-otm-disk-stall d))
  :rule-classes :type-prescription)

(defthm fn-otm-deadline-of-limit-posp
  (posp (fn-otm-deadline-of-limit n))
  :rule-classes :type-prescription)

(defthm fn-otm-disk-since-natp
  (natp (fn-otm-disk-since d))
  :rule-classes :type-prescription)

;; The stall deadline is never below the slow one.
(defthm fn-otm-disk-deadline-at-most-stall
  (<= (fn-otm-disk-deadline d) (fn-otm-disk-stall d))
  :rule-classes :linear)

(defthm fn-otm-stall-of-limit-of-stall
  (equal (fn-otm-stall-of-limit (fn-otm-disk-stall d)) (fn-otm-disk-stall d))
  :hints (("Goal" :in-theory (enable fn-otm-stall-of-limit))))

;; A stall recorded from the disk's own accessor reads back unchanged.
(defthm fn-otm-stall-of-make-of-stall
  (equal (max (fn-otm-deadline-of-limit (fn-otm-disk-deadline d))
              (fn-otm-stall-of-limit (nfix (fn-otm-disk-stall d))))
         (fn-otm-disk-stall d)))

(defthm fn-otm-of-make
  (and (equal (fn-otm-ocp (fn-otm-make ocp d c)) ocp)
       (equal (fn-otm-disk (fn-otm-make ocp d c)) d)
       (equal (fn-otm-clock (fn-otm-make ocp d c)) c)))

(defthm fn-otm-now-of-list
  (and (equal (fn-otm-now (fn-otm-make ocp d (list n r j))) (nfix n))
       (equal (fn-otm-regressions (fn-otm-make ocp d (list n r j))) (nfix r))
       (equal (fn-otm-jseq (fn-otm-make ocp d (list n r j))) (nfix j))))

(defthm fn-otm-c-of-list
  (and (equal (fn-otm-c-now (list n r j)) (nfix n))
       (equal (fn-otm-c-regressions (list n r j)) (nfix r))
       (equal (fn-otm-c-jseq (list n r j)) (nfix j))))

(defthm fn-otm-now-natp
  (natp (fn-otm-now s))
  :rule-classes :type-prescription)

(defthm fn-otm-jseq-natp
  (natp (fn-otm-jseq s))
  :rule-classes :type-prescription)

(local (in-theory (disable fn-otm-disk-make fn-otm-disk-pending fn-otm-disk-since
                           fn-otm-disk-deadline fn-otm-disk-slow fn-otm-disk-last
                           fn-otm-disk-max fn-otm-disk-episodes fn-otm-deadline-of-limit
                           fn-otm-disk-stall fn-otm-disk-cadence fn-otm-disk-stalled
                           fn-otm-disk-stalls fn-otm-stall-of-limit fn-otm-cadence-of-limit
                           fn-otm-make fn-otm-ocp fn-otm-disk fn-otm-clock fn-otm-now
                           fn-otm-regressions fn-otm-jseq fn-otm-c-now fn-otm-c-regressions
                           fn-otm-c-jseq
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
;; fnn-owner-disk-event calls from the committer through fn-otm-disk-step
;; (fn-otm-disk-step-unfolds).
(defthm fn-otm-disk-event-keeps-the-pipeline
  (equal (fn-otm-ocp (mv-nth 1 (fn-otm-disk-event s kind reading arg)))
         (fn-otm-ocp s))
  :hints (("Goal" :in-theory (e/d (fn-otm-now fn-otm-regressions fn-otm-jseq)
                                  (fn-otm-disk-issue fn-otm-disk-tick fn-otm-disk-return)))))

;; KEYSTONE (the recorded time never goes backwards).  The recorded time is
;; monotone, a reading below it is counted by name and moves nothing back,
;; and every event is one journal entry (design section 3.7).  The subject
;; is fn-otm-disk-event, every clock event the host appends.
(defthm fn-otm-recorded-time-is-monotone
  (let ((s2 (mv-nth 1 (fn-otm-disk-event s kind reading arg))))
    (and (<= (fn-otm-now s) (fn-otm-now s2))
         (equal (fn-otm-now s2) (max (fn-otm-now s) (nfix reading)))
         (equal (fn-otm-regressions s2)
                (if (< (nfix reading) (fn-otm-now s))
                    (+ 1 (fn-otm-regressions s))
                  (fn-otm-regressions s)))
         (equal (fn-otm-jseq s2) (+ 1 (fn-otm-jseq s)))))
  :hints (("Goal" :in-theory (e/d (fn-otm-now fn-otm-regressions fn-otm-jseq)
                                  (fn-otm-disk-issue fn-otm-disk-tick fn-otm-disk-return)))))

;; The disk event at a reading: the core step at the recorded time.
(defthm fn-otm-disk-event-unfolds
  (implies (<= (fn-otm-now s) (nfix reading))
           (and (equal (fn-otm-disk (mv-nth 1 (fn-otm-disk-event s kind reading arg)))
                       (cond ((or (eq kind :clock) (eq kind :served))
                              (mv-nth 1 (fn-otm-disk-tick (fn-otm-disk s) (nfix reading))))
                             ((eq kind :issue)
                              (mv-nth 1 (fn-otm-disk-issue (fn-otm-disk s) (nfix reading) arg)))
                             ((eq kind :return)
                              (mv-nth 1 (fn-otm-disk-return (fn-otm-disk s) (nfix reading))))
                             (t (fn-otm-disk s))))
                (equal (fn-otm-now (mv-nth 1 (fn-otm-disk-event s kind reading arg)))
                       (nfix reading))
                (equal (mv-nth 0 (fn-otm-disk-event s kind reading arg))
                       (cond ((or (eq kind :clock) (eq kind :served))
                              (mv-nth 0 (fn-otm-disk-tick (fn-otm-disk s) (nfix reading))))
                             ((eq kind :issue)
                              (mv-nth 0 (fn-otm-disk-issue (fn-otm-disk s) (nfix reading) arg)))
                             ((eq kind :return)
                              (mv-nth 0 (fn-otm-disk-return (fn-otm-disk s) (nfix reading))))
                             (t :fault)))))
  :hints (("Goal" :in-theory (e/d (fn-otm-now fn-otm-regressions fn-otm-jseq)
                                  (fn-otm-disk-issue fn-otm-disk-tick fn-otm-disk-return)))))

;; -----------------------------------------------------------------------------
;; The disk machine.

(local (in-theory (e/d (fn-otm-now fn-otm-regressions fn-otm-jseq) (fn-otm-disk-elapsed))))

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

;; A stalled disk is a slow one: past H is past D.
(defthm fn-otm-stall-due-is-overdue
  (implies (fn-otm-disk-stall-due-p d now) (fn-otm-disk-overdue-p d now))
  :rule-classes :forward-chaining)

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

;; The admission is the mode's: shed exactly in :slow and :stalled.
(defthm fn-otm-admit-is-the-mode
  (iff (equal (fn-otm-admit-post s) :shed)
         (member-equal (fn-otm-mode s) '(:slow :stalled)))
  :hints (("Goal" :use ((:instance fn-otm-disk-deadline-at-most-stall (d (fn-otm-disk s)))))))

;; The backpressure always has its reason on the page: a POST is shed
;; exactly when health and status, rendered from the same value, print the
;; disk-slow or disk-stalled line.
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
 (defthm fn-otm-take-of-append-append
   (implies (and (true-listp a) (<= (nfix n) (len a)))
            (equal (take n (append (append a b) c)) (take n a)))))

(local
 (defthm fn-otm-len-of-append-left
   (<= (len a) (len (append a b)))
   :rule-classes :linear))

(local
 (defthm fn-otm-len-of-append-append
   (<= (len a) (len (append (append a b) c)))
   :rule-classes :linear))

(local
 (defthm fn-otm-disk-tag-cases
   (and (implies (fn-otm-disk-stall-due-p d now)
                 (equal (fn-otm-disk-tag d now)
                        (fn-osch-chars-octets (coerce "disk stalled: barrier " 'list))))
        (implies (and (fn-otm-disk-overdue-p d now) (not (fn-otm-disk-stall-due-p d now)))
                 (equal (fn-otm-disk-tag d now)
                        (fn-osch-chars-octets (coerce "disk slow: barrier " 'list))))
        (implies (not (fn-otm-disk-overdue-p d now))
                 (equal (fn-otm-disk-tag d now)
                        (fn-osch-chars-octets (coerce "disk ok:" 'list)))))
   :hints (("Goal" :in-theory (enable fn-osch-text)))))

(local
 (defthm fn-otm-disk-overdue-p-of-nfix
   (and (equal (fn-otm-disk-overdue-p d (nfix now)) (fn-otm-disk-overdue-p d now))
        (equal (fn-otm-disk-stall-due-p d (nfix now)) (fn-otm-disk-stall-due-p d now)))
   :hints (("Goal" :in-theory (enable fn-otm-disk-elapsed)))))

;; The tag's first six octets say which: "disk s" (slow or stalled) or not.
(local
 (defthm fn-otm-disk-tag-prefix
   (and (true-listp (fn-otm-disk-tag d now))
        (iff (equal (take 6 (fn-otm-disk-tag d now)) '(100 105 115 107 32 115))
             (fn-otm-disk-overdue-p d now)))
   :hints (("Goal" :in-theory (e/d (fn-osch-text) (fn-otm-disk-overdue-p fn-otm-disk-stall-due-p))
            :cases ((fn-otm-disk-stall-due-p d now) (fn-otm-disk-overdue-p d now))))))

(local
 (defthm fn-otm-disk-tag-len
   (<= 6 (len (fn-otm-disk-tag d now)))
   :rule-classes :linear
   :hints (("Goal" :in-theory (e/d (fn-osch-text) (fn-otm-disk-overdue-p fn-otm-disk-stall-due-p))))))

(defthm fn-otm-shed-iff-slow
  (iff (equal (fn-otm-admit-post s) :shed)
       (fn-otm-slow-line-p (fn-otm-disk-lines s)))
  :hints (("Goal" :in-theory (disable fn-otm-disk-body fn-otm-disk-tag fn-otm-disk-overdue-p
                                      fn-otm-disk-stall-due-p fn-osch-chars-octets))))

;; Recovery needs no operator action: after the completion event the node
;; admits every POST, and no later clock event makes the disk slow again
;; until the next barrier is issued.
(defthm fn-otm-return-recovers
  (implies (fn-otm-disk-pending (fn-otm-disk s))
           (let ((s2 (mv-nth 1 (fn-otm-disk-event s :return reading arg))))
             (and (equal (fn-otm-admit-post s2) :admit)
                  (not (fn-otm-disk-pending (fn-otm-disk s2)))
                  (not (fn-otm-disk-stalled (fn-otm-disk s2)))
                  (member-equal (mv-nth 0 (fn-otm-disk-event s :return reading arg))
                                '(:returned :recovered :recovered-from-stall))))))

;; The completion after a stall is named: the host's log says the articles
;; whose posters were told uncertain are stored.
(defthm fn-otm-return-after-a-stall-is-named
  (implies (and (fn-otm-disk-pending (fn-otm-disk s)) (fn-otm-disk-stalled (fn-otm-disk s)))
           (equal (mv-nth 0 (fn-otm-disk-event s :return reading arg)) :recovered-from-stall)))

(defthm fn-otm-clock-event-never-issues
  (implies (not (fn-otm-disk-pending (fn-otm-disk s)))
           (let ((s2 (mv-nth 1 (fn-otm-disk-event s :clock reading arg))))
             (and (not (fn-otm-disk-pending (fn-otm-disk s2)))
                  (equal (fn-otm-admit-post s2) :admit)))))

;; The completion's latency is recorded: the last barrier's latency is the
;; recorded completion time's distance from the recorded issue time.
(defthm fn-otm-return-records-the-latency
  (implies (and (fn-otm-disk-pending (fn-otm-disk s)) (natp reading)
                (<= (fn-otm-now s) reading)
                (<= (fn-otm-disk-since (fn-otm-disk s)) reading))
           (equal (fn-otm-disk-last
                   (fn-otm-disk (mv-nth 1 (fn-otm-disk-event s :return reading arg))))
                  (- reading (fn-otm-disk-since (fn-otm-disk s))))))

;; The committer's timed wait reaches the deadline: a clock event appended
;; WAIT-MS after the recorded time (or later) from a pending barrier not yet
;; past D finds it past D -- the POSTs after it are shed -- and enters :slow
;; or, when the same reading is past H, :stalled.
(defthm fn-otm-wait-reaches-the-deadline
  (implies (and (fn-otm-wait-ms s)
                (not (fn-otm-disk-overdue-p (fn-otm-disk s) (fn-otm-now s)))
                (natp reading)
                (<= (fn-otm-disk-since (fn-otm-disk s)) (fn-otm-now s))
                (<= (+ (fn-otm-now s) (fn-otm-wait-ms s)) reading))
           (let ((s2 (mv-nth 1 (fn-otm-disk-event s :clock reading arg))))
             (and (posp (fn-otm-wait-ms s))
                  (equal (fn-otm-admit-post s2) :shed)
                  (member-equal (mv-nth 0 (fn-otm-disk-event s :clock reading arg))
                                '(:became-slow :became-stalled :none))))))

;; A barrier is issued only when none is pending (one in flight at a time),
;; and an issued barrier is pending from the recorded time of its issue,
;; with the limits the host read.
(defthm fn-otm-issue-only-when-none-pending
  (iff (equal (mv-nth 0 (fn-otm-disk-event s :issue reading arg)) :issued)
       (not (fn-otm-disk-pending (fn-otm-disk s)))))

(defthm fn-otm-issue-is-pending-and-admits
  (implies (and (not (fn-otm-disk-pending (fn-otm-disk s))) (natp reading)
                (<= (fn-otm-now s) reading))
           (let ((s2 (mv-nth 1 (fn-otm-disk-event s :issue reading arg))))
             (and (fn-otm-disk-pending (fn-otm-disk s2))
                  (not (fn-otm-disk-stalled (fn-otm-disk s2)))
                  (equal (fn-otm-disk-since (fn-otm-disk s2)) reading)
                  (equal (fn-otm-disk-deadline (fn-otm-disk s2))
                         (car (fn-otm-limits arg)))
                  (equal (fn-otm-disk-stall (fn-otm-disk s2))
                         (cadr (fn-otm-limits arg)))
                  (equal (fn-otm-disk-cadence (fn-otm-disk s2))
                         (caddr (fn-otm-limits arg)))
                  (equal (fn-otm-admit-post s2) :admit))))
  :hints (("Goal" :in-theory (enable fn-otm-limits fn-otm-deadline-of-limit
                                     fn-otm-stall-of-limit fn-otm-cadence-of-limit))))

; KEYSTONE (PRF-311): reads and status never wait for the barrier.
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
  ; KEYSTONE (PRF-311).  While the batch's barrier is pending and a reader
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


;; =============================================================================
;; Slice 2: the stall deadline H, the posters' uncertain answer, and F4-W.

;; The stall's release (host/native/owner.lisp fnn-owner-commit-pipeline, at
;; the :became-stalled word): every member of the batch in flight and of
;; the next batch START-NEXT staged is answered as fn-ocs-member-release
;; names under the action :stalled -- its own uncertain reply and a close,
;; or the close alone -- never its acceptance or refusal.  Their bytes may
;; still become durable: the barrier is pending, not failed.  RFC 3977
;; section 6.3.1 asks exactly that of the client ("SHOULD either check
;; whether the article was successfully posted before resending"), which is
;; what the uncertain reply says.
(defun fn-otm-stall-releases (outcomes)
  (declare (xargs :guard t))
  (fn-ocs-member-releases :stalled outcomes))

(local
 (defthm fn-otm-stall-release-is-uncertain
   (member-equal (fn-ocs-member-release :stalled word renderable)
                 '(:own-uncertain :uncertain-reply :close))
   :hints (("Goal" :in-theory (enable fn-ocs-member-release)))))

(local
 (defthm fn-otm-stall-release-never-rendered
   (not (equal (fn-ocs-member-release :stalled word renderable) :rendered))
   :hints (("Goal" :in-theory (enable fn-ocs-member-release)))))

(defun fn-otm-uncertain-releases-p (rs)
  (declare (xargs :guard t))
  (if (consp rs)
      (and (member-equal (car rs) '(:own-uncertain :uncertain-reply :close))
           (fn-otm-uncertain-releases-p (cdr rs)))
    t))

;; KEYSTONE (PRF-311, slice 2).  When H fires no member is told acceptance
;; or refusal: every release is uncertain (:own-uncertain, :uncertain-reply
;; or :close), one per member.  With fn-otm-disk-event-keeps-the-pipeline
;; (the stall produced no :complete and no phase change), a member's own
;; outcome is still told only in a COMPLETE after a fenced barrier
;; (fn-ocs-members-told-only-after-the-barrier) -- and a member told
;; uncertain here is not answered again (the host drops it from the
;; batch's members).  The subject is fn-otm-stall-releases, which the
;; committer calls.
(defthm fn-otm-stall-tells-no-member-its-outcome
  (and (not (member-equal :rendered (fn-otm-stall-releases outcomes)))
       (equal (len (fn-otm-stall-releases outcomes)) (len outcomes))
       (fn-otm-uncertain-releases-p (fn-otm-stall-releases outcomes)))
  :hints (("Goal" :in-theory (e/d (fn-otm-stall-releases fn-ocs-member-releases)
                                  (fn-ocs-member-release))
           :induct (len outcomes))))

;; -----------------------------------------------------------------------------
;; F4-W: every POST is answered accepted, refused, uncertain or try-later
;; within H + L of its article's arrival (design section 4), L the lateness
;; of one committer wake -- its timed wait expiring later than asked (the
;; thread descheduled).  The design's H + quantum + cadence is this bound
;; with L <= cadence and the release's quantum added: the wait below never
;; reaches past H, so the cadence does not appear.
;;
;; A POST whose article arrived while the disk sheds is refused at once
;; (fn-otm-shed-iff-slow; its command answered 440 first).  One admitted
;; before D joined the batch in flight or the next one (both pending on
;; this barrier), or is queued behind them; each is told at the barrier's
;; completion (accepted or refused, or uncertain after a failed barrier),
;; or, if that has not come, at the stall: the members uncertain, the
;; queued ones refused try-later.  What is proved here is the model half:
;; the committer's clock events, each within its wait plus L of the recorded
;; time, reach the stall -- the :became-stalled word -- at a recorded time at
;; most since + H + L, however long the device takes; the host answers the
;; members in that wake.  Hypothesis (h5) of the design: the committer is
;; not blocked on the device (it never is: the syncer is).

;; The committer's wait never reaches past H.
(defthm fn-otm-wait-stays-within-the-stall
  (implies (and (fn-otm-disk-pending (fn-otm-disk s))
                (<= (fn-otm-disk-since (fn-otm-disk s)) (fn-otm-now s))
                (not (fn-otm-disk-stall-due-p (fn-otm-disk s) (fn-otm-now s))))
           (<= (+ (fn-otm-now s) (fn-otm-wait-ms s))
               (+ (fn-otm-disk-since (fn-otm-disk s)) (fn-otm-disk-stall (fn-otm-disk s)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-otm-disk-elapsed))))

;; One committer clock event at reading R: the value after it.
(defun fn-otm-clock-step (s r)
  (declare (xargs :guard t))
  (mv-let (w s2) (fn-otm-disk-event s :clock r nil)
    (declare (ignore w))
    s2))

(defun fn-otm-clock-word (s r)
  (declare (xargs :guard t))
  (mv-let (w s2) (fn-otm-disk-event s :clock r nil)
    (declare (ignore s2))
    w))

;; The committer's clock events: RS the readings, in order.
(defun fn-otm-clock-run (s rs)
  (declare (xargs :guard t :measure (len rs)))
  (if (consp rs)
      (fn-otm-clock-run (fn-otm-clock-step s (car rs)) (cdr rs))
    s))

;; The reading whose clock event entered :stalled, or nil.
(defun fn-otm-stall-reading (s rs)
  (declare (xargs :guard t :measure (len rs)))
  (if (consp rs)
      (if (eq (fn-otm-clock-word s (car rs)) :became-stalled)
          (nfix (car rs))
        (fn-otm-stall-reading (fn-otm-clock-step s (car rs)) (cdr rs)))
    nil))

;; Each reading is at or after the recorded time and at most the wait plus
;; LATE after it (the timed wait's expiry, or an earlier wake).
(defun fn-otm-clock-run-okp (s rs late)
  (declare (xargs :guard t :measure (len rs)))
  (if (consp rs)
      (and (natp (car rs))
           (<= (fn-otm-now s) (car rs))
           (<= (car rs) (+ (fn-otm-now s) (nfix (fn-otm-wait-ms s)) (nfix late)))
           (fn-otm-clock-run-okp (fn-otm-clock-step s (car rs)) (cdr rs) late))
    t))

(local
 (defthm fn-otm-tick-step-facts
   (implies (and (fn-otm-disk-pending (fn-otm-disk s))
                 (not (fn-otm-disk-stalled (fn-otm-disk s)))
                 (natp r) (<= (fn-otm-now s) r))
            (let ((w (fn-otm-clock-word s r))
                  (d2 (fn-otm-disk (fn-otm-clock-step s r))))
              (and (iff (equal w :became-stalled)
                        (fn-otm-disk-stall-due-p (fn-otm-disk s) r))
                   (equal (fn-otm-now (fn-otm-clock-step s r)) r)
                   (fn-otm-disk-pending d2)
                   (equal (fn-otm-disk-since d2) (fn-otm-disk-since (fn-otm-disk s)))
                   (equal (fn-otm-disk-stall d2) (fn-otm-disk-stall (fn-otm-disk s)))
                   (equal (fn-otm-disk-deadline d2) (fn-otm-disk-deadline (fn-otm-disk s)))
                   (equal (fn-otm-disk-cadence d2) (fn-otm-disk-cadence (fn-otm-disk s)))
                   (implies (not (fn-otm-disk-stall-due-p (fn-otm-disk s) r))
                            (not (fn-otm-disk-stalled d2)))
                   (iff (fn-otm-disk-stall-due-p d2 r)
                        (fn-otm-disk-stall-due-p (fn-otm-disk s) r)))))
   :hints (("Goal" :in-theory (enable fn-otm-clock-word fn-otm-clock-step
                                      fn-otm-disk-stall-due-p fn-otm-disk-overdue-p
                                      fn-otm-disk-elapsed)))))

(local
 (defthm fn-otm-stall-due-of-since
   (implies (and (fn-otm-disk-pending d) (natp r) (<= (fn-otm-disk-since d) r))
            (iff (fn-otm-disk-stall-due-p d r)
                 (<= (+ (fn-otm-disk-since d) (fn-otm-disk-stall d)) r)))
   :hints (("Goal" :in-theory (enable fn-otm-disk-stall-due-p fn-otm-disk-elapsed)))))

(local (in-theory (disable fn-otm-disk-event fn-otm-disk-stall-due-p fn-otm-clock-word
                           fn-otm-clock-step fn-otm-now fn-otm-regressions fn-otm-jseq)))

;; KEYSTONE F4-W (PRF-311, slice 2).  From a barrier pending and not yet past
;; H (since <= the recorded time), committer clock events each within its
;; wait plus LATE: if one of them entered :stalled (the posters told) its
;; reading is at most since + H + LATE; if none did, every reading so far
;; is before since + H.  The device's latency is not a quantity here.  The
;; subject is fn-otm-disk-event (the committer's :clock through
;; fn-otm-disk-step) with the wait fn-otm-wait-ms, both host-called in
;; host/native/owner.lisp fnn-owner-commit-pipeline.
(defthm fn-otm-f4w-stall-within-h
  (implies (and (fn-otm-disk-pending (fn-otm-disk s))
                (not (fn-otm-disk-stalled (fn-otm-disk s)))
                (<= (fn-otm-disk-since (fn-otm-disk s)) (fn-otm-now s))
                (not (fn-otm-disk-stall-due-p (fn-otm-disk s) (fn-otm-now s)))
                (fn-otm-clock-run-okp s rs late))
           (let ((r (fn-otm-stall-reading s rs))
                 (h (+ (fn-otm-disk-since (fn-otm-disk s))
                       (fn-otm-disk-stall (fn-otm-disk s)))))
             (and (implies r (<= r (+ h (nfix late))))
                  (implies (not r)
                           (and (not (fn-otm-disk-stalled (fn-otm-disk (fn-otm-clock-run s rs))))
                                (< (fn-otm-now (fn-otm-clock-run s rs)) h))))))
  :rule-classes nil
  :hints (("Goal" :induct (fn-otm-clock-run-okp s rs late)
           :in-theory (enable fn-otm-stall-reading fn-otm-clock-run fn-otm-clock-run-okp))
          ("Subgoal *1/1" :use ((:instance fn-otm-wait-stays-within-the-stall)))))

(in-theory (disable fn-otm-next fn-otm-observe fn-otm-commit-event fn-otm-committer-wake
                    fn-otm-disk-event fn-otm-admit-post fn-otm-mode fn-otm-wait-ms fn-otm-log-line
                    fn-otm-shed-reply fn-otm-post-command-reply fn-otm-health-lines
                    fn-otm-disk-lines fn-otm-stall-releases))
