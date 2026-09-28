; fn: a graceful stop drains the POSTs in flight to their replies (lane
; health-truth-stop, 2026-09-28; PKT-875, PRF-357).
;
; Before this book a SIGTERM made every I/O loop end its connections at
; once, while the committer still held a batch whose barrier had not
; returned: the batch then committed and its posters were told nothing but
; a closed socket (4 of 4 at one stop in planning/evidence/fitness-2026-09-28.md
; f2).  A client can only call that uncertain, and the article was stored.
;
; Now the stop is a DRAIN before the fence.  The owner stops accepting and
; stops stepping input (no new submission is queued), the I/O loops keep
; delivering, the committer keeps committing what is queued and in flight,
; and each member is told at its batch's COMPLETE as always
; (books/owner-commit-steps.lisp fn-ocs-members-told-only-after-the-barrier:
; 240 only after its barrier returned fenced).  The drain ends when nothing
; is in flight, no member awaits its reply and no reply is unsent.  If that
; does not happen by the DRAIN DEADLINE, the committer releases every member
; of the batches in flight as the stall does (books/owner-time-model.lisp
; fn-otm-stall-releases: uncertain, never accepted or refused;
; fn-otm-stall-tells-no-member-its-outcome) and sheds what is queued
; (refused try-later, nothing stored); the drain then waits at most the
; send grace for those replies to leave, and stops.
;
; The drain deadline is the live configuration's stall deadline H
; (`barrier-stall-ms', default 30,000 ms: fn-otm-limits): the operator's
; profile field for "a barrier pending this long is answered uncertain".  A
; member whose barrier has not returned at H is told uncertain whether or
; not the node is stopping; the stop never answers earlier than the stall
; would, and never later than H plus the grace.
;
; Every decision reads recorded time (design section 3.7): S0 is the gate's
; scheduler value at the drain's start and S at the observation, each after a
; clock event the host appended (host/native/owner.lisp
; fnn-owner-sched-snapshot).  The subject is fn-osd-drain-next (the step,
; fn-osd-drain-step, and whether the release was made), which
; host/native/owner.lisp fnn-owner-drain-service calls once per observation.
;
; THE BOUND (lane sigterm-hang, 2026-09-28).  The stop ends within H plus
; the grace plus one observation, whatever state the connections are in:
; AWAITING and UNSENT are arbitrary in fn-osd-drain-stops-by-the-deadline,
; and a connection mid-command (a POST's article not yet complete) is in
; neither -- it awaits no completion and holds no reply -- so it never holds
; the drain; the fence then closes it (its incomplete article is not
; stored and is owed nothing).  A member whose article committed is told its
; reply at its COMPLETE, or uncertain at the release.  Batch AZ found the
; host never reaching this drain in `once' mode with such a client
; (host/native/mux.lisp fnn-mux-serve-once waited for the client's end,
; which the loops no longer cause at a SIGTERM); the wait now returns at the
; SIGTERM as the accept loops do.  Outside the bound: the fence's own
; :control quantum waits for a barrier the device never returns (the
; process's exit, never a reply; a kill -9 is then a crash point).
(in-package "ACL2")
(include-book "owner-time-model")

; The send grace: how long, after the release at the deadline, the drain
; waits for the uncertain replies to leave.  The I/O loops' own send deadline
; (host/native/mux.lisp +fnn-mux-send-seconds+, 10 s): a reply a client does
; not read within it is not waited for at a stop either.
(defconst *fn-osd-grace-ms* 10000)

; How often the host observes while it drains (milliseconds).
(defconst *fn-osd-poll-ms* 100)

(defun fn-osd-poll-ms ()
  (declare (xargs :guard t))
  *fn-osd-poll-ms*)

; The drain deadline for the configuration's limits (D H C): H.
(defun fn-osd-deadline (limits)
  (declare (xargs :guard t))
  (cadr (fn-otm-limits limits)))

(defthm fn-osd-deadline-posp
  (posp (fn-osd-deadline limits))
  :rule-classes :type-prescription)

; The deadline (H of the same limits) is at least D: the drain never
; answers a member uncertain before the disk would be called slow.
(defthm fn-osd-deadline-is-past-the-slow-deadline
  (<= (car (fn-otm-limits limits)) (fn-osd-deadline limits))
  :rule-classes nil)

(defun fn-osd-elapsed (s0 s)
  (declare (xargs :guard t))
  (nfix (- (fn-otm-now s) (fn-otm-now s0))))

; A batch is in flight in S: staged, fenced or failed, its COMPLETE not yet
; run (books/owner-commit-steps.lisp fn-ocs-in-flight-p over the gate's phase).
(defun fn-osd-in-flight-p (s)
  (declare (xargs :guard t))
  (fn-ocs-in-flight-p (fn-otm-phase s)))

; The members of the batches in flight were told uncertain: the pending
; barrier passed its stall deadline H (fn-otm-disk-stalled: the committer
; then releases both batches by fn-otm-stall-releases, as the disk's own
; answer, stopping or not).
(defun fn-osd-stall-told-p (s)
  (declare (xargs :guard t))
  (fn-otm-disk-stalled (fn-otm-disk s)))

; Everything owed has been told: no member awaits (AWAITING, the waiting
; connections plus the queued submissions), no reply is unsent (UNSENT, the
; connections holding a completion's reply not yet written), and no batch is
; in flight -- or its members were released, by this drain's release or by
; the stall.  A released member still awaiting its delivery counts in
; AWAITING, so the release is quiet only once each was handed its reply.
(defun fn-osd-quiet-p (s awaiting unsent released)
  (declare (xargs :guard t))
  (and (zp (nfix awaiting)) (zp (nfix unsent))
       (or (and released t) (not (fn-osd-in-flight-p s))
           (fn-osd-stall-told-p s))))

(in-theory (disable fn-osd-quiet-p fn-osd-deadline fn-osd-elapsed fn-osd-in-flight-p
                    fn-osd-stall-told-p))

; The drain's step at the observation (S AWAITING UNSENT) with the drain
; started at S0 under LIMITS, RELEASED whether the deadline's release was
; made: :stop (fence and close), :release (tell the members in flight
; uncertain and shed the queue: the committer's release), or :wait.
(defun fn-osd-drain-step (s0 s limits awaiting unsent released)
  (declare (xargs :guard t))
  (let ((elapsed (fn-osd-elapsed s0 s))
        (h (fn-osd-deadline limits)))
    (cond ((fn-osd-quiet-p s awaiting unsent released) :stop)
          ((< elapsed h) :wait)
          ((not released) :release)
          ((< elapsed (+ h *fn-osd-grace-ms*)) :wait)
          (t :stop))))

; The service log's lines for the drain (the host writes each once).
(defun fn-osd-log-line (word s0 s limits awaiting)
  (declare (xargs :guard t))
  (cond ((eq word :start)
         (append (fn-osch-text "stopping: answering the posts in flight first (deadline ")
                 (fn-osch-decimal (fn-osd-deadline limits))
                 (fn-osch-text " ms); no new command is read")))
        ((eq word :release)
         (append (fn-osch-text "stopping: the drain deadline passed after ")
                 (fn-osch-decimal (fn-osd-elapsed s0 s))
                 (fn-osch-text " ms; the posts in flight are told the outcome is uncertain")))
        ((eq word :stop)
         (append (fn-osch-text "stopping: drained after ")
                 (fn-osch-decimal (fn-osd-elapsed s0 s))
                 (fn-osch-text " ms")
                 (fn-osch-kv "unanswered" awaiting)))
        (t nil)))

; -----------------------------------------------------------------------------
; Theorems

(defthm fn-osd-drain-step-cases
  (member-equal (fn-osd-drain-step s0 s limits awaiting unsent released)
                '(:stop :release :wait))
  :rule-classes nil
  :hints (("Goal" :in-theory '(fn-osd-drain-step member-equal))))

; KEYSTONE (the stop closes no connection that is owed a reply before the
; deadline).  The subject is fn-osd-drain-step (host/native/owner.lisp
; fnn-owner-drain-service: its :stop is the only way the drain reaches the
; fence, fnn-owner-stop-service).  It answers :stop only when nothing is
; owed -- no member awaits, no reply is unsent, and no batch is in flight
; unless its members were released (by this drain or by the stall) -- or
; after the release, past the deadline and its grace.  With fn-ocs-members-told-only-after-the-barrier
; (a member is told 240 only in the COMPLETE after its barrier returned
; fenced), every member whose batch fenced during the drain is told its
; reply before its connection closes.
(defthm fn-osd-stops-only-when-nothing-is-owed
  (implies (equal (fn-osd-drain-step s0 s limits awaiting unsent released) :stop)
           (or (fn-osd-quiet-p s awaiting unsent released)
               (and released
                    (<= (+ (fn-osd-deadline limits) *fn-osd-grace-ms*)
                        (fn-osd-elapsed s0 s)))))
  :rule-classes nil
  :hints (("Goal" :in-theory '(fn-osd-drain-step))))

; KEYSTONE (no member is told uncertain before the deadline).  :release --
; the committer's fn-otm-stall-releases of every member in flight -- only
; once, and only at or past H since the drain began.  Before H a member in
; flight is pending: it is told at its COMPLETE.
(defthm fn-osd-releases-only-at-the-deadline
  (implies (equal (fn-osd-drain-step s0 s limits awaiting unsent released) :release)
           (and (not released)
                (<= (fn-osd-deadline limits) (fn-osd-elapsed s0 s))
                (not (fn-osd-quiet-p s awaiting unsent released))))
  :rule-classes nil
  :hints (("Goal" :in-theory '(fn-osd-drain-step))))

; KEYSTONE (the drain ends).  At H, anything still owed is released; at H
; plus the grace after the release, the drain stops.  With the host's
; observation every *fn-osd-poll-ms*, a stop is reached within H + grace +
; one poll of the SIGTERM.
(defthm fn-osd-drain-ends-by-the-deadline
  (and (implies (and (not released)
                     (<= (fn-osd-deadline limits) (fn-osd-elapsed s0 s))
                     (not (fn-osd-quiet-p s awaiting unsent released)))
                (equal (fn-osd-drain-step s0 s limits awaiting unsent released)
                       :release))
       (implies (and released
                     (<= (+ (fn-osd-deadline limits) *fn-osd-grace-ms*)
                         (fn-osd-elapsed s0 s)))
                (equal (fn-osd-drain-step s0 s limits awaiting unsent released)
                       :stop)))
  :rule-classes nil
  :hints (("Goal" :in-theory '(fn-osd-drain-step))))

;; ----------------------------------------------------------------------------
;; The host's call: the step and whether the release was made (the drain's
;; only state besides S0 and LIMITS).

(defun fn-osd-drain-next (s0 s limits awaiting unsent released)
  (declare (xargs :guard t))
  (let ((step (fn-osd-drain-step s0 s limits awaiting unsent released)))
    (mv step (or (and released t) (eq step :release)))))

(defthm fn-osd-drain-next-step-unfolds
  (equal (mv-nth 0 (fn-osd-drain-next s0 s limits awaiting unsent released))
         (fn-osd-drain-step s0 s limits awaiting unsent released))
  :hints (("Goal" :in-theory '(fn-osd-drain-next mv-nth))))

;; The drain over a sequence of observations, each (S AWAITING UNSENT) as
;; fnn-owner-drain-service takes them: the number taken until :stop, or nil
;; if it has not stopped by the last.
(defun fn-osd-obs-s (o)
  (declare (xargs :guard t))
  (and (consp o) (car o)))
(defun fn-osd-obs-awaiting (o)
  (declare (xargs :guard t))
  (and (consp o) (consp (cdr o)) (cadr o)))
(defun fn-osd-obs-unsent (o)
  (declare (xargs :guard t))
  (and (consp o) (consp (cdr o)) (consp (cddr o)) (caddr o)))

(defun fn-osd-drain-run (s0 obs limits released)
  (declare (xargs :guard t))
  (if (atom obs)
      nil
    (let ((o (car obs)))
      (mv-let (step released2)
        (fn-osd-drain-next s0 (fn-osd-obs-s o) limits (fn-osd-obs-awaiting o)
                           (fn-osd-obs-unsent o) released)
        (if (eq step :stop)
            1
          (let ((k (fn-osd-drain-run s0 (cdr obs) limits released2)))
            (and k (+ 1 k))))))))

;; An observation at or past the deadline and its grace since S0.
(defun fn-osd-past-grace-p (s0 o limits)
  (declare (xargs :guard t))
  (<= (+ (fn-osd-deadline limits) *fn-osd-grace-ms*)
      (fn-osd-elapsed s0 (fn-osd-obs-s o))))

(local
 (defthm fn-osd-drain-run-two-past-grace
   (implies (and (consp (cdr obs))
                 (fn-osd-past-grace-p s0 (car obs) limits)
                 (fn-osd-past-grace-p s0 (cadr obs) limits))
            (let ((k (fn-osd-drain-run s0 obs limits released)))
              (and (posp k) (<= k 2))))
   :rule-classes nil
   :hints (("Goal" :expand ((fn-osd-drain-run s0 obs limits released)
                            (fn-osd-drain-run s0 (cdr obs) limits t))
                   :in-theory (enable fn-osd-drain-next fn-osd-past-grace-p
                                      fn-osd-drain-step)))))

(local
 (defun fn-osd-drain-run-induct (i obs released s0 limits)
   (if (or (zp i) (atom obs))
       (list obs released)
     (mv-let (step released2)
       (fn-osd-drain-next s0 (fn-osd-obs-s (car obs)) limits
                          (fn-osd-obs-awaiting (car obs))
                          (fn-osd-obs-unsent (car obs))
                          released)
       (declare (ignore step))
       (fn-osd-drain-run-induct (1- i) (cdr obs) released2 s0 limits)))))

; KEYSTONE (the stop terminates within the deadline, for any connection
; state).  For any observations -- any AWAITING and UNSENT, so any number of
; connections mid-article, mid-commit or holding an unread reply -- if the
; I-th and the next both lie at or past H plus the grace, the drain has
; stopped by the (I+2)-th: at the first it releases (if it had not) or
; stops, at the next it stops.  The host observes every *fn-osd-poll-ms*
; on a clock that never goes back (each observation follows a clock event),
; so the first observation past H + grace and the next are two such, and
; the stop comes within H + grace + one poll (+ one observation's work) of
; the drain's start; the fence follows at once.
(defthm fn-osd-drain-stops-by-the-deadline
  (implies (and (natp i)
                (consp (nthcdr (+ 1 i) obs))
                (fn-osd-past-grace-p s0 (nth i obs) limits)
                (fn-osd-past-grace-p s0 (nth (+ 1 i) obs) limits))
           (let ((k (fn-osd-drain-run s0 obs limits released)))
             (and (posp k) (<= k (+ 2 i)))))
  :rule-classes nil
  :hints (("Goal" :induct (fn-osd-drain-run-induct i obs released s0 limits)
                  :in-theory (e/d (nth nthcdr) (fn-osd-past-grace-p fn-osd-drain-next)))
          ("Subgoal *1/2" :expand ((fn-osd-drain-run s0 obs limits released)))
          ("Subgoal *1/1" :use ((:instance fn-osd-drain-run-two-past-grace)))))

(in-theory (disable fn-osd-drain-step fn-osd-drain-next fn-osd-drain-run
                    fn-osd-past-grace-p))
