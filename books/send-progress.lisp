; When the owner refuses a reply's send (CONVERGE-2 row 20).
;
; The owner used to give every queued reply window a fixed 10 s to be accepted
; by the socket (host/native/mux.lisp +fnn-mux-send-seconds+) and cut the
; connection with Errno 110 when the time ran out.  A reader that keeps
; draining was cut: on the CONVERGE-2 developer image a client with a 4 KiB
; receive buffer reading 38 KB/s (1 MiB per 27.4 s) leaves the kernel's send
; queue full after 3,383,427 octets and then needs 3,383,427 / 38,000 = 89 s
; to drain it; the fixed deadline, armed at the window, fired at 10 s while
; the reader was progressing.  A reader that is draining is not stalled.
;
; ACL2 decides, the host observes and enforces.  While a window waits the
; host takes, each mux tick, an observation (NOW OUTQ HANDED):
;
;   NOW     the monotonic clock in milliseconds;
;   OUTQ    the kernel's unsent octets for the socket (ioctl SIOCOUTQ on
;           Linux), or NIL where the platform gives no figure ("unknown");
;   HANDED  the octets of this reply the kernel has accepted so far.
;
; The state (SINCE START START-OUTQ LAST-OUTQ LAST-HANDED) is what the verdict
; remembers: the time of the last progress, the time and queue the reply
; started with, and the previous observation's queue and handed count.
;
; PROGRESS between two observations is the queue shrinking (the reader read
; and the peer acknowledged) or more octets accepted (the kernel had room, so
; some left).  Either is evidence the reader is draining, and does not depend
; on whether the connection is encrypted: OUTQ counts the wire's octets,
; HANDED the plain ones, and only their change is compared.  An unknown OUTQ
; leaves HANDED alone to show progress (the old deadline's own evidence, the
; write the socket took).
;
; The verdict is :continue, (:refuse :send-stalled) or (:refuse
; :reader-too-slow):
;
;   send-stalled     no progress for :send-stall-seconds (default 10 s, the
;                    fixed deadline's figure, now a window the reader keeps
;                    resetting);
;   reader-too-slow  progress at this observation, but over the reply so far the octets that left
;                    the queue are fewer than :send-min-octets-per-second a
;                    second, judged once a stall window has elapsed and only
;                    while a backlog is queued in the kernel (OUTQ positive or
;                    unknown): a reader that keeps its queue empty is not slow
;                    however long the server took to render, and nothing is
;                    refused for the owner's own pace.  The octets that left
;                    are HANDED plus the queue the reply started with less
;                    OUTQ now (HANDED alone where OUTQ is unknown).
;
; The floor's default, 4096 octets per second, is nine times under the slowest
; reader the native tests name (38 KB/s): the measured reader is at 38,000 and
; the margin is for a noisy link, not for the attack; an operator tightens the
; row against a slow-read attack, and the per-connection memory budget
; (books/connection-budget.lisp) already bounds what a slow reader can hold.
; A malformed argument is refused as :send-stalled: the host builds these from
; the kernel and the clock, so malformed means it lost track, and keeping a
; connection whose progress is unknown is the wrong default.
;
; Keystones:
;   fn-send-progress-draining-reader-continues  a reader whose queue shrinks
;     within the window (or that was seen draining within it) and whose pace is
;     at the floor is never refused; instantiated by the measured 38 KB/s
;     reader (fn-send-progress-measured-reader-continues, a ground run);
;   fn-send-progress-stalled-refused  no progress for the window is refused
;     :send-stalled, and the first observation at or after the window refuses,
;     so a stopped reader is refused within the window plus one observation's
;     interval (fn-send-progress-stopped-reader-refused, a ground run);
;   fn-send-progress-too-slow-refused  a reader that progresses but under the
;     floor, past the window, is refused :reader-too-slow;
;   fn-send-progress-verdict-answers  the verdict is one of the three answers,
;     computed from its arguments alone (no clock, no socket).

(in-package "ACL2")
(include-book "profile-limits")

(defconst *fn-send-stall-seconds* (fn-profile-limit :send-stall-seconds))
(defconst *fn-send-min-octets-per-second* (fn-profile-limit :send-min-octets-per-second))

; ---- observation and state ----

(defun fn-send-obs-p (obs)
  (declare (xargs :guard t))
  (and (true-listp obs)
       (equal (len obs) 3)
       (natp (nth 0 obs))
       (or (null (nth 1 obs)) (natp (nth 1 obs)))
       (natp (nth 2 obs))))

(defun fn-send-state-p (st)
  (declare (xargs :guard t))
  (and (true-listp st)
       (equal (len st) 5)
       (natp (nth 0 st))
       (natp (nth 1 st))
       (<= (nth 1 st) (nth 0 st))
       (or (null (nth 2 st)) (natp (nth 2 st)))
       (or (null (nth 3 st)) (natp (nth 3 st)))
       (natp (nth 4 st))))

; State and observation, and the observation not before the last progress.
(defun fn-send-pair-p (st obs)
  (declare (xargs :guard t))
  (and (fn-send-state-p st)
       (fn-send-obs-p obs)
       (<= (nth 0 st) (nth 0 obs))))

; The state a reply starts with, at its first observation (NOW OUTQ, nothing
; handed yet).
(defun fn-send-progress-begin (now outq)
  (declare (xargs :guard t))
  (list (nfix now) (nfix now)
        (if (natp outq) outq nil)
        (if (natp outq) outq nil)
        0))

; The queue shrank, or octets were accepted.
(defun fn-send-progress-p (st obs)
  (declare (xargs :guard (fn-send-pair-p st obs)
                  :guard-hints (("Goal" :in-theory (enable fn-send-pair-p
                                                           fn-send-state-p fn-send-obs-p)))))
  (or (< (nth 4 st) (nth 2 obs))
      (and (natp (nth 1 obs)) (natp (nth 3 st))
           (< (nth 1 obs) (nth 3 st)))))

; The state after OBS: the time of the last progress moves to now when OBS shows
; progress, and the last observation is OBS's.  A malformed pair leaves STATE.
(defun fn-send-progress-next (st obs)
  (declare (xargs :guard t))
  (if (fn-send-pair-p st obs)
      (list (if (fn-send-progress-p st obs) (nth 0 obs) (nth 0 st))
            (nth 1 st)
            (nth 2 st)
            (nth 1 obs)
            (nth 2 obs))
    st))

; Octets that left the queue over the reply so far.
(defun fn-send-drained (st obs)
  (declare (xargs :guard (fn-send-pair-p st obs)
                  :guard-hints (("Goal" :in-theory (enable fn-send-pair-p
                                                           fn-send-state-p fn-send-obs-p)))))
  (if (and (natp (nth 1 obs)) (natp (nth 2 st)))
      (nfix (- (+ (nth 2 obs) (nth 2 st)) (nth 1 obs)))
    (nth 2 obs)))

; ---- the verdict ----

(defun fn-send-progress-verdict (st obs stall-seconds min-octets-per-second)
  (declare (xargs :guard t))
  (if (and (fn-send-pair-p st obs)
           (natp stall-seconds) (natp min-octets-per-second))
      (let* ((now (nth 0 obs))
             (since (if (fn-send-progress-p st obs) now (nth 0 st)))
             (window (* 1000 stall-seconds))
             (elapsed (- now (nth 1 st))))
        (cond ((<= window (- now since)) '(:refuse :send-stalled))
              ((and (fn-send-progress-p st obs)
                    (or (null (nth 1 obs)) (< 0 (nth 1 obs)))
                    (<= window elapsed)
                    (< (* 1000 (fn-send-drained st obs))
                       (* min-octets-per-second elapsed)))
               '(:refuse :reader-too-slow))
              (t :continue)))
    '(:refuse :send-stalled)))

; At the profile's rows: the entry the host calls.
(defun fn-send-progress-decide (st obs)
  (declare (xargs :guard t))
  (fn-send-progress-verdict st obs
                            *fn-send-stall-seconds* *fn-send-min-octets-per-second*))

; ---- keystones ----

; KEYSTONE.  A reader that is draining is never refused: it showed progress
; at this observation or within the window before it, and its pace over the
; reply is at the floor (or the reply has not run a window yet, or no backlog
; is queued).
(defthm fn-send-progress-draining-reader-continues
  (implies (and (fn-send-pair-p st obs)
                (posp stall-seconds) (natp min-octets-per-second)
                (or (fn-send-progress-p st obs)
                    (< (- (nth 0 obs) (nth 0 st)) (* 1000 stall-seconds)))
                (or (equal (nth 1 obs) 0)
                    (< (- (nth 0 obs) (nth 1 st)) (* 1000 stall-seconds))
                    (<= (* min-octets-per-second (- (nth 0 obs) (nth 1 st)))
                        (* 1000 (fn-send-drained st obs)))))
           (equal (fn-send-progress-verdict st obs stall-seconds min-octets-per-second)
                  :continue))
  :rule-classes nil)

; KEYSTONE.  No progress for the window is refused by name, and the first
; observation at or after the window refuses it.
(defthm fn-send-progress-stalled-refused
  (implies (and (fn-send-pair-p st obs)
                (natp stall-seconds) (natp min-octets-per-second)
                (not (fn-send-progress-p st obs))
                (<= (* 1000 stall-seconds) (- (nth 0 obs) (nth 0 st))))
           (equal (fn-send-progress-verdict st obs stall-seconds min-octets-per-second)
                  '(:refuse :send-stalled)))
  :rule-classes nil)

; KEYSTONE.  A reader that progresses now but is under the floor, a backlog
; queued and a window run, is refused :reader-too-slow.
(defthm fn-send-progress-too-slow-refused
  (implies (and (fn-send-pair-p st obs)
                (posp stall-seconds) (natp min-octets-per-second)
                (fn-send-progress-p st obs)
                (not (equal (nth 1 obs) 0))
                (<= (* 1000 stall-seconds) (- (nth 0 obs) (nth 1 st)))
                (< (* 1000 (fn-send-drained st obs))
                   (* min-octets-per-second (- (nth 0 obs) (nth 1 st)))))
           (equal (fn-send-progress-verdict st obs stall-seconds min-octets-per-second)
                  '(:refuse :reader-too-slow)))
  :rule-classes nil)

; KEYSTONE.  One of three answers, and a malformed argument is refused.
(defthm fn-send-progress-verdict-answers
  (and (or (equal (fn-send-progress-verdict st obs stall min-rate) :continue)
           (equal (fn-send-progress-verdict st obs stall min-rate)
                  '(:refuse :send-stalled))
           (equal (fn-send-progress-verdict st obs stall min-rate)
                  '(:refuse :reader-too-slow)))
       (implies (not (and (fn-send-pair-p st obs) (natp stall) (natp min-rate)))
                (equal (fn-send-progress-verdict st obs stall min-rate)
                       '(:refuse :send-stalled))))
  :rule-classes nil)

; The state the host keeps stays well formed, and its last progress is the
; observation's time exactly when the observation shows progress.
(defthm fn-send-progress-next-state
  (implies (fn-send-pair-p st obs)
           (and (fn-send-state-p (fn-send-progress-next st obs))
                (equal (nth 0 (fn-send-progress-next st obs))
                       (if (fn-send-progress-p st obs) (nth 0 obs) (nth 0 st)))
                (equal (nth 1 (fn-send-progress-next st obs)) (nth 1 st))
                (<= (nth 0 (fn-send-progress-next st obs)) (nth 0 obs))))
  :rule-classes nil)

; A reply's first observation, in the state it starts: not refused (for a
; positive window).
(defthm fn-send-progress-begin-continues
  (implies (and (natp now) (or (null outq) (natp outq)) (posp stall-seconds)
                (natp min-octets-per-second))
           (and (fn-send-state-p (fn-send-progress-begin now outq))
                (equal (fn-send-progress-verdict (fn-send-progress-begin now outq)
                                                 (list now outq 0)
                                                 stall-seconds min-octets-per-second)
                       :continue)))
  :rule-classes nil)

; ---- the measured reader, ground ----

; A reader that drains DRAIN octets every STEP ms from a queue of OUTQ at NOW,
; the writer having handed HANDED: the observations after N steps.
(defun fn-send-reader-trace (n now outq handed step drain)
  (declare (xargs :guard (and (natp n) (natp now) (natp outq) (natp handed)
                              (natp step) (natp drain))))
  (if (zp n)
      nil
    (let ((now (+ now step))
          (outq (nfix (- outq drain))))
      (cons (list now outq handed)
            (fn-send-reader-trace (1- n) now outq handed step drain)))))

; The first refusal over the observations in order, or :continue, with the
; state advanced by each.
(defun fn-send-progress-run (st trace stall-seconds min-octets-per-second)
  (declare (xargs :guard t :measure (acl2-count trace)))
  (if (atom trace)
      :continue
    (let ((v (fn-send-progress-verdict st (car trace) stall-seconds min-octets-per-second)))
      (if (equal v :continue)
          (fn-send-progress-run (fn-send-progress-next st (car trace))
                                (cdr trace) stall-seconds min-octets-per-second)
        v))))

; The measured reader: 38,000 octets per second (9,500 per 250 ms tick), the
; kernel queue holding 3,383,427 octets when the writer blocked, observed each
; tick for 87.5 s of the 89 s the queue takes to drain (a drained queue is a
; reply the socket has taken, and the host stops observing it): at the
; profile's rows it is never refused.
(defthm fn-send-progress-measured-reader-continues
  (equal (fn-send-progress-run (fn-send-progress-begin 0 0)
                               (fn-send-reader-trace 350 0 3383427 3383427 250 9500)
                               *fn-send-stall-seconds* *fn-send-min-octets-per-second*)
         :continue)
  :rule-classes nil)

; The same queue, the reader stopped: refused :send-stalled at the first
; observation 10 s after the last progress, 40 ticks of 250 ms, and the run
; reaches no later one.
(defthm fn-send-progress-stopped-reader-refused
  (equal (fn-send-progress-run (fn-send-progress-begin 0 0)
                               (fn-send-reader-trace 400 0 3383427 3383427 250 0)
                               *fn-send-stall-seconds* *fn-send-min-octets-per-second*)
         '(:refuse :send-stalled))
  :rule-classes nil)
