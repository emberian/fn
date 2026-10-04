; S9 drain over carried counts and explicit producer-fence observations.
; The host must establish both observations; a bare zero is never success.
(in-package "ACL2")
(include-book "owner-feed-counts")
(include-book "owner-stop-drain")

(defun fn-ort-intake-action (retiringp)
  (declare (xargs :guard t))
  (if retiringp :refused :admit))

(defun fn-ort-fenced-input-consumed (received)
  (declare (xargs :guard t))
  (nfix received))

(include-book "owner-retire-settlement")

(defun fn-ort-drain-step-counted (s0 s seconds pending intake-fenced producers-settled)
  (declare (xargs :guard t))
  (cond ((and (equal intake-fenced t) (equal producers-settled t)
              (natp pending) (equal pending 0)) :drained)
        ((<= (* 1000 (nfix seconds)) (fn-osd-elapsed s0 s)) :deadline)
        (t :wait)))

; The producer fence.  From the retire request on, every intake site of
; host/native/owner.lisp refuses a new submission under the owner mutex
; (fn-ort-intake-action: fnn-owner-handle-chunk-read for every connection
; read, fnn-owner-complete-bound-submission for the control, operator and BP
; application posts, fnn-owner-complete-bp-transit-submission for BP
; transit), so what can still move the carried feed count is a submission
; already in the owner's queue.  The committer's START takes, attempts and
; feeds each queued member's outcome (fn-own-feed-enqueue-all-counted) in
; one hold of that mutex (fnn-owner-commit-start-locked, fnn-owner-drain-
; one), so observed under the same mutex an empty queue is settled
; producers: nothing taken is still to be counted.
(defun fn-ort-producers-settled (queue)
  (declare (xargs :guard t))
  (if (consp queue) nil t))

; The drain step host/owner-host.lisp fn-owner-retire-step answers for
; host/native/owner.lisp fnn-owner-maybe-retire, under the owner mutex, from
; the carried feed count and the owner's queue: intake is fenced (the host
; calls it only while retiring) and the producers are the queue's.
(defun fn-ort-retire-step (s0 s seconds pending queue)
  (declare (xargs :guard t))
  (fn-ort-drain-step-counted s0 s seconds pending t
                             (fn-ort-producers-settled queue)))

; KEYSTONE (the drain ends by its window).  At or past SECONDS since the
; request's snapshot the step never answers :wait, whatever is pending or
; queued.
(defthm fn-ort-retire-step-ends-by-the-window
  (implies (<= (* 1000 (nfix seconds)) (fn-osd-elapsed s0 s))
           (not (equal (fn-ort-retire-step s0 s seconds pending queue) :wait))))

; KEYSTONE (a drained node stops drained).  Nothing pending in the feeds and
; nothing queued: the step answers :drained, before the window or after it.
(defthm fn-ort-retire-step-drains-a-settled-zero
  (implies (and (equal pending 0) (not (consp queue)))
           (equal (fn-ort-retire-step s0 s seconds pending queue) :drained)))

; KEYSTONE (a drain is never cut short).  Before the window, with a feed
; entry still tried or a submission still queued, the step waits.
(defthm fn-ort-retire-step-waits-while-anything-drains
  (implies (and (< (fn-osd-elapsed s0 s) (* 1000 (nfix seconds)))
                (or (not (equal pending 0)) (consp queue)))
           (equal (fn-ort-retire-step s0 s seconds pending queue) :wait)))

(defthm fn-ort-retire-step-drained-means-settled-and-zero
  (implies (equal (fn-ort-retire-step s0 s seconds pending queue) :drained)
           (and (equal pending 0) (not (consp queue))))
  :rule-classes nil)

; The final checkpoint at the drain's end.  Only a drained node takes it:
; at :deadline the window was decided by the clock-only precheck
; (fn-ort-window-step) precisely so the stop waits on no owner gate and no
; free-space I/O, and a stalled barrier -- the usual reason a drain reaches
; its window -- would hold the compaction request behind it.
(defun fn-ort-final-checkpoint-action (step)
  (declare (xargs :guard t))
  (if (equal step :drained) :checkpoint :stop))

(defthm fn-ort-final-checkpoint-only-when-drained
  (equal (equal (fn-ort-final-checkpoint-action step) :checkpoint)
         (equal step :drained)))

 ; A clock-only precheck runs before acquiring the semantic owner mutex.
(defun fn-ort-window-step (s0 s seconds)
  (declare (xargs :guard t))
  (if (<= (* 1000 (nfix seconds)) (fn-osd-elapsed s0 s)) :deadline :wait))

(defthm fn-ort-window-step-never-drained
  (not (equal (fn-ort-window-step s0 s seconds) :drained)))

(defthm fn-ort-window-step-deadline-is-counted-deadline
  (implies (equal (fn-ort-window-step s0 s seconds) :deadline)
           (not (equal (fn-ort-drain-step-counted
                        s0 s seconds pending intake-fenced producers-settled) :wait))))

(defthm fn-ort-drained-requires-zero-and-both-fences
  (implies (equal (fn-ort-drain-step-counted
                  s0 s seconds pending intake-fenced producers-settled) :drained)
           (and (equal pending 0) (equal intake-fenced t)
                (equal producers-settled t)))
  :rule-classes nil)

(defthm fn-ort-deadline-is-independent-of-the-fences
  (implies (<= (* 1000 (nfix seconds)) (fn-osd-elapsed s0 s))
           (not (equal (fn-ort-drain-step-counted
                        s0 s seconds pending intake-fenced producers-settled) :wait))))

(defthm fn-ort-counted-drain-waits-before-window-without-fenced-zero
  (implies (and (< (fn-osd-elapsed s0 s) (* 1000 (nfix seconds)))
                (not (and (equal intake-fenced t) (equal producers-settled t)
                          (natp pending) (equal pending 0))))
           (equal (fn-ort-drain-step-counted
                   s0 s seconds pending intake-fenced producers-settled) :wait)))

(in-theory (disable fn-ort-drain-step-counted fn-ort-intake-action
                    fn-ort-producers-settled fn-ort-retire-step
                    fn-ort-final-checkpoint-action
                    fn-ort-fenced-input-consumed fn-ort-window-step
                    fn-ort-log-close-action fn-ort-log-close-exit
                    fn-ort-report-close-action fn-ort-log-caller-action))
