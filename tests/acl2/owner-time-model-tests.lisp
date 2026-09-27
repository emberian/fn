; Witnesses and teeth for books/owner-time-model.lisp (lane time-model,
; 2026-09-27; PRF-311).  Every scheduler state is REACHED from fn-otm-init
; through the picks, the commit events and the disk events the host makes
; (fnn-owner-gate-pick, fnn-owner-commit-event, fnn-owner-disk-event).
(in-package "ACL2")
(include-book "../../books/owner-time-model")
(include-book "must-fail-checked")

(defun otmt-class (s w) (mv-let (c s2) (fn-otm-next s w) (declare (ignore s2)) c))
(defun otmt-pick (s w) (mv-let (c s2) (fn-otm-next s w) (declare (ignore c)) s2))
(defun otmt-event (s e) (mv-let (a s2) (fn-otm-commit-event s e) (declare (ignore a)) s2))
(defun otmt-action (s e) (mv-let (a s2) (fn-otm-commit-event s e) (declare (ignore s2)) a))
(defun otmt-disk (s kind now dl)
  (mv-let (w s2) (fn-otm-disk-event s kind now dl) (declare (ignore w)) s2))
(defun otmt-disk-word (s kind now dl)
  (mv-let (w s2) (fn-otm-disk-event s kind now dl) (declare (ignore s2)) w))
(defun otmt-text (s) (fn-osch-chars-octets (coerce s 'list)))

; Waiting counts by slot: control reader poster transit commit inspect.
(defconst *otmt-commit-only* '(0 0 0 0 1 0))
(defconst *otmt-rci* '(0 2 0 0 1 1))      ; readers, the committer, a status
(defconst *otmt-ri* '(0 2 0 0 0 1))       ; readers and a status
(defconst *otmt-rc* '(0 2 0 0 1 0))
(defconst *otmt-cr* '(1 2 0 0 0 0))       ; a mutating control and readers
(defconst *otmt-i* '(0 0 0 0 0 1))        ; status alone

; --- A reached run.  The committer's :commit pick at an idle owner, its
; START sealed a batch (:sync), the barrier handed to the syncer at 1,000 ms
; with no configured deadline (the default, 5,000 ms).
(defconst *otmt-s0* (otmt-pick (fn-otm-init) *otmt-commit-only*))
(assert-event (equal (otmt-class (fn-otm-init) *otmt-commit-only*) :commit))
(assert-event (equal (otmt-action *otmt-s0* :started) :sync))
(defconst *otmt-s1a* (otmt-event *otmt-s0* :started))
(assert-event (equal (otmt-disk-word *otmt-s1a* :issue 1000 0) :issued))
(defconst *otmt-s1* (otmt-disk *otmt-s1a* :issue 1000 0))
(assert-event (fn-otm-barrier-pending-p *otmt-s1*))
(assert-event (equal (fn-otm-disk-deadline (fn-otm-disk *otmt-s1*)) 5000))
; A configured limit is used as given.
(assert-event (equal (fn-otm-disk-deadline (fn-otm-disk (otmt-disk *otmt-s1a* :issue 1000 250)))
                     250))
; A second issue while one is pending is refused (one barrier in flight).
(assert-event (equal (otmt-disk-word *otmt-s1* :issue 2000 0) :fault))

; Clock events (the committer's cadence, or on demand before a decision)
; record the time every decision reads.
(defun otmt-at (s reading) (otmt-disk s :clock reading 0))

; Before the deadline: admitted, health says ok, the committer waits the rest.
(assert-event (equal (fn-otm-now *otmt-s1*) 1000))
(assert-event (equal (fn-otm-admit-post *otmt-s1*) :admit))
(assert-event (equal (fn-otm-admit-post (otmt-at *otmt-s1* 5999)) :admit))
(assert-event (equal (fn-otm-wait-ms *otmt-s1*) 5000))
(assert-event (equal (fn-otm-wait-ms (otmt-at *otmt-s1* 4000)) 2000))
(assert-event (equal (fn-otm-disk-lines (otmt-at *otmt-s1* 3000))
                     (otmt-text "disk ok: pending-ms=2000 last-barrier-ms=0 max-barrier-ms=0 deadline-ms=5000 slow-episodes=0
")))
(assert-event (equal (otmt-disk-word *otmt-s1* :clock 5999 0) :none))
; At the deadline: shed, health says slow with the figure, the clock event
; enters :slow once, the committer then appends a clock event per cadence.
(assert-event (equal (fn-otm-admit-post (otmt-at *otmt-s1* 6000)) :shed))
(assert-event (equal (fn-otm-wait-ms (otmt-at *otmt-s1* 6000)) 1000))
(assert-event (equal (fn-otm-disk-lines (otmt-at *otmt-s1* 12500))
                     (otmt-text "disk slow: barrier 11500 ms pending deadline-ms=5000 slow-episodes=1 posts=try-later
")))
(assert-event (equal (otmt-disk-word *otmt-s1* :clock 6000 0) :became-slow))
(defconst *otmt-s1s* (otmt-at *otmt-s1* 6000))
(assert-event (equal (otmt-disk-word *otmt-s1s* :clock 7000 0) :none))
(assert-event (equal (fn-otm-disk-episodes (fn-otm-disk *otmt-s1s*)) 1))
(assert-event (equal (fn-otm-log-line *otmt-s1s* :became-slow)
                     (otmt-text "disk slow: a barrier has waited 5000 ms (deadline 5000 ms); new posts are refused try-later until it completes")))
(assert-event (equal (fn-otm-shed-reply (otmt-at *otmt-s1s* 9000))
                     (append (otmt-text "441 posting failed; the disk is slow (a write has waited 8000 ms, deadline 5000 ms): nothing was stored, try again later")
                             '(13 10))))
; A reading below the recorded time (a clock that ran backwards): recorded
; by name, nothing moves back -- the disk stays slow, the line names it.
(assert-event (equal (otmt-disk-word (otmt-at *otmt-s1s* 9000) :clock 2000 0) :clock-regressed))
(defconst *otmt-back* (otmt-at (otmt-at *otmt-s1s* 9000) 2000))
(assert-event (and (equal (fn-otm-now *otmt-back*) 9000)
                   (equal (fn-otm-regressions *otmt-back*) 1)
                   (equal (fn-otm-admit-post *otmt-back*) :shed)))
(assert-event (equal (fn-otm-disk-lines *otmt-back*)
                     (otmt-text "disk slow: barrier 8000 ms pending deadline-ms=5000 slow-episodes=1 posts=try-later
clock regressed: readings=1
")))
; The disk events kept the pipeline: the commit is still staged.
(assert-event (equal (fn-otm-ocp *otmt-s1s*) (fn-otm-ocp *otmt-s1a*)))

; --- The completion after a 30 s stall: recovered, the latency recorded,
; every later POST admitted, health ok with the figures.
(assert-event (equal (otmt-disk-word *otmt-s1s* :return 31000 0) :recovered))
(defconst *otmt-s2* (otmt-disk *otmt-s1s* :return 31000 0))
(assert-event (equal (fn-otm-disk-last (fn-otm-disk *otmt-s2*)) 30000))
(assert-event (equal (fn-otm-admit-post *otmt-s2*) :admit))
(assert-event (equal (fn-otm-admit-post (otmt-at *otmt-s2* 99000)) :admit))
(assert-event (equal (fn-otm-disk-lines (otmt-at *otmt-s2* 40000))
                     (otmt-text "disk ok: pending-ms=0 last-barrier-ms=30000 max-barrier-ms=30000 deadline-ms=5000 slow-episodes=1
")))
(assert-event (equal (fn-otm-log-line *otmt-s2* :recovered)
                     (otmt-text "disk recovered: the barrier completed after 30000 ms")))
(assert-event (equal (otmt-disk-word *otmt-s2* :return 32000 0) :fault))
; A fast barrier: returned, not recovered, no episode.
(assert-event (equal (otmt-disk-word (otmt-disk *otmt-s1a* :issue 1000 0) :return 1004 0) :returned))

; --- fn-otm-shed-iff-slow: both directions at reached states.
(assert-event (and (equal (fn-otm-admit-post (otmt-at *otmt-s1* 6000)) :shed)
                   (fn-otm-slow-line-p (fn-otm-disk-lines (otmt-at *otmt-s1* 6000)))))
(assert-event (and (equal (fn-otm-admit-post (otmt-at *otmt-s1* 5999)) :admit)
                   (not (fn-otm-slow-line-p (fn-otm-disk-lines (otmt-at *otmt-s1* 5999))))))

; --- fn-otm-wait-reaches-the-deadline: positive witness (the complete
; antecedent and conclusion), and each hypothesis removed.
(defconst *otmt-w* (otmt-at *otmt-s1* 2500))
(assert-event (let ((w (fn-otm-wait-ms *otmt-w*)))
                (and w (<= (fn-otm-disk-since (fn-otm-disk *otmt-w*)) (fn-otm-now *otmt-w*))
                     (posp w)
                     (equal (fn-otm-admit-post (otmt-at *otmt-w* (+ 2500 w))) :shed)
                     (equal (otmt-disk-word *otmt-w* :clock (+ 2500 w) 0) :became-slow))))
; A reading short of the wait: the conclusion fails.
(assert-event (equal (fn-otm-admit-post (otmt-at *otmt-w* (+ 2500 (fn-otm-wait-ms *otmt-w*) -1)))
                     :admit))
; No barrier pending (the wait is nil): a clock event far later sheds nothing.
(assert-event (and (null (fn-otm-wait-ms *otmt-s2*))
                   (equal (fn-otm-admit-post (otmt-at *otmt-s2* 999999)) :admit)))
; The recorded time before the issue (a barrier issued at a reading above
; the recorded time is impossible after the issue records it; reached by a
; state whose issue came with a regressed reading): the since-hypothesis
; fails and the deadline is measured from the issue, not from the
; recorded time.
(defconst *otmt-reg* (otmt-disk (otmt-at *otmt-s1a* 8000) :issue 3000 0))
(assert-event (and (equal (fn-otm-now *otmt-reg*) 8000)
                   (equal (fn-otm-disk-since (fn-otm-disk *otmt-reg*)) 8000)))
(must-fail-checked
 (defthm otmt-tooth-wait-needs-the-wait
   (implies (and (natp reading) (<= (fn-otm-disk-since (fn-otm-disk s)) (fn-otm-now s))
                 (<= (fn-otm-now s) reading))
            (equal (fn-otm-admit-post (mv-nth 1 (fn-otm-disk-event s :clock reading deadline)))
                   :shed))
   :rule-classes nil))

; --- fn-otm-return-recovers: without a pending barrier, a return is a fault.
(assert-event (equal (otmt-disk-word (fn-otm-init) :return 5 0) :fault))

; --- KEYSTONE fn-otm-disk-event-keeps-the-pipeline, at every reached disk
; event above.
(assert-event (and (equal (fn-otm-ocp *otmt-s1*) (fn-otm-ocp *otmt-s1a*))
                   (equal (fn-otm-ocp *otmt-s2*) (fn-otm-ocp *otmt-s1a*))))

; =============================================================================
; KEYSTONE fn-otm-barrier-reader-bound.
;
; Reached positive witness: the barrier pending (*otmt-s1*); a status, the
; committer's START-NEXT (its wake is :start-next: a member queued, the syncer
; not returned) and two readers wait; then a status and the readers.  The
; quanta before the reader: :inspect, :commit (took a member), :inspect.
(assert-event (equal (fn-otm-committer-wake *otmt-s1* nil t) :start-next))
(defconst *otmt-ws* (list (list *otmt-rci* :next-started)
                          (list *otmt-rci* :next-started)
                          (list *otmt-ri* nil)
                          (list *otmt-ri* nil)))
(assert-event (fn-otm-barrier-pending-p *otmt-s1*))
(assert-event (fn-otm-barrier-walk-okp *otmt-s1* *otmt-ws*))
(assert-event (equal (fn-otm-barrier-walk *otmt-s1* *otmt-ws*)
                     '((:inspect . :next-started) (:commit . :next-started) (:inspect))))
(assert-event (and (equal (fn-otm-walk-others *otmt-s1* *otmt-ws*) 0)
                   (equal (fn-otm-walk-started *otmt-s1* *otmt-ws*) 1)
                   (equal (fn-otm-walk-inspects *otmt-s1* *otmt-ws*) 2)
                   (equal (fn-otm-walk-commits *otmt-s1* *otmt-ws*) 1)
                   (<= (fn-otm-walk-inspects *otmt-s1* *otmt-ws*)
                       (+ 1 (fn-otm-walk-commits *otmt-s1* *otmt-ws*)))))
; The disk's state is not an input of the walk: the same walk from the
; slow disk (the tick taken) and from a disk that has waited 25 s picks the
; same quanta.
(assert-event (equal (fn-otm-barrier-walk *otmt-s1s* *otmt-ws*)
                     (fn-otm-barrier-walk *otmt-s1* *otmt-ws*)))

; Hypothesis removed: the barrier NOT pending (an idle owner, reached: the
; batch completed).  A mutating control quantum runs before the reader:
; the conclusion fails while the walk hypothesis still holds.
(defconst *otmt-idle* (otmt-event (otmt-event *otmt-s1* :fenced) :completed))
(assert-event (not (fn-otm-barrier-pending-p *otmt-idle*)))
(assert-event (fn-otm-barrier-walk-okp *otmt-idle* (list (list *otmt-cr* nil))))
(assert-event (equal (fn-otm-walk-others *otmt-idle* (list (list *otmt-cr* nil))) 1))
; ... and while pending the same waiting counts admit no control quantum.
(assert-event (equal (fn-otm-walk-others *otmt-s1* (list (list *otmt-cr* nil))) 0))

; Hypothesis removed: a reader does NOT wait at every pick (status alone
; waits, three times).  :inspect quanta run with no :commit between them:
; the inspect conclusion fails.
(defconst *otmt-ws-i* (list (list *otmt-i* nil) (list *otmt-i* nil) (list *otmt-i* nil)))
(assert-event (not (fn-otm-barrier-walk-okp *otmt-s1* *otmt-ws-i*)))
(assert-event (and (equal (fn-otm-walk-inspects *otmt-s1* *otmt-ws-i*) 3)
                   (equal (fn-otm-walk-commits *otmt-s1* *otmt-ws-i*) 0)))
; with the reader waiting it alternates: the retained hypothesis checked
(assert-event (fn-otm-barrier-walk-okp *otmt-s1* (list (list *otmt-ri* nil))))

; Hypothesis removed: the commit class waits when the committer's wake is
; NOT :start-next (a next batch already open, reached by the first
; START-NEXT).  A second START-NEXT that took members runs: the started
; conclusion fails.
(defconst *otmt-ws-c* (list (list *otmt-rc* :next-started) (list *otmt-rc* :next-started)))
(assert-event (not (fn-otm-barrier-walk-okp *otmt-s1* *otmt-ws-c*)))
(assert-event (equal (fn-otm-committer-wake (otmt-event (otmt-pick *otmt-s1* *otmt-rc*) :next-started)
                                            nil t)
                     :wait))
(assert-event (equal (fn-otm-walk-started *otmt-s1* *otmt-ws-c*) 2))
; the first item alone satisfies it
(assert-event (fn-otm-barrier-walk-okp *otmt-s1* (list (list *otmt-rc* :next-started))))

(must-fail-checked
 (defthm otmt-tooth-bound-needs-pending
   (implies (fn-otm-barrier-walk-okp s ws)
            (equal (fn-otm-walk-others s ws) 0))
   :rule-classes nil))
