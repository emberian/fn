; Witnesses and teeth for books/owner-time-model.lisp (lane time-model,
; 2026-09-27; PRF-311).  Every scheduler state is REACHED from fn-otm-init
; through the picks, the commit events and the disk events the host makes
; (fnn-owner-gate-pick, fnn-owner-commit-event, fnn-owner-disk-event).
(in-package "ACL2")
(include-book "../../books/owner-time-model")
(include-book "../../books/owner-time-journal")
(include-book "../../books/owner-time-admission")
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
                     (otmt-text "disk ok: pending-ms=2000 last-barrier-ms=0 max-barrier-ms=0 deadline-ms=5000 stall-ms=30000 slow-episodes=0 stalls=0
")))
(assert-event (equal (otmt-disk-word *otmt-s1* :clock 5999 0) :none))
; At the deadline: shed, health says slow with the figure, the clock event
; enters :slow once, the committer then appends a clock event per cadence.
(assert-event (equal (fn-otm-admit-post (otmt-at *otmt-s1* 6000)) :shed))
(assert-event (equal (fn-otm-wait-ms (otmt-at *otmt-s1* 6000)) 1000))
(assert-event (equal (fn-otm-disk-lines (otmt-at *otmt-s1* 12500))
                     (otmt-text "disk slow: barrier 11500 ms pending deadline-ms=5000 stall-ms=30000 slow-episodes=1 stalls=0 posts=try-later
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
                     (otmt-text "disk slow: barrier 8000 ms pending deadline-ms=5000 stall-ms=30000 slow-episodes=1 stalls=0 posts=try-later
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
                     (otmt-text "disk ok: pending-ms=0 last-barrier-ms=30000 max-barrier-ms=30000 deadline-ms=5000 stall-ms=30000 slow-episodes=1 stalls=0
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
   :rule-classes nil
   ;; Fail fast (lane time-model-2): no induction, the event and the
   ;; admission kept closed; the reached witness above is the refutation.
   :hints (("Goal" :do-not-induct t :in-theory (disable fn-otm-disk-event fn-otm-admit-post)))))

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

; The refutation of the keystone without fn-otm-barrier-pending-p is the idle
; witness above, stated as a theorem (proved by evaluation):
(defthm otmt-bound-needs-pending-refuted
  (let ((s *otmt-idle*) (ws (list (list *otmt-cr* nil))))
    (and (not (fn-otm-barrier-pending-p s))
         (fn-otm-barrier-walk-okp s ws)
         (not (equal (fn-otm-walk-others s ws) 0))))
  :rule-classes nil)
; The weakened statement also does not prove; bounded, because the unbounded
; search ran 145M prover steps (180 s) before it failed (batch AX).
(must-fail-checked
 (with-prover-step-limit 200000
  (defthm otmt-tooth-bound-needs-pending
    (implies (fn-otm-barrier-walk-okp s ws)
             (equal (fn-otm-walk-others s ws) 0))
    :rule-classes nil)))

; =============================================================================
; Slice 2 (lane time-model-2): H, the stall's release, F4-W, the journal.

; --- The limits: a barrier issued at 10,000 ms with D=2,000, H=5,000 and a
; cadence of 500 ms (the three `policy set' rows, fn-otm-limits).
(defconst *t2-l* '(2000 5000 500))
(defconst *t2-s1* (otmt-disk *otmt-s1a* :issue 10000 *t2-l*))
(assert-event (and (equal (fn-otm-disk-deadline (fn-otm-disk *t2-s1*)) 2000)
                   (equal (fn-otm-disk-stall (fn-otm-disk *t2-s1*)) 5000)
                   (equal (fn-otm-disk-cadence (fn-otm-disk *t2-s1*)) 500)))
; H configured below D is read as D; absent rows are the defaults.
(assert-event (equal (fn-otm-limits '(8000 3000 0)) '(8000 8000 1000)))
(assert-event (equal (fn-otm-limits 0) '(5000 30000 1000)))
; The committer's waits: to D, then the cadence, then the rest to H, then the cadence.
(assert-event (equal (fn-otm-wait-ms *t2-s1*) 2000))
(assert-event (equal (fn-otm-wait-ms (otmt-at *t2-s1* 11000)) 1000))
(assert-event (equal (otmt-disk-word *t2-s1* :clock 12000 0) :became-slow))
(defconst *t2-slow* (otmt-at *t2-s1* 12000))
(assert-event (and (equal (fn-otm-mode *t2-slow*) :slow)
                   (equal (fn-otm-wait-ms *t2-slow*) 500)
                   (equal (fn-otm-wait-ms (otmt-at *t2-slow* 14800)) 200)
                   (equal (fn-otm-admit-post *t2-slow*) :shed)))
; At H: the clock event enters :stalled once; health names it; the posters'
; release is the host's at this word.
(assert-event (equal (otmt-disk-word *t2-slow* :clock 15000 0) :became-stalled))
(defconst *t2-stalled* (otmt-at *t2-slow* 15000))
(assert-event (and (equal (fn-otm-mode *t2-stalled*) :stalled)
                   (fn-otm-disk-stalled (fn-otm-disk *t2-stalled*))
                   (equal (fn-otm-disk-stalls (fn-otm-disk *t2-stalled*)) 1)
                   (equal (fn-otm-disk-episodes (fn-otm-disk *t2-stalled*)) 1)
                   (equal (fn-otm-wait-ms *t2-stalled*) 500)
                   (equal (otmt-disk-word *t2-stalled* :clock 16000 0) :none)))
(assert-event (equal (fn-otm-disk-lines *t2-stalled*)
                     (otmt-text "disk stalled: barrier 5000 ms pending deadline-ms=2000 stall-ms=5000 slow-episodes=1 stalls=1 posts=try-later members=uncertain
")))
(assert-event (equal (fn-otm-log-line *t2-stalled* :became-stalled)
                     (otmt-text "disk stalled: a barrier has waited 5000 ms (stall deadline 5000 ms); its posters are told the outcome is uncertain: it may still complete")))
(assert-event (fn-otm-slow-line-p (fn-otm-disk-lines *t2-stalled*)))
(assert-event (equal (fn-otm-post-command-reply *t2-stalled*)
                     (append (otmt-text "440 posting not permitted now; the disk is stalled (a write has waited 5000 ms, deadline 2000 ms), try again later")
                             '(13 10))))
; A first clock event already past H (none at D): slow and stalled at once.
(assert-event (equal (otmt-disk-word *t2-s1* :clock 16000 0) :became-stalled))
(assert-event (equal (fn-otm-disk-episodes (fn-otm-disk (otmt-at *t2-s1* 16000))) 1))
; The completion after the stall: named; the articles are stored.
(assert-event (equal (otmt-disk-word *t2-stalled* :return 40000 0) :recovered-from-stall))
(defconst *t2-back* (otmt-disk *t2-stalled* :return 40000 0))
(assert-event (and (equal (fn-otm-admit-post *t2-back*) :admit)
                   (not (fn-otm-disk-stalled (fn-otm-disk *t2-back*)))
                   (equal (fn-otm-disk-last (fn-otm-disk *t2-back*)) 30000)))
(assert-event (equal (fn-otm-log-line *t2-back* :recovered-from-stall)
                     (otmt-text "disk recovered after a stall: the barrier completed after 30000 ms; the articles whose posters were told uncertain are stored")))

; --- KEYSTONE fn-otm-stall-tells-no-member-its-outcome: the members of a
; batch (an accepted one, a refused one without a renderable reply, an
; uncertain one) are each told uncertain; the same members in a COMPLETE
; are told their outcomes (the conclusion is not vacuous).
(defconst *t2-outcomes* '((:accepted t) (:refused nil) (:uncertain t)))
(assert-event (equal (fn-otm-stall-releases *t2-outcomes*)
                     '(:uncertain-reply :close :own-uncertain)))
(assert-event (fn-otm-uncertain-releases-p (fn-otm-stall-releases *t2-outcomes*)))
(assert-event (equal (fn-ocs-member-releases :complete *t2-outcomes*)
                     '(:rendered :rendered :own-uncertain)))
(assert-event (not (fn-otm-uncertain-releases-p (fn-ocs-member-releases :complete *t2-outcomes*))))

; --- KEYSTONE fn-otm-f4w-stall-within-h.  Positive witness: from *t2-s1*
; (pending since 10,000, H 5,000, not stalled), the committer's readings,
; each within its wait plus LATE = 300: the stall is entered at 15,000,
; within since + H + LATE.
(defconst *t2-rs* '(12000 12500 13000 13500 14000 14500 15000 15500))
(assert-event (and (fn-otm-disk-pending (fn-otm-disk *t2-s1*))
                   (not (fn-otm-disk-stalled (fn-otm-disk *t2-s1*)))
                   (<= (fn-otm-disk-since (fn-otm-disk *t2-s1*)) (fn-otm-now *t2-s1*))
                   (not (fn-otm-disk-stall-due-p (fn-otm-disk *t2-s1*) (fn-otm-now *t2-s1*)))
                   (fn-otm-clock-run-okp *t2-s1* *t2-rs* 300)
                   (equal (fn-otm-stall-reading *t2-s1* *t2-rs*) 15000)
                   (<= 15000 (+ 10000 5000 300))))
; Late wakes (each 300 ms after its wait): the stall at 15,300, still in bound.
(defconst *t2-rs-late* '(12300 12800 13300 13800 14300 14800 15300))
(assert-event (and (fn-otm-clock-run-okp *t2-s1* *t2-rs-late* 300)
                   (equal (fn-otm-stall-reading *t2-s1* *t2-rs-late*) 15300)))
; No reading reaches H yet: not stalled, the recorded time before since + H.
(assert-event (and (null (fn-otm-stall-reading *t2-s1* '(12000 12500)))
                   (< (fn-otm-now (fn-otm-clock-run *t2-s1* '(12000 12500))) 15000)))
; Hypothesis removed, the run's pacing: a wake 8 s late (not within its
; wait plus LATE): the stall comes at 20,000, past the bound.
(assert-event (and (not (fn-otm-clock-run-okp *t2-s1* '(12000 20000) 300))
                   (equal (fn-otm-stall-reading *t2-s1* '(12000 20000)) 20000)
                   (< (+ 10000 5000 300) 20000)))
; Hypothesis removed, not yet stalled: from the stalled value no reading is
; the stall's, yet the disk is stalled -- the "none yet" conclusion fails.
(assert-event (and (fn-otm-clock-run-okp *t2-stalled* '(15500) 300)
                   (null (fn-otm-stall-reading *t2-stalled* '(15500)))
                   (fn-otm-disk-stalled (fn-otm-disk (fn-otm-clock-run *t2-stalled* '(15500))))))
; Hypothesis removed, not past H at the recorded time (corrupted state:
; a second :issue while one is pending is the host's fault, exit 4, but
; the model records its reading): recorded 15,500, not stalled, no reading
; -- the "before since + H" conclusion fails.
(defconst *t2-late-now* (otmt-disk *t2-s1* :issue 15500 *t2-l*))
(assert-event (and (equal (otmt-disk-word *t2-s1* :issue 15500 *t2-l*) :fault)
                   (fn-otm-disk-stall-due-p (fn-otm-disk *t2-late-now*) (fn-otm-now *t2-late-now*))
                   (not (fn-otm-disk-stalled (fn-otm-disk *t2-late-now*)))
                   (null (fn-otm-stall-reading *t2-late-now* nil))
                   (<= 15000 (fn-otm-now (fn-otm-clock-run *t2-late-now* nil)))))
; Hypothesis removed, pending: after the completion no stall is entered,
; whatever the readings; the recorded time passes since + H.
(assert-event (and (not (fn-otm-disk-pending (fn-otm-disk *t2-back*)))
                   (fn-otm-clock-run-okp *t2-back* '(99000) 60000)
                   (null (fn-otm-stall-reading *t2-back* '(99000)))
                   (<= (+ (fn-otm-disk-since (fn-otm-disk *t2-back*))
                          (fn-otm-disk-stall (fn-otm-disk *t2-back*)))
                       (fn-otm-now (fn-otm-clock-run *t2-back* '(99000))))))

; --- The wall reading (N3): ACL2 decides validity.
(assert-event (equal (fn-otm-wall-reading 946684801 250000 946684800) '(1250 t)))
(assert-event (equal (fn-otm-wall-reading 946684799 999999 946684800) '(0 nil)))
(assert-event (equal (fn-otm-wall-reading 946684799 999999 946684800)
                     (fn-otm-wall-reading "garbage" -1 946684800)))

; =============================================================================
; The journal (books/owner-time-journal.lisp).

; The codec.
(assert-event (equal (fn-otm-jline '(0 12 305)) (otmt-text "0 12 305
")))
(assert-event (equal (fn-otm-journal-read (fn-otm-jlines '((1 2 3) (0 45 6789))))
                     '((1 2 3) (0 45 6789))))
(defun t2-jparse (octets) (mv-let (st es) (fn-otm-jparse octets nil nil nil) (list st es)))
(assert-event (equal (t2-jparse (otmt-text "1 2")) '(:torn nil)))
(assert-event (equal (t2-jparse (otmt-text "1 x
")) '(:malformed nil)))
(assert-event (equal (fn-otm-start-line 5 7) (otmt-text "0 0 5 7 0 0 0
")))

; A reached run of the host's calls, interleaved (the gate's pick, the
; START's event, the issue, a served read's reading with its wall clock, the
; committer's clock events through D and H, the stall's note: 2 members
; told, 1 queued POST refused, the completion).
(defconst *t2-steps*
  (list (list :next *otmt-commit-only*) (list :commit :started)
        (list :event :issue 10000 *t2-l*)
        (list :event :served 11000 '(123456 t))
        (list :next *otmt-rci*)
        (list :event :clock 12000 nil)
        (list :event :clock 15000 nil)
        (list :note 2 1)
        (list :event :return 40000 nil)))
(defun t2-run-entries (s steps) (mv-let (es s2) (fn-otm-run s steps) (declare (ignore s2)) es))
(defun t2-run-state (s steps) (mv-let (es s2) (fn-otm-run s steps) (declare (ignore es)) s2))
(defun t2-replay-verdict (s es) (mv-let (v s2) (fn-otm-replay s es) (declare (ignore s2)) v))
(defun t2-replay-state (s es) (mv-let (v s2) (fn-otm-replay s es) (declare (ignore v)) s2))
(defconst *t2-entries* (t2-run-entries (fn-otm-init) *t2-steps*))
(assert-event (equal *t2-entries*
                     '((1 3 10000 2000 5000 500 1)
                       (2 2 11000 123456 1 0 7)
                       (3 1 12000 0 0 0 5)
                       (4 1 15000 0 0 0 6)
                       (5 5 15000 2 1 0 0)
                       (6 4 40000 0 0 0 4))))
(defconst *t2-file* (fn-otm-jlines *t2-entries*))
; KEYSTONE fn-otm-journal-determines-the-decisions, positive witness: the
; file reads back whole and replays to agreement at the run's disk and clock.
(assert-event (and (fn-otm-run-okp *t2-steps*)
                   (equal (car (t2-jparse *t2-file*)) :whole)
                   (equal (t2-replay-verdict (fn-otm-init) (fn-otm-journal-read *t2-file*)) :agrees)
                   (equal (fn-otm-disk (t2-replay-state (fn-otm-init) (fn-otm-journal-read *t2-file*)))
                          (fn-otm-disk (t2-run-state (fn-otm-init) *t2-steps*)))
                   (equal (fn-otm-clock (t2-replay-state (fn-otm-init) (fn-otm-journal-read *t2-file*)))
                          (fn-otm-clock (t2-run-state (fn-otm-init) *t2-steps*)))))
; A run's segment after its start entry replays from anywhere (the start
; resets to fn-otm-init).
(assert-event (equal (t2-replay-verdict *t2-stalled*
                                        (cons '(0 0 5 7 0 0 0) *t2-entries*))
                     :agrees))
; Teeth: a journaled word that is not what the event decides; a dropped
; entry (the sink's bound, or a torn file); a run with an event kind the
; host never appends (fn-otm-run-okp removed): diverged, gap, malformed.
(assert-event (equal (t2-replay-verdict (fn-otm-init)
                                        (list (car *t2-entries*) (cadr *t2-entries*)
                                              '(3 1 12000 0 0 0 7)))
                     '(:diverged 3)))
(assert-event (equal (t2-replay-verdict (fn-otm-init) (cons (car *t2-entries*) (cddr *t2-entries*)))
                     '(:gap 3)))
(defconst *t2-bad-steps* (list (list :event :bogus 5 nil)))
(assert-event (and (not (fn-otm-run-okp *t2-bad-steps*))
                   (equal (t2-replay-verdict (fn-otm-init) (t2-run-entries (fn-otm-init) *t2-bad-steps*))
                          '(:malformed 1))))
; fn-otm-decisions-read-only-the-journal-state: two values with the same
; disk and clock but different pipelines decide alike; a different clock
; does not (the admission turns).
(assert-event (equal (fn-otm-admit-post (fn-otm-make nil (fn-otm-disk *t2-slow*) (fn-otm-clock *t2-slow*)))
                     (fn-otm-admit-post *t2-slow*)))
(assert-event (not (equal (fn-otm-admit-post (fn-otm-make nil (fn-otm-disk *t2-slow*) (list 11000 0 0)))
                          (fn-otm-admit-post *t2-slow*))))

; =============================================================================
; The 440 at the command (books/owner-time-admission.lisp): the posting bit
; of a real injection configuration is set without touching the rest.
(defconst *t2-cfg* (fn-inj-make-config t "fn" nil 1000))
(assert-event (and (fn-inj-config-allow *t2-cfg*)
                   (not (fn-inj-config-allow (fn-otm-cfg-with-allow *t2-cfg* nil)))
                   (equal (cdr (fn-otm-cfg-with-allow *t2-cfg* nil)) (cdr *t2-cfg*))
                   (equal (fn-otm-cfg-with-allow (fn-otm-cfg-with-allow *t2-cfg* nil)
                                                 (fn-inj-config-allow *t2-cfg*))
                          *t2-cfg*)))

; =============================================================================
; The replies name the disk's reason (lane ax-fix/reply-text).  The host's
; call, fn-otm-read-span, on live stobjs over owner-reader-read-tests' owner
; (*lgt-finished*: a configured owner that permits posting, connection 0 a
; reader) and its catalog, as g12b-host-read runs fn-orr-read-span.
(include-book "owner-reader-read-tests")
(defun t2r-host-read-in (oc views id octs admit replies rows payloads fn-octets fn-arena fn-cat)
  (declare (xargs :mode :program :stobjs (fn-octets fn-arena fn-cat)))
  (let* ((fn-octets (fn-octets-from-list octs fn-octets))
         (fn-arena (fn-arena-clear fn-arena))
         (fn-arena (fn-arn-seal-many payloads fn-arena))
         (fn-cat (fn-sca-load-held-rows rows (fn-own-view-index (fn-own-view (fn-ocfg-owner oc)))
                                        fn-arena fn-cat)))
    (mv (fn-otm-read-span oc views id 0 (len octs) admit replies fn-octets fn-arena fn-cat)
        fn-octets fn-arena fn-cat)))
(defun t2r-host-read (oc views id octs admit replies)
  (declare (xargs :mode :program))
  (with-local-stobj fn-octets
    (mv-let (result fn-octets)
      (with-local-stobj fn-arena
        (mv-let (result fn-octets fn-arena)
          (with-local-stobj fn-cat
            (mv-let (result fn-octets fn-arena fn-cat)
              (t2r-host-read-in oc views id octs admit replies (orrt-records *lgt-finished*)
                                *g12b-payloads* fn-octets fn-arena fn-cat)
              (mv result fn-octets fn-arena)))
          (mv result fn-octets)))
      result)))
(defun t2r-effect-text (effect)
  (declare (xargs :mode :program))
  (coerce (fn-nntp-octets-chars (cadr effect)) 'string))
(defconst *t2r-post* (append (fn-nntp-string-octets "POST") '(13 10)))
(defconst *t2r-crlf* (coerce (list (code-char 13) (code-char 10)) 'string))

; The replies the host reads with the admission (fn-otm-shed-replies): the
; stalled disk's 440 and 441 name the stall with its figures; slow, the
; slowness; while the disk admits there are none.
(assert-event
 (equal (fn-otm-shed-replies *t2-stalled*)
        (cons (append (otmt-text "440 posting not permitted now; the disk is stalled (a write has waited 5000 ms, deadline 2000 ms), try again later") '(13 10))
              (append (otmt-text "441 posting failed; the disk is stalled (a write has waited 5000 ms, deadline 2000 ms): nothing was stored, try again later") '(13 10)))))
(assert-event
 (equal (car (fn-otm-shed-replies *t2-slow*))
        (append (otmt-text "440 posting not permitted now; the disk is slow (a write has waited 2000 ms, deadline 2000 ms), try again later") '(13 10))))
(assert-event (and (equal (fn-otm-admit-post *t2-s1*) :admit)
                   (null (fn-otm-shed-replies *t2-s1*))
                   (null (fn-otm-shed-replies *t2-back*))))

; KEYSTONE fn-otm-read-span-while-shedding, its effects conjunct with the
; rewrite taken.  MUTATION witness: the reached owner's connections were
; opened under a configuration without posting (its owner's injection
; configuration is NIL), so connection 0's posting bit is turned on, as a
; connection opened under a posting configuration has it
; (fn-otm-owner-with-allow).  Admitted, its POST is offered (340 and the
; article marker); while the stalled disk sheds, the host's call answers
; ACL2's 440 with the disk's reason, one reply, the whole command consumed,
; and the connection's bit is back on afterwards.
(defconst *t2r-open* (fn-otm-owner-with-allow *lgt-finished* 0 t))
(defconst *t2r-open-admit* (t2r-host-read *t2r-open* *orrt-views* 0 *t2r-post* :admit nil))
(defconst *t2r-open-shed*
  (t2r-host-read *t2r-open* *orrt-views* 0 *t2r-post* :shed (fn-otm-shed-replies *t2-stalled*)))
(assert-event
 (let ((effects (fn-own-tls-result-effects *t2r-open-admit*)))
   (and (fn-otm-conn-allow *t2r-open* 0)
        (fn-own-conn-shapep (fn-own-find-conn 0 (fn-own-conns (fn-ocfg-owner *t2r-open*))))
        (fn-post-offeredp effects)
        (equal (t2r-effect-text (car effects))
               (concatenate 'string "340 send article to be posted" *t2r-crlf*)))))
(assert-event
 (let ((effects (fn-own-tls-result-effects *t2r-open-shed*)))
   (and (equal effects (list (list :reply (car (fn-otm-shed-replies *t2-stalled*)))))
        (equal (t2r-effect-text (car effects))
               (concatenate 'string "440 posting not permitted now; the disk is stalled (a write has waited 5000 ms, deadline 2000 ms), try again later" *t2r-crlf*))
        (not (fn-post-offeredp effects))
        (equal (fn-own-tls-result-consumed *t2r-open-shed*) (len *t2r-post*))
        (fn-otm-conn-allow (fn-own-tls-result-owner *t2r-open-shed*) 0))))
; The conclusion's rewrite is the served machine's 440 replaced: the same
; read with no replies answers the generic 440.
(assert-event
 (equal (fn-own-tls-result-effects
         (t2r-host-read *t2r-open* *orrt-views* 0 *t2r-post* :shed nil))
        (list *fn-otm-generic-440*)))
; REACHED, the rewrite's condition: on the reached owner, whose connection 0
; does not permit posting, the shed read's 440 is the served machine's own:
; the disk is not the reason that connection may not post.
(defconst *t2r-closed-shed*
  (t2r-host-read *lgt-finished* *orrt-views* 0 *t2r-post* :shed (fn-otm-shed-replies *t2-stalled*)))
(assert-event (and (not (fn-otm-conn-allow *lgt-finished* 0))
                   (equal (fn-own-tls-result-effects *t2r-closed-shed*)
                          (list *fn-otm-generic-440*))))
; The 441 of an article whose POST got 340 before (the served machine's
; :posting-disallowed refusal, fn-otm-posting-disallowed-refusal-is-the-
; generic-441), among other effects: only it is replaced, by the slow
; disk's line; the rest is kept, in place.
(defconst *t2r-other* (list :reply (append (otmt-text "211 0 0 0 fn.letters") '(13 10))))
(assert-event
 (equal (fn-otm-disk-reply-effects (list *t2r-other* *fn-otm-generic-441* '(:close))
                                   (fn-otm-shed-replies *t2-slow*))
        (list *t2r-other*
              (list :reply (append (otmt-text "441 posting failed; the disk is slow (a write has waited 2000 ms, deadline 2000 ms): nothing was stored, try again later") '(13 10)))
              '(:close))))
(assert-event (equal (t2r-effect-text *fn-otm-generic-441*)
                     (concatenate 'string "441 posting failed; posting is not permitted" *t2r-crlf*)))

