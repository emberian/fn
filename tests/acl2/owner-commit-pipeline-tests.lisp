; Witnesses and teeth for books/owner-commit-pipeline.lisp (lane log-2,
; 2026-09-27).  Every state is REACHED from fn-ocp-init through the picks,
; the committer's wakes and the commit events the host makes
; (fnn-owner-gate-pick, fnn-owner-commit-wake, fnn-owner-commit-event).
(in-package "ACL2")
(include-book "../../books/owner-commit-pipeline")
(include-book "std/testing/must-fail" :dir :system)

(defun ocpt-class (s w) (mv-let (c s2) (fn-ocp-next s w) (declare (ignore s2)) c))
(defun ocpt-pick (s w) (mv-let (c s2) (fn-ocp-next s w) (declare (ignore c)) s2))
(defun ocpt-event (s e) (mv-let (a s2) (fn-ocp-commit-event s e) (declare (ignore a)) s2))
(defun ocpt-action (s e) (mv-let (a s2) (fn-ocp-commit-event s e) (declare (ignore s2)) a))
(defun ocpt-phase (s) (fn-ocs-phase (fn-ocp-ocs s)))
(defun ocpt-step-action (p n e)
  (mv-let (a p2 n2) (fn-ocp-commit-step p n e) (declare (ignore p2 n2)) a))

(defconst *ocpt-commit-only* '(0 0 0 0 1 0))
(defconst *ocpt-readers-commit* '(0 3 0 0 1 0))
(defconst *ocpt-readers* '(0 3 0 0 0 0))

; The pipeline, step by step: a :commit pick at an idle owner, START sealed
; a batch (:sync), a member queued during the barrier (:start-next), the
; next batch opened behind it, the barrier returned (:collect), COMPLETE,
; the next batch sealed (:sync), its barrier, its COMPLETE, idle.
(defconst *ocpt-s0* (ocpt-pick (fn-ocp-init) *ocpt-commit-only*))
(assert-event (equal (ocpt-class (fn-ocp-init) *ocpt-commit-only*) :commit))
(assert-event (equal (ocpt-action *ocpt-s0* :started) :sync))
(defconst *ocpt-s1* (ocpt-event *ocpt-s0* :started))
(assert-event (equal (ocpt-phase *ocpt-s1*) :staged))
(assert-event (equal (fn-ocp-committer-wake *ocpt-s1* nil t) :start-next))
(assert-event (equal (fn-ocp-committer-wake *ocpt-s1* nil nil) :wait))
(assert-event (equal (ocpt-action *ocpt-s1* :next-started) :wait))
(defconst *ocpt-s2* (ocpt-event *ocpt-s1* :next-started))
(assert-event (fn-ocp-open-next *ocpt-s2*))
; With a next batch open, a queued member waits: one batch behind at most.
(assert-event (equal (fn-ocp-committer-wake *ocpt-s2* nil t) :wait))
(assert-event (equal (ocpt-action *ocpt-s2* :next-started) :fault))
; Readers wait while the next batch is open: the pick admits the commit.
(assert-event (equal (ocpt-class *ocpt-s2* *ocpt-readers-commit*) :commit))
(assert-event (equal (ocpt-class *ocpt-s2* *ocpt-readers*) nil))
(assert-event (equal (fn-ocp-committer-wake *ocpt-s2* t t) :collect))
(assert-event (equal (ocpt-action *ocpt-s2* :fenced) :complete))
(defconst *ocpt-s3* (ocpt-event *ocpt-s2* :fenced))
(assert-event (equal (ocpt-action *ocpt-s3* :completed) :sync))
(defconst *ocpt-s4* (ocpt-event *ocpt-s3* :completed))
(assert-event (and (equal (ocpt-phase *ocpt-s4*) :staged) (not (fn-ocp-open-next *ocpt-s4*))))
(defconst *ocpt-s5* (ocpt-event (ocpt-event *ocpt-s4* :fenced) :completed))
(assert-event (and (equal (ocpt-phase *ocpt-s5*) :idle) (not (fn-ocp-open-next *ocpt-s5*))))
; Idle again: the readers are admitted.
(assert-event (equal (ocpt-class *ocpt-s5* *ocpt-readers*) :reader))

; A failed barrier stops with both batches; an uncertain member behind the
; barrier stops at once, and the barrier's later word changes nothing.
(assert-event (equal (ocpt-action *ocpt-s2* :failed) :stop))
(assert-event (equal (ocpt-action *ocpt-s1* :next-uncertain) :stop))
(defconst *ocpt-s6* (ocpt-event *ocpt-s1* :next-uncertain))
(assert-event (equal (fn-ocp-committer-wake *ocpt-s6* t nil) :collect))
(assert-event (equal (ocpt-action *ocpt-s6* :fenced) :stop))
(assert-event (equal (ocpt-phase (ocpt-event (ocpt-event *ocpt-s6* :fenced) :completed)) :idle))

; --- fn-ocp-commit-event-completes-only-after-the-barrier: positive witness
; (the complete antecedent and conclusion at a reached state).
(assert-event (and (equal (ocpt-action *ocpt-s2* :fenced) :complete)
                   (equal (ocpt-phase *ocpt-s2*) :staged)))
; Teeth: without the antecedent the conclusion fails (a reached idle state
; and an event that is not the barrier's word).
(must-fail
 (defthm ocpt-tooth-complete-needs-the-action
   (and (equal (fn-ocs-phase (fn-ocp-ocs s)) :staged) (equal event :fenced))
   :rule-classes nil))
(assert-event (not (equal (ocpt-phase *ocpt-s5*) :staged)))

; --- KEYSTONE fn-ocp-next-open-only-in-flight: positive witness, and the
; hypothesis removed (a reached state whose event leaves no next batch and
; no batch in flight).
(assert-event (and (fn-ocp-open-next (ocpt-event *ocpt-s1* :next-started))
                   (fn-ocs-in-flight-p (ocpt-phase (ocpt-event *ocpt-s1* :next-started)))))
(assert-event (and (not (fn-ocp-open-next (ocpt-event *ocpt-s4* :fenced)))
                   (not (fn-ocs-in-flight-p (ocpt-phase *ocpt-s5*)))))
(must-fail
 (defthm ocpt-tooth-in-flight-needs-an-open-next
   (fn-ocs-in-flight-p (fn-ocs-phase (fn-ocp-ocs (mv-nth 1 (fn-ocp-commit-event s event)))))
   :rule-classes nil))

; --- fn-ocp-sync-only-when-none-in-flight: both reached arms, and a staged
; batch never syncs again (a second append would be refused by the kernel).
(assert-event (equal (ocpt-step-action :staged nil :started) :fault))
(assert-event (equal (ocpt-step-action :fenced nil :completed) :none))

; --- fn-ocp-start-next-only-behind-a-sync: each hypothesis of the wake.
(assert-event (equal (fn-ocp-wake :idle nil nil t) :wait))
(assert-event (equal (fn-ocp-wake :staged t nil t) :wait))
(assert-event (equal (fn-ocp-wake :staged nil t t) :collect))
(assert-event (equal (fn-ocp-wake :staged nil nil nil) :wait))
