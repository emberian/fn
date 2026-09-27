; Witnesses and teeth for books/owner-commit-steps.lisp (lane
; owner-scheduler-2, 2026-09-27; PKT-688 (4) slice 2; PRF-267).
;
; Every witness state is REACHED from fn-ocs-init through the picks and the
; commit events the host makes (fnn-owner-gate-pick, fnn-owner-commit-event),
; not written by hand: the batch in flight is the state after a :commit pick
; at an idle owner and the START's :started event.
(in-package "ACL2")
(include-book "../../books/owner-commit-steps")
(include-book "std/testing/must-fail" :dir :system)

(defun ocst-class (s w)
  (mv-let (class s2) (fn-ocs-next s w) (declare (ignore s2)) class))
(defun ocst-pick (s w)
  (mv-let (class s2) (fn-ocs-next s w) (declare (ignore class)) s2))
(defun ocst-event (s e)
  (mv-let (action s2) (fn-ocs-commit-event s e) (declare (ignore action)) s2))
(defun ocst-action (s e)
  (mv-let (action s2) (fn-ocs-commit-event s e) (declare (ignore s2)) action))
(defun ocst-ocm-class (s w c)
  (mv-let (class s2) (fn-ocm-next s w c) (declare (ignore s2)) class))
(defun ocst-step-action (p e)
  (mv-let (action p2) (fn-ocs-commit-step p e) (declare (ignore p2)) action))
(defun ocst-step-phase (p e)
  (mv-let (action p2) (fn-ocs-commit-step p e) (declare (ignore action)) p2))

; Waiting vectors (control reader poster transit commit inspect).
(defconst *ocst-commit-only* '(0 0 0 0 1 0))
(defconst *ocst-all* '(1 3 1 1 1 1))
(defconst *ocst-readers* '(0 3 0 0 0 0))
(defconst *ocst-readers-inspect* '(0 3 0 0 0 1))
(defconst *ocst-commit-inspect* '(0 3 0 0 1 1))
(defconst *ocst-inspect-only* '(0 0 0 0 0 1))

; The reachable states: an idle owner admits the waiting commit (fn-ocm's
; idle rule), whose START staged a batch; then an :inspect ran during the
; barrier (LASTI set).
(defconst *ocst-s-commit* (ocst-pick (fn-ocs-init) *ocst-commit-only*))
(defconst *ocst-s-flight* (ocst-event *ocst-s-commit* :started))
(defconst *ocst-s-flight-lasti* (ocst-pick *ocst-s-flight* *ocst-inspect-only*))
; Out of a batch with LASTI set: an idle owner served one inspect.
(defconst *ocst-s-idle-lasti* (ocst-pick (fn-ocs-init) *ocst-inspect-only*))

(assert-event (equal (ocst-class (fn-ocs-init) *ocst-commit-only*) :commit))
(assert-event (equal (ocst-action *ocst-s-commit* :started) :barrier))
(assert-event (equal (fn-ocs-phase *ocst-s-flight*) :staged))
(assert-event (fn-ocs-in-flight-p (fn-ocs-phase *ocst-s-flight-lasti*)))
(assert-event (fn-ocs-lasti *ocst-s-flight-lasti*))
(assert-event (and (not (fn-ocs-in-flight-p (fn-ocs-phase *ocst-s-idle-lasti*)))
                   (fn-ocs-lasti *ocst-s-idle-lasti*)))

; --- fn-ocs-in-flight-admits-only-inspect-commit-and-reader ------------------
; Witness: in flight, every class waits; the pick is :inspect, :commit or
; :reader (PKT-828: readers run during the barrier, at the reader view).
(assert-event (and (fn-ocs-in-flight-p (fn-ocs-phase *ocst-s-flight*))
                   (member-equal (ocst-class *ocst-s-flight* *ocst-all*)
                                 '(:inspect :commit :reader nil))))
(assert-event (equal (ocst-class *ocst-s-flight* *ocst-all*) :inspect))
(assert-event (equal (ocst-class *ocst-s-flight-lasti* *ocst-all*) :commit))
; Only readers wait during the barrier: they are admitted.
(assert-event (equal (ocst-class *ocst-s-flight* *ocst-readers*) :reader))
; Control, a control-socket poster and transit wait in flight (nobody is
; admitted), and are admitted once the batch is done.
(defconst *ocst-control-poster-transit* '(1 0 1 1 0 0))
(assert-event (equal (ocst-class *ocst-s-flight* *ocst-control-poster-transit*) nil))
; Hypothesis removal: out of a batch (the COMPLETE ran: :fenced then
; :completed) control IS admitted -- the conclusion fails.
(defconst *ocst-s-done*
  (ocst-event (ocst-event *ocst-s-flight* :fenced) :completed))
(assert-event (not (fn-ocs-in-flight-p (fn-ocs-phase *ocst-s-done*))))
(assert-event (equal (ocst-class *ocst-s-done* *ocst-readers*) :reader))
(assert-event (equal (ocst-class *ocst-s-done* *ocst-control-poster-transit*) :control))
(must-fail
 (assert-event (member-equal (ocst-class *ocst-s-done* *ocst-control-poster-transit*)
                             '(:inspect :commit :reader nil))))

; --- fn-ocs-in-flight-commit-before-reader -------------------------------------
; Witness: in flight, the commit and readers wait (no inspect): the commit.
(defconst *ocst-commit-readers* '(0 3 0 0 1 0))
(assert-event (equal (ocst-class *ocst-s-flight* *ocst-commit-readers*) :commit))
; Hypothesis removal: no commit waiting -- the reader.
(assert-event (equal (ocst-class *ocst-s-flight* *ocst-readers*) :reader))
; Hypothesis removal: out of a batch the commit class is fn-ocm-next's
; (admitted when idle or after its bound): readers first.
(assert-event (equal (ocst-class *ocst-s-done* *ocst-commit-readers*) :reader))

; --- fn-ocs-next-otherwise-is-ocm-next --------------------------------------
; Witness: out of a batch, LASTI set, readers and an inspect wait: the pick
; is fn-ocm-next's :reader.
(assert-event (and (not (fn-ocs-in-flight-p (fn-ocs-phase *ocst-s-idle-lasti*)))
                   (equal (ocst-class *ocst-s-idle-lasti* *ocst-readers-inspect*) :reader)
                   (equal (ocst-class *ocst-s-idle-lasti* *ocst-readers-inspect*)
                          (ocst-ocm-class (fn-ocs-ocm *ocst-s-idle-lasti*)
                                          (fn-ocs-w4 *ocst-readers-inspect*) nil))))
; Hypothesis removal (in flight): control and readers wait; fn-ocm-next
; would pick control, the in-flight pick is the reader.
(defconst *ocst-control-readers-inspect* '(1 3 0 0 0 1))
(assert-event (equal (ocst-class *ocst-s-flight-lasti* *ocst-control-readers-inspect*) :reader))
(assert-event (not (equal (ocst-class *ocst-s-flight-lasti* *ocst-control-readers-inspect*)
                          (ocst-ocm-class (fn-ocs-ocm *ocst-s-flight-lasti*)
                                          (fn-ocs-w4 *ocst-control-readers-inspect*) nil))))
; Hypothesis removal (an :inspect pick): not fn-ocm-next's either.
(assert-event (equal (ocst-class (fn-ocs-init) *ocst-readers-inspect*) :inspect))
(assert-event (not (equal (ocst-class (fn-ocs-init) *ocst-readers-inspect*)
                          (ocst-ocm-class (fn-ocs-ocm (fn-ocs-init))
                                          (fn-ocs-w4 *ocst-readers-inspect*) nil))))
; An :inspect pick keeps the four classes' cursor and the commit's count.
(assert-event (equal (fn-ocs-ocm (ocst-pick (fn-ocs-init) *ocst-readers-inspect*))
                     (fn-ocs-ocm (fn-ocs-init))))

; --- the step machine ---------------------------------------------------------
; The whole cycle: START -> barrier -> COMPLETE -> idle.
(assert-event (equal (ocst-step-action :idle :started) :barrier))
(assert-event (equal (ocst-step-phase :idle :started) :staged))
(assert-event (equal (ocst-step-action :staged :fenced) :complete))
(assert-event (equal (ocst-step-phase :staged :fenced) :fenced))
(assert-event (equal (ocst-step-action :fenced :completed) :none))
(assert-event (equal (ocst-step-phase :fenced :completed) :idle))
; The failed barrier: the stop, then idle.
(assert-event (equal (ocst-step-action :staged :failed) :stop))
(assert-event (equal (ocst-step-phase :failed :completed) :idle))
; An uncertain member inside the START: no barrier, the stop.
(assert-event (equal (ocst-step-action :idle :started-uncertain) :stop))
(assert-event (equal (ocst-step-action :idle :started-none) :none))
; fn-ocs-complete-only-after-the-barrier, witness and its two hypotheses:
; a :fenced event without a staged batch, and a staged batch whose barrier
; failed, are never :complete.
(assert-event (equal (ocst-step-action :idle :fenced) :fault))
(assert-event (equal (ocst-step-action :staged :failed) :stop))
(must-fail (assert-event (equal (ocst-step-action :idle :fenced) :complete)))
(must-fail (assert-event (equal (ocst-step-action :staged :failed) :complete)))
; A second START while a batch is in flight is a fault, and the batch stays
; in flight until :completed.
(assert-event (equal (ocst-step-action :staged :started) :fault))
(assert-event (equal (ocst-step-phase :staged :started) :staged))
(assert-event (equal (ocst-step-action :fenced :started) :fault))
(assert-event (fn-ocs-in-flight-p (ocst-step-phase :fenced :started)))

; --- KEYSTONE fn-ocs-inspect-waits-at-most-one ---------------------------------
; Witness (in a batch): LASTI set, the COMPLETE and an inspect wait; the
; commit runs first (its :completed ends the batch), then the inspect.
(defconst *ocst-ws-flight*
  (list (list *ocst-commit-inspect* :completed) (list *ocst-commit-inspect* nil)))
(assert-event (fn-ocs-inspect-waitsp *ocst-ws-flight*))
(assert-event (equal (fn-ocs-inspect-delay *ocst-s-flight-lasti* *ocst-ws-flight*) 1))
(assert-event (<= (fn-ocs-inspect-delay *ocst-s-flight-lasti* *ocst-ws-flight*) 1))
; Witness (out of a batch): a reader storm and an inspect, LASTI set.
(defconst *ocst-ws-storm*
  (list (list *ocst-readers-inspect* nil) (list *ocst-readers-inspect* nil)
        (list *ocst-readers-inspect* nil)))
(assert-event (fn-ocs-inspect-waitsp *ocst-ws-storm*))
(assert-event (equal (fn-ocs-inspect-delay *ocst-s-idle-lasti* *ocst-ws-storm*) 1))
(assert-event (equal (fn-ocs-inspect-delay (fn-ocs-init) *ocst-ws-storm*) 0))
; Hypothesis removal: the inspect arrives only at the fourth pick; three
; reader quanta run first -- the antecedent and the conclusion both fail.
(defconst *ocst-ws-late*
  (list (list *ocst-readers* nil) (list *ocst-readers* nil) (list *ocst-readers* nil)
        (list *ocst-readers-inspect* nil)))
(assert-event (not (fn-ocs-inspect-waitsp *ocst-ws-late*)))
(assert-event (equal (fn-ocs-inspect-delay (fn-ocs-init) *ocst-ws-late*) 3))
(must-fail
 (assert-event (<= (fn-ocs-inspect-delay (fn-ocs-init) *ocst-ws-late*) 1)))

; --- the keystone's per-pick subjects -------------------------------------------
; fn-ocs-inspect-first-when-not-last: witness (an inspect waits, LASTI clear)
; and its two hypotheses removed: LASTI set with a reader waiting picks the
; reader; no inspect waiting picks the reader.
(assert-event (and (fn-ocs-inspect-waits-p *ocst-readers-inspect*)
                   (not (fn-ocs-lasti *ocst-s-done*))
                   (equal (ocst-class *ocst-s-done* *ocst-readers-inspect*) :inspect)))
(assert-event (and (fn-ocs-lasti *ocst-s-idle-lasti*)
                   (not (equal (ocst-class *ocst-s-idle-lasti* *ocst-readers-inspect*) :inspect))))
(assert-event (and (not (fn-ocs-inspect-waits-p *ocst-readers*))
                   (not (equal (ocst-class *ocst-s-done* *ocst-readers*) :inspect))))
; fn-ocs-inspect-waiting-picks-someone: witness in a batch with LASTI set and
; no commit waiting (the inspect runs again); removed: nobody waits for
; the owner in a batch but control -- nobody is picked.
(assert-event (and (fn-ocs-inspect-waits-p *ocst-inspect-only*)
                   (equal (ocst-class *ocst-s-flight-lasti* *ocst-inspect-only*) :inspect)))
(assert-event (null (ocst-class *ocst-s-flight-lasti* *ocst-control-poster-transit*)))
; fn-ocs-other-pick-clears-lasti: the commit's pick in a batch clears it; an
; inspect pick sets it (the hypothesis "not :inspect" removed).
(assert-event (and (equal (ocst-class *ocst-s-flight-lasti* *ocst-commit-inspect*) :commit)
                   (not (fn-ocs-lasti (ocst-pick *ocst-s-flight-lasti* *ocst-commit-inspect*)))))
(assert-event (fn-ocs-lasti (ocst-pick *ocst-s-flight* *ocst-inspect-only*)))

; -----------------------------------------------------------------------------
; The members' replies (fn-ocs-member-releases; keystone
; fn-ocs-members-told-only-after-the-barrier, lane scheduler-2-rebase).  The
; actions are the ones the committer's reached states name (fn-ocs-commit-event
; from *ocst-s-flight*, the batch a START staged), never written by hand.
(defconst *ocst-a-complete* (ocst-action *ocst-s-flight* :fenced))
(defconst *ocst-a-failed* (ocst-action *ocst-s-flight* :failed))
(defconst *ocst-a-start-uncertain* (ocst-action *ocst-s-done* :started-uncertain))
(assert-event (equal *ocst-a-complete* :complete))
(assert-event (equal *ocst-a-failed* :stop))
(assert-event (equal *ocst-a-start-uncertain* :stop))

; Three members: accepted (its word :durable, a render kept), refused before
; its attempt (no render), accepted again.
(defconst *ocst-members* '((:durable t) (:refused nil) (:durable t)))

; Positive witness (the keystone's complete antecedent and conclusion): the
; fenced batch tells each member its own outcome, acceptance and refusal alike;
; a member is :rendered, and the phase was :staged and the event :fenced.
(assert-event (equal (fn-ocs-member-releases *ocst-a-complete* *ocst-members*)
                     '(:rendered :rendered :rendered)))
(assert-event (and (member-equal :rendered
                                 (fn-ocs-member-releases
                                  (ocst-step-action (fn-ocs-phase *ocst-s-flight*) :fenced)
                                  *ocst-members*))
                   (equal (fn-ocs-phase *ocst-s-flight*) :staged)))

; The failed barrier (the recovery event): the stop, and no member is told
; acceptance or refusal -- a kept render gets ACL2's uncertain reply, the
; refused member (whose refusal may rest on an earlier member) closes.
(assert-event (equal (fn-ocs-member-releases *ocst-a-failed* *ocst-members*)
                     '(:uncertain-reply :close :uncertain-reply)))
(assert-event (not (member-equal :rendered
                                 (fn-ocs-member-releases *ocst-a-failed* *ocst-members*))))

; A START that ended at a member ACL2 answered uncertain: that member gets its
; own uncertain line, the ones before it ACL2's uncertain reply.
(assert-event (equal (fn-ocs-member-releases *ocst-a-start-uncertain*
                                             '((:durable t) (:uncertain t)))
                     '(:uncertain-reply :own-uncertain)))
; An uncertain word is answered uncertain even in a COMPLETE (a mutation of the
; host's pairing; the START never stages it).
(assert-event (equal (fn-ocs-member-release :complete :uncertain t) :own-uncertain))

; Hypothesis-removal witness for the keystone (its one hypothesis: some member
; is :rendered).  At the START (phase :idle, event :started) the action is the
; barrier: the hypothesis fails (no member :rendered) and so does the
; conclusion (the phase is not :staged).  The keystone cannot be weakened to
; drop it.
(assert-event (equal (ocst-step-action :idle :started) :barrier))
(assert-event (not (member-equal :rendered
                                 (fn-ocs-member-releases :barrier *ocst-members*))))
(assert-event (not (equal :idle :staged)))

; Mutation witnesses (labelled: a release that told a stopped batch's members
; their rendered outcome is what the keystone refuses).
(must-fail
 (assert-event (member-equal :rendered
                             (fn-ocs-member-releases *ocst-a-failed* *ocst-members*))))
(must-fail
 (assert-event (equal (fn-ocs-member-release :stop :refused nil) :rendered)))

; -----------------------------------------------------------------------------
; Teeth for the step machine's characterizations (keystone-audit 2026-09-27).
; fn-ocs-barrier-only-from-a-start: witness (the START at an idle owner) and
; its hypothesis removed -- the fenced barrier's step is not :barrier and the
; conclusion fails there (the phase is in flight, the event not :started).
(assert-event (and (equal (ocst-step-action :idle :started) :barrier)
                   (not (fn-ocs-in-flight-p :idle))
                   (equal (ocst-step-phase :idle :started) :staged)))
(assert-event (and (not (equal (ocst-step-action :staged :fenced) :barrier))
                   (fn-ocs-in-flight-p :staged)
                   (not (equal :fenced :started))))
; fn-ocs-staged-only-by-a-start: both disjuncts reached (the START; a fault
; at a staged batch), and the hypothesis removed -- the COMPLETE's step leaves
; :fenced and neither disjunct holds.
(assert-event (equal (ocst-step-phase :staged :started) :staged))
(assert-event (equal (ocst-step-action :staged :started) :fault))
(assert-event (and (not (equal (ocst-step-phase :staged :fenced) :staged))
                   (not (equal (ocst-step-action :staged :fenced) :barrier))
                   (not (equal (ocst-step-action :staged :fenced) :fault))))
; fn-ocs-failed-barrier-stops-telling-no-member: the event hypothesis removed
; is the keystone witness above (:fenced: :complete, members :rendered); the
; phase hypothesis removed: :failed at an idle owner is a fault, not the stop.
(assert-event (and (equal (ocst-step-action :idle :failed) :fault)
                   (not (equal (ocst-step-action :idle :failed) :stop))))
; fn-ocs-in-flight-until-completed: its event hypothesis removed at each
; in-flight phase (:completed leaves the batch), its phase hypothesis
; removed (the idle START stages: in flight, but from out of flight).
(assert-event (and (not (fn-ocs-in-flight-p (ocst-step-phase :fenced :completed)))
                   (not (fn-ocs-in-flight-p (ocst-step-phase :failed :completed)))
                   (fn-ocs-in-flight-p (ocst-step-phase :staged :failed))))
(assert-event (and (not (fn-ocs-in-flight-p :idle))
                   (not (fn-ocs-in-flight-p (ocst-step-phase :idle :fenced)))))
; fn-ocs-inspect-pick-keeps-the-ocm, its hypothesis removed: a :reader pick
; at an idle owner moves the four classes' cursor.
(assert-event (and (equal (ocst-class (fn-ocs-init) *ocst-readers*) :reader)
                   (not (equal (fn-ocs-ocm (ocst-pick (fn-ocs-init) *ocst-readers*))
                               (fn-ocs-ocm (fn-ocs-init))))))
