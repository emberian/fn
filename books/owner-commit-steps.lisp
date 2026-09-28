; fn: the owner's commit in three scheduled steps -- the log barrier runs off
; the owner (lane owner-scheduler-2, 2026-09-27; PKT-688 (4) slice 2, decided
; by the coordinator: "the POST's durable commit becomes its own scheduled
; class, so a control request never waits behind a commit's fsyncs, and the
; commit itself is bounded per scheduling step"; PRF-267).
;
; books/owner-commit-class.lisp (lane commit-onto-log) made the batch commit
; a class: one :commit quantum drains every queued served submission into the
; record log's open batch, appends it, fences the segment (fdatasync) and
; only then releases the members' replies.  That quantum holds the owner
; across the fdatasync, so a status request that arrives during it waits for
; the barrier (slice 1's measurement: a POST quantum of up to 7.8 s under the
; file route).  This book splits it:
;
;   START     an owned :commit quantum: at most the operator's batch bound
;             of members, each through its sequential life, into the open
;             batch.  Nothing is durable; no reply leaves the owner.
;   BARRIER   NOT a quantum.  The committer thread, the owner released, runs
;             the batch's append and fdatasync (host/native/io.lisp
;             fnn-log-commit-open-batch: the log struct and the store's
;             fence bit, never an owner global).
;   COMPLETE  an owned :commit quantum: the log kernel's acknowledgements,
;             the members' deferred log lines and feed resolutions, then
;             their replies (the 240s) -- or, after a failed barrier, the
;             uncertain answer and the stop (exit 3).
;
; `fn-ocs-commit-step' names each step from the commit's PHASE and the event
; the host observed; the host runs the I/O the step names and nothing else.
; The phase is part of the scheduler's value, and `fn-ocs-next' (which
; host/native/owner.lisp fnn-owner-gate-pick calls at every release of the
; owner and every arrival at an idle one) decides from it:
;
;   - while a batch is IN FLIGHT (staged, fenced or failed, not yet
;     completed) only :commit (its COMPLETE, or the START-NEXT that prepares
;     the next batch behind the barrier), :inspect and :reader are
;     admitted (coordinator decision PKT-828, 2026-09-27: the fsync holds no
;     owner-level exclusion; only the in-flight batch's members wait for
;     their replies).  :inspect is the class of the live status and health
;     pages (host/native/control.lisp fnn-control-live-status-answer, chosen
;     when ACL2's fn-native-live-status-host-requestp accepts the frame):
;     the render changes nothing the owner holds and touches no record, no
;     log and no feed.  :reader is a served NNTP connection's quantum: its
;     reads run at the READER VIEW, the view captured before the batch in
;     flight was prepared (books/owner-reader-view.lisp), so nothing of the
;     batch in flight or of the next one is revealed before its COMPLETE,
;     and its POST only queues a submission, which a later START (or the
;     START-NEXT) takes into the open batch, never the one in flight.
;     Posters through the control socket, transit (peer sessions re-pin to
;     the live store node) and mutating control wait.
;   - otherwise the pick is books/owner-commit-class.lisp's `fn-ocm-next'
;     over the four classes and the commit class, unchanged.
;   - in both regimes a waiting :inspect is admitted unless the pick before
;     was an :inspect and another class waits: it alternates, so it waits
;     at most ONE quantum (keystone `fn-ocs-inspect-waits-at-most-one'),
;     and a quantum is never a barrier.
;
; Every pick that is not an :inspect outside a batch is `fn-ocm-next''s own
; (`fn-ocs-next-otherwise-is-ocm-next'), so PRF-248's control bound and the
; commit class's bound hold over the non-inspect quanta; the inspect quanta
; interleave at most one between two of them.
(in-package "ACL2")
(include-book "owner-commit-class")

;; The tau system is off in this book (lane tau-pass, tools/tau_cost.py).
;; Its work is proof time no prover step counts (docs/proof-style.md
;; 9.1); planning/evidence/tau-cost-*.json has this book's figures.
(local (in-theory (disable (tau-system))))

; -----------------------------------------------------------------------------
; The classes: the five of books/owner-commit-class.lisp at their slots and
; :inspect at slot 5.

(defconst *fn-ocs-slots* 6)

(defun fn-ocs-classp (x)
  (declare (xargs :guard t))
  (or (eq x :inspect) (fn-ocm-classp x)))

(defun fn-ocs-class-index (c)
  (declare (xargs :guard t))
  (if (eq c :inspect) 5 (fn-ocm-class-index c)))

; -----------------------------------------------------------------------------
; The commit's steps.  PHASE: :idle (no batch), :staged (the START ran; the
; barrier is the next step), :fenced (the barrier returned; COMPLETE is due),
; :failed (the barrier failed; the stop is due).  EVENT: what the host
; observed at the end of the step it ran.  Answers (mv ACTION PHASE'):
;   :barrier   run the batch's append and fdatasync, the owner released
;   :complete  (a :commit quantum) acknowledge, then release the replies
;   :stop      (a :commit quantum) the uncertain answer and the stop
;   :none      nothing more for this batch
;   :fault     the host reported an event the step does not expect

(defun fn-ocs-in-flight-p (phase)
  (declare (xargs :guard t))
  (or (eq phase :staged) (eq phase :fenced) (eq phase :failed)))

(defun fn-ocs-commit-step (phase event)
  (declare (xargs :guard t))
  (cond ((eq phase :staged)
         (cond ((eq event :fenced) (mv :complete :fenced))
               ((eq event :failed) (mv :stop :failed))
               (t (mv :fault :staged))))
        ((or (eq phase :fenced) (eq phase :failed))
         (if (eq event :completed) (mv :none :idle) (mv :fault phase)))
        (t
         (cond ((eq event :started) (mv :barrier :staged))
               ((eq event :started-none) (mv :none :idle))
               ;; A member ACL2 answered uncertain inside the START: the
               ;; batch is not appended; the same quantum answers and stops.
               ((eq event :started-uncertain) (mv :stop :idle))
               (t (mv :fault :idle))))))

; -----------------------------------------------------------------------------
; The scheduler's value: (OCM PHASE LASTI), OCM books/owner-commit-class.lisp's
; state, PHASE the commit's, LASTI whether the last pick was an :inspect.

(defun fn-ocs-init ()
  (declare (xargs :guard t))
  (list (fn-ocm-init) :idle nil))

(defun fn-ocs-ocm (s)
  (declare (xargs :guard t))
  (if (consp s) (car s) nil))

(defun fn-ocs-phase (s)
  (declare (xargs :guard t))
  (let ((p (if (and (consp s) (consp (cdr s))) (cadr s) :idle)))
    (if (fn-ocs-in-flight-p p) p :idle)))

(defun fn-ocs-lasti (s)
  (declare (xargs :guard t))
  (if (and (consp s) (consp (cdr s)) (consp (cddr s)) (caddr s)) t nil))

(defun fn-ocs-make (ocm phase lasti)
  (declare (xargs :guard t))
  (list ocm phase (if lasti t nil)))

; WAITING: six naturals by slot (control reader poster transit commit
; inspect).  The four classes' counts, as books/owner-scheduler.lisp reads
; them, and whether the commit and the inspect classes wait.
(defun fn-ocs-w4 (w)
  (declare (xargs :guard t))
  (list (fn-osch-waits 0 w) (fn-osch-waits 1 w) (fn-osch-waits 2 w)
        (fn-osch-waits 3 w)))

(defun fn-ocs-commit-waits-p (w)
  (declare (xargs :guard t))
  (posp (fn-osch-waits 4 w)))

(defun fn-ocs-inspect-waits-p (w)
  (declare (xargs :guard t))
  (posp (fn-osch-waits 5 w)))

(defun fn-ocs-reader-waits-p (w)
  (declare (xargs :guard t))
  (posp (fn-osch-waits 1 w)))

; The pick.  Answers (mv CLASS S'), CLASS one of the six or nil.  In flight
; the commit's steps go first (a START-NEXT or the COMPLETE: at most one
; waits at a time, the committer's), then the readers; the four classes'
; cursor is not moved by an in-flight pick.
(defun fn-ocs-next (s w)
  (declare (xargs :guard t))
  (let ((inspect (fn-ocs-inspect-waits-p w))
        (commit (fn-ocs-commit-waits-p w))
        (reader (fn-ocs-reader-waits-p w))
        (phase (fn-ocs-phase s)))
    (if (fn-ocs-in-flight-p phase)
        (cond ((and inspect (or (not (or commit reader)) (not (fn-ocs-lasti s))))
               (mv :inspect (fn-ocs-make (fn-ocs-ocm s) phase t)))
              (commit (mv :commit (fn-ocs-make (fn-ocs-ocm s) phase nil)))
              (reader (mv :reader (fn-ocs-make (fn-ocs-ocm s) phase nil)))
              (t (mv nil s)))
      (mv-let (class ocm) (fn-ocm-next (fn-ocs-ocm s) (fn-ocs-w4 w) commit)
        (cond ((and inspect (or (null class) (not (fn-ocs-lasti s))))
               (mv :inspect (fn-ocs-make (fn-ocs-ocm s) phase t)))
              (class (mv class (fn-ocs-make ocm phase nil)))
              (t (mv nil s)))))))

; The commit's event, applied by the host inside the :commit quantum that
; observed it (and, for the barrier's outcome, inside the quantum that
; follows it).  The pick's state is kept.
(defun fn-ocs-commit-event (s event)
  (declare (xargs :guard t))
  (mv-let (action phase) (fn-ocs-commit-step (fn-ocs-phase s) event)
    (mv action (fn-ocs-make (fn-ocs-ocm s) phase (fn-ocs-lasti s)))))

; The hold and wait fold: books/owner-commit-class.lisp's (an :inspect
; quantum folds into the control row, as the class it was before this book).
(defun fn-ocs-observe (s class hold-ms wait-ms)
  (declare (xargs :guard t))
  (fn-ocs-make (fn-ocm-observe (fn-ocs-ocm s) class hold-ms wait-ms)
               (fn-ocs-phase s) (fn-ocs-lasti s)))

(defun fn-ocs-health-lines (s)
  (declare (xargs :guard t))
  (fn-ocm-health-lines (fn-ocs-ocm s)))

; =============================================================================
; Theorems
;
; No pick of the four classes or of the commit class is an :inspect.
(local
 (defthm fn-ocs-osch-next-not-inspect
   (and (not (equal (mv-nth 0 (fn-osch-next s w)) :inspect))
        (not (equal (car (fn-osch-next s w)) :inspect)))
   :hints (("Goal" :in-theory (enable fn-osch-next)))))

(local
 (defthm fn-ocs-ocm-next-not-inspect
   (and (not (equal (mv-nth 0 (fn-ocm-next s w c)) :inspect))
        (not (equal (car (fn-ocm-next s w c)) :inspect)))
   :hints (("Goal" :in-theory (disable fn-osch-next fn-osch-idlep)))))

; fn-ocm-next's pick is used whole below, never reopened.
(local (in-theory (disable fn-ocm-next fn-ocm-next-otherwise-is-osch-next
                           fn-ocm-commit-pick-keeps-the-sched fn-ocs-w4)))

; While a batch is in flight only :inspect, :commit and :reader are
; admitted (or nobody): no control-socket poster, transit or mutating
; control quantum runs between a batch's START and its COMPLETE.
(defthm fn-ocs-in-flight-admits-only-inspect-commit-and-reader
  (implies (fn-ocs-in-flight-p (fn-ocs-phase s))
           (member-equal (mv-nth 0 (fn-ocs-next s w)) '(:inspect :commit :reader nil)))
  :hints (("Goal" :in-theory (disable fn-ocm-next fn-ocs-phase))))

; The pick names a class that waits: :inspect, and in flight :commit and
; :reader, by their counts (the four classes' by PRF-248's
; fn-osch-pick-has-a-waiter through fn-ocm-next).
(defthm fn-ocs-inspect-and-commit-picks-wait
  (and (implies (equal (mv-nth 0 (fn-ocs-next s w)) :inspect)
                (fn-ocs-inspect-waits-p w))
       (implies (and (equal (mv-nth 0 (fn-ocs-next s w)) :commit)
                     (fn-ocs-in-flight-p (fn-ocs-phase s)))
                (fn-ocs-commit-waits-p w))
       (implies (and (equal (mv-nth 0 (fn-ocs-next s w)) :reader)
                     (fn-ocs-in-flight-p (fn-ocs-phase s)))
                (fn-ocs-reader-waits-p w)))
  :hints (("Goal" :in-theory (disable fn-ocm-next fn-ocs-phase fn-ocs-w4
                                      fn-ocs-inspect-waits-p fn-ocs-commit-waits-p
                                      fn-ocs-reader-waits-p))))

; In flight a waiting commit step is never passed over for a reader: the
; START-NEXT and the COMPLETE are not delayed by the readers the barrier
; admits (at most one :inspect runs before it).
(defthm fn-ocs-in-flight-commit-before-reader
  (implies (and (fn-ocs-in-flight-p (fn-ocs-phase s))
                (fn-ocs-commit-waits-p w))
           (member-equal (mv-nth 0 (fn-ocs-next s w)) '(:inspect :commit)))
  :hints (("Goal" :in-theory (disable fn-ocm-next fn-ocs-phase fn-ocs-w4
                                      fn-ocs-inspect-waits-p fn-ocs-commit-waits-p
                                      fn-ocs-reader-waits-p))))

; Outside a batch, every pick that is not an :inspect is fn-ocm-next's own
; pick from the same state, and it leaves fn-ocm-next's state: PRF-248's
; control bound and fn-ocm-commit-waits-at-most-the-bound hold over the
; non-inspect quanta.  An :inspect pick leaves the four classes' and the
; commit class's state untouched.
(defthm fn-ocs-next-otherwise-is-ocm-next
  (implies (and (not (fn-ocs-in-flight-p (fn-ocs-phase s)))
                (not (equal (mv-nth 0 (fn-ocs-next s w)) :inspect)))
           (and (equal (mv-nth 0 (fn-ocs-next s w))
                       (mv-nth 0 (fn-ocm-next (fn-ocs-ocm s) (fn-ocs-w4 w)
                                              (fn-ocs-commit-waits-p w))))
                (implies (mv-nth 0 (fn-ocs-next s w))
                         (equal (fn-ocs-ocm (mv-nth 1 (fn-ocs-next s w)))
                                (mv-nth 1 (fn-ocm-next (fn-ocs-ocm s) (fn-ocs-w4 w)
                                                       (fn-ocs-commit-waits-p w)))))))
  :hints (("Goal" :in-theory (disable fn-ocm-next fn-ocs-w4 fn-ocs-phase
                                      fn-ocs-inspect-waits-p fn-ocs-commit-waits-p))))

(defthm fn-ocs-inspect-pick-keeps-the-ocm
  (implies (equal (mv-nth 0 (fn-ocs-next s w)) :inspect)
           (equal (fn-ocs-ocm (mv-nth 1 (fn-ocs-next s w))) (fn-ocs-ocm s)))
  :hints (("Goal" :in-theory (disable fn-ocm-next fn-ocs-w4 fn-ocs-phase
                                      fn-ocs-inspect-waits-p fn-ocs-commit-waits-p))))

; The phase is the commit's alone: a pick and a fold keep it.
(defthm fn-ocs-next-keeps-the-phase
  (equal (fn-ocs-phase (mv-nth 1 (fn-ocs-next s w))) (fn-ocs-phase s))
  :hints (("Goal" :in-theory (disable fn-ocm-next fn-ocs-w4
                                      fn-ocs-inspect-waits-p fn-ocs-commit-waits-p))))

; -----------------------------------------------------------------------------
; The step machine: the replies are released only after the barrier.

; COMPLETE (which releases the members' replies) is named only for a staged
; batch whose barrier the host observed returning.
(defthm fn-ocs-complete-only-after-the-barrier
  (implies (equal (mv-nth 0 (fn-ocs-commit-step phase event)) :complete)
           (and (equal phase :staged) (equal event :fenced)))
  :rule-classes nil)

; A batch is staged only by a START with members, whose action is the
; barrier (or it stays staged on an event the step does not expect: a fault).
(defthm fn-ocs-staged-only-by-a-start
  (implies (equal (mv-nth 1 (fn-ocs-commit-step phase event)) :staged)
           (or (and (not (fn-ocs-in-flight-p phase))
                    (equal event :started)
                    (equal (mv-nth 0 (fn-ocs-commit-step phase event)) :barrier))
               (and (equal phase :staged)
                    (equal (mv-nth 0 (fn-ocs-commit-step phase event)) :fault))))
  :rule-classes nil)

; The barrier is named only by a START, and what follows a staged batch is
; its COMPLETE, its stop, or a fault: never another START before the batch
; is completed.
(defthm fn-ocs-barrier-only-from-a-start
  (implies (equal (mv-nth 0 (fn-ocs-commit-step phase event)) :barrier)
           (and (not (fn-ocs-in-flight-p phase)) (equal event :started)
                (equal (mv-nth 1 (fn-ocs-commit-step phase event)) :staged)))
  :rule-classes nil)

(defthm fn-ocs-in-flight-until-completed
  (implies (and (fn-ocs-in-flight-p phase) (not (equal event :completed)))
           (fn-ocs-in-flight-p (mv-nth 1 (fn-ocs-commit-step phase event)))))

;; -----------------------------------------------------------------------------
;; The members' replies (lane scheduler-2-rebase, onto commit-onto-log's
;; per-member uncertain replies, 19202b0da).  The batch's ACTION is the step's
;; (:complete after a fenced barrier; :stop after a member ACL2 answered
;; uncertain, or a failed barrier); each member's OUTCOME is (WORD RENDERABLE):
;; WORD its own outcome word from ACL2 (the attempt's served or transit word,
;; :refused for a refusal before the attempt, :uncertain for an uncertain one),
;; RENDERABLE whether the owner kept what ACL2's uncertain reply for it is
;; rendered from (host/owner-host.lisp fn-owner-uncertain-reply-of's
;; arguments, taken before its outcome was fed).  The release names how the
;; host answers the member:
;;   :rendered         its own rendered completion: the acceptance or the
;;                     refusal its word decided, unchanged
;;   :own-uncertain    its own rendered completion, ACL2's uncertain line,
;;                     then the close
;;   :uncertain-reply  ACL2's uncertain reply for it, then the close
;;   :close            the close with no reply (uncertain to its client)
;; A member is told acceptance or refusal only in a COMPLETE, so only after
;; its batch's barrier returned; after a stop no member is told either (a
;; refusal can rest on an earlier member of the same batch whose record the
;; log may not hold), and the stop is the recovery event.

(defun fn-ocs-member-release (action word renderable)
  (declare (xargs :guard t))
  (cond ((eq word :uncertain) :own-uncertain)
        ((eq action :complete) :rendered)
        (renderable :uncertain-reply)
        (t :close)))

(defun fn-ocs-outcome-word (x)
  (declare (xargs :guard t))
  (if (consp x) (car x) nil))

(defun fn-ocs-outcome-renderable (x)
  (declare (xargs :guard t))
  (and (consp x) (consp (cdr x)) (cadr x) t))

; The host's call: every member's release, in the members' order.
; Executes by a loop (PKT-877, lane serve-depth): the recursion took one
; control-stack frame per element.  The :logic is the recursion, unchanged;
; the :exec collects onto an accumulator and reverses it (revappend).
(defun fn-ocs-member-releases-loop (action outcomes acc)
  (declare (xargs :guard (true-listp acc) :verify-guards nil))
  (if (consp outcomes)
      (fn-ocs-member-releases-loop action
                                   (cdr outcomes)
                                   (cons (fn-ocs-member-release action
                                                                (fn-ocs-outcome-word (car outcomes))
                                                                (fn-ocs-outcome-renderable (car outcomes)))
                                         acc))
    (revappend acc nil)))

(defun fn-ocs-member-releases (action outcomes)
  (declare (xargs :verify-guards nil :guard t))
  (mbe :logic
       (if (consp outcomes)
           (cons (fn-ocs-member-release action (fn-ocs-outcome-word (car outcomes))
                                        (fn-ocs-outcome-renderable (car outcomes)))
                 (fn-ocs-member-releases action (cdr outcomes)))
         nil)
       :exec (fn-ocs-member-releases-loop action outcomes nil)))

(local
 (defthm fn-ocs-member-releases-loop-is-revappend
   (equal (fn-ocs-member-releases-loop action outcomes acc)
          (revappend acc (fn-ocs-member-releases action outcomes)))
   :hints (("Goal" :induct (fn-ocs-member-releases-loop action outcomes acc)
                   :in-theory (union-theories '(fn-ocs-member-releases-loop fn-ocs-member-releases revappend car-cons cdr-cons)
                                              (theory 'minimal-theory))))))

(verify-guards fn-ocs-member-releases-loop)

(verify-guards fn-ocs-member-releases
  :hints (("Goal"
           :in-theory
           (union-theories '(revappend fn-ocs-member-releases)
                           (union-theories (theory 'minimal-theory)
                                           (executable-counterpart-theory :here)))
           :use
           ((:instance fn-ocs-member-releases-loop-is-revappend (acc nil))))))


(defthm fn-ocs-member-releases-length
  (equal (len (fn-ocs-member-releases action outcomes)) (len outcomes)))

(defthm fn-ocs-member-releases-nth-unfolds
  (implies (< (nfix i) (len outcomes))
           (equal (nth i (fn-ocs-member-releases action outcomes))
                  (fn-ocs-member-release
                   action (fn-ocs-outcome-word (nth i outcomes))
                   (fn-ocs-outcome-renderable (nth i outcomes))))))

; Per member: its own word decides its reply in a COMPLETE (acceptance or
; refusal alike, never replaced), an uncertain word is always answered
; uncertain, and outside a COMPLETE every member is answered uncertain.
(defthm fn-ocs-member-rendered-only-in-a-complete
  (iff (equal (fn-ocs-member-release action word renderable) :rendered)
       (and (equal action :complete) (not (equal word :uncertain)))))

(defthm fn-ocs-member-otherwise-uncertain
  (implies (not (equal (fn-ocs-member-release action word renderable) :rendered))
           (member-equal (fn-ocs-member-release action word renderable)
                         '(:own-uncertain :uncertain-reply :close))))

(defthm fn-ocs-member-uncertain-word-told-uncertain
  (implies (equal word :uncertain)
           (equal (fn-ocs-member-release action word renderable) :own-uncertain)))

;; Whether some member's word is not :uncertain (the members a COMPLETE
;; tells their rendered outcome).
(defun fn-ocs-member-releases-some-told-p (outcomes)
  (declare (xargs :guard t))
  (if (consp outcomes)
      (or (not (equal (fn-ocs-outcome-word (car outcomes)) :uncertain))
          (fn-ocs-member-releases-some-told-p (cdr outcomes)))
    nil))

(local (in-theory (disable fn-ocs-member-release)))

(local
 (defthm fn-ocs-member-releases-rendered-member
   (iff (member-equal :rendered (fn-ocs-member-releases action outcomes))
        (and (equal action :complete)
             (fn-ocs-member-releases-some-told-p outcomes)))
   :hints (("Goal" :in-theory (enable fn-ocs-member-release)))))

; KEYSTONE (PRF-267, the replies).  The subjects are the two calls the host
; makes for a batch (host/native/owner.lisp fnn-owner-commit-batch and
; fnn-owner-commit-queued-locked: the step's action from `fn-ocs-commit-step'
; -- through `fn-ocs-commit-event' for the committer -- then
; `fn-ocs-member-releases' over the members' outcomes).  Some member is told
; its rendered acceptance or refusal only when the batch was staged and its
; barrier returned fenced; after a failed barrier the step is the stop (the
; recovery event: the store fenced, exit 3) and no member is told acceptance
; or refusal.
(defthm fn-ocs-members-told-only-after-the-barrier
  (implies (member-equal :rendered
                         (fn-ocs-member-releases
                          (mv-nth 0 (fn-ocs-commit-step phase event)) outcomes))
           (and (equal phase :staged) (equal event :fenced)))
  :rule-classes nil
  :hints (("Goal" :in-theory (disable fn-ocs-member-releases-rendered-member)
           :use ((:instance fn-ocs-member-releases-rendered-member
                            (action (mv-nth 0 (fn-ocs-commit-step phase event))))
                 (:instance fn-ocs-complete-only-after-the-barrier)))))

(defthm fn-ocs-failed-barrier-stops-telling-no-member
  (implies (and (equal phase :staged) (equal event :failed))
           (and (equal (mv-nth 0 (fn-ocs-commit-step phase event)) :stop)
                (not (member-equal :rendered
                                   (fn-ocs-member-releases
                                    (mv-nth 0 (fn-ocs-commit-step phase event))
                                    outcomes))))))

; The committer's form of the keystone: its action comes from the gate's
; scheduler value through fn-ocs-commit-event.
(defthm fn-ocs-commit-event-action-unfolds
  (equal (mv-nth 0 (fn-ocs-commit-event s event))
         (mv-nth 0 (fn-ocs-commit-step (fn-ocs-phase s) event))))

; -----------------------------------------------------------------------------
; A refusal that wrote nothing is told at its drain (lane full-vs-uncertain,
; 2026-09-28; PRF-354).
;
; AGENTS.md: "Uncertain, refused and accepted stay distinct at every
; boundary."  A member whose attempt was refused for capacity (:unaffordable,
; :memberships: books/store-capacity-vector.lisp fn-cvec-article-refusal-word)
; or for its inputs (:malformed) staged no record: the prepare refused before
; any Store mutation and the host consumed the refused reservation
; (host/native/owner.lisp fnn-owner-attempt; host/owner-host.lisp
; fn-owner-prepare-buffer).  Its outcome, nothing stored, is known when it is
; drained, whatever any barrier does afterwards.  Before this such a member
; waited in its batch like every other and was told uncertain when a barrier
; that held no record of its own failed (:stop) or stalled past H (:stalled;
; books/owner-time-model.lisp fn-otm-stall-releases): a known refusal
; reported uncertain because of an unrelated sync.
;
; Now the START (host/native/owner.lisp fnn-owner-commit-start-locked, which
; is also START-NEXT's and the inline quantum's drain) asks
; `fn-ocs-told-at-drain-p' of each member's word and hands such a member its
; rendered refusal at once; it never joins the batch.  A START all of whose
; members were told so keeps none and names no barrier
; (`fn-ocs-unstaged-start-tells-its-refusals').
;
; Not told at the drain: a refusal that names another record (:duplicate,
; :conflict, and the generic :refused, which carries transit's already-have
; and the filing and login refusals).  It may rest on a member of the same
; batch, or of the batch in flight, whose record the log does not hold yet;
; it still waits for the barrier (fn-ocs-member-release).  A capacity refusal
; also reads the capacity the unfenced members use, but only its REASON does:
; the outcome it reports, nothing stored, holds whatever they become.

(defconst *fn-ocs-drain-refusals* '(:unaffordable :memberships :malformed))

(defun fn-ocs-told-at-drain-p (word)
  (declare (xargs :guard t))
  (if (member-equal word *fn-ocs-drain-refusals*) t nil))

; What the predicate admits, by its definition: never an acceptance, never
; an uncertain word, never a refusal that names another record.
(defthm fn-ocs-told-at-drain-p-by-definition
  (implies (fn-ocs-told-at-drain-p word)
           (and (not (equal word :durable))
                (not (equal word :durable-key-change-refused))
                (not (equal word :uncertain))
                (not (equal word :duplicate))
                (not (equal word :conflict))
                (not (equal word :refused))))
  :rule-classes nil)

; The number of members the batch keeps: those not told at their drain.
(defun fn-ocs-kept-count (words)
  (declare (xargs :guard t))
  (if (consp words)
      (+ (if (fn-ocs-told-at-drain-p (car words)) 0 1)
         (fn-ocs-kept-count (cdr words)))
    0))

(defun fn-ocs-all-told-at-drain-p (words)
  (declare (xargs :guard t))
  (if (consp words)
      (and (fn-ocs-told-at-drain-p (car words))
           (fn-ocs-all-told-at-drain-p (cdr words)))
    t))

; The START's observation for fn-ocs-commit-step (and books/owner-commit-
; pipeline.lisp fn-ocp-commit-step): UNCERTAIN whether a member's outcome or
; an observation was uncertain, KEPT how many members the batch kept.  Host:
; host/native/owner.lisp fnn-owner-commit-start-event.
(defun fn-ocs-start-event (uncertain kept)
  (declare (xargs :guard t))
  (cond (uncertain :started-uncertain)
        ((posp kept) :started)
        (t :started-none)))

(defthm fn-ocs-all-told-keeps-none
  (implies (fn-ocs-all-told-at-drain-p words)
           (equal (fn-ocs-kept-count words) 0)))

; KEYSTONE (PRF-354).  The subjects are the host's calls at a START
; (host/native/owner.lisp fnn-owner-commit-start-locked: fn-ocs-told-at-drain-p
; per member; fnn-owner-commit-start-event: fn-ocs-start-event; the inline
; quantum's fn-ocs-commit-step).  WORDS are the drained members' outcome
; words, observed certain.  When every one of them is a refusal that wrote
; nothing, the batch keeps no member, the START reports :started-none, and
; the step names no barrier and leaves the owner idle: each member was told
; its own refusal at its drain and no sync is run for them.
(defthm fn-ocs-unstaged-start-tells-its-refusals
  (implies (fn-ocs-all-told-at-drain-p words)
           (let ((event (fn-ocs-start-event nil (fn-ocs-kept-count words))))
             (and (equal (fn-ocs-kept-count words) 0)
                  (equal event :started-none)
                  (equal (mv-nth 0 (fn-ocs-commit-step :idle event)) :none)
                  (equal (mv-nth 1 (fn-ocs-commit-step :idle event)) :idle)))))

; And a member that names another record is kept: its START names the
; barrier, as before.
(defthm fn-ocs-kept-member-starts-the-barrier
  (implies (and (consp words) (not (fn-ocs-told-at-drain-p (car words))))
           (equal (mv-nth 0 (fn-ocs-commit-step
                             :idle (fn-ocs-start-event nil (fn-ocs-kept-count words))))
                  :barrier)))

; -----------------------------------------------------------------------------
; KEYSTONE.  The subject is `fn-ocs-next', which host/native/owner.lisp
; fnn-owner-gate-pick calls at every release of the owner and every arrival
; at an idle one; the commit's events are `fn-ocs-commit-event', which the
; committer (fnn-owner-committer-loop) applies inside its :commit quanta.
;
; WS the successive pick observations, each (W EVENT): W the waiting counts
; at the pick, EVENT what the commit reports if the pick is a :commit (any
; event: the bound does not depend on the commit's behaviour).  While the
; inspect class has a waiter at every pick, at most ONE quantum of another
; class runs before an :inspect quantum, from any state, in or out of a
; batch.  The barrier is no quantum at all (it is the :barrier ACTION, which
; the committer runs with the owner released), so the wall time an :inspect
; request waits is at most the longest single quantum plus its own -- never
; a barrier's fdatasync.

(defun fn-ocs-item-w (x)
  (declare (xargs :guard t))
  (if (consp x) (car x) nil))

(defun fn-ocs-item-event (x)
  (declare (xargs :guard t))
  (if (and (consp x) (consp (cdr x))) (cadr x) nil))

(defun fn-ocs-after (class s event)
  (declare (xargs :guard t))
  (if (eq class :commit) (mv-let (action s2) (fn-ocs-commit-event s event)
                           (declare (ignore action))
                           s2)
    s))

(defun fn-ocs-inspect-waitsp (ws)
  (declare (xargs :guard t))
  (if (consp ws)
      (and (fn-ocs-inspect-waits-p (fn-ocs-item-w (car ws)))
           (fn-ocs-inspect-waitsp (cdr ws)))
    t))

(defun fn-ocs-inspect-delay (s ws)
  (declare (xargs :guard t :measure (len ws)))
  (if (consp ws)
      (mv-let (class s2) (fn-ocs-next s (fn-ocs-item-w (car ws)))
        (cond ((eq class :inspect) 0)
              ((null class)
               (fn-ocs-inspect-delay s2 (cdr ws)))
              (t (+ 1 (fn-ocs-inspect-delay
                       (fn-ocs-after class s2 (fn-ocs-item-event (car ws)))
                       (cdr ws))))))
    0))

; The keystone's per-pick subjects, each about the function the gate calls
; (fn-ocs-next): a waiting :inspect is picked unless the pick before was an
; :inspect; with an :inspect waiting somebody is picked; any other pick
; clears LASTI; and a commit event keeps it.
(defthm fn-ocs-inspect-first-when-not-last
   (implies (and (fn-ocs-inspect-waits-p w) (not (fn-ocs-lasti s)))
            (equal (mv-nth 0 (fn-ocs-next s w)) :inspect))
   :hints (("Goal" :in-theory (disable fn-ocm-next fn-ocs-w4 fn-ocs-phase
                                       fn-ocs-commit-waits-p))))

(defthm fn-ocs-inspect-waiting-picks-someone
   (implies (fn-ocs-inspect-waits-p w)
            (mv-nth 0 (fn-ocs-next s w)))
   :hints (("Goal" :in-theory (disable fn-ocm-next fn-ocs-w4 fn-ocs-phase
                                       fn-ocs-commit-waits-p))))

(defthm fn-ocs-other-pick-clears-lasti
   (implies (and (mv-nth 0 (fn-ocs-next s w))
                 (not (equal (mv-nth 0 (fn-ocs-next s w)) :inspect)))
            (not (fn-ocs-lasti (mv-nth 1 (fn-ocs-next s w)))))
   :hints (("Goal" :in-theory (disable fn-ocm-next fn-ocs-w4 fn-ocs-phase
                                       fn-ocs-inspect-waits-p fn-ocs-commit-waits-p))))

(local
 (defthm fn-ocs-after-keeps-lasti
   (equal (fn-ocs-lasti (fn-ocs-after class s event)) (fn-ocs-lasti s))))

(local (in-theory (disable fn-ocs-next fn-ocs-after fn-ocs-lasti fn-ocs-inspect-waits-p)))

(local
 (defthm fn-ocs-inspect-delay-zero-when-not-last
   (implies (and (fn-ocs-inspect-waitsp ws) (not (fn-ocs-lasti s)))
            (equal (fn-ocs-inspect-delay s ws) 0))
   :hints (("Goal" :expand ((fn-ocs-inspect-delay s ws))))))

(defthm fn-ocs-inspect-waits-at-most-one
  ; KEYSTONE (PRF-267).
  (implies (fn-ocs-inspect-waitsp ws)
           (<= (fn-ocs-inspect-delay s ws) 1))
  :rule-classes :linear
  :hints (("Goal" :expand ((fn-ocs-inspect-delay s ws))
           :in-theory (disable fn-ocs-inspect-delay))))

(in-theory (disable fn-ocs-next fn-ocs-commit-event fn-ocs-observe fn-ocs-health-lines
                    fn-ocs-member-release fn-ocs-member-releases))
