; fn: the owner's pipelined group commit -- the next batch prepares while the
; batch in flight's fdatasync runs (lane log-2, 2026-09-27; design
; 2026-09-27-storage-log section 8, "the barrier overlaps the next batch's
; prepares"; PKT-COL "publication off the mutex").
;
; books/owner-commit-steps.lisp (lane owner-scheduler-2) split the commit in
; three: START (a :commit quantum: members into the log's open batch), the
; BARRIER with the owner released, COMPLETE (a :commit quantum: the replies).
; This book lets a second START run while the barrier is in flight:
;
;   START       (:commit quantum) at most the batch bound of queued members
;               into the kernel's open batch, then the SEAL: the batch's
;               append (fn-lgk-append: the batch becomes the one in flight).
;   SYNC        not a quantum: the syncer thread's fdatasync and the kernel's
;               fence, under the log's own lock (host/native/io.lisp
;               fnn-log-sync-sealed-batch); the owner is released.
;   START-NEXT  (:commit quantum, only while a batch is in flight and no
;               next batch is open) queued members into the kernel's open
;               batch BEHIND the one in flight: fn-lgk-prepare admits it
;               (only a faulted kernel refuses) and fn-lgk-fence keeps it.
;               Nothing is appended: fn-lgk-append refuses while a batch is
;               in flight, so the log's order is the batches' order.
;   COMPLETE    (:commit quantum, only after SYNC returned fenced) the
;               acknowledgements, lines, feed resolutions and replies of the
;               batch in flight; then, when a next batch is open, its SEAL,
;               and it becomes the batch in flight (its members' replies wait
;               for ITS sync).
;   STOP        a failed sync, or an uncertain member of either batch: every
;               member of both batches is answered uncertain and the owner
;               stops (exit 3); recovery decides from the log (T7).
;
; The gate's pick is books/owner-commit-steps.lisp's fn-ocs-next unchanged
; (fn-ocp-next-is-ocs-next), and a next batch is open only while the ocs
; phase is in flight (fn-ocp-next-open-only-in-flight), so while any
; prepared record is not yet durable only :inspect, :commit and :reader
; quanta run (fn-ocs-in-flight-admits-only-inspect-commit-and-reader), and a
; reader reads at the view captured before the batch in flight was prepared
; (books/owner-reader-view.lisp, coordinator decision PKT-828): no control-
; socket poster, transit or mutating control quantum runs, and no read
; reveals a record of either batch before its COMPLETE.
(in-package "ACL2")
(include-book "owner-commit-steps")

; -----------------------------------------------------------------------------
; The scheduler value: (OCS NEXT), OCS books/owner-commit-steps.lisp's value,
; NEXT whether a next batch is open behind the batch in flight.

(defun fn-ocp-ocs (s)
  (declare (xargs :guard t))
  (if (consp s) (car s) nil))

(defun fn-ocp-open-next (s)
  (declare (xargs :guard t))
  (if (and (consp s) (consp (cdr s)) (cadr s)) t nil))

(defun fn-ocp-make (ocs next)
  (declare (xargs :guard t))
  (list ocs (if next t nil)))

(defun fn-ocp-init ()
  (declare (xargs :guard t))
  (fn-ocp-make (fn-ocs-init) nil))

; -----------------------------------------------------------------------------
; The commit's steps.  PHASE is the ocs phase (:idle :staged :fenced
; :failed), NEXT whether a next batch is open.  EVENT is what the host
; observed at the end of the step it ran.  Answers (mv ACTION PHASE' NEXT'):
;   :sync      hand the sealed batch to the syncer (START sealed it, or
;              COMPLETE sealed the next batch)
;   :wait      nothing to run under the owner; wait for the sync or a
;              queued member
;   :complete  (a :commit quantum) acknowledge the batch in flight and
;              release its replies; then seal the next batch if one is open
;   :stop      (a :commit quantum) every member of both batches uncertain,
;              the owner stops
;   :none      no batch remains
;   :fault     an event the step does not expect
(defun fn-ocp-commit-step (phase next event)
  (declare (xargs :guard t))
  (let ((next (if next t nil)))
    (cond
     ((eq phase :staged)
      (cond ((eq event :next-started)
             (if next (mv :fault phase next) (mv :wait :staged t)))
            ((eq event :next-none) (mv :wait :staged next))
            ((eq event :next-uncertain) (mv :stop :failed next))
            ((eq event :fenced) (mv :complete :fenced next))
            ((eq event :failed) (mv :stop :failed next))
            (t (mv :fault phase next))))
     ((eq phase :fenced)
      (cond ((not (eq event :completed)) (mv :fault phase next))
            (next (mv :sync :staged nil))
            (t (mv :none :idle nil))))
     ((eq phase :failed)
      ;; Already stopping (an uncertain member behind the barrier): the
      ;; barrier's word changes nothing; every member is uncertain.
      (cond ((eq event :completed) (mv :none :idle nil))
            ((or (eq event :fenced) (eq event :failed)) (mv :stop :failed next))
            (t (mv :fault phase next))))
     (t
      (cond ((eq event :started) (mv :sync :staged nil))
            ((eq event :started-none) (mv :none :idle nil))
            ((eq event :started-uncertain) (mv :stop :idle nil))
            (t (mv :fault :idle nil)))))))

; The classes a batch in flight shuts out (fn-ocs-in-flight-admits-only-
; inspect-commit-and-reader): control (slot 0), poster (slot 2) and transit
; (slot 3).  W is the gate's six waiting counts.
(defun fn-ocp-excluded-waits-p (w)
  (declare (xargs :guard t))
  (or (posp (fn-osch-waits 0 w)) (posp (fn-osch-waits 2 w))
      (posp (fn-osch-waits 3 w))))

; The committer's wake while a batch is in flight: RETURNED whether the
; syncer returned, QUEUED whether a member waits, BLOCKED whether a class the
; batch in flight shuts out waits at the gate.  :collect (report the sync's
; word in a :commit quantum), :start-next, or :wait.
;
; Lane durability-bugs (PKT-700/701, scheduler-3's finding): with no BLOCKED
; the pipeline under sustained POST load always had a batch in flight -- the
; COMPLETE sealed the next batch, which a START-NEXT had prepared behind the
; barrier -- so a control, poster or transit waiter was never admitted.  A
; waiting shut-out class now stops the pipeline from preparing another batch:
; the batches already sealed or open complete and the owner leaves flight,
; where books/owner-scheduler.lisp's cyclic pick (PRF-248) serves it.  The
; bound is books/owner-commit-fairness.lisp's.
(defun fn-ocp-wake (phase next returned queued blocked)
  (declare (xargs :guard t))
  (cond ((not (fn-ocs-in-flight-p phase)) :wait)
        (returned :collect)
        ((and (eq phase :staged) queued (not next) (not blocked)) :start-next)
        (t :wait)))

; -----------------------------------------------------------------------------
; The host's entries over the gate's value.

(defun fn-ocp-next (s w)
  (declare (xargs :guard t))
  (mv-let (class ocs) (fn-ocs-next (fn-ocp-ocs s) w)
    (mv class (fn-ocp-make ocs (fn-ocp-open-next s)))))

(defun fn-ocp-observe (s class hold-ms wait-ms)
  (declare (xargs :guard t))
  (fn-ocp-make (fn-ocs-observe (fn-ocp-ocs s) class hold-ms wait-ms)
               (fn-ocp-open-next s)))

(defun fn-ocp-health-lines (s)
  (declare (xargs :guard t))
  (fn-ocs-health-lines (fn-ocp-ocs s)))

(defun fn-ocp-commit-event (s event)
  (declare (xargs :guard t))
  (let ((ocs (fn-ocp-ocs s)))
    (mv-let (action phase next)
      (fn-ocp-commit-step (fn-ocs-phase ocs) (fn-ocp-open-next s) event)
      (mv action (fn-ocp-make (fn-ocs-make (fn-ocs-ocm ocs) phase (fn-ocs-lasti ocs))
                              next)))))

(defun fn-ocp-committer-wake (s returned queued w)
  (declare (xargs :guard t))
  (fn-ocp-wake (fn-ocs-phase (fn-ocp-ocs s)) (fn-ocp-open-next s)
               (if returned t nil) (if queued t nil) (fn-ocp-excluded-waits-p w)))

; =============================================================================
; Theorems.

(local (in-theory (disable fn-ocs-next fn-ocs-observe fn-ocs-health-lines)))

(defthm fn-ocp-phase-of-ocs-make
  (equal (fn-ocs-phase (fn-ocs-make ocm phase lasti))
         (if (fn-ocs-in-flight-p phase) phase :idle)))

(local (in-theory (disable fn-ocs-make fn-ocs-phase)))

; The pick is books/owner-commit-steps.lisp's: every keystone of that book
; (PRF-267's inspect bound, the in-flight admission, PRF-248's control bound
; through fn-ocm-next) holds of the host's pick unchanged.
(defthm fn-ocp-next-is-ocs-next
  (and (equal (mv-nth 0 (fn-ocp-next s w)) (mv-nth 0 (fn-ocs-next (fn-ocp-ocs s) w)))
       (equal (fn-ocp-ocs (mv-nth 1 (fn-ocp-next s w)))
              (mv-nth 1 (fn-ocs-next (fn-ocp-ocs s) w)))
       (equal (fn-ocp-open-next (mv-nth 1 (fn-ocp-next s w))) (fn-ocp-open-next s))))

; COMPLETE, which releases the replies of the batch in flight, is named only
; when the syncer returned fenced for that batch.  A next batch's members are
; not the batch in flight until COMPLETE seals it (:sync from :fenced), so
; their replies wait for their own sync.
(defthm fn-ocp-complete-only-after-the-barrier
  (implies (equal (mv-nth 0 (fn-ocp-commit-step phase next event)) :complete)
           (and (equal phase :staged) (equal event :fenced)))
  :rule-classes nil)

; The replies' release, over the host's entry: COMPLETE is the action only
; when the commit was staged (a sealed batch in flight) and the host reported
; the barrier fenced.
(defthm fn-ocp-commit-event-completes-only-after-the-barrier
  (implies (equal (mv-nth 0 (fn-ocp-commit-event s event)) :complete)
           (and (equal (fn-ocs-phase (fn-ocp-ocs s)) :staged) (equal event :fenced)))
  :rule-classes nil
  :hints (("Goal" :use ((:instance fn-ocp-complete-only-after-the-barrier
                                   (phase (fn-ocs-phase (fn-ocp-ocs s)))
                                   (next (fn-ocp-open-next s)))))))

; A batch is handed to the syncer only when none is in flight: from an idle
; owner after a START, or by COMPLETE after the batch in flight was fenced
; and acknowledged.  So appends are in the batches' order and at most one
; batch is ever in flight.
(defthm fn-ocp-sync-only-when-none-in-flight
  (implies (equal (mv-nth 0 (fn-ocp-commit-step phase next event)) :sync)
           (or (and (not (fn-ocs-in-flight-p phase)) (equal event :started))
               (and (equal phase :fenced) next (equal event :completed))))
  :rule-classes nil)

; PRF-354 over the committer's step (host/native/owner.lisp
; fnn-owner-commit-pipeline's START, through fn-otm-commit-event, which is
; this step: fn-otm-commit-event-is-ocp-commit-event): a START whose members
; were all refusals told at their drain names no sync.
(defthm fn-ocp-unstaged-start-issues-no-sync
  (implies (fn-ocs-all-told-at-drain-p words)
           (let ((event (fn-ocs-start-event nil (fn-ocs-kept-count words))))
             (and (equal (mv-nth 0 (fn-ocp-commit-step :idle next event)) :none)
                  (equal (mv-nth 1 (fn-ocp-commit-step :idle next event)) :idle)
                  (not (mv-nth 2 (fn-ocp-commit-step :idle next event)))))))

; A next batch is opened only behind a batch in flight, and only one.
(defthm fn-ocp-next-opens-only-behind-a-sync
  (implies (and (not next) (mv-nth 2 (fn-ocp-commit-step phase next event)))
           (and (equal phase :staged) (equal event :next-started)))
  :rule-classes nil)

(defthm fn-ocp-start-next-only-behind-a-sync
  (implies (equal (fn-ocp-wake phase next returned queued blocked) :start-next)
           (and (equal phase :staged) (not next) (not returned) queued (not blocked)))
  :rule-classes nil)

; A waiting control, poster or transit request stops the pipeline: the
; committer's wake never prepares another batch while one waits.
(defthm fn-ocp-no-start-next-while-a-shut-out-class-waits
  (implies (fn-ocp-excluded-waits-p w)
           (not (equal (fn-ocp-committer-wake s returned queued w) :start-next))))

; KEYSTONE.  A next batch is open only while the ocs phase is in flight, so
; the gate (fn-ocs-next, fn-ocp-next-is-ocs-next) admits only :inspect,
; :commit and :reader while any prepared record -- of the batch in flight or
; of the next one -- is not yet durable, and the readers read at the reader
; view (books/owner-reader-view.lisp fn-ocv-reader-view-is-the-completed-
; prefix): no quantum can reveal it.  The subject is fn-ocp-commit-event, which
; host/native/owner.lisp fnn-owner-commit-event calls inside the committer's
; :commit quanta.
(defthm fn-ocp-next-open-only-in-flight
  (implies (fn-ocp-open-next (mv-nth 1 (fn-ocp-commit-event s event)))
           (fn-ocs-in-flight-p
            (fn-ocs-phase (fn-ocp-ocs (mv-nth 1 (fn-ocp-commit-event s event))))))
  :hints (("Goal" :in-theory (enable fn-ocs-phase))))

(defthm fn-ocp-in-flight-admits-only-inspect-commit-and-reader
  (implies (fn-ocs-in-flight-p (fn-ocs-phase (fn-ocp-ocs s)))
           (member-equal (mv-nth 0 (fn-ocp-next s w)) '(:inspect :commit :reader nil)))
  :hints (("Goal" :use ((:instance fn-ocs-in-flight-admits-only-inspect-commit-and-reader
                                   (s (fn-ocp-ocs s)))))))

(in-theory (disable fn-ocp-next fn-ocp-commit-event fn-ocp-observe fn-ocp-health-lines
                    fn-ocp-committer-wake))
