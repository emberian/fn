; fn: a bound submission's commit as two quanta with the batch job off the
; owner (ruling 19, item LOCK-R2-COMMIT-INLINE-LOG-IO; 2026-10-07).
;
; THE DEFECT THIS RETIRES.  A bound submission or a BP transit that finds
; queued members commits them before its own record
; (host/native/owner.lisp fnn-owner-commit-queued-locked): START, the batch
; job (intent frames, extension, append, fdatasync, resolution frames) and
; COMPLETE, all inside the quantum the caller holds, so the owner mutex O is
; held across durable I/O (five R2 lock keys in host/native/io.lisp).
;
; THE SHAPE.  The batch job's own shape (books/owner-queued-work.lisp
; fn-oqw-phases): decided under O, executed off O, completed under O.
;   QUANTUM 1 (under O)  START captures the queued batch; the caller's
;                        submission is HELD (not taken, not queued).
;   OFF O                the batch job runs its phases (fn-oqw-step), on the
;                        syncer, holding no owner lock.
;   QUANTUM 2 (under O)  COMPLETE (the batch's replies), then, in the same
;                        quantum, the held submission's take, intent and
;                        resolution -- only after the batch reached :fenced.
; `fn-och-step' is the step the host calls in both quanta: the pipelined
; commit's step (books/owner-commit-pipeline.lisp fn-ocp-commit-step) with a
; HELD flag beside its NEXT flag.  A batch with a held submission never
; opens a next batch behind it (no START-NEXT takes a submission between the
; caller's two quanta), and its phases are the pipeline's in-flight phases,
; so the gate admits only :inspect, :commit and :reader between them
; (fn-ocs-in-flight-admits-only-inspect-commit-and-reader) and no control,
; poster or transit quantum takes a submission there either.
;
; STATEMENTS (statement first; ruling 19).
;   S0 fn-och-step-without-a-held-batch-is-the-pipeline's: with nothing held
;      and no held event, the step is fn-ocp-commit-step's.
;   S1 fn-och-phased-is-the-inline-commit: the phased run's effects, labels
;      dropped, are the inline commit's (fn-och-inline, built from the step
;      the inline host calls today, fn-ocs-commit-step), under every answer
;      of the batch job's effects.
;   S1b fn-och-phased-holds-the-owner-only-in-quanta: every effect the run
;      labels :off is a batch-job phase and every batch-job phase is :off.
;   S2 fn-och-a-held-batch-opens-no-next: a held batch never answers :wait
;      (a START-NEXT's) and never opens a next batch; until it is answered it
;      stays in an in-flight phase.
;   S3 fn-och-submit-only-behind-the-fence: the held submission is taken only
;      after the batch's :fence returned, or when START captured no batch.
;   S4 fn-och-a-failed-or-faulted-job-takes-no-submission: an uncertain job
;      stops (:stop, the uncertain answer and exit 3) and a faulted one
;      faults, as inline, and neither takes the held submission.
;   S5 fn-och-only-the-held-caller-collects: the committer never collects a
;      held batch nor starts a next one behind it; the held caller collects
;      it exactly when the syncer returned (its quantum 2 is the :commit pick
;      after the job, on its own thread).
(in-package "ACL2")
(include-book "owner-commit-pipeline")
(include-book "owner-queued-work")

; -----------------------------------------------------------------------------
; The step.  PHASE NEXT as fn-ocp-commit-step's; HELD whether the batch in
; flight carries a caller's held submission.  Answers (mv ACTION PHASE NEXT
; HELD).  Events of the held path: at :idle, :started-held (START captured a
; batch for a caller that holds its submission) and :started-none-held
; (no member kept: run the :frames job off O before submission); in flight, the job's
; :fenced / :failed and COMPLETE's :completed, as the pipeline's.
(defun fn-och-step (phase next held event)
  (declare (xargs :guard t))
  (cond
   ((not held)
    (cond ((and (not (member-eq phase '(:staged :fenced :failed)))
                (eq event :started-held))
           (mv :sync :staged nil t))
          ((and (not (member-eq phase '(:staged :fenced :failed)))
                (eq event :started-none-held))
           (mv :frames :staged nil t))
          (t (mv-let (action phase next) (fn-ocp-commit-step phase next event)
               (mv action phase next nil)))))
   ((and (eq event :crash) (fn-ocs-in-flight-p phase)) (mv :stop :failed nil t))
   ((eq phase :staged)
    (cond ((eq event :frames-fenced) (mv :submit :idle nil nil))
          ((eq event :frames-failed) (mv :stop :failed nil t))
          ((eq event :frames-fault) (mv :fault :failed nil t))
          ((eq event :fenced) (mv :complete :fenced nil t))
          ((eq event :failed) (mv :stop :failed nil t))
          (t (mv :fault :staged nil t))))
   ((eq phase :fenced)
    (cond ((eq event :completed) (mv :submit :idle nil nil))
          ;; COMPLETE found the owner stopping: no submission is taken.
          ((eq event :completed-stopping) (mv :none :idle nil nil))
          (t (mv :fault :fenced nil t))))
   ((eq phase :failed)
    (if (eq event :completed) (mv :none :idle nil nil) (mv :fault :failed nil t)))
   ;; A held flag outside an in-flight phase is no state the steps make: a fault.
   (t (mv :fault phase nil nil))))

; -----------------------------------------------------------------------------
; The inline commit as the host runs it today (fnn-owner-commit-queued-locked
; and its caller): its effects in order.  START-EVENT is START's event
; (:started, :started-none, :started-uncertain), WORDS the batch job's
; effects' answers.  :start START; the job's phases; :complete COMPLETE;
; :stop the uncertain answer and the stop; :fault the fault; :submit the
; caller's own take, intent and resolution.
(defun fn-och-job-final (words)
  (declare (xargs :guard t))
  (fn-oqw-final :batch (fn-oqw-start :batch) words))

(defun fn-och-job-trace (words)
  (declare (xargs :guard t))
  (fn-oqw-trace :batch (fn-oqw-start :batch) words))

(defun fn-och-inline (start-event words)
  (declare (xargs :guard t))
  (mv-let (a1 p1) (fn-ocs-commit-step :idle start-event)
    (declare (ignore p1))
    (cons :start
          (cond ((eq a1 :barrier)
                 (let ((outcome (fn-oqw-outcome-of-final (fn-och-job-final words))))
                   (append (fn-och-job-trace words)
                           (if (eq outcome :fault)
                               '(:fault)
                             (mv-let (a2 p2)
                               (fn-ocs-commit-step :staged
                                                   (if (eq outcome :fenced) :fenced :failed))
                               (declare (ignore p2))
                               (if (eq a2 :complete) '(:complete :submit) '(:stop)))))))
                ((eq a1 :none)
                 (append (fn-oqw-trace :frames (fn-oqw-start :frames) words)
                         (case (fn-oqw-final :frames (fn-oqw-start :frames) words)
                           (:done '(:submit)) (:uncertain '(:stop)) (otherwise '(:fault)))))
                ((eq a1 :stop) '(:stop))
                (t '(:fault))))))

; -----------------------------------------------------------------------------
; The phased run: the effects with where each runs, (:owner . E) inside a
; quantum, (:off . E) on the syncer.  START's event for a caller that holds
; its submission is the held one; a word START does not answer is
; :unknown-start, which every step refuses (:fault), as inline.
(defun fn-och-held-event (start-event)
  (declare (xargs :guard t))
  (cond ((eq start-event :started) :started-held)
        ((eq start-event :started-none) :started-none-held)
        ((eq start-event :started-uncertain) :started-uncertain)
        (t :unknown-start)))

(defun fn-och-off (trace)
  (declare (xargs :guard t))
  (if (consp trace)
      (cons (cons :off (car trace)) (fn-och-off (cdr trace)))
    nil))

; The second quantum: from the step's state after START and the job's
; outcome, the effects under the owner.
(defun fn-och-q2 (p1 n1 h1 outcome)
  (declare (xargs :guard t))
  (if (eq outcome :fault)
      '((:owner . :fault))
    (mv-let (a2 p2 n2 h2)
      (fn-och-step p1 n1 h1 (if (eq outcome :fenced) :fenced :failed))
      (cond ((eq a2 :complete)
             (mv-let (a3 p3 n3 h3) (fn-och-step p2 n2 h2 :completed)
               (declare (ignore p3 n3 h3))
               (cons '(:owner . :complete)
                     (if (eq a3 :submit)
                         '((:owner . :submit))
                       '((:owner . :fault))))))
            ((eq a2 :stop) '((:owner . :stop)))
            (t '((:owner . :fault)))))))

(defun fn-och-run (start-event words)
  (declare (xargs :guard t))
  (mv-let (a1 p1 n1 h1) (fn-och-step :idle nil nil (fn-och-held-event start-event))
    (cons
     '(:owner . :start)
     (cond
      ((eq a1 :sync)
       (append (fn-och-off (fn-och-job-trace words))
               (fn-och-q2 p1 n1 h1 (fn-oqw-outcome-of-final (fn-och-job-final words)))))
      ((eq a1 :frames)
       (append (fn-och-off (fn-oqw-trace :frames (fn-oqw-start :frames) words))
               (case (fn-oqw-final :frames (fn-oqw-start :frames) words)
                 (:done '((:owner . :submit)))
                 (:uncertain '((:owner . :stop)))
                 (otherwise '((:owner . :fault))))))
      ((eq a1 :stop) '((:owner . :stop)))
      (t '((:owner . :fault)))))))

; Every :off effect is a batch-job phase and every batch-job phase is :off.
(defun fn-och-labelsp (run)
  (declare (xargs :guard t))
  (if (consp run)
      (and (consp (car run))
           (iff (eq (car (car run)) :off)
                (member-equal (cdr (car run)) (fn-oqw-phases :batch)))
           (member-eq (car (car run)) '(:owner :off))
           (fn-och-labelsp (cdr run)))
    t))

; The effects after the first :fence (all of RUN when it has none).
(defun fn-och-after-fence (effects)
  (declare (xargs :guard t))
  (cond ((atom effects) nil)
        ((eq (car effects) :fence) (cdr effects))
        (t (fn-och-after-fence (cdr effects)))))

; -----------------------------------------------------------------------------
; The statements.

; S0.  The committer's own path is the pipeline's, unchanged.
(defthm fn-och-step-without-a-held-batch-is-the-pipelines
  (implies (and (not held)
                (not (member-equal event '(:started-held :started-none-held))))
           (and (equal (mv-nth 0 (fn-och-step phase next held event))
                       (mv-nth 0 (fn-ocp-commit-step phase next event)))
                (equal (mv-nth 1 (fn-och-step phase next held event))
                       (mv-nth 1 (fn-ocp-commit-step phase next event)))
                (equal (mv-nth 2 (fn-och-step phase next held event))
                       (mv-nth 2 (fn-ocp-commit-step phase next event)))
                (not (mv-nth 3 (fn-och-step phase next held event))))))

; KEYSTONE S1.  The phased commit has the inline commit's effects, in its
; order, under every answer of the batch job's effects and every START.
(defthm fn-och-phased-is-the-inline-commit
  (equal (strip-cdrs (fn-och-run start-event words))
         (fn-och-inline start-event words)))

(local
 (defthm fn-och-labelsp-of-append
   (equal (fn-och-labelsp (append a b))
          (and (fn-och-labelsp a) (fn-och-labelsp b)))))

(local
 (defthm fn-och-off-of-a-trace-is-labelled
   (implies (subsetp-equal trace (fn-oqw-phases :batch))
            (fn-och-labelsp (fn-och-off trace)))))

(local
 (defun fn-och-trace-ind (phase words)
   (declare (xargs :measure (acl2-count words)))
   (if (or (atom words) (fn-oqw-terminalp phase))
       nil
     (fn-och-trace-ind (fn-oqw-step :batch phase (car words)) (cdr words)))))

(local
 (defthm fn-och-batch-step-stays-known
   (implies (or (member-equal phase (fn-oqw-phases :batch)) (fn-oqw-terminalp phase))
            (or (member-equal (fn-oqw-step :batch phase word) (fn-oqw-phases :batch))
                (fn-oqw-terminalp (fn-oqw-step :batch phase word))))
   :hints (("Goal" :in-theory (enable fn-oqw-step fn-oqw-after fn-oqw-terminalp fn-oqw-phases)))
   :rule-classes nil))

(local
 (defthm fn-och-trace-phases
   (implies (or (member-equal phase (fn-oqw-phases :batch)) (fn-oqw-terminalp phase))
            (subsetp-equal (fn-oqw-trace :batch phase words) (fn-oqw-phases :batch)))
   :hints (("Goal" :induct (fn-och-trace-ind phase words)
                   :in-theory (e/d (fn-oqw-trace)
                                   (fn-oqw-trace-opens-at-a-known-phase fn-oqw-step
                                    fn-oqw-terminalp fn-oqw-phases)))
           ("Subgoal *1/2" :use ((:instance fn-och-batch-step-stays-known (word (car words))))))))

; KEYSTONE S1b.  The owner is held only in the quanta: the run's :off
; effects are exactly the batch job's phases.
(local
 (defthm fn-och-q2-is-labelled
   (fn-och-labelsp (fn-och-q2 p1 n1 h1 outcome))))

(local
 (defthm fn-och-job-trace-is-labelled
   (fn-och-labelsp (fn-och-off (fn-och-job-trace words)))
   :hints (("Goal" :in-theory (disable fn-oqw-trace)
                   :use ((:instance fn-och-trace-phases (phase (fn-oqw-start :batch))))))))

(defthm fn-och-phased-holds-the-owner-only-in-quanta
  (fn-och-labelsp (fn-och-run start-event words))
  :hints (("Goal" :in-theory (disable fn-och-q2 fn-och-job-trace fn-och-off fn-och-job-final
                                      fn-oqw-outcome-of-final))))

; KEYSTONE S2.  A held batch opens no next batch and answers no START-NEXT;
; until it is answered (back at :idle) it is in an in-flight phase, where the
; gate admits only :inspect, :commit and :reader.
(defthm fn-och-a-held-batch-opens-no-next
  (implies held
           (and (not (mv-nth 2 (fn-och-step phase next held event)))
                (not (equal (mv-nth 0 (fn-och-step phase next held event)) :wait))
                (implies (mv-nth 3 (fn-och-step phase next held event))
                         (fn-ocs-in-flight-p (mv-nth 1 (fn-och-step phase next held event)))))))

; KEYSTONE S3.  The held submission is taken only behind the batch's fence:
; when the run takes it after the batch job ran, the job's :fence returned
; and the take follows it.
(defthm fn-och-submit-only-behind-the-fence
  (let ((effects (strip-cdrs (fn-och-run start-event words))))
    (implies (and (member-equal :submit effects)
                  (consp (fn-och-job-trace words))
                  (equal start-event :started))
             (and (equal (fn-och-job-final words) :done)
                  (member-equal :submit (fn-och-after-fence effects))))))

; KEYSTONE S4.  A job that ended uncertain stops and one that faulted
; faults, as inline, and neither takes the held submission.
(defthm fn-och-a-failed-or-faulted-job-takes-no-submission
  (let ((effects (strip-cdrs (fn-och-run :started words)))
        (final (fn-och-job-final words)))
    (implies (not (equal final :done))
             (and (not (member-equal :submit effects))
                  (equal (car (last effects))
                         (if (equal final :uncertain) :stop :fault))))))

; -----------------------------------------------------------------------------
; The wakes (C's ruling-19 option 1).  The batch in flight is collected by
; exactly one thread.  For a held batch it is the held caller (its quantum 2
; is the :commit pick that follows the job); the committer never collects it
; and never prepares a next batch behind it.  RETURNED whether the syncer
; returned; QUEUED BLOCKED as fn-ocp-wake's.
(defun fn-och-committer-wake (phase next held returned queued blocked)
  (declare (xargs :guard t))
  (if held :wait (fn-ocp-wake phase next returned queued blocked)))

(defun fn-och-caller-wake (phase held returned)
  (declare (xargs :guard t))
  (if (and held (fn-ocs-in-flight-p phase) returned) :collect :wait))

; KEYSTONE S5.  With a held batch in flight the committer neither collects it
; nor starts a next batch; the held caller collects it exactly when the syncer
; returned.  Without a held batch the committer's wake is the pipeline's.
(defthm fn-och-only-the-held-caller-collects
  (and (implies held
                (equal (fn-och-committer-wake phase next held returned queued blocked) :wait))
       (iff (equal (fn-och-caller-wake phase held returned) :collect)
            (and held (fn-ocs-in-flight-p phase) returned))
       (implies (not held)
                (and (equal (fn-och-committer-wake phase next held returned queued blocked)
                            (fn-ocp-wake phase next returned queued blocked))
                     (equal (fn-och-caller-wake phase held returned) :wait)))))

; -----------------------------------------------------------------------------
; Gap answers for the host split (C6, 2026-10-08).
;
; (1) The committer's START.  A committer that passed its snapshot before a
; caller's quantum 1 captured the batch must not run its own START (its drain
; would take members) while that batch is held: it asks first, and a refused
; pass returns as a pipeline that took nobody (:none).
(defun fn-och-committer-may-start (phase held)
  (declare (xargs :guard t))
  (and (not held) (not (fn-ocs-in-flight-p phase))))

; (2) The stop.  A held batch's stop is the step's own: :failed -> :stop (every
; member uncertain, fn-ocs-member-release with action :stop), then :completed
; -> :none; a COMPLETE that found the owner stopping sends :completed-stopping
; -> :none.  Neither takes the held submission.
;
; (3) The caller's answer, from the last action quantum 2's events named:
; :submit -> its submission is taken (the take, intent and resolution);
; :none or :stop -> it is refused with the stopping answer (the owner is
; stopping and the submission was never taken; the client may retry against
; the recovered node); anything else -> :fault.
(defun fn-och-caller-answer (action)
  (declare (xargs :guard t))
  (cond ((eq action :submit) :submitted)
        ((member-eq action '(:none :stop)) :stopping)
        (t :fault)))

; The answer of a held caller whose job ended FINAL, when COMPLETE found the
; owner STOPPING or not.
(defun fn-och-held-outcome (final stopping)
  (declare (xargs :guard t))
  (let ((outcome (fn-oqw-outcome-of-final final)))
    (if (eq outcome :fault)
        :fault
      (mv-let (a2 p2 n2 h2)
        (fn-och-step :staged nil t (if (eq outcome :fenced) :fenced :failed))
        (if (eq a2 :stop)
            (mv-let (a3 p3 n3 h3) (fn-och-step p2 n2 h2 :completed)
              (declare (ignore a3 p3 n3 h3))
              (fn-och-caller-answer :stop))
          (mv-let (a3 p3 n3 h3)
            (fn-och-step p2 n2 h2 (if stopping :completed-stopping :completed))
            (declare (ignore p3 n3 h3))
            (fn-och-caller-answer a3)))))))

; KEYSTONE S6.  The committer never STARTs while a batch is held or in
; flight, and may START at an idle owner with nothing held (its path today).
(defthm fn-och-committer-never-starts-under-a-held-batch
  (and (implies held (not (fn-och-committer-may-start phase held)))
       (iff (fn-och-committer-may-start phase nil)
            (not (fn-ocs-in-flight-p phase)))))

; KEYSTONE S7.  The held caller's answer: taken exactly when the job ran every
; phase and COMPLETE did not find the owner stopping; the stopping answer when
; the job ended uncertain or the owner is stopping; a fault for a faulted job.
; A stop never takes the submission and never answers it as taken.
(defthm fn-och-held-caller-answer
  (let ((a (fn-och-held-outcome final stopping)))
    (and (member-equal a '(:submitted :stopping :fault))
         (iff (equal a :submitted) (and (equal final :done) (not stopping)))
         (iff (equal a :stopping)
              (or (equal final :uncertain) (and (equal final :done) stopping)))
         (iff (equal a :fault)
              (and (not (equal final :done)) (not (equal final :uncertain))))))
  :hints (("Goal" :in-theory (enable fn-oqw-outcome-of-final))))

; S7 agrees with the inline commit for a non-stopping owner: the inline
; effects end in :submit exactly when the held caller's answer is :submitted.
(defthm fn-och-held-caller-answer-is-the-inline-commits
  (iff (equal (fn-och-held-outcome (fn-och-job-final words) nil) :submitted)
       (member-equal :submit (fn-och-inline :started words))))


; The no-member drain has the queued-work :frames job's own outcome.
(defun fn-och-frames-event (final)
  (declare (xargs :guard t))
  (case final
    (:done :frames-fenced)
    (:uncertain :frames-failed)
    (otherwise :frames-fault)))

; Effects of the actual step: all queued-work phases are I/O, including
; :intents (FNFD append, journal barrier, then the drain's refusal replies).
(defun fn-och-action-effects (action)
  (declare (xargs :guard t))
  (case action
    (:sync (fn-och-off (fn-oqw-phases :batch)))
    (:frames (fn-och-off (fn-oqw-phases :frames)))
    (otherwise (list (cons :owner action)))))

(defthm fn-och-frames-held-until-the-job-returns
  (and (equal (fn-och-step :idle nil nil :started-none-held)
              '(:frames :staged nil t))
       (equal (mv-nth 0 (fn-och-step :staged nil t (fn-och-frames-event final)))
              (case final (:done :submit) (:uncertain :stop) (otherwise :fault)))
       (iff (mv-nth 3 (fn-och-step :staged nil t (fn-och-frames-event final)))
            (not (equal final :done)))))

; Process death at either boundary between the caller's quanta, or within
; an off-owner job, is a crash observation. No completion can turn that
; uncertain job into a submission. Persistent FNFD bytes are separately
; recovered by feed-journal's :crash/scan model; scheduler state is volatile.
(defthm fn-och-held-crash-never-submits
  (implies (and held (fn-ocs-in-flight-p phase))
           (mv-let (action phase2 next2 held2) (fn-och-step phase next held :crash)
             (and (equal action :stop)
                  (equal phase2 :failed)
                  (equal (mv-nth 0 (fn-och-step phase2 next2 held2 :completed)) :none)))))
