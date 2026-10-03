; fn: off-owner work and its receipt (lane owner-offlock, 2026-10-03;
; r71 F4 F6 F7 F8, r72 item 3, sweep S014 S022; decisions
; build/coordinator/decisions/whole-system-correctness-2026-10-03.md
; section 10.5 R2 and host-into-acl2-2026-10-03.md).
;
; THE RULE.  Blocking I/O and waits never run while the owner mutex is held.
; Owner work that must block becomes a JOB: decided under the owner (what to
; do, captured as immutable values), executed by a thread that holds no
; owner lock, and completed by a RECEIPT the owner consumes in a later
; section.  This book is the decision half of that shape, so the generated
; protocol can absorb it: the host keeps the thread and the syscalls.
;
;   1. THE JOB'S EFFECT ORDER (fn-oqw-step).  A job of KIND runs the phases
;      fn-oqw-phases names, in that order, one at a time; the host executes
;      the phase ACL2 names and reports one word: :ok (the effect returned),
;      :uncertain (its outcome is not known: an ambiguous persistence
;      failure, a recovery event) or anything else (a fault).  ACL2 names
;      the next phase, or a terminal: :done (every effect returned),
;      :uncertain, :fault.  A phase never runs after one that did not return
;      :ok (fn-oqw-trace-is-an-ok-prefix).
;
;      KIND :batch is the commit's batch (host/native/owner.lisp
;      fnn-owner-commit-pipeline; before this lane its first three phases
;      ran inside the START quantum under the owner and its last inside the
;      COMPLETE quantum):
;        :intents      the members' FNFD intent frames (and a refusal told
;                      at its drain: its resolution frame, then its reply),
;                      in drain order, each written and fsynced
;        :extend       the log segment's extension (fallocate, fdatasync)
;        :append       the sealed batch's positioned write (cut log-written)
;        :fence        the barrier (fdatasync, cut log-fenced)
;        :resolutions  the members' FNFD resolution frames, in order
;      so no record reaches the log before every intent it depends on is
;      durable, and no resolution before the barrier that made its record
;      durable (fn-oqw-batch-effect-order).
;
;      KIND :frames is a START that kept no member of the log (every member
;      a refusal told at its drain, or the START ended uncertain): only the
;      FNFD frames its drain owes, and its refusals' replies, in order.
;
;   2. THE RECEIPT (fn-oqw-receipt) over the time-bars ledger
;      (books/owner-time-bars.lisp: a job is a request issued under a fresh
;      generation; its completion is consumed once, into its own
;      generation).  The outcomes are distinct words: :fenced (the job ran
;      every phase), :failed (a phase was uncertain: the recovery event),
;      :fault (a phase faulted, or the receipt names an unfinished job),
;      :stale (another generation's), :consumed (this generation's again).
;      A stale or consumed receipt answers no one and changes nothing;
;      neither is ever reported as an outcome of the job
;      (fn-oqw-receipt-outcomes-are-distinct).
(in-package "ACL2")
(include-book "owner-time-bars")

; -----------------------------------------------------------------------------
; 1. The job's phases and its step.

(defun fn-oqw-phases (kind)
  (declare (xargs :guard t))
  (cond ((equal kind :batch) '(:intents :extend :append :fence :resolutions))
        ((equal kind :frames) '(:intents))
        (t nil)))

(defun fn-oqw-terminalp (phase)
  (declare (xargs :guard t))
  (if (member-equal phase '(:done :uncertain :fault)) t nil))

; The phase after PHASE in PHASES: :done after the last; :fault for a phase
; the list does not name.
(defun fn-oqw-after (phase phases)
  (declare (xargs :guard t))
  (cond ((atom phases) :fault)
        ((equal phase (car phases))
         (if (consp (cdr phases)) (cadr phases) :done))
        (t (fn-oqw-after phase (cdr phases)))))

; The first phase of a job of KIND (:fault for an unknown kind).
(defun fn-oqw-start (kind)
  (declare (xargs :guard t))
  (let ((phases (fn-oqw-phases kind)))
    (if (consp phases) (car phases) :fault)))

; The host-called step: the phase that follows PHASE when its effect
; answered WORD.
(defun fn-oqw-step (kind phase word)
  (declare (xargs :guard t))
  (cond ((fn-oqw-terminalp phase) phase)
        ((equal word :ok) (fn-oqw-after phase (fn-oqw-phases kind)))
        ((equal word :uncertain) :uncertain)
        (t :fault)))

; A run: the phases executed, in order, when the effects answer WORDS in
; turn (one word per executed phase), and the phase it ends in.
(defun fn-oqw-trace (kind phase words)
  (declare (xargs :guard t :measure (acl2-count words)))
  (if (or (atom words) (fn-oqw-terminalp phase))
      nil
    (cons phase (fn-oqw-trace kind (fn-oqw-step kind phase (car words)) (cdr words)))))

(defun fn-oqw-final (kind phase words)
  (declare (xargs :guard t :measure (acl2-count words)))
  (if (or (atom words) (fn-oqw-terminalp phase))
      phase
    (fn-oqw-final kind (fn-oqw-step kind phase (car words)) (cdr words))))

(defun fn-oqw-all-ok (words)
  (declare (xargs :guard t))
  (if (consp words)
      (and (equal (car words) :ok) (fn-oqw-all-ok (cdr words)))
    t))

; Opening a run at a known phase, one answer at a time (the keystones below
; are about the batch's five named phases).
(defthm fn-oqw-trace-opens-at-a-known-phase
  (implies (syntaxp (and (quotep kind) (quotep phase)))
           (equal (fn-oqw-trace kind phase words)
                  (if (or (atom words) (fn-oqw-terminalp phase))
                      nil
                    (cons phase
                          (if (equal (car words) :ok)
                              (fn-oqw-trace kind (fn-oqw-after phase (fn-oqw-phases kind))
                                            (cdr words))
                            nil))))))

(defthm fn-oqw-final-opens-at-a-known-phase
  (implies (syntaxp (and (quotep kind) (quotep phase)))
           (equal (fn-oqw-final kind phase words)
                  (if (or (atom words) (fn-oqw-terminalp phase))
                      phase
                    (if (equal (car words) :ok)
                        (fn-oqw-final kind (fn-oqw-after phase (fn-oqw-phases kind))
                                      (cdr words))
                      (if (equal (car words) :uncertain) :uncertain :fault))))))

; -----------------------------------------------------------------------------
; KEYSTONE.  The batch job's effect order.  From the first phase, under any
; answers: the append runs only after the intents and the extension both
; returned; the barrier only after the append returned; a resolution frame
; only after the barrier returned; the job is :done only when all five
; returned, and then it ran exactly the five phases in order.  The subject
; is fn-oqw-step (with fn-oqw-start), host-called in host/native/owner.lisp
; fnn-owner-run-job, which executes exactly the phase the step names.
(defthm fn-oqw-batch-effect-order
  (let ((trace (fn-oqw-trace :batch (fn-oqw-start :batch) words)))
    (and (implies (member-equal :append trace)
                  (and (equal (first words) :ok)
                       (equal (second words) :ok)))
         (implies (member-equal :fence trace)
                  (equal (third words) :ok))
         (implies (member-equal :resolutions trace)
                  (and (equal (first words) :ok) (equal (second words) :ok)
                       (equal (third words) :ok) (equal (fourth words) :ok)))
         (iff (equal (fn-oqw-final :batch (fn-oqw-start :batch) words) :done)
              (and (fn-oqw-all-ok (take 5 words)) (<= 5 (len words))))
         (implies (equal (fn-oqw-final :batch (fn-oqw-start :batch) words) :done)
                  (equal trace (fn-oqw-phases :batch)))))
  :hints (("Goal" :in-theory (disable fn-oqw-trace fn-oqw-final))))

; A failed effect ends the job: the step after a phase that answered
; anything but :ok is a terminal -- :uncertain for an uncertain word, :fault
; otherwise -- and a terminal never steps again, so no phase runs after it.
; The subject is fn-oqw-step, host-called in host/native/owner.lisp
; fnn-owner-run-job.
(defthm fn-oqw-a-failed-effect-ends-the-job
  (implies (and (not (fn-oqw-terminalp phase))
                (not (equal word :ok)))
           (and (equal (fn-oqw-step kind phase word)
                       (if (equal word :uncertain) :uncertain :fault))
                (fn-oqw-terminalp (fn-oqw-step kind phase word))
                (equal (fn-oqw-step kind (fn-oqw-step kind phase word) word2)
                       (fn-oqw-step kind phase word)))))

; -----------------------------------------------------------------------------
; 2. The receipt.  L the time-bars ledger, GEN the generation the job was
; issued under, FINAL the phase the job ended in, CIDS the connections the
; job's completion answers.  (OUTCOME ANSWER L'): ANSWER and L' are
; fn-otb-complete's.

(defun fn-oqw-outcome-of-final (final)
  (declare (xargs :guard t))
  (cond ((equal final :done) :fenced)
        ((equal final :uncertain) :failed)
        (t :fault)))

(defun fn-oqw-receipt (l gen final cids)
  (declare (xargs :guard t))
  (let ((c (fn-otb-complete l gen cids)))
    (if (equal (car c) :apply)
        (list (fn-oqw-outcome-of-final final) (cadr c) (caddr c))
      (list (car c) nil (caddr c)))))

; KEYSTONE.  The receipt's outcomes are distinct and decided by name: the
; job's own completion (open at its generation) is :fenced exactly when it
; ran every phase, :failed exactly when it ended uncertain, :fault for any
; other end (a fault, or a job that had not finished); a completion of
; another generation is :stale and one already consumed :consumed, and
; neither answers anyone nor changes the ledger.  The subject is
; fn-oqw-receipt, host-called in host/native/owner.lisp
; fnn-owner-commit-pipeline after the job's join.
(defthm fn-oqw-receipt-outcomes-are-distinct
  (let* ((r (fn-oqw-receipt l gen final cids))
         (outcome (car r)))
    (and (member-equal outcome '(:fenced :failed :fault :stale :consumed))
         (iff (equal outcome :fenced)
              (and (fn-otb-open l) (equal (nfix gen) (fn-otb-gen l))
                   (equal final :done)))
         (iff (equal outcome :failed)
              (and (fn-otb-open l) (equal (nfix gen) (fn-otb-gen l))
                   (equal final :uncertain)))
         (iff (equal outcome :fault)
              (and (fn-otb-open l) (equal (nfix gen) (fn-otb-gen l))
                   (not (equal final :done)) (not (equal final :uncertain))))
         (iff (equal outcome :stale) (not (equal (nfix gen) (fn-otb-gen l))))
         (implies (member-equal outcome '(:stale :consumed))
                  (and (null (cadr r)) (equal (caddr r) l)))
         (implies (member-equal outcome '(:fenced :failed :fault))
                  (and (equal (cdr r) (cdr (fn-otb-complete l gen cids)))
                       (not (fn-otb-open (caddr r)))))))
  :hints (("Goal" :in-theory (e/d (fn-otb-complete)
                                  (fn-otb-gen fn-otb-told fn-otb-minus)))))

(in-theory (disable fn-oqw-step fn-oqw-receipt))
