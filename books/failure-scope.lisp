; fn: the failure scope of a host boundary (lane failure-scope, t45;
; build/coordinator/decisions/whole-system-correctness-2026-10-03.md section
; 10.6 step 2; its review build/coordinator/lanedumps/failure-scope-review-1.md).
;
; The host runs every owner quantum, every worker thread and every command
; inside ONE boundary (host/native/owner.lisp fnn-owner-gated and
; fnn-owner-shared-action-locked, the threads' tops, host/native/io.lisp
; fnn-exit-code-for).  When a condition escapes a boundary the host OBSERVES
; two things and decides nothing:
;
;   CLASS  the concrete class the condition was signalled with, as the
;          lower-case name of that CL class (host/native/io.lisp
;          fnn-condition-class) -- never a parent: a subclass this book does
;          not list is not a refusal, whatever it inherits from;
;   STEP   the publication the boundary's body has landed and not yet
;          fenced (host/native/io.lisp fnn-durable-step: :replaced or
;          :linked once a rename or link returned success; nil again once a
;          directory barrier completed, fnn-fsync-dir): the byte model's
;          uncertain window, from the rename on until the directory is
;          durable.  An unlink or a mkdir opens no window.
;
; This book decides the KIND, in the words books/outcome-class.lisp
; fn-outcome-of-host-condition takes:
;
;   :indeterminate  the fence: exit 3, recovery before further mutation;
;   :fault          exit 4;
;   :usage          exit 5;
;   :refusal        the known refusal class: it passes the boundary unfenced,
;                   scoped to its caller (a connection, a request);
;   :job-failure    (fn-fs-classify-job only) a private job's own failure.
;
; The tables are CLOSED (review M1): a class in none of them is a fault, so
; a new store-layer condition cannot pass as a refusal until it is named
; here.  An OS error after a durable step is the fence (review M2, r72 F6:
; the class alone does not say where in the effect sequence it happened; a
; rename that landed and a directory barrier that failed is an uncertain
; publication).  tests/test_native_owner.py checks that every condition the
; host defines under fnn-store-error is in a table.
;
; The service's exit code, once a stop is installed, is a LATTICE
; (fn-fs-stop-exit-escalate), never first-wins (sweep S015).
(in-package "ACL2")

(include-book "outcome-class")

(defconst *fn-fs-indeterminate-classes*
  '("fnn-store-indeterminate"
    ;; host/native/snapshot-producer.lisp, snapshot-startup.lisp,
    ;; recovery-payload-view.lisp, tcpcl.lisp: an uncertain capture or
    ;; source, each a subclass of the fence.
    "fnn-snapshot-capture-uncertain" "fnn-snapshot-startup-retained"
    "fnn-snapshot-startup-root-retained" "fnn-tcl-source-indeterminate"))

(defconst *fn-fs-fault-classes*
  '("fnn-store-fault" "fnn-fixed-callback-fault" "fnn-entry-guard-fault"
    "fnn-input-overbound"
    ;; host/native/extent.lisp: an extent whose trailer or lease is wrong.
    "fnn-extent-fault"))

(defconst *fn-fs-usage-classes* '("fnn-usage-error"))

(defconst *fn-fs-refusal-classes*
  '(;; fnn-refuse: the bare known refusal.
    "fnn-store-error"
    ;; a Store write refused before publication (nothing stored).
    "fnn-store-io-refusal"
    ;; a Store open ACL2 refused by name, and its profile form.
    "fnn-store-open-refusal" "fnn-store-profile-refusal"
    ;; host/native/owner.lisp: a pending admission verdict (:yield,
    ;; :continue, :demand, :unavailable) is a refusal of that request until
    ;; the retained scheduler's join resolves such an intent (TCB-SHRINK
    ;; review: before, a serious condition no handler named, exit 4).
    "fnn-owner-admission-pending"))

;; One POSIX failure (host/native/io.lisp fnn-os-error): a fault before any
;; durable step of the boundary, the fence after one.
(defconst *fn-fs-os-classes* '("fnn-os-error"))

(defconst *fn-fs-known-classes*
  (append *fn-fs-indeterminate-classes* *fn-fs-fault-classes*
          *fn-fs-usage-classes* *fn-fs-refusal-classes* *fn-fs-os-classes*))

(defconst *fn-fs-kinds* '(:indeterminate :fault :usage :refusal :job-failure))

(defun fn-fs-kindp (x)
  (declare (xargs :guard t))
  (if (member-equal x *fn-fs-kinds*) t nil))

; The shared scope: an owner quantum, a worker thread of the owner, a
; command.  Everything that is not a known refusal or usage error either
; fences or faults.
(defun fn-fs-classify (class step)
  (declare (xargs :guard t))
  (cond ((member-equal class *fn-fs-indeterminate-classes*) :indeterminate)
        ((member-equal class *fn-fs-os-classes*)
         (if step :indeterminate :fault))
        ((member-equal class *fn-fs-fault-classes*) :fault)
        ((member-equal class *fn-fs-usage-classes*) :usage)
        ((member-equal class *fn-fs-refusal-classes*) :refusal)
        (t :fault)))

; A private job's scope (the exporter writing an archive outside the store,
; Astra's `private-job'): an OS failure BEFORE the job published anything is
; the job's own failure -- its outcome word, serving continues -- never the
; service's fault; after a durable step it is the job's uncertain outcome
; (still :indeterminate: the job reports it as such).  A core or store fault
; is the service's, as in every scope.
(defun fn-fs-classify-job (class step)
  (declare (xargs :guard t))
  (if (and (member-equal class *fn-fs-os-classes*) (not step))
      :job-failure
    (fn-fs-classify class step)))

; The exit code of the condition that ended a command (host/native/io.lisp
; fnn-exit-code-for): the kind's code, books/outcome-class.lisp.
(defun fn-fs-exit-code (class step)
  (declare (xargs :guard t))
  (fn-outcome-host-condition-exit-code (fn-fs-classify class step)))

; -----------------------------------------------------------------------------
; The service's exit code when a later terminal outcome arrives after its
; stop was installed (host/native/owner.lisp fnn-owner-stop-service-locked;
; sweep S015: the graceful SIGTERM stop installed exit 0 before a batch's
; barrier failed, and the failure was lost).  A lattice, never first-wins:
; ok (0) < refused (1), usage (5) < fault (4) < fenced (3).  Once the fence
; is installed nothing lowers it (the owner's fn-bprc-fence-is-never-masked;
; specs/host.md "a fence dominates"); a fault is never lowered to a stop;
; two outcomes of one rank keep the first (which fault's text is primary).
; The host records the dominated outcome on stderr; it decides nothing.

(defun fn-fs-stop-exit-rank (code)
  (declare (xargs :guard t))
  (cond ((equal code (fn-outcome-code :fenced)) 3)
        ((equal code (fn-outcome-code :fault)) 2)
        ((or (equal code (fn-outcome-code :refused))
             (equal code (fn-outcome-code :usage)))
         1)
        (t 0)))

(defun fn-fs-stop-exit-escalate (current new)
  (declare (xargs :guard t))
  (if (< (fn-fs-stop-exit-rank current) (fn-fs-stop-exit-rank new))
      new
    current))

; -----------------------------------------------------------------------------
; Theorems.

(defthm fn-fs-classify-is-a-kind
  (fn-fs-kindp (fn-fs-classify class step)))

(defthm fn-fs-classify-job-is-a-kind
  (fn-fs-kindp (fn-fs-classify-job class step)))

; The tables are closed: a class in none of them is a fault.
(defthm fn-fs-unknown-class-is-a-fault
  (implies (not (member-equal class *fn-fs-known-classes*))
           (equal (fn-fs-classify class step) :fault)))

; Teeth (review M1): a store-error subclass the table does not name is a
; fault, not the refusal its parent is.
(defthm fn-fs-an-unlisted-store-error-subclass-is-a-fault
  (equal (fn-fs-classify "fnn-store-future-refusal" step) :fault))

; A refusal is answered only from the refusal table, never inherited.
(defthm fn-fs-refusal-only-from-the-table
  (implies (equal (fn-fs-classify class step) :refusal)
           (member-equal class *fn-fs-refusal-classes*)))

; The fence is answered for the fence classes and for an OS error after a
; durable step, and for nothing else.
(defthm fn-fs-indeterminate-iff
  (iff (equal (fn-fs-classify class step) :indeterminate)
       (or (member-equal class *fn-fs-indeterminate-classes*)
           (and (member-equal class *fn-fs-os-classes*) step))))

; Review M2 (r72 F6): an OS error after the first durable step of the
; boundary is the fence; before any step it is a fault.
(defthm fn-fs-os-error-after-a-durable-step-is-the-fence
  (implies step
           (equal (fn-fs-classify "fnn-os-error" step) :indeterminate)))

(defthm fn-fs-os-error-before-any-step-is-a-fault
  (equal (fn-fs-classify "fnn-os-error" nil) :fault))

; The private-job scope differs from the shared one on exactly one point:
; an OS failure before any durable step is the job's, not the service's.
(defthm fn-fs-classify-job-differs-only-on-an-early-os-error
  (implies (not (and (member-equal class *fn-fs-os-classes*) (not step)))
           (equal (fn-fs-classify-job class step) (fn-fs-classify class step))))

(defthm fn-fs-classify-job-never-faults-the-service-on-an-early-os-error
  (equal (fn-fs-classify-job "fnn-os-error" nil) :job-failure))

(defthm fn-fs-classify-job-fences-after-a-durable-step
  (implies step
           (equal (fn-fs-classify-job "fnn-os-error" step) :indeterminate)))

; The exit code is the fenced one exactly for the fence (the owner's analogue
; of fn-outcome-host-condition-fences-iff-indeterminate).
(defthm fn-fs-exit-code-is-fenced-iff-indeterminate
  (iff (equal (fn-fs-exit-code class step) (fn-outcome-code :fenced))
       (equal (fn-fs-classify class step) :indeterminate)))

; The lattice.
(defthm fn-fs-stop-exit-fence-is-never-masked
  (implies (or (equal current (fn-outcome-code :fenced))
               (equal new (fn-outcome-code :fenced)))
           (equal (fn-fs-stop-exit-escalate current new)
                  (fn-outcome-code :fenced))))

; Monotone: the exit never goes down, whichever outcome came first.
(defthm fn-fs-stop-exit-escalate-is-monotone
  (and (<= (fn-fs-stop-exit-rank current)
           (fn-fs-stop-exit-rank (fn-fs-stop-exit-escalate current new)))
       (<= (fn-fs-stop-exit-rank new)
           (fn-fs-stop-exit-rank (fn-fs-stop-exit-escalate current new)))))

; A graceful stop (ok) is the bottom: any later terminal outcome replaces it.
(defthm fn-fs-stop-exit-ok-is-the-bottom
  (implies (not (equal (fn-fs-stop-exit-rank new) 0))
           (equal (fn-fs-stop-exit-escalate (fn-outcome-code :accepted) new)
                  new)))

; A fault is never lowered to a stop or a refusal.
(defthm fn-fs-stop-exit-fault-is-kept
  (implies (and (equal current (fn-outcome-code :fault))
                (not (equal new (fn-outcome-code :fenced))))
           (equal (fn-fs-stop-exit-escalate current new)
                  (fn-outcome-code :fault))))

; First-wins only between two outcomes of one rank.
(defthm fn-fs-stop-exit-first-wins-at-equal-rank
  (implies (equal (fn-fs-stop-exit-rank current) (fn-fs-stop-exit-rank new))
           (equal (fn-fs-stop-exit-escalate current new) current)))


; =============================================================================
; The declared forms (lane WRAPPER, rebuild step 0;
; planning/handoff-2026-10-03/failure-scope.md, planning/design/
; repair-triage-2026-10-03.md section 3 step 0).  host/native/owner.lisp's
; `def-section' and `def-actor' and host/native/io.lisp's `fnn-failure-scope'
; are the ONE generated host envelope; every decision they take is a function
; below, called guard-t and direct (a handler cannot afford a second failure
; inside fnn-core).  The host observes and orders; it decides nothing.

; -----------------------------------------------------------------------------
; Sections.  A declaration names who runs it (its actors), the gate classes it
; enters as, and what it admits once the service is stopping: a :live section
; is refused (the stopping refusal fnn-owner-serialized used to write by
; hand); a (:cleanup PURPOSE) section runs after the fence, and only for a
; purpose in the closed post-fence set (review M4): the fault itself, the
; abandon of a connection, a pass's finish, an unpin, the settlement of a
; worker's join, the observation of a close.  Pending-extent release is NOT a
; purpose (t43: a stopped owner never retries an ambiguous fd).

(defconst *fn-fs-actors*
  '(:control :mux :web :feed :pull :bp :committer :syncer :publisher :exporter
    :accept :cold :maintenance :command))

(defconst *fn-fs-gate-classes*
  '(:control :reader :poster :transit :commit :inspect))

(defconst *fn-fs-cleanup-purposes*
  '(:fault :abandon :finish :unpin :settle :close-observation))

(defun fn-fs-keyword-subsetp (xs universe)
  (declare (xargs :guard (true-listp universe)))
  (if (atom xs)
      (null xs)
    (and (member-equal (car xs) universe)
         (fn-fs-keyword-subsetp (cdr xs) universe))))

(defun fn-fs-admissionp (admits)
  (declare (xargs :guard t))
  (or (equal admits :live)
      (and (consp admits)
           (equal (car admits) :cleanup)
           (consp (cdr admits))
           (member-equal (cadr admits) *fn-fs-cleanup-purposes*)
           (null (cddr admits))
           t)))

; The host refuses to load a def-section whose declaration this answers nil
; for (owner.lisp fnn-section-declare): the image does not build.
(defun fn-fs-section-declp (actors classes admits)
  (declare (xargs :guard t))
  (and (consp actors)
       (fn-fs-keyword-subsetp actors *fn-fs-actors*)
       (consp classes)
       (fn-fs-keyword-subsetp classes *fn-fs-gate-classes*)
       (fn-fs-admissionp admits)))

; Each entry: run the body, or refuse it (the known refusal "owner service is
; stopping", raised inside the boundary, so it passes unfenced to its caller).
(defun fn-fs-section-admit (admits stopping)
  (declare (xargs :guard t))
  (if (and stopping (equal admits :live)) :refuse :run))

; The class an entry runs as must be one its section declared; anything else
; is a defect of the host (a fault), never a quiet admission.
(defun fn-fs-section-class-ok (classes class)
  (declare (xargs :guard t))
  (if (and (true-listp classes) (member-equal class classes)) t nil))

; The boundary's unwind (review M3): the body completed, or a condition left
; it and was classified (DECIDED is the recorded decision); an unwind with
; neither -- a throw, a thread termination -- is a fault.
(defun fn-fs-unwind (completed decided)
  (declare (xargs :guard t))
  (if (or completed decided) :settled :fault))

; What the section's boundary does with the kind fn-fs-classify answered:
; the fence (exit 3) and the fault (exit 4) are installed before the mutex is
; released; a known refusal or usage error passes, scoped to the caller.
(defun fn-fs-section-action (kind)
  (declare (xargs :guard t))
  (case kind
    (:indeterminate :fence)
    ((:refusal :usage) :pass)
    (otherwise :fault)))

; -----------------------------------------------------------------------------
; The connection scope (def-actor :end-connection; host/native/io.lisp
; fnn-failure-scope :connection; HOST-LIFECYCLE's fnn-connection-scoped and
; the I/O loop's per-connection handler were its hand versions).  One
; connection's failure ends that connection with a word ACL2 names; the
; process's failures stay the process's.  The connection-local classes are a
; closed table like the others: the socket conditions the runtime signals,
; the TLS session's, the end of a stream.  A class in no table is a fault.

(defconst *fn-fs-connection-classes*
  '(;; sb-bsd-sockets: the base class (an errno with no class of its own,
    ;; ECONNRESET among them) and its subclasses.
    "socket-error" "operation-in-progress" "address-family-not-supported"
    "not-connected-error" "network-unreachable-error" "host-unreachable-error"
    "network-down-error" "network-reset-error" "connection-reset-error"
    "connection-aborted-error" "socket-type-not-supported-error"
    "protocol-not-supported-error" "operation-not-permitted-error"
    "operation-not-supported-error" "out-of-memory-error" "no-buffers-error"
    "invalid-argument-error" "operation-timeout-error"
    "connection-refused-error" "bad-file-descriptor-error" "interrupted-error"
    "address-in-use-error"
    ;; host/native/tls.lisp: a TLS session's failure is its peer's.
    "fnn-tls-error" "fnn-tls-unavailable" "fnn-tls-config-error"
    "fnn-tls-handshake-error" "fnn-tls-io-error" "fnn-tls-verify-error"))

; host/native/owner.lisp: an unexpected failure inside a named non-semantic
; connection call (fnn-owner-connection-call); the core's fault transition for
; that connection settles it.
(defconst *fn-fs-abandon-classes* '("fnn-owner-connection-fault"))

(defconst *fn-fs-connection-kinds*
  '(:indeterminate :fault :abandon :refused :lost))

(defun fn-fs-classify-connection (class step)
  (declare (xargs :guard t))
  (cond ((member-equal class *fn-fs-indeterminate-classes*) :indeterminate)
        ((member-equal class *fn-fs-os-classes*)
         (if step :indeterminate :lost))
        ((member-equal class *fn-fs-fault-classes*) :fault)
        ((member-equal class *fn-fs-abandon-classes*) :abandon)
        ((member-equal class *fn-fs-connection-classes*) :lost)
        ((member-equal class *fn-fs-usage-classes*) :refused)
        ((member-equal class *fn-fs-refusal-classes*) :refused)
        (t :fault)))

; The connection's session word (ACL2's run class counts it, fn-bprc-note):
; a refusal is :refused, a lost connection :uncertain.  The process kinds
; have no word: they leave the scope.
(defun fn-fs-connection-word (kind)
  (declare (xargs :guard t))
  (case kind
    (:refused :refused)
    (:lost :uncertain)
    (otherwise nil)))

; A connection boundary on a thread that serves many (the I/O loop): the
; fence and the fault are installed for the service, then this connection is
; finished; the loop goes on to observe the stop.  A connection boundary that
; is its thread's only work (a listener's handler) re-signals the process
; kinds instead (:resignal), to its actor's top boundary.
(defun fn-fs-connection-action (kind)
  (declare (xargs :guard t))
  (case kind
    (:indeterminate :fence)
    (:fault :fault)
    (:abandon :abandon)
    (otherwise :end)))

; -----------------------------------------------------------------------------
; The settled scope: cleanup after a boundary that has already decided (a
; section call's re-signal: the section fenced or faulted the service before
; it re-signalled), or best-effort work whose own failure is the
; connection's (a log line, a socket close).  A connection-local failure is
; absorbed; a process failure (the fence's or a fault's class) is absorbed
; ONLY once the service is stopping -- the fence it implies is installed --
; and is re-signalled otherwise, so nothing is swallowed before the fence.

(defun fn-fs-settled-action (kind stopping)
  (declare (xargs :guard t))
  (case kind
    ((:refused :lost) :absorb)
    ((:indeterminate :fault) (if stopping :absorb :resignal))
    (otherwise :resignal)))

; -----------------------------------------------------------------------------
; Actors (def-actor). Reservation precedes spawn; the native start latch
; prevents the child's body running before its thread object is installed.
; Registration survives its exit and a failed/timed-out join. Only an
; affirmative physical termination observation, after terminal cleanup,
; produces the lifecycle receipt. An operation's I/O receipt is separate.
; States: :spawning, :running, (:exited KIND), (:joined KIND).
; Events: (:spawned OK), (:exit KIND), (:joined PHYSICALLY-ENDED).
; A failed spawn observes no child was created and ends the reservation.

(defconst *fn-fs-exit-kinds*
  '(:ok :indeterminate :fault :refusal :usage :job-failure))

(defun fn-fs-exit-kindp (x)
  (declare (xargs :guard t))
  (if (member-equal x *fn-fs-exit-kinds*) t nil))

; How the thread's body ended, as its top boundary observed it.
(defun fn-fs-actor-exit-kind (completed kind)
  (declare (xargs :guard t))
  (cond (completed :ok)
        ((fn-fs-exit-kindp kind) kind)
        (t :fault)))

(defun fn-fs-actor-step (st event)
  (declare (xargs :guard t))
  (cond ((and (equal st :spawning) (consp event)
              (equal (car event) :spawned) (consp (cdr event)))
         (if (cadr event) :running (list :joined :fault)))
        ;; Reserving before spawn also makes an early exit observable.
        ((and (member-equal st '(:spawning :running)) (consp event)
              (equal (car event) :exit) (consp (cdr event)))
         (list :exited (fn-fs-actor-exit-kind nil (cadr event))))
        ;; Failed join says nothing about termination or cleanup.
        ((and (member-equal st '(:spawning :running)) (consp event)
              (equal (car event) :joined) (consp (cdr event)) (cadr event))
         (list :joined :fault))
        ((and (consp st) (equal (car st) :exited) (consp (cdr st))
              (consp event) (equal (car event) :joined) (consp (cdr event))
              (cadr event))
         (list :joined (cadr st)))
        (t st)))

; Includes the reservation: shutdown cannot miss a spawn in progress.
(defun fn-fs-actor-registered-p (st)
  (declare (xargs :guard t))
  (or (member-equal st '(:spawning :running))
      (and (consp st) (equal (car st) :exited))))

; Fault escalation is independent of discharge. The host names physical
; termination only after checking the thread's primitive observation.
(defun fn-fs-actor-join-action (physically-ended join-returned)
  (declare (xargs :guard t))
  (if (and physically-ended join-returned) :settle :fault))

(defun fn-fs-actor-receipt (st)
  (declare (xargs :guard t))
  (and (consp st) (equal (car st) :joined) (consp (cdr st))
       (cadr st)))

; What the owner does with a receipt: the fence for an uncertain end, the
; fault for a fault, nothing for the rest (a job's own failure was answered
; to its caller; a refusal ended a request).
(defun fn-fs-receipt-action (kind)
  (declare (xargs :guard t))
  (case kind
    (:indeterminate :fence)
    (:fault :fault)
    (otherwise :none)))

; -----------------------------------------------------------------------------
; Actor declarations (def-actor, host/native/owner.lisp).  A declaration names
; the actor's KIND (the words a section's :actors use), whether its thread
; joins the owner's worker roster (ROSTER, a boolean), the host function that
; joins it (the host's word, checked by tools/lock_discipline_check.py R4),
; and its FAILURE policy: how a condition that escapes its body is decided.
;   :service  the service's boundary decides it (fn-fs-classify): the fence,
;             the fault, or a pass scoped to its caller;
;   :job      a private job's (fn-fs-classify-job): an OS failure before it
;             published anything is its own, never the service's;
;   :result   the body catches its own failure and hands the outcome word to
;             the parent that joins it; nothing escapes to a boundary.
; The host refuses to load a def-actor this answers nil for
; (fnn-actor-declare): the image does not build.

(defconst *fn-fs-actor-failures* '(:service :job :result))

(defun fn-fs-actor-declp (kind roster failure)
  (declare (xargs :guard t))
  ; ROSTER by member-equal, not booleanp: the raw harnesses load this body
  ; into plain SBCL with only member-equal supplied.
  (and (member-equal kind *fn-fs-actors*)
       (member-equal roster '(t nil))
       (member-equal failure *fn-fs-actor-failures*)
       t))

; -----------------------------------------------------------------------------
; Admission to a live inbox (def-actor :admit; r71 F9, review S1).  The
; receiver sets CLOSED under its inbox lock before its final drain; an offer
; is decided under the same lock: :admitted, or :closed, and the offerer
; keeps (and closes) what it offered.

(defun fn-fs-inbox-admit (closed)
  (declare (xargs :guard t))
  (if closed :closed :admitted))

; -----------------------------------------------------------------------------
; Theorems of the declared forms.

(defthm fn-fs-section-declp-refuses-an-unlisted-cleanup-purpose
  (implies (not (member-equal purpose *fn-fs-cleanup-purposes*))
           (not (fn-fs-section-declp actors classes (list :cleanup purpose)))))

; Teeth (review M4): pending-extent release is not a post-fence purpose.
(defthm fn-fs-pending-extent-release-is-no-cleanup-purpose
  (not (fn-fs-section-declp '(:maintenance) '(:control)
                            '(:cleanup :release-pending-extents))))

(defthm fn-fs-section-declp-positive-witness
  (and (fn-fs-section-declp '(:control) '(:control :inspect) :live)
       (fn-fs-section-declp '(:maintenance) '(:control) '(:cleanup :fault))))

(defthm fn-fs-section-declp-refuses-an-unknown-actor-or-class
  (and (not (fn-fs-section-declp '(:somebody) '(:control) :live))
       (not (fn-fs-section-declp '(:control) '(:everything) :live))
       (not (fn-fs-section-declp nil '(:control) :live))
       (not (fn-fs-section-declp '(:control) nil :live))))

; A :live section never runs once the service is stopping; a cleanup does.
(defthm fn-fs-a-live-section-is-refused-once-stopping
  (implies stopping
           (equal (fn-fs-section-admit :live stopping) :refuse)))

(defthm fn-fs-section-admit-runs-before-the-stop
  (equal (fn-fs-section-admit admits nil) :run))

(defthm fn-fs-a-cleanup-section-runs-after-the-fence
  (implies (not (equal admits :live))
           (equal (fn-fs-section-admit admits stopping) :run)))

(defthm fn-fs-section-class-ok-only-for-a-declared-class
  (implies (fn-fs-section-class-ok classes class)
           (member-equal class classes)))

(defthm fn-fs-unwind-faults-an-unexplained-exit
  (equal (equal (fn-fs-unwind completed decided) :fault)
         (and (not completed) (not decided))))

; No action consumes the fence or a fault: the section installs both, and
; passes only the refusal table's classes.
(defthm fn-fs-section-passes-only-the-refusal-and-usage-tables
  (implies (equal (fn-fs-section-action (fn-fs-classify class step)) :pass)
           (or (member-equal class *fn-fs-refusal-classes*)
               (member-equal class *fn-fs-usage-classes*)))
  :hints (("Goal" :in-theory (enable fn-fs-classify))))

(defthm fn-fs-section-fences-iff-indeterminate
  (iff (equal (fn-fs-section-action (fn-fs-classify class step)) :fence)
       (equal (fn-fs-classify class step) :indeterminate))
  :hints (("Goal" :in-theory (enable fn-fs-classify))))

; The connection scope: closed, and a process kind is never a session word.
(defthm fn-fs-unknown-class-is-a-connection-fault
  (implies (and (not (member-equal class *fn-fs-known-classes*))
                (not (member-equal class *fn-fs-connection-classes*))
                (not (member-equal class *fn-fs-abandon-classes*)))
           (equal (fn-fs-classify-connection class step) :fault)))

; Teeth (review M1 in the connection scope): a store-error subclass the
; tables do not name ends no connection quietly; it is the process's fault.
(defthm fn-fs-an-unlisted-store-error-subclass-is-a-connection-fault
  (equal (fn-fs-classify-connection "fnn-store-future-refusal" step) :fault))

(defthm fn-fs-connection-ends-quietly-only-for-the-tables
  (implies (equal (fn-fs-connection-action (fn-fs-classify-connection class step))
                  :end)
           (or (member-equal class *fn-fs-connection-classes*)
               (member-equal class *fn-fs-refusal-classes*)
               (member-equal class *fn-fs-usage-classes*)
               (and (member-equal class *fn-fs-os-classes*) (not step)))))

; A fence class, and an OS error inside the uncertain window, fence in the
; connection scope as in a section: a connection never hides them.
(defthm fn-fs-connection-fences-iff-the-section-fences
  (iff (equal (fn-fs-classify-connection class step) :indeterminate)
       (equal (fn-fs-classify class step) :indeterminate))
  :hints (("Goal" :in-theory (enable fn-fs-classify))))

(defthm fn-fs-a-section-fault-is-a-connection-fault-or-abandon-or-lost
  (implies (equal (fn-fs-classify class step) :fault)
           (member-equal (fn-fs-classify-connection class step)
                         '(:fault :abandon :lost)))
  :hints (("Goal" :in-theory (enable fn-fs-classify))))

(defthm fn-fs-connection-word-only-for-connection-kinds
  (implies (fn-fs-connection-word kind)
           (member-equal kind '(:refused :lost))))

(defthm fn-fs-connection-kind-is-a-kind
  (member-equal (fn-fs-classify-connection class step) *fn-fs-connection-kinds*))

; The settled scope never absorbs the fence or a fault before the stop.
(defthm fn-fs-settled-absorbs-a-process-kind-only-once-stopping
  (implies (and (member-equal kind '(:indeterminate :fault))
                (not stopping))
           (equal (fn-fs-settled-action kind stopping) :resignal)))

(defthm fn-fs-settled-absorbs-a-connection-kind
  (implies (member-equal kind '(:refused :lost))
           (equal (fn-fs-settled-action kind stopping) :absorb)))

(defthm fn-fs-settled-resignals-an-abandon
  (equal (fn-fs-settled-action :abandon stopping) :resignal))

; Actors: registered from the spawn until the join; only the join ends it.
(defthm fn-fs-actor-spawn-registers
  (fn-fs-actor-registered-p (fn-fs-actor-step :spawning '(:spawned t))))

(defthm fn-fs-actor-failed-spawn-is-never-registered
  (and (not (fn-fs-actor-registered-p (fn-fs-actor-step :spawning '(:spawned nil))))
       (equal (fn-fs-actor-receipt (fn-fs-actor-step :spawning '(:spawned nil)))
              :fault)))

(defthm fn-fs-actor-exit-keeps-the-registration
  (implies (and (fn-fs-actor-registered-p st)
                (consp event) (equal (car event) :exit))
           (fn-fs-actor-registered-p (fn-fs-actor-step st event))))

(defthm fn-fs-actor-only-physical-end-or-failed-spawn-deregisters
  (implies (and (fn-fs-actor-registered-p st)
                (not (fn-fs-actor-registered-p (fn-fs-actor-step st event))))
           (and (consp event) (consp (cdr event))
                (or (and (equal (car event) :joined) (cadr event))
                    (and (equal st :spawning)
                         (equal (car event) :spawned) (not (cadr event)))))))

(defthm fn-fs-actor-failed-join-retains-custody
  (and (equal (fn-fs-actor-step st '(:joined nil)) st)
       (equal (fn-fs-actor-join-action nil join-returned) :fault)))

(defthm fn-fs-actor-joined-is-final
  (implies (and (consp st) (equal (car st) :joined))
           (equal (fn-fs-actor-step st event) st)))

; The receipt carries the exit its top boundary recorded...
(defthm fn-fs-actor-receipt-carries-the-recorded-exit
  (implies (fn-fs-exit-kindp kind)
           (equal (fn-fs-actor-receipt
                   (fn-fs-actor-step (fn-fs-actor-step :running (list :exit kind))
                                     '(:joined t)))
                  kind)))

; ...and a thread that ended unrecorded, or whose join failed, is a fault
; (review Q3 teeth: an unclassified non-local exit yields a fault receipt).
(defthm fn-fs-actor-unrecorded-physical-end-is-a-fault-receipt
  (equal (fn-fs-actor-receipt (fn-fs-actor-step :running '(:joined t)))
         :fault))

(defthm fn-fs-actor-failed-join-produces-no-receipt
  (implies (fn-fs-actor-registered-p st)
           (not (fn-fs-actor-receipt (fn-fs-actor-step st '(:joined nil))))))

(defthm fn-fs-actor-early-exit-survives-spawn-publication
  (equal (fn-fs-actor-step (fn-fs-actor-step :spawning (list :exit kind))
                          '(:spawned t))
         (list :exited (fn-fs-actor-exit-kind nil kind))))

; Reached witnesses: failed join with a live child; early exit; the
; uncertain outcome after cleanup and join. They affirm entire conclusions.
(defthm fn-fs-actor-lifecycle-positive-witness
  (and (fn-fs-actor-registered-p :spawning)
       (fn-fs-actor-registered-p (fn-fs-actor-step :running '(:joined nil)))
       (not (fn-fs-actor-receipt (fn-fs-actor-step :running '(:joined nil))))
       (equal (fn-fs-actor-receipt
               (fn-fs-actor-step
                (fn-fs-actor-step :running '(:exit :indeterminate)) '(:joined t)))
              :indeterminate)))

(defthm fn-fs-actor-exit-kind-of-an-unknown-word-is-a-fault
  (implies (and (not completed) (not (fn-fs-exit-kindp kind)))
           (equal (fn-fs-actor-exit-kind completed kind) :fault)))

(defthm fn-fs-receipt-action-never-drops-a-process-kind
  (and (equal (fn-fs-receipt-action :indeterminate) :fence)
       (equal (fn-fs-receipt-action :fault) :fault)))

; An actor is declared with a known kind, a boolean roster and a policy from
; the closed set; anything else stops the image's load.
(defthm fn-fs-actor-declp-refuses-an-unknown-kind-or-policy
  (implies (or (not (member-equal kind *fn-fs-actors*))
               (not (booleanp roster))
               (not (member-equal failure *fn-fs-actor-failures*)))
           (not (fn-fs-actor-declp kind roster failure))))

; Teeth: the words a hand-written thread used (a fence policy, a roster slot
; name) and an actor nobody declared are refused; the declared owner actors
; are accepted.
(defthm fn-fs-actor-declp-teeth
  (and (not (fn-fs-actor-declp :committer nil :fence))
       (not (fn-fs-actor-declp :committer :roster :service))
       (not (fn-fs-actor-declp :somebody t :service))
       (not (fn-fs-actor-declp :syncer t nil))))

(defthm fn-fs-actor-declp-positive-witness
  (and (fn-fs-actor-declp :committer nil :service)
       (fn-fs-actor-declp :syncer t :result)
       (fn-fs-actor-declp :publisher t :job)
       (fn-fs-actor-declp :web t :service)))

(defthm fn-fs-inbox-admit-closed
  (and (equal (fn-fs-inbox-admit t) :closed)
       (equal (fn-fs-inbox-admit nil) :admitted)))


(in-theory (disable fn-fs-classify fn-fs-classify-job fn-fs-exit-code fn-fs-kindp
                    fn-fs-stop-exit-rank fn-fs-stop-exit-escalate
                    fn-fs-section-declp fn-fs-section-admit fn-fs-section-class-ok
                    fn-fs-unwind fn-fs-section-action fn-fs-classify-connection
                    fn-fs-connection-word fn-fs-connection-action fn-fs-settled-action
                    fn-fs-actor-exit-kind fn-fs-actor-step fn-fs-actor-registered-p
                    fn-fs-actor-receipt fn-fs-actor-join-action fn-fs-receipt-action fn-fs-inbox-admit
                    fn-fs-actor-declp))
