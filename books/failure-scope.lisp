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

(in-theory (disable fn-fs-classify fn-fs-classify-job fn-fs-exit-code fn-fs-kindp
                    fn-fs-stop-exit-rank fn-fs-stop-exit-escalate))
