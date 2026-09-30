;;; host/native/owner.lisp -- the writable native owner service.
;;;
;;; This file is raw Common Lisp under the native host trust tag.  It owns
;;; scheduling, sockets and filesystem effects only.  Every protocol, owner,
;;; configuration, submission and outcome decision is a direct call to a
;;; host/owner-host.lisp wrapper through fnn-core/fnn-core-state.  All calls
;;; and Store mutations are serialized by one mutex because ACL2's live state
;;; and the exclusive Store writer are one process-owned machine; client
;;; sockets remain concurrent and never carry semantic state in raw Lisp.

;;;
;;; The scheduler (planning/design-2026-09-26-owner-scheduler.md; HST-023;
;;; PRF-248): the mutex is entered through a GATE.  A thread names its
;;; SERVICE CLASS (:control, :reader, :poster, :transit) and waits at the
;;; gate; ACL2 decides which class runs next (books/owner-scheduler.lisp
;;; fn-osch-next: the first waiting class in cyclic order from a cursor, so a
;;; control request waits at most three quanta of the other classes,
;;; fn-osch-control-waits-at-most-the-bound), and within a class the host
;;; serves arrival order.  The mutex itself is uncontended: the gate admits
;;; one thread.  What a quantum is stays what it was, one bounded semantic
;;; step; what left the critical section is the reply's rendering: a served
;;; step returns an immutable render PLAN (books/served-plan.lisp) and the
;;; I/O loop (host/native/mux.lisp) renders it into a fresh buffer, a window
;;; at a time, after the mutex is released (fnn-owner-render-next).
;;; The live octet buffer `fn-octets' is now input-only under the mutex.

(in-package "ACL2")

(defvar *fnn-owner-start-hooks* nil)
(defvar *fnn-owner-stop-hooks* nil)
(defvar *fnn-owner-close-hooks* nil)

;;; The kernel's accept queue for the served listener: connections that have
;;; completed the handshake and are waiting for this file's accept thread.
;;; It is not a connection limit -- how many connections this owner will hold
;;; is fn-own-open's (books/owner.lisp `max-conns'), which refuses past the
;;; bound with the model's own answer.  The queue only decides what happens to
;;; a client that arrives while the accept thread is launching a worker for
;;; the previous one: with the fnn-listen default of 1 the second client's
;;; connection is dropped and it sees a reset or a hang for no reason it can
;;; act on.  Sixteen was the depth host/native/control.lisp uses; a reader
;;; port facing strangers (PRF-161) is flooded by clients the owner must
;;; each answer with ACL2's 400, and with sixteen the kernel held the rest
;;; half-open for its SYN-ACK retries: 69 of 500 flood connections from one
;;; address read nothing for 10 s on hbox
;;; (planning/evidence/public-exposure-2026-09-26.md section 4).  The queue
;;; still decides nothing: every connection it hands over meets fn-exp-open.
(defconstant +fnn-owner-listen-backlog+ 128)

(define-condition fnn-owner-connection-fault (error)
  ((operation :initarg :operation :reader fnn-owner-connection-fault-operation)
   (cause :initarg :cause :reader fnn-owner-connection-fault-cause))
  (:report (lambda (condition stream)
             (format stream "~(~a~): ~a"
                     (fnn-owner-connection-fault-operation condition)
                     (fnn-owner-connection-fault-cause condition)))))

(defstruct (fnn-owner-cold-read (:constructor %make-fnn-owner-cold-read))
  token worker prev next queuedp settledp outcome)

(defstruct (fnn-owner-service (:constructor %make-fnn-owner-service))
  store lock listener stopping (exit-code +fnn-exit-ok+) (feeds nil)
  (workers nil) (clients nil) tls-context
  ;; Intrusive cold-read queue, guarded by owner mutex. Metadata remains
  ;; owned until worker relinquishment and atomic result settlement.
  (cold-head nil) (cold-tail nil)
  ;; The scheduler gate in front of LOCK (fnn-owner-gated), and the roster
  ;; mutex that protects WORKERS, CLIENTS, PUBLISHER and the stop flag's
  ;; publication to the accept threads: host lists, not owner state, so
  ;; their edits never queue at the gate.
  (gate nil) (roster (sb-thread:make-mutex :name "fn owner roster"))
  ;; A response's arena generation is held from capture under LOCK until
  ;; its output drains or its connection cancels.  In particular a cursor
  ;; must not see online reclaim's replacement catalog between quanta.
  (response-pins nil)
  ;; The checkpoint publication's thread while one runs (fnn-owner-maybe-publish).
  (publisher nil)
  ;; Row S3b: the export's thread while one runs (fnn-owner-export-request),
  ;; the last export's outcome ((:done . N) or (:failed . WORD)) and its
  ;; DIR: ACL2's two observations for `store export' and `store export
  ;; --status' (books/owner-export-request.lisp fn-oex-request-word,
  ;; fn-oex-status-word), kept under the roster.
  (exporter nil) (export-outcome nil) (export-dir nil)
  ;; PRF-359's NEED (ACL2's fn-owner-space-need of the live configuration),
  ;; kept under the owner mutex each time the owner computes it, so the
  ;; free-space observation (statvfs) is taken off the mutex, before a
  ;; quantum's gate entry (fnn-owner-space-preobserve): no I/O inside the
  ;; semantic critical section.  NIL until the run's first computation.
  (space-need nil)
  ;; The I/O loops that serve every reader and transit connection
  ;; (host/native/mux.lisp), and the round-robin cursor over them.
  (mux nil) (mux-next 0)
  (start-hooks nil) (stop-hooks nil) (close-hooks nil)
  ;; Private executable-test injection.  Production instances leave this NIL;
  ;; the value names a real connection envelope, not a second fault decision.
  (connection-fault-operation nil)
  ;; PRF-252: consumer waits (fnn-owner-consumer-local-wait).  COMMITS counts
  ;; durable Store publications and stops; each raises WAIT-QUEUE under
  ;; WAIT-LOCK.  WAITERS is the number of waits admitted and not yet
  ;; answered; ACL2 admits one more (fn-cwait-admit).  Lock order: the owner
  ;; mutex, then WAIT-LOCK; a waiter never holds the owner mutex while it
  ;; sleeps.
  (wait-lock (sb-thread:make-mutex :name "fn consumer wait"))
  (wait-queue (sb-thread:make-waitqueue :name "fn consumer commit"))
  (commits 0) (waiters 0)
  ;; Lane commit-onto-log: BATCHING when the store commits
  ;; through the record log.  A served read step then queues its submission
  ;; and returns :await; the committer thread (fnn-owner-committer-loop)
  ;; admitted as the :commit class drains every queued submission in one
  ;; quantum and fences the log once (fnn-owner-commit-queued-locked).
  ;; QUEUED counts the submissions queued since the last commit quantum
  ;; (host bookkeeping for the wake-up, never an input to a decision);
  ;; AWAITING maps a connection id to the mux connection waiting for its
  ;; completion, DONE a completion that arrived before its connection
  ;; registered; SPARING the member sockets a failed batch's stop spares.
  ;; The octets the next served read may take: ACL2's
  ;; fn-cbud-step-read-octets (host/owner-host.lisp fn-owner-read-octets),
  ;; read under the owner mutex (fnn-owner-refresh-read-octets) and read
  ;; here, without the mutex, by the I/O loops (host/native/mux.lisp).
  (read-octets nil)
  ;; Row S9: NIL, or (S0 SECONDS) from the retire request on: the snapshot
  ;; the drain window starts at and its length (books/owner-retire.lisp).
  ;; Set once under the roster mutex; read without it by the accept loops.
  (retire nil)
  (batching nil) (committer nil) (queued 0)
  ;; SYNCED: the syncer thread returned (lane log-2; fnn-owner-start-syncer).
  (synced nil)
  (commit-lock (sb-thread:make-mutex :name "fn owner commit"))
  (commit-ready (sb-thread:make-waitqueue :name "fn owner commit ready"))
  ;; guarded-by: fnn-owner-service-commit-lock (every access below takes it)
  (awaiting (make-hash-table)) (done (make-hash-table)) (sparing nil)
  ;; PKT-875 (books/owner-stop-drain.lisp): set by a graceful stop's drain
  ;; when ACL2 answers :release (the drain deadline passed); the committer
  ;; then tells every member in flight uncertain and sheds the queue, as at a
  ;; stall.  Read and written under COMMIT-LOCK.
  (drain-release nil))

;;; Inside a commit quantum (fnn-owner-commit-queued-locked) the effects that
;;; would let a member's outcome leave the owner before the log's barrier are
;;; held here and released after it, in order: the service log lines and the
;;; feed resolutions.  NIL outside a commit quantum.
(defvar *fnn-owner-deferred* nil)
;;; The last drained member's (OWNER ID TRANSITP KIND REASON): what renders
;;; its uncertain reply if the batch's barrier fails (fn-owner-uncertain-reply-of).
(defvar *fnn-owner-uncertain-render* nil)

(defun fnn-owner-signal-commit (service)
  "Wake every consumer wait: a Store publication is durable, or the owner stops.
The waiters poll again (ACL2 decides what each answers); this only signals."
  (sb-thread:with-mutex ((fnn-owner-service-wait-lock service))
    (incf (fnn-owner-service-commits service))
    (sb-thread:condition-broadcast (fnn-owner-service-wait-queue service))))

(defstruct (fnn-owner-feed-journal (:constructor %make-fnn-owner-feed-journal))
  peer path fd phase (replayed 0))

(defvar *fnn-owner-startup-hooks* nil)
;;; The service log.  The line is ACL2's (books/owner-log.lisp), left in the
;;; global `fn-owner-log-line' by the wrapper that just ran under the owner
;;; mutex; host/native/io.lisp fnn-log-line writes its octets and one LF to
;;; `*fnn-owner-log-fd*' (the `[log] path' run opened) or stderr and decides
;;; nothing.  The store's swallowed staging cleanup line (fnn-publish) goes
;;; through the same writer.

(defun fnn-owner-log (&optional (global 'fn-owner-log-line) optional)
  "Write the ACL2-rendered line in GLOBAL.  OPTIONAL: an empty line is none."
  (let ((line (fnn-global global)))
    (unless (fnn-octet-list-p line)
      (fnn-fault "owner returned a malformed log line"))
    (unless (and optional (null line))
      (if *fnn-owner-deferred*
          (push (cons :log line) (cdr *fnn-owner-deferred*))
        (fnn-log-line line)))))


(defun fnn-owner-run-startup-hooks (service)
  "Run ACL2-backed lifecycle adapters after recovery and before listen."
  (dolist (hook *fnn-owner-startup-hooks*)
    (unless (eq (funcall hook service) :accepted)
      (fnn-refuse "owner startup hook refused")))
  :accepted)

;;; Measurement (adapter-retirement-2; opt-in, FN_OWNER_MEASURE=1 at start):
;;; per label, how many times the owner mutex was held, for how long, and
;;; how many octets SBCL allocated while it was (sb-ext:get-bytes-consed is
;;; process-wide: a measurement run keeps other threads quiet).  The label
;;; is the dynamic *fnn-owner-measure-label*: :control inside a control
;;; request (an operator post), :feed-flush for the flush's own cost (nested
;;; in a hold), :other otherwise.  Off, it costs one special-variable test
;;; per hold.  The totals go to stderr when the owner stops
;;; (fnn-owner-measure-report).  It decides nothing and changes no state the
;;; owner reads.
(defvar *fnn-owner-measure* nil)
(defvar *fnn-owner-measure-label* :other)
(defvar *fnn-owner-measure-table*
  (make-hash-table :test 'eq :synchronized t))

(defun fnn-owner-measure-now ()
  "Microseconds from gettimeofday (get-internal-real-time advanced in whole
milliseconds on hbox). Exported SB-EXT, not an SB-UNIX internal: a raw
SBCL's SB-UNIX may lack the internal clock symbols."
  (multiple-value-bind (seconds microseconds) (sb-ext:get-time-of-day)
    (+ (* seconds 1000000) microseconds)))

(defun fnn-owner-measure-note (label start bytes)
  (let* ((held (- (fnn-owner-measure-now) start))
         (consed (- (sb-ext:get-bytes-consed) bytes))
         (row (or (gethash label *fnn-owner-measure-table*)
                  (setf (gethash label *fnn-owner-measure-table*)
                        (list 0 0 0 0)))))
    (incf (first row))
    (incf (second row) held)
    (setf (third row) (max (third row) held))
    (incf (fourth row) consed)))

(defmacro fnn-owner-measured ((label) &body body)
  (let ((start (gensym "START")) (bytes (gensym "BYTES")))
    `(if *fnn-owner-measure*
         (let ((,start (fnn-owner-measure-now))
               (,bytes (sb-ext:get-bytes-consed)))
           (unwind-protect (progn ,@body)
             (fnn-owner-measure-note ,label ,start ,bytes)))
       (progn ,@body))))

(defun fnn-owner-measure-report ()
  (when *fnn-owner-measure*
    (maphash
     (lambda (label row)
       (destructuring-bind (count held most consed) row
         (format *error-output*
                 "~&fn-owner-measure ~(~a~) holds=~d held-us=~d max-us=~d bytes=~d~%"
                 label count
                 held most
                 consed)))
     *fnn-owner-measure-table*)
    (finish-output *error-output*)))

(defun fnn-owner-core (name &rest args)
  (apply #'fnn-core-state name args))

(defun fnn-owner-refresh-read-octets (service)
  "Install ACL2's read size for the next served read (under the owner mutex:
the exposure install, and every served step, so a live change of the step
rate reaches the next read)."
  (let ((octets (fnn-owner-core 'fn-owner-read-octets)))
    (unless (and (integerp octets) (> octets 0))
      (fnn-fault "owner returned a malformed read size"))
    (setf (fnn-owner-service-read-octets service) octets)))

(defun fnn-owner-octets-global (name)
  (let ((value (fnn-global name)))
    (unless (fnn-octet-list-p value)
      (fnn-fault "owner returned non-octets in ~a" name))
    (fnn-octets value)))

;;; The render plan (books/served-plan.lisp; HST-023, PRF-248).  A served
;;; step answers with an immutable PLAN (the step's effects, whose reply
;;; octets are pointers into the connection's pinned archive) and the I/O
;;; loop (host/native/mux.lisp fnn-mux-queue-plan, fnn-mux-flush) renders it
;;; OFF the mutex, one window at a time into a fresh buffer of the window's
;;; size, writing each window before it asks for the next.  ACL2 sizes each
;;; window (fn-splan-window-size): a materialized effect, an octet list the
;;; arm built inside the step, is rendered whole, because holding its list
;;; while the socket drains costs sixteen octets per octet where the vector
;;; costs one (so the per-connection reply term of
;;; books/connection-budget.lisp stays the reply's size; it becomes a fixed
;;; window when the arms emit effects that point into the pinned view, the
;;; design's section 3.3, PKT-644 (a)).  fn-splan-window's keystone says the
;;; windows concatenate to fn-served-reply-octets of the effects; a
;;; :malformed status (a reply effect that is not octets) is a core fault, as
;;; a non-octet reply was before.  The buffer is a private `fn-octets$c'
;;; object (books/octets-stobj.lisp's foundation), never the live stobj:
;;; nothing touches the live `fn-octets' outside the mutex.
(defun fnn-make-render-buffer (n)
  "A private render buffer that holds N octets."
  (fn-octets$c-reserve n (create-fn-octets$c)))

(defun fnn-owner-render-next (plan &optional compressedp)
  "Render the next window of PLAN: (values OCTETS PLAN-REST DONEP CURSORP),
OCTETS a fresh vector (empty only when nothing remained, or at a cursor),
DONEP when nothing remains after it.  COMPRESSEDP: the connection has a
COMPRESS layer, and the window is ACL2's flush-schedule window
(books/nntp-compress.lisp fn-zc-render-window-size), each one sync flush.
CURSORP (lane join-f2-13, PRF-1020): the plan's next window is a cursor's
quantum (books/served-plan.lisp fn-splan-at-cursorp: a served OVER/XOVER
range), which the caller runs under the owner mutex
(fnn-owner-cursor-step) before it renders again; nothing is rendered here."
  (when (fnn-core 'fn-splan-at-cursorp plan)
    (return-from fnn-owner-render-next
      (values (fnn-make-octets 0) plan nil t)))
  (let ((size (if compressedp
                  (fnn-core 'fn-zc-render-window-size
                            (fnn-core 'fn-splan-window-size plan))
                (fnn-core 'fn-splan-window-size plan))))
    (unless (and (integerp size) (>= size 0))
      (fnn-fault "owner returned a malformed render window size"))
    (destructuring-bind (status rest buf)
        (fnn-call 'fn-splan-window plan size (fnn-make-render-buffer size))
      ;; :cursor (lane join-f2-13): the window ended in front of a cursor
      ;; effect, its octets written; the size above never reaches one (it
      ;; is the octets of the effect the window starts in), so the status
      ;; is :ok here, but a window that met one is whole as well.
      (unless (member status '(:ok :cursor))
        (fnn-fault "owner returned non-octets in its served reply"))
      (let ((array (svref buf 0)) (fill (svref buf 1)))
        (values (if (= fill (length array))
                    (the fnn-octets array)
                  (subseq (the fnn-octets array) 0 fill))
                rest
                (and (fnn-core 'fn-splan-donep rest) t)
                nil)))))

;;; The cursor quantum (lane join-f2-13, PRF-1020; books/served-plan-cursor.lisp).
;;; A served OVER/XOVER range's step answers a CURSOR (books/served-catalog.lisp
;;; fn-nntp-over-range-ovw: the range parsed and clamped once, no number
;;; probed); the plan stops in front of it and each quantum below probes at
;;; most W numbers and builds at most W NOV lines (books/over-window.lisp
;;; fn-ovw-step-window-at-most-w) under the owner mutex, admitted by the gate
;;; as the connection's class like its steps (D27: bounded work per hold, the
;;; range's size never).  ACL2 decides W (fn-splan-cursor-window: its constant,
;;; or a developer image's FN_NATIVE_OVER_WINDOW for the natives).  The
;;; keystone fn-splan-cw-drain-is-the-expanded-reply says the windows and
;;; quanta together write the reply the served machine decided, expanded
;;; (fn-ovw-expand), for every W and however the socket paced them; with
;;; fn-ovw-run-is-over-range-cat that is the unbounded reader's reply.
(defun fnn-owner-over-window ()
  "ACL2's cursor quantum, the developer selector's override passed through."
  (let ((raw (fnn-developer-selector "FN_NATIVE_OVER_WINDOW")))
    (fnn-core 'fn-splan-cursor-window
              (and raw (> (length raw) 0)
                   (every #'digit-char-p raw)
                   (parse-integer raw)))))

(defun fnn-owner-response-pin (service cid)
  "Hold ACL2's arena-reader generation for CID's response.  The caller
holds the owner mutex, before returning its captured plan.  Only one
outstanding response belongs to this connection."
  (unless (eq (fnn-owner-response-pin-step service (list :acquire cid)) :acquired)
    (fnn-fault "connection ~a could not capture its response ownership" cid)))

(defun fnn-owner-response-unpin (service cid)
  "CID's captured response drained or was cancelled.  Idempotent cleanup,
including a service stop; no owner semantic operation is needed."
  (unless (member (fnn-owner-response-pin-step service (list :release cid))
                  '(:released :absent))
    (fnn-fault "connection ~a could not settle its response ownership" cid)))

(defun fnn-owner-response-pin-step (service event)
  "ACL2 alone updates response ownership and the shared arena-pin table.
The same lock protects both this call and every other arena pin event."
  (sb-thread:with-mutex (*fnn-arena-pins-lock*)
    (destructuring-bind (owners pins status)
        (fnn-call 'fn-rpin-step (fnn-owner-service-response-pins service)
                  (or *fnn-arena-pins* (fnn-core 'fn-arpn-initial)) event)
      (setf (fnn-owner-service-response-pins service) owners
            *fnn-arena-pins* pins)
      (when (and (eq status :released)
                 (fnn-developer-selector "FN_NATIVE_OVER_TEST_PAUSE_AFTER_QUANTUM"))
        (fnn-err "OVER response-settled cid=~d status=released" (second event)))
      status)))

(defun fnn-owner-cursor-step (service cid plan class)
  "One quantum of PLAN's cursor under the owner mutex: the plan with the
quantum's reply in the cursor's place (and the cursor that remains)."
  (fnn-owner-serialized
   service cid
   (lambda ()
     (destructuring-bind (status rest)
         (fnn-call 'fn-splan-cursor-step plan (fnn-owner-over-window)
                   (fnn-live-stobj 'fn-arena) (fnn-live-stobj 'fn-cat))
       (unless (eq status :ok)
         (fnn-fault "owner returned a malformed cursor in its served reply"))
       rest))
   class))

(defun fnn-owner-render-next-quantum (service cid plan class &optional compressedp)
  "Render a window, running at most one cursor quantum under the owner
mutex as CID's CLASS: (values OCTETS PLAN-REST DONEP YIELDP).  Empty
progress yields with the exact continuation and response hold intact."
  (multiple-value-bind (octets rest donep cursorp)
      (fnn-owner-render-next plan compressedp)
    (unless cursorp
      (return-from fnn-owner-render-next-quantum (values octets rest donep nil)))
    (setq plan (fnn-owner-cursor-step service cid rest class))
    ;; A deterministic native witness: pause OFF the owner mutex while
    ;; the response still owns its generation, before rendering/writing.
    ;; Production refuses this selector (host/native/io.lisp).
    (let ((stall (fnn-developer-selector "FN_NATIVE_OVER_TEST_PAUSE_AFTER_QUANTUM")))
      (when (and stall (plusp (length stall)) (probe-file stall))
        (fnn-err "OVER quantum-held cid=~d" cid)
        (loop while (and (probe-file stall)
                         (not (fnn-owner-service-stopping service)))
              do (sleep 0.05))))
    (multiple-value-bind (octets rest donep cursorp)
        (fnn-owner-render-next plan compressedp)
      (values octets rest donep cursorp))))

(defun fnn-owner-list-global (name)
  "An ACL2 octet list left in NAME, as the list (no vector is made)."
  (let ((value (fnn-global name)))
    (unless (fnn-octet-list-p value)
      (fnn-fault "owner returned non-octets in ~a" name))
    value))

(defun fnn-owner-action (name &rest args)
  (let ((value (apply #'fnn-owner-core name args)))
    (unless (keywordp value)
      (fnn-fault "owner returned non-action from ~a" name))
    value))

;;; The SASL context of a served connection (books/nntp-auth.lisp
;;; (:sasl-context SEED BINDING); host/owner-host.lisp fn-owner-sasl-context).
;;; The seed is read from the OS CSPRNG off the owner mutex, at ACL2's width;
;;; installing it is one owner action under the caller's quantum.
(defun fnn-owner-sasl-seed ()
  "Fresh CSPRNG octets for one connection's SCRAM server nonces."
  (fnn-csprng-octets (fnn-core 'fn-owner-sasl-seed-octets) "SASL seed"))

(defun fnn-owner-sasl-context (cid seed binding)
  "Install CID's SASL context; the caller holds the owner mutex."
  (unless (eq (fnn-owner-action 'fn-owner-sasl-context cid seed binding) :ok)
    (fnn-fault "owner rejected the SASL context")))

(defun fnn-owner-arena-action (name &rest args)
  "fnn-owner-action for an owner entry that reads or seals the payload arena
(the records flip: the duplicate test reads stored bytes by handle)."
  (let ((value (apply #'fnn-core-arena-state name args)))
    (unless (keywordp value)
      (fnn-fault "owner returned non-action from ~a" name))
    value))

(defun fnn-owner-buffer-arena-action (name &rest args)
  "fnn-owner-buffer-action for an entry over the buffer AND the arena: the
POST's duplicate test and prepare (fn-owner-existing-action-buffer,
fn-owner-prepare-buffer), which seals the buffer's payload on acceptance."
  (let ((value (apply #'fnn-core-buffer-arena-state name args)))
    (unless (keywordp value)
      (fnn-fault "owner returned non-action from ~a" name))
    value))

(defun fnn-owner-buffer-action (name &rest args)
  "fnn-owner-action for a wrapper that reads the octet buffer.  The owner's
prepare answers owner outcomes (:unaffordable, :clock-unusable, ...) that the
Store node's action list +fnn-actions+ does not name; the buffer twins keep
the owner's keyword check, not the Store's."
  (let ((value (apply #'fnn-core-buffer-state name args)))
    (unless (keywordp value)
      (fnn-fault "owner returned non-action from ~a" name))
    value))

(defun fnn-owner-observe (operation result)
  (fnn-owner-action 'fn-owner-io operation result))

;;; The clock the owner decides under (books/clock.lisp; decision D10-a).
;;;
;;; Reading the two clocks is I/O and is this file's job.  What a reading is
;;; worth is fn-own-observe's (books/owner.lisp): it answers :observed,
;;; :refused or :invalid, and a refusal costs the owner its clock.  Nothing
;;; here compares two readings or decides that one is stale.
;;;
;;; This is the shape tools/run_owner.py had and the native host dropped:
;;; that file takes a reading at open, which fn-own-open pins as the
;;; connection's READER environment, and one before every read, which
;;; fn-own-read supplies to the injection decision so that two posts on one
;;; connection are injected at two times (RFC 5537 section 3.4).  The native
;;; host took one reading at startup and none afterwards, so every article of
;;; a run carried the same Date and Injection-Date and DATE answered one
;;; value for the life of the process.
;;;
;;; The wall reading is milliseconds since the DTN epoch, the unit
;;; fn-clock-observation takes.  gettimeofday is its one source, so the
;;; seconds and the sub-second part cannot come from two different instants;
;;; get-universal-time, which this used, has one-second resolution and gives
;;; every submission inside a second the same reading.
(defvar *fnn-owner-time-service* nil
  "The running service whose gate records the served reads' clock events
(lane time-model-2); nil outside `fnn-owner-run'.")

(defun fnn-owner-advance-clock ()
  "Hand the owner one fresh reading of this host's clocks.

The caller holds the owner mutex.  :refused is the model's answer to a
reading it cannot reconcile, not a host fault: a clock-less owner refuses to
inject, refuses to declare a group and answers DATE 503, each with its own
line, and the next reading is admitted whatever it says.  :invalid means this
function supplied no observation at all, which is a defect here."
  (multiple-value-bind (wall has-wall) (fnn-owner-wall-milliseconds)
    ;; Lane time-model-2 (N3 of lane proto-determinism): the monotonic
    ;; reading is a recorded event -- a :served clock event on the running
    ;; service's gate, journaled with the wall reading
    ;; (books/owner-time-journal.lisp) -- and the owner's observation is
    ;; made from that same reading.
    (let* ((mono (if *fnn-owner-time-service*
                     (nth-value 1 (fnn-owner-disk-event *fnn-owner-time-service* :served
                                                        (list wall has-wall)))
                   (fnn-owner-monotonic-ms)))
           (outcome (fnn-owner-action
                     'fn-owner-observe mono wall +fnn-owner-wall-error-ms+ has-wall)))
      (when (eq outcome :invalid)
        (fnn-fault "owner was handed a malformed clock reading"))
      ;; PRF-359 (PKT-872): the free space, when ACL2 says an observation
      ;; is due (fn-otm-space-due-p: none yet, or a cadence old), before
      ;; this read's write admission reads the value.
      (when *fnn-owner-time-service*
        (fnn-owner-space-observe-if-due *fnn-owner-time-service*))
      outcome)))

(defun fnn-owner-finish ()
  (fnn-owner-action 'fn-owner-finish))

(defun fnn-owner-finish-identity ()
  "An identity event's completion with the catalog's T4 then T2 (host/owner-host.lisp fn-owner-finish-identity)."
  (fnn-owner-core 'fn-owner-finish-identity))

(defun fnn-owner-finish-submission ()
  "The article completion's word, fn-ccar-own-finish's, which is fn-own-finish's (host/owner-host.lisp)."
  (fnn-owner-core 'fn-owner-finish-submission))

;;; The typed results (books/owner-results.lisp; wave 5 adapter retirement).
;;; A wrapper that used to answer a keyword and leave the rest of its result
;;; in f-put-global mailboxes returns ONE value; its recognizer is checked
;;; here, once, at the boundary -- a shape check, as fnn-owner-action's
;;; keyword check is, never a semantic one -- and a value that fails it is
;;; a core fault (exit 4).  Fields are read through ACL2's accessors.
(defun fnn-owner-result (recognizer name &rest args)
  (let ((value (apply #'fnn-owner-core name args)))
    (unless (fnn-core recognizer value)
      (fnn-fault "owner returned a malformed result from ~(~a~)" name))
    value))

(defun fnn-owner-names (name &rest args)
  "A wrapper's list of names (strings): no LF grammar, nothing split here."
  (apply #'fnn-owner-result 'string-listp name args))

;;; FeedPublication: WORD, PEER, the sealed frame PLAN ((PEER . FRAME) ...),
;;; TOKEN, the rendered COMMAND, its STATUS and the LOG-LINE.
(defun fnn-owner-feed-step (name &rest args)
  (apply #'fnn-owner-result 'fn-ores-feed-publication-p name args))

(defun fnn-owner-feed-arena-step (name &rest args)
  "fnn-owner-feed-step for an entry that READS the payload arena (the reply
chunk: a 335/238's article is the row's bytes through the arena,
books/owner-feed-article.lisp fn-ofa-feed-article).  It seals nothing."
  (let ((value (apply #'fnn-core-arena-state name args)))
    (unless (fnn-core 'fn-ores-feed-publication-p value)
      (fnn-fault "owner returned a malformed result from ~(~a~)" name))
    value))

(defun fnn-owner-feed-word (publication)
  (fnn-core 'fn-ores-feedpub-word publication))

(defun fnn-owner-feed-command (publication)
  (fnn-octets (fnn-core 'fn-ores-feedpub-command publication)))

(defun fnn-owner-feed-log (publication)
  "Write the publication's ACL2-rendered line; an empty one is none."
  (let ((line (fnn-core 'fn-ores-feedpub-log-line publication)))
    (when line (fnn-log-line line))))

(defun fnn-owner-feed-directory (store)
  (fnn-join (fnn-store-root store) "feed"))

(defun fnn-owner-feed-path (store peer)
  "Return the leaf directory and journal path selected by the ACL2 codec."
  (let* ((components (fnn-feed-filename-components peer))
         (directory (fnn-owner-feed-directory store)))
    (fnn-safe-directory directory t)
    (dolist (component (butlast components))
      (setq directory (fnn-join directory component))
      (fnn-safe-directory directory t))
    (values directory (fnn-join directory (car (last components))))))

(defun fnn-owner-feed-sync-namespace (store directory journal)
  "Fence every created v1 parent before the store's existing parent phase."
  (fnn-fsync-dir directory)
  (fnn-owner-feed-phase journal :directory-durable)
  (let ((feed (fnn-owner-feed-directory store)))
    (unless (string= directory feed)
      (let ((parent (fnn-parent directory)))
        (loop while (not (string= parent feed)) do
          (fnn-fsync-dir parent)
          (setq parent (fnn-parent parent))))
      (fnn-fsync-dir feed)))
  (fnn-fsync-dir (fnn-store-root store))
  (fnn-owner-feed-phase journal :parent-durable))

(defun fnn-owner-feed-phase (journal event)
  (let ((next (fnn-core 'fn-feed-journal-phase-step
                        (fnn-owner-feed-journal-phase journal) event)))
    (unless (keywordp next) (fnn-fault "malformed FNFD phase result"))
    (setf (fnn-owner-feed-journal-phase journal) next)
    (when (eq next :uncertain)
      (fnn-indeterminate "FNFD journal requires recovery"))
    next))

(defun fnn-owner-feed-read (journal size)
  (let ((out (fnn-make-octets size)) (at 0))
    (loop while (< at size) do
      (let* ((tmp (fnn-make-octets (- size at)))
             (piece (fnn-read-fd (fnn-owner-feed-journal-fd journal) tmp)))
        (when (zerop piece) (return))
        (replace out tmp :start1 at :end2 piece)
        (incf at piece)))
    (subseq out 0 at)))

(defun fnn-owner-feed-close (journal)
  (let ((fd (fnn-owner-feed-journal-fd journal)))
    (when fd
      (setf (fnn-owner-feed-journal-fd journal) nil)
      (fnn-close fd))))

(defun fnn-owner-feed-open (store peer)
  "Open, replay and repair one FNFD file through the ACL2 scanner."
  (let ((fd nil) (journal nil))
    (handler-case
        (multiple-value-bind (directory path) (fnn-owner-feed-path store peer)
          (progn
          (setq fd (fnn-open path (logior sb-posix:o-rdwr sb-posix:o-creat
                                          +fnn-o-nofollow+) #o600))
          (unless (fnn-regular-p (fnn-fstat fd))
            (fnn-fault "refusing non-regular FNFD journal: ~a" path))
          (setq journal (%make-fnn-owner-feed-journal
                         :peer peer :path path :fd fd :phase :closed))
          (fnn-owner-feed-phase journal :opened)
          (unless (eq (fnn-owner-action 'fn-owner-feed-journal-begin) :ok)
            (fnn-fault "owner refused FNFD scan start"))
          (let ((prefix-size
                  (fnn-nat (fnn-owner-core 'fn-owner-feed-journal-prefix-size))))
            (loop
              (let* ((prefix (fnn-owner-feed-read journal prefix-size))
                     (plan (fnn-core 'fn-feed-journal-prefix
                                     (fnn-octet-list prefix)))
                     (frame (if (and (integerp plan) (>= plan 0))
                                (fnn-owner-feed-read journal plan)
                              (fnn-make-octets 0)))
                     (status
                       (fnn-owner-action
                        'fn-owner-feed-journal-scan
                        (fnn-octet-list (fnn-string-octets peer))
                        (fnn-octet-list prefix) (fnn-octet-list frame))))
                (case status
                  (:next (incf (fnn-owner-feed-journal-replayed journal)))
                  (:invalid
                   (fnn-fault "invalid complete FNFD evidence: ~a" path))
                  ((:end :repair)
                   (fnn-owner-feed-phase journal status)
                   (when (eq status :repair)
                     (fnn-posix (path)
                       (sb-posix:ftruncate
                        fd (fnn-nat
                            (fnn-owner-core 'fn-owner-feed-journal-offset))))
                     (fnn-owner-feed-phase journal :truncated))
                   (return))
                  (t (fnn-fault "unexpected FNFD scan result: ~a" status))))))
          (fnn-fsync-file fd)
          (fnn-owner-feed-phase journal :content-durable)
          (fnn-owner-feed-sync-namespace store directory journal)
          (fnn-posix (path) (sb-posix:lseek fd 0 sb-posix:seek-end))
          journal))
      (error (e)
        (when fd (ignore-errors (fnn-close fd)))
        (error e)))))

(defun fnn-owner-feed-append (journal frame)
  "Append one ACL2-sealed frame and cross every ordered durability barrier."
  (handler-case
      (let ((envelope (fnn-core 'fn-feed-journal-wrap
                                (fnn-octet-list frame))))
        (unless (fnn-octet-list-p envelope)
          (fnn-fault "owner refused FNFD envelope"))
        (fnn-owner-feed-phase journal :append)
        (fnn-write-all (fnn-owner-feed-journal-fd journal)
                       (fnn-octets envelope))
        (fnn-owner-feed-phase journal :written)
        (fnn-fsync-file (fnn-owner-feed-journal-fd journal))
        (fnn-owner-feed-phase journal :append-durable))
    (error (e)
      (ignore-errors (fnn-owner-feed-phase journal :failed))
      (fnn-owner-feed-close journal)
      (fnn-indeterminate "FNFD append uncertain: ~a (~a)"
                         (fnn-owner-feed-journal-path journal) e))))

(defun fnn-owner-feed-decoded-peer (components location)
  "Refuse a discovered entry unless ACL2 reconstructs its exact peer label."
  (multiple-value-bind (peer accepted)
      (fnn-feed-filename-decode-components components)
    (unless accepted
      (fnn-fault "conflicting FNFD filename evidence: ~a" location))
    peer))

(defun fnn-owner-feed-observe-directory (directory remaining namespace)
  "Read one namespace with the ACL2-selected remaining total budget.

The bounded raw primitive faults before retaining an excess entry.  Its count
then becomes an ACL2 observation, which returns the one budget available to
all later sibling and child directories.
"
  (let ((names (fnn-list-directory-bounded directory remaining namespace)))
    (values names
            (fnn-feed-filename-observation-remaining remaining (length names)))))

(defun fnn-owner-feed-v1-peers (directory components depth remaining)
  "Enumerate the bounded v1 tree; every entry is decoded or reported.

COMPONENTS begins with `v1'.  A journal leaf may coexist with child chunk
directories because one encoded label can be a prefix of a longer label.
"
  (let ((peers nil))
    (fnn-safe-directory directory)
    (multiple-value-bind (names after-observation)
        (fnn-owner-feed-observe-directory directory remaining "FNFD v1 namespace")
      (setq remaining after-observation)
      (dolist (name names)
        (let ((path (fnn-join directory name)))
          (cond
            ((string= name "journal.fnfd")
             (fnn-check-regular path)
             (let ((peer (fnn-owner-feed-decoded-peer
                          (append components (list name)) path)))
               (when (member peer peers :test #'string=)
                 (fnn-fault "duplicate FNFD journal peer: ~a" peer))
               (push peer peers)))
            ((fnn-lstat path)
             (unless (and (< depth (fnn-feed-filename-max-v1-chunks))
                          (fnn-feed-filename-component-p name))
               (fnn-fault "invalid FNFD v1 namespace entry: ~a" path))
             (unless (fnn-directory-p (fnn-lstat path))
               (fnn-fault "invalid FNFD v1 namespace entry: ~a" path))
             (multiple-value-bind (nested after-nested)
                 (fnn-owner-feed-v1-peers path (append components (list name))
                                          (1+ depth) remaining)
               (setq remaining after-nested)
               (dolist (peer nested)
                 (when (member peer peers :test #'string=)
                   (fnn-fault "duplicate FNFD journal peer: ~a" peer))
                 (push peer peers))))
            (t (fnn-fault "unreadable FNFD v1 namespace entry: ~a" path)))))
      (unless peers
        (fnn-fault "empty FNFD v1 namespace: ~a" directory))
      (values (nreverse peers) remaining))))

(defun fnn-owner-feed-existing-peers (store)
  "Return every recoverable FNFD peer; conflicting evidence is never skipped."
  (let ((directory (fnn-owner-feed-directory store))
        (peers nil)
        (remaining (fnn-feed-filename-observation-limit)))
    (when (fnn-lstat directory)
      (fnn-safe-directory directory)
      (multiple-value-bind (names after-observation)
          (fnn-owner-feed-observe-directory directory remaining "FNFD feed namespace")
        (setq remaining after-observation)
        (dolist (name names)
          (let ((path (fnn-join directory name)))
            (cond
              ((string= name "v1")
               (unless (fnn-directory-p (fnn-lstat path))
                 (fnn-fault "invalid FNFD v1 namespace: ~a" path))
               (multiple-value-bind (nested after-nested)
                   (fnn-owner-feed-v1-peers path (list name) 0 remaining)
                 (setq remaining after-nested)
                 (dolist (peer nested)
                   (when (member peer peers :test #'string=)
                     (fnn-fault "duplicate FNFD journal peer: ~a" peer))
                   (push peer peers))))
              ((and (> (length name) 5)
                    (string= ".fnfd" (subseq name (- (length name) 5))))
               (fnn-check-regular path)
               (let ((peer (fnn-owner-feed-decoded-peer (list name) path)))
                 (when (member peer peers :test #'string=)
                   (fnn-fault "duplicate FNFD journal peer: ~a" peer))
                 (push peer peers)))
              (t (fnn-fault "conflicting FNFD namespace entry: ~a" path))))))
    (nreverse peers))))

(defun fnn-owner-feed-open-all (service configured)
  ;; The order is the configured peers, then the historical journals by name:
  ;; never the directory's listing order, which differs between filesystems
  ;; and copies of one store (lane proto-determinism: the owner's feeds were
  ;; in readdir order, a configured peer included, because remove-duplicates
  ;; keeps the LAST occurrence).
  (let* ((store (fnn-owner-service-store service))
         (peers (append configured
                        (sort (copy-list (fnn-owner-feed-existing-peers store)) #'string<)))
         (opened nil))
    (handler-case
        (progn
          (dolist (peer (remove-duplicates peers :test #'string= :from-end t))
            (push (cons peer (fnn-owner-feed-open store peer)) opened))
          (nreverse opened))
      (error (e)
        (dolist (entry opened) (fnn-owner-feed-close (cdr entry)))
        (error e)))))

(defun fnn-owner-feed-close-all (service)
  (dolist (entry (fnn-owner-service-feeds service))
    (fnn-owner-feed-close (cdr entry)))
  (setf (fnn-owner-service-feeds service) nil))

(defun fnn-owner-feed-open-missing (service configured)
  "Install journals for newly configured feeds before they can enqueue.

Historical journals remain open until owner shutdown because replayed
obligations may still name a peer removed from the current configuration."
  (let* ((current (fnn-owner-service-feeds service))
         (known (mapcar #'car current))
         (missing (loop for peer in configured
                        unless (member peer known :test #'string=)
                        collect peer))
         (opened nil))
    (handler-case
        (progn
          (dolist (peer missing)
            (push (cons peer (fnn-owner-feed-open
                              (fnn-owner-service-store service) peer)) opened))
          (setf (fnn-owner-service-feeds service)
                (append current (nreverse opened))))
      (error (e)
        (dolist (entry opened) (fnn-owner-feed-close (cdr entry)))
        (error e)))))

(defun fnn-owner-feed-refresh-configuration (service)
  "Apply ACL2's live configuration to feeds and provision its journals.

Call while holding the owner mutex immediately after a durable configuration
completion.  FN-OWNER-FEED-CONFIGURE is the sole peer membership decision."
  (fnn-owner-feed-open-missing service (fnn-owner-names 'fn-owner-feed-configure)))

(defun fnn-owner-feed-flush (service publication)
  "Persist PUBLICATION's sealed frame plan before its authorized effect.

Each pair of the plan names its peer's journal and carries the sealed frame,
in append order (books/owner-results.lisp fn-ores-sealed-plan-is-indexed-fetch:
the plan is the old by-index fetch); nothing is fetched by index and no name
list is split.  The recognizer (fnn-owner-feed-step) already checked every
pair is a string and a non-empty octet list."
  (fnn-owner-measured (:feed-flush)
    (dolist (pair (fnn-core 'fn-ores-feedpub-plan publication))
      (let ((journal (cdr (assoc (car pair) (fnn-owner-service-feeds service)
                                 :test #'string=))))
        (unless journal
          (fnn-fault "FNFD obligation has no journal for peer ~a" (car pair)))
        (fnn-owner-feed-append journal (fnn-octets (cdr pair)))))))

(defun fnn-owner-feed-reconcile (service)
  (loop
    (let* ((publication (fnn-owner-feed-step 'fn-owner-feed-reconcile-next))
           (resolution (fnn-owner-feed-word publication)))
      (case resolution
        (:done (return))
        (:uncertain
         (fnn-indeterminate "feed intent cannot be resolved from recovered store"))
        ((:feed-commit :feed-abort)
         (fnn-owner-feed-flush service publication)
         (unless (eq (fnn-owner-action 'fn-owner-feed-reconcile-apply) :ok)
           (fnn-fault "owner refused recovered feed resolution")))
        (t (fnn-fault "unexpected feed reconciliation: ~a" resolution))))))

(defun fnn-owner-recover-core (store records max-connections entry)
  "Install the owner from the Store open this process just ran.  The open
(full replay, or the verified state checkpoint over the records after it) left
its extended checkpoint E and ACL2's (fn-sco-store-open E ...) in the global
`fn-store-sco-open'; fn-owner-recover-from-store-open installs from them with
fn-ock-install, which is fn-ock-recover-extended of E
(fn-ock-install-of-store-open-by-definition), so the keystone
fn-owner-recover-from-checkpoint-equals-full-recover says both paths install
the full open's owner, and nothing is replayed a second time.  Returns the
checkpoint's S, or NIL."
  (declare (ignore records))
  (let* ((mode (fnn-store-open-mode store))
         (s (and (eq (first mode) :checkpoint) (second mode)))
         ;; THE SWITCH (PRF-1037): ENTRY is the node secret's current entry
         ;; (fnn-owner-read-node-secret, read before this open); ACL2 derives
         ;; the paged Message-ID table's key from it and installs it before
         ;; the rows are loaded (fn-owner-install-extended).
         (result (fnn-owner-action 'fn-owner-recover-from-store-open max-connections entry)))
    ;; A watermark past RFC 3977 section 6's bound is a damaged Store, refused
    ;; by name (books/owner-number-bound.lisp fn-onb-open-okp); the node does
    ;; not start on it.
    (when (eq result :article-numbers-damaged)
      (fnn-refuse "store ~a is damaged: an article-number watermark exceeds RFC 3977's bound (2147483647)"
                  (fnn-store-root store)))
    (unless (eq result :recovering)
      (fnn-fault "owner rejected committed history"))
    (unless (eq (fnn-owner-core 'fn-owner-sco-note-durable s) :noted)
      (fnn-fault "owner refused the durable checkpoint sequence"))
    ;; The base's canonical payload count: the arena's count after the open
    ;; (host/owner-host.lisp fn-owner-sco-note-base-payloads).
    (unless (eq (fnn-owner-core 'fn-owner-sco-note-base-payloads
                                (first (fnn-call 'fn-arena-count (fnn-live-arena))))
                :noted)
      (fnn-fault "owner refused the base payload count"))
    s))

;;; SEC-006 (PRF-210): read the node's key ring and hand it to the owner,
;;; which carries it (books/owner.lisp fn-own-node-secret): the current
;;; entry from STORE/keys/node-secret.key, then each retained older epoch
;;; E-1 .. 1 from node-secret-E.key, each read by ACL2
;;; (host/native/io.lisp fnn-node-secret-read-entry, fn-ns-file-parse).
;;; Refused by name, and the node does not start, when the current file is
;;; missing (it is NEVER regenerated here: `store ROOT node-secret create'
;;; is the only verb that makes one), a retained epoch is missing, a file is
;;; not regular, is readable or writable by group or others, or does not
;;; parse, or ACL2 does not accept the ring (fn-owner-install-node-secret
;;; answers :refused unless fn-ns-ringp).
(defun fnn-owner-read-node-secret (store)
  "Read the ring's files: (CURRENT . RETAINED), the current entry first.
Read BEFORE the recovery (fnn-owner-recover-core takes the current entry:
THE SWITCH, PRF-1037, keys the catalog's paged Message-ID table from it at
the open) and installed after it (fnn-owner-install-node-secret): one read,
one ring, so the table's key and the served boundary's are one source."
  (let* ((path (fnn-node-secret-path store))
         (current (or (fnn-node-secret-read-entry path "node secret")
                      (fnn-refuse "node secret ~a is missing: run `store ~a node-secret create' once (a start never creates one)"
                                  path (fnn-store-root store))))
         (epoch (fnn-core 'fn-ns-entry-epoch current))
         (retained
           (loop for e downfrom (1- epoch) to 1
                 collect (let ((older (fnn-node-secret-epoch-path store e)))
                           (or (fnn-node-secret-read-entry older "retained node secret")
                               (fnn-refuse "node secret retained epoch ~d missing: ~a"
                                           e older))))))
    (cons current retained)))

(defun fnn-owner-install-node-secret (store ring)
  "Hand the ring fnn-owner-read-node-secret read to the owner."
  (unless (eq (fnn-owner-core 'fn-owner-install-node-secret ring)
              :installed)
    (fnn-refuse "node secret files in ~a do not form a key ring (epochs must decrease from the current one)"
                (fnn-node-secret-directory store))))

(defun fnn-owner-install (root max-connections &optional fault)
  (multiple-value-bind (store count) (fnn-open-live-store root t fault)
    (let ((service nil))
      (handler-case
          (progn
            ;; PKT-648: the store's durability policy against its mount
            ;; (books/store-mount-identity.lisp fn-smid-start-verdict),
            ;; before the owner serves anything.
            (fnn-check-filesystem-identity store t)
            ;; SEC-006: the ring is READ before the recovery (its current
            ;; entry keys the catalog's Message-ID table at the open) and
            ;; INSTALLED after the recovery that builds the owner.
            (let ((ring (fnn-owner-read-node-secret store)))
              (fnn-owner-recover-core store count max-connections (car ring))
              (fnn-owner-install-node-secret store ring))
            ;; `ms=': milliseconds from the image's entry to here (the
            ;; recovery included), the measured length of a start that
            ;; `install.sh --upgrade' quotes as the next gap (io.lisp
            ;; *fnn-process-started*).
            (let ((ms (fnn-ms-since-process-start)))
              (fnn-err "OWNER-OPEN ~a ms=~d" (fnn-open-report store) ms)
              ;; The service log's line for it, ACL2's rendering
              ;; (books/native-health.lisp fn-nh-run-opened-line): what
              ;; `install.sh --upgrade' reads for the gap to expect.
              (fnn-log-line (fnn-core 'fn-native-health-host-run-opened-line ms)))
            ;; The persisted profile ACL2 decoded at open, handed back once:
            ;; the owner's transaction budget is derived from it there.
            (unless (eq (fnn-owner-core 'fn-owner-install-profile
                                        (fnn-store-config store))
                        :installed)
              (fnn-fault "owner refused the store profile"))
            ;; The recovery barriers again (three, fnn-store-recovery-barriers):
            ;; fresh namespace observations, now delivered to fn-owner.
            (let ((phase nil))
              (dolist (barrier (fnn-store-recovery-barriers store))
                (handler-case (funcall barrier)
                  (fnn-os-error (e)
                    (fnn-owner-observe :recovery-barrier :uncertain)
                    (error e)))
                (setq phase (fnn-owner-observe :recovery-barrier :ok)))
              (unless (eq phase :ready)
                (fnn-fault "owner did not complete recovery barriers")))
            ;; The first reading, against a clock-less owner.  Every later
            ;; reading is taken at the event that decides under it, in
            ;; fnn-mux-begin and fnn-owner-handle-chunk: this one is
            ;; not an anchor the run is dated against.
            (unless (eq (fnn-owner-advance-clock) :observed)
              (fnn-fault "owner refused its first clock observation"))
            (let ((configured (fnn-owner-names 'fn-owner-feed-configure)))
              (setq service
                    (%make-fnn-owner-service
                     :store store
                     :lock (sb-thread:make-mutex :name "fn owner/store")
                     :gate (fnn-make-owner-gate)
                     :start-hooks *fnn-owner-start-hooks*
                     :stop-hooks *fnn-owner-stop-hooks*
                     :close-hooks *fnn-owner-close-hooks*
                     ;; Served submissions are committed in
                     ;; batches by the committer thread.
                     :batching (fnn-store-logp store)
                     :stopping nil))
              (progn
                (setf (fnn-owner-service-feeds service)
                      (fnn-owner-feed-open-all service configured))
                (fnn-owner-feed-reconcile service)
                (when configured
                  (let ((restart (fnn-owner-feed-step 'fn-owner-feed-restart)))
                    (unless (eq (fnn-owner-feed-word restart) :restarted)
                      (fnn-fault "owner refused the feed restart"))
                    (fnn-owner-feed-flush service restart))))
              ;; The open keeps no records (PKT-823): the pending key
              ;; statement is read off the newest record alone.
              (fnn-owner-key-statement-recover
               service (and (plusp count) (list (fnn-history-last-record store))))
              ;; The Store open's loaded checkpoint is consumed (the owner's
              ;; base is the open's extension, fn-owner-sco-base): release it,
              ;; so the reopened owner does not hold the checkpoint's capture
              ;; beside the extension (checkpoint-arena-2's reopen heap).  A
              ;; later read of a history whose prefix was the
              ;; checkpoint's then faults by name (fnn-log-history-plan).
              (fnn-core-state 'fn-store-sco-clear)
              (fnn-log-history-release-prefix store)
              service))
        (error (e)
          (when service (fnn-owner-feed-close-all service))
          (fnn-store-close store)
          (error e))))))

(defmacro fnn-with-roster ((service) &body body)
  `(sb-thread:with-mutex ((fnn-owner-service-roster ,service)) ,@body))

;;; The scheduler gate (books/owner-scheduler.lisp).  Every entry to the owner
;;; mutex names its class; the gate keeps how many threads of each class wait
;;; (a host observation), the per-class arrival tickets, whether a thread is
;;; inside and which, the class ACL2 last admitted, and ACL2's scheduler
;;; value (the cursor and the hold/wait fold `health' prints).  The class's
;;; slot is ACL2's (fn-osch-class-index over *fn-osch-order*); the host
;;; keeps no order of its own.  The gate mutex is held for a list update and
;;; one ACL2 call, never across a step or any I/O.
(defstruct (fnn-owner-gate (:constructor %make-fnn-owner-gate))
  (mutex (sb-thread:make-mutex :name "fn owner gate"))
  (ready (sb-thread:make-waitqueue :name "fn owner gate ready"))
  ;; Slots 0-3 the four classes of books/owner-scheduler.lisp, slot 4 the
  ;; commit class (books/owner-commit-class.lisp), slot 5 :inspect (the live
  ;; status and health pages; books/owner-commit-steps.lisp).
  (waiting (make-array 6 :initial-element 0))
  (next-ticket (make-array 6 :initial-element 0))
  (serving (make-array 6 :initial-element 0))
  (busy nil)
  (holder nil)
  (turn nil)
  (sched nil))

(defun fnn-make-owner-gate ()
  (%make-fnn-owner-gate :sched (fnn-core 'fn-otm-init)))

(defun fnn-owner-class-index (class)
  "The class's slot, ACL2's (fn-osch-class-index); a name ACL2 does not
recognise is a host fault."
  (unless (fnn-core 'fn-ocs-classp class)
    (fnn-fault "unknown owner service class ~a" class))
  (let ((i (fnn-core 'fn-ocs-class-index class)))
    (unless (and (integerp i) (<= 0 i 5))
      (fnn-fault "owner returned a malformed service class slot"))
    i))

(defun fnn-ms-since (started)
  (round (* 1000 (- (get-internal-real-time) started)) internal-time-units-per-second))

(defun fnn-owner-gate-pick (gate)
  "The owner is free and nobody was admitted: ask ACL2 which class runs
(nil when no class waits).  The caller holds the gate mutex."
  (destructuring-bind (class sched)
      ;; books/owner-commit-steps.lisp: the phase of the commit in flight is
      ;; part of ACL2's value; the six counts are the host's observation.
      ;; books/owner-time-model.lisp: the value also carries the disk's
      ;; state; the pick is the pipeline's (fn-otm-next-is-ocp-next).
      (fnn-call 'fn-otm-next (fnn-owner-gate-sched gate)
                (coerce (fnn-owner-gate-waiting gate) 'list))
    (setf (fnn-owner-gate-sched gate) sched
          (fnn-owner-gate-turn gate) (and class (fnn-owner-class-index class)))
    (sb-thread:condition-broadcast (fnn-owner-gate-ready gate))))

(defun fnn-owner-gate-enter (gate class)
  "Wait at the gate as CLASS until admitted; return the wait in milliseconds.
A thread already inside cannot enter again: a nested quantum would wait on
itself for ever, so it is a fault here (as SBCL's recursive-lock error was)."
  (let* ((i (fnn-owner-class-index class))
         (started (get-internal-real-time))
         (ticket nil))
    (sb-thread:with-mutex ((fnn-owner-gate-mutex gate))
      (when (eq (fnn-owner-gate-holder gate) sb-thread:*current-thread*)
        (fnn-fault "owner re-entered by the thread holding it"))
      (setq ticket (svref (fnn-owner-gate-next-ticket gate) i))
      (incf (svref (fnn-owner-gate-next-ticket gate) i))
      (incf (svref (fnn-owner-gate-waiting gate) i))
      (loop
        (when (and (not (fnn-owner-gate-busy gate)) (null (fnn-owner-gate-turn gate)))
          (fnn-owner-gate-pick gate))
        (when (and (not (fnn-owner-gate-busy gate))
                   (eql (fnn-owner-gate-turn gate) i)
                   (= ticket (svref (fnn-owner-gate-serving gate) i)))
          (setf (fnn-owner-gate-busy gate) t
                (fnn-owner-gate-holder gate) sb-thread:*current-thread*
                (fnn-owner-gate-turn gate) nil)
          (incf (svref (fnn-owner-gate-serving gate) i))
          (decf (svref (fnn-owner-gate-waiting gate) i))
          (return))
        (sb-thread:condition-wait (fnn-owner-gate-ready gate)
                                  (fnn-owner-gate-mutex gate))))
    (fnn-ms-since started)))

(defun fnn-owner-gate-leave (gate class hold-ms wait-ms)
  "Leave the owner: fold this quantum's hold and wait, and let ACL2 admit
the next class (none when nothing waits: fn-osch-next answers nil)."
  (sb-thread:with-mutex ((fnn-owner-gate-mutex gate))
    (setf (fnn-owner-gate-busy gate) nil
          (fnn-owner-gate-holder gate) nil
          (fnn-owner-gate-sched gate)
          (fnn-core 'fn-otm-observe (fnn-owner-gate-sched gate) class hold-ms wait-ms))
    (fnn-owner-gate-pick gate)))

(defun fnn-owner-monotonic-ms ()
  "One reading of the monotonic clock, in milliseconds: the only clock the
disk's deadline logic reads (books/owner-time-model.lisp takes it as NOW;
the host compares no times; ACL2 converts the ticks: io.lisp fnn-monotonic-ms)."
  (fnn-monotonic-ms))

(defun fnn-owner-space-event (service need)
  "PRF-359 (PKT-872): record the store filesystem's free octets (statvfs,
host/native/io.lisp fnn-disk-free-octets; nil when it cannot observe) with
ACL2's NEED as a :space event (books/owner-time-model.lisp): below the need
the disk is :full and every write is shed.  The host compares nothing."
  (let ((free (ignore-errors
               (fnn-disk-free-octets (fnn-owner-service-store service)))))
    (fnn-owner-disk-event service :space
                          (list (and (integerp free) (>= free 0) free) need))))

(defun fnn-owner-space-observe-if-due (service)
  "Under the owner mutex (fn-owner-space-need reads the live configuration):
keep ACL2's NEED for the observation the next quantum takes before its gate
entry (fnn-owner-space-preobserve).  No statvfs here: the observation is I/O
and stays outside the semantic critical section (a greeting, a read, the
checkpoint capture)."
  (setf (fnn-owner-service-space-need service) (fnn-owner-core 'fn-owner-space-need)))

(defun fnn-owner-space-preobserve (service &optional force)
  "Off the owner mutex, before a quantum's gate entry: a :space event (statvfs,
at the NEED the owner last computed) when ACL2 says one is due
(fn-otm-space-due-p over the gate's value), or FORCE (a status render).  The
observation precedes the quantum's admission, so a write the quantum admits
is judged against it (PRF-359).  Nothing before the run's first NEED."
  (let ((need (fnn-owner-service-space-need service)))
    (when (and need (eq service *fnn-owner-time-service*)
               (or force
                   (fnn-core 'fn-otm-space-due-p (fnn-owner-gate-sched-value service))))
      (fnn-owner-space-event service need))))

(defun fnn-owner-space-prime (service)
  "The run's first NEED (under the owner mutex) and its first observation
(off it), before the listener serves."
  (fnn-owner-serialized service nil
                        (lambda () (fnn-owner-space-observe-if-due service)))
  (fnn-owner-space-preobserve service t))

(defun fnn-owner-sched-snapshot (service)
  "ACL2's scheduler value for `health' and `status'
(books/owner-time-model.lisp fn-otm-health-lines, fn-otm-disk-lines): a clock
event is appended on demand first, so the figures are at the render's time.
The free space (PRF-359: health's `disk' state reads it) is observed by the
caller before it takes the owner mutex (fnn-owner-space-preobserve FORCE)."
  (fnn-owner-disk-event service :clock)
  (let ((gate (fnn-owner-service-gate service)))
    (sb-thread:with-mutex ((fnn-owner-gate-mutex gate))
      (fnn-owner-gate-sched gate))))

;;; The disk's events (books/owner-time-model.lisp, lane time-model, PRF-311).
;;; Each carries one monotonic reading, which ACL2 records before it applies
;;; the event; every disk decision reads the recorded time.  The reading is
;;; taken INSIDE the gate mutex, which orders every clock event, so a
;;; reading below the recorded time is a true regression of the clock and
;;; never two producers' readings arriving out of order.  The gate mutex is
;;; held for the reading and the one ACL2 call.

(defun fnn-owner-disk-event (service kind &optional (arg 0))
  "Append the disk event KIND (:clock, :served with ARG (WALL HAS-WALL),
:issue with ARG the limits, :return) at a fresh reading to ACL2's value
(books/owner-time-journal.lisp fn-otm-disk-step), offer its journal entry to
the writer and write the service log line ACL2 renders for its word.
Returns (values WORD READING)."
  (let* ((gate (fnn-owner-service-gate service))
         (word nil) (line nil) (entry nil) (reading nil))
    (sb-thread:with-mutex ((fnn-owner-gate-mutex gate))
      (setq reading (fnn-owner-monotonic-ms))
      (destructuring-bind (w sched jline lline)
          (fnn-core 'fn-otm-disk-step (fnn-owner-gate-sched gate) kind reading arg)
        ;; The words are ACL2's table (books/owner-time-journal.lisp, defevent
        ;; fn-otm-word): its generated recognizer decides, not a host copy.
        (unless (fnn-core 'fn-otm-wordp w)
          (fnn-fault "owner returned a malformed disk event word ~a" w))
        (when (eq w :fault)
          (fnn-fault "owner refused the disk event ~a" kind))
        (setf (fnn-owner-gate-sched gate) sched
              word w
              entry jline
              line lline)
        ;; Offered under the gate mutex, which numbered it: the queue then
        ;; holds the entries in their sequence (offered after the release,
        ;; two producers' entries landed 161, 162, 160; batch AY,
        ;; test_native_slow_disk).  The offer only enqueues (never writes,
        ;; never waits), and the queue's lock never takes the gate mutex.
        (fnn-journal-line entry)))
    (when line (fnn-log-line line))
    (values word reading)))

(defun fnn-owner-journal-note (service a b)
  "Journal a note (books/owner-time-journal.lisp fn-otm-note-step): a
decision that changed nothing in the value, with its two counts."
  (let ((gate (fnn-owner-service-gate service)) (entry nil))
    (sb-thread:with-mutex ((fnn-owner-gate-mutex gate))
      (destructuring-bind (sched jline)
          (fnn-core 'fn-otm-note-step (fnn-owner-gate-sched gate) a b)
        (setf (fnn-owner-gate-sched gate) sched entry jline)
        ;; Under the gate mutex, in sequence (fnn-owner-disk-event).
        (fnn-journal-line entry)))))

(defun fnn-owner-disk-admission (service)
  "The write admission at the gate's recorded time (fn-otm-admit-post):
:admit or :shed.  Appends nothing: the caller's own clock event came first."
  (let* ((gate (fnn-owner-service-gate service))
         (word (fnn-core 'fn-otm-admit-post
                         (sb-thread:with-mutex ((fnn-owner-gate-mutex gate))
                           (fnn-owner-gate-sched gate)))))
    (unless (member word '(:admit :shed))
      (fnn-fault "owner returned a malformed admission ~a" word))
    word))

(defun fnn-owner-gate-sched-value (service)
  "The gate's scheduler value (books/owner-time-model.lisp), read once under
the gate mutex: the admission, the reason lines and the peer read's class
are ACL2's over this one value."
  (let ((gate (fnn-owner-service-gate service)))
    (sb-thread:with-mutex ((fnn-owner-gate-mutex gate))
      (fnn-owner-gate-sched gate))))

(defun fnn-owner-peer-read-class (service)
  "The class a peer connection's read enters the gate as (PKT-858,
books/owner-time-admission.lisp fn-otm-peer-read-class): :reader while the
disk sheds at the gate's recorded time (the read runs under the disk-slow
posture, so IHAVE is answered 436 and CHECK 431 at once), else :transit
(which waits for a batch in flight).  Appends nothing: the committer's timed
wakes append the clock events that move the disk past its deadline."
  (let ((class (let ((gate (fnn-owner-service-gate service)))
                 ;; Under the gate mutex, as fnn-owner-gate-pick's fn-otm-next.
                 (sb-thread:with-mutex ((fnn-owner-gate-mutex gate))
                   (fnn-core 'fn-otm-peer-read-class (fnn-owner-gate-sched gate))))))
    (unless (member class '(:reader :transit))
      (fnn-fault "owner returned a malformed peer read class ~a" class))
    class))

(defun fnn-owner-disk-stalled-p (service)
  "Whether the pending barrier's :stalled mode was entered (a clock event
past H): the committer then tells the batch's posters uncertain."
  (let ((gate (fnn-owner-service-gate service)))
    (and (fnn-core 'fn-otm-disk-stalled
                   (fnn-core 'fn-otm-disk
                             (sb-thread:with-mutex ((fnn-owner-gate-mutex gate))
                               (fnn-owner-gate-sched gate))))
         t)))

(defun fnn-owner-disk-wait-ms (service)
  "ACL2's timed wait for the committer (fn-otm-wait-ms): milliseconds, or nil."
  (let ((gate (fnn-owner-service-gate service)))
    (let ((ms (fnn-core 'fn-otm-wait-ms
                        (sb-thread:with-mutex ((fnn-owner-gate-mutex gate))
                          (fnn-owner-gate-sched gate)))))
      (unless (or (null ms) (and (integerp ms) (plusp ms)))
        (fnn-fault "owner returned a malformed wait ~a" ms))
      ms)))

(defun fnn-owner-disk-admit (service)
  "A served POST's admission (fn-otm-admit-post): a clock event is appended
on demand first.  :admit or :shed."
  (fnn-owner-disk-event service :clock)
  (fnn-owner-disk-admission service))

(defun fnn-owner-shed-queued-locked (service)
  "The disk is slow: every queued served POST, oldest first, is answered
ACL2's try-later refusal (host/owner-host.lisp fn-owner-shed-outcome:
fn-own-outcome's :refused outcome, nothing stored, with the reason line)
and delivered to its connection.  Stops at a queued submission that is not
a served POST (ACL2's fn-owner-queue-head-served-p) or when the owner takes
nothing.  The caller holds the owner mutex.  Returns the number shed."
  (let ((n 0) (gate (fnn-owner-service-gate service)))
    (loop
      (unless (fnn-owner-core 'fn-owner-queue-head-served-p) (return))
      (let* ((took (fnn-owner-take))
             (taken (fnn-owner-taken-word took)))
        (unless (eq taken :taken) (return))
        (let ((cid (fnn-nat (fnn-owner-taken-id took))))
          (fnn-owner-action 'fn-owner-shed-outcome cid
                            (sb-thread:with-mutex ((fnn-owner-gate-mutex gate))
                              (fnn-owner-gate-sched gate)))
          (fnn-owner-log)
          (fnn-owner-deliver service cid (fnn-owner-list-global 'fn-owner-output))
          (incf n))))
    n))

(defmacro fnn-owner-gated ((service class) &body body)
  "Run BODY under the owner mutex, admitted by the gate as CLASS."
  (let ((g (gensym "GATE")) (c (gensym "CLASS")) (w (gensym "WAITED"))
        (h (gensym "HELD")))
    `(let* ((,g (progn
                  ;; PRF-359's observation, off the mutex, before the
                  ;; quantum is admitted (fnn-owner-space-preobserve).
                  (fnn-owner-space-preobserve ,service)
                  (fnn-owner-service-gate ,service)))
            (,c ,class)
            (,w (fnn-owner-gate-enter ,g ,c))
            (,h (get-internal-real-time)))
       (unwind-protect
            (sb-thread:with-mutex ((fnn-owner-service-lock ,service))
              ;; adapter-retirement-2's opt-in hold measurement (FN_OWNER_MEASURE)
              (fnn-owner-measured (*fnn-owner-measure-label*) ,@body))
         (fnn-owner-gate-leave ,g ,c (fnn-ms-since ,h) ,w)))))

(defun fnn-owner-stop-service-locked (service exit-code &optional answering)
  "Fence while the owner mutex is held; the first terminal outcome wins.

ANSWERING is the socket of the connection whose own ACL2 reply reported the
stop, or nil.  It is not shut down here: its worker still owes that reply (the
uncertain `441 ... do not repost'), sends it after the mutex is released and
then closes the connection itself.  Setting STOPPING under this mutex is the
fence; no semantic action of any worker, that one included, can run after it
(fnn-owner-serialized refuses once STOPPING is set).

ANSWERING is also remembered in SPARING (PKT-562): a later stop -- the run's
cleanup stop, which passes no ANSWERING -- spares it too, so it cannot shut
the socket while that worker is still writing its reply."
  (fnn-payload-lifecycle-drain service)
  (fnn-with-roster (service)
    (unless (fnn-owner-service-stopping service)
      (setf (fnn-owner-service-stopping service) t
            (fnn-owner-service-exit-code service) exit-code)))
  (let ((sparing (sb-thread:with-mutex ((fnn-owner-service-commit-lock service))
                   (when answering
                     (pushnew answering (fnn-owner-service-sparing service)))
                   (copy-list (fnn-owner-service-sparing service)))))
  (let ((listener (fnn-owner-service-listener service)))
    (when listener
      ;; close(2) in another thread does not reliably wake a blocked accept(2)
      ;; on Linux.  Shutdown first so the accept loop observes a socket error,
      ;; sees STOPPING while this mutex is still held, and returns.
      (ignore-errors
        (sb-bsd-sockets:socket-shutdown listener :direction :io))))
  ;; Wake every client before command cleanup waits for its worker.  Shared
  ;; journals and Store state remain open until all workers have returned.
  ;; Only the worker that cached the socket fd may close it; shutdown wakes its
  ;; raw read without making that integer available for reuse underneath it.
  (dolist (socket (fnn-with-roster (service)
                    (copy-list (fnn-owner-service-clients service))))
    (unless (member socket sparing)
      (ignore-errors
        (sb-bsd-sockets:socket-shutdown socket :direction :io)))))
  ;; The committer thread wakes, finds the owner stopping and returns.
  (sb-thread:with-mutex ((fnn-owner-service-commit-lock service))
    (sb-thread:condition-broadcast (fnn-owner-service-commit-ready service)))
  ;; PRF-252: a sleeping consumer wait wakes, finds the owner stopping and
  ;; is answered (its next step is refused by fnn-owner-serialized).
  (fnn-owner-signal-commit service)
  ;; Hooks only signal external listeners/clients.  They run inside the same
  ;; first-terminal boundary and must be idempotent and nonblocking.
  (dolist (hook (fnn-owner-service-stop-hooks service))
    (ignore-errors (funcall hook service))))

(defun fnn-owner-stop-service (service exit-code)
  (fnn-owner-gated (service :control)
    (fnn-owner-stop-service-locked service exit-code)))

(defun fnn-owner-fence-service (service)
  "Stop this owner image after an ambiguous Store or FNFD observation."
  (fnn-owner-stop-service service +fnn-exit-uncertain+))

(defvar *fnn-owner-last-fault* nil
  "The first owner fault's text in this run (friend-path-2): `run' writes it
into the service log's stop line and its own result line, so `health',
`status' and the service manager's journal say why the node stopped.")

(defun fnn-owner-fault-service (service cid condition)
  "Contain an invalid core/store image, distinct from client refusal or EOF."
  (unless *fnn-owner-last-fault*
    (setq *fnn-owner-last-fault*
          (ignore-errors
           (format nil "owner core/store fault; process stopped: ~a" condition))))
  (fnn-owner-gated (service :control)
    (unless (fnn-owner-service-stopping service)
      (when cid
        (ignore-errors (fnn-owner-action 'fn-owner-fault cid)))
      (fnn-owner-stop-service-locked service +fnn-exit-fault+)))
  (fnn-err "owner core/store fault; process stopped: ~a" condition))

(defun fnn-owner-shared-action-locked (service cid thunk)
  "Run THUNK while the caller holds the owner mutex.

Only a known semantic refusal may leave this boundary without first fencing.
An indeterminate observation is exit 3.  A core/store fault, an unclassified
OS failure, or any other serious condition is exit 4.  The fence is installed
before the mutex can be released, so no queued client can mutate afterward."
  (handler-case
      (if (fnn-developer-selector "FN_NATIVE_FAULT_BACKTRACE")
          ;; Developer image only: the stack of a memory fault or any other
          ;; serious condition, printed where it was signalled (the handler
          ;; below has unwound it).
          (handler-bind ((serious-condition
                           (lambda (c)
                             (unless (typep c 'fnn-store-error)
                               (ignore-errors
                                (fnn-err "fault backtrace: ~a" c)
                                (sb-debug:print-backtrace :count 80 :stream *error-output*))))))
            (funcall thunk))
        (funcall thunk))
    (fnn-store-indeterminate (condition)
      (fnn-owner-stop-service-locked service +fnn-exit-uncertain+)
      (error condition))
    (fnn-store-fault (condition)
      (when cid (ignore-errors (fnn-owner-action 'fn-owner-fault cid)))
      (fnn-owner-stop-service-locked service +fnn-exit-fault+)
      (error condition))
    ;; FNN-STORE-ERROR is the existing known semantic-refusal class.  It has
    ;; made no ambiguous persistence observation and remains connection scoped.
    (fnn-store-error (condition) (error condition))
    ;; An OS or arbitrary failure inside a semantic/persistence action has no
    ;; safe connection-only attribution.  Preserve the shared state by stopping.
    ((or fnn-os-error serious-condition) (condition)
      (when cid (ignore-errors (fnn-owner-action 'fn-owner-fault cid)))
      (fnn-owner-stop-service-locked service +fnn-exit-fault+)
      (error condition))))

(defun fnn-owner-serialized (service cid thunk &optional (class :control))
  "Run one semantic action, fencing before its mutex can be released.

CLASS is the service class the gate admits this quantum as
(books/owner-scheduler.lisp *fn-osch-order*): :reader for a reader
connection's quanta (its open, steps, idle, close and release), :transit for
a peer connection's and for the feeds', the BP node's and its applications'
(fnn-owner-transit-serialized), :poster for a submission through the control
socket, and :control (the default) for the control socket's requests and the
maintenance steps (the checkpoint capture, the publication's done step, the
log reopen)."
  (fnn-owner-gated (service class)
    (when (fnn-owner-service-stopping service)
      (fnn-refuse "owner service is stopping"))
    (fnn-owner-shared-action-locked service cid thunk)))

(defun fnn-owner-transit-serialized (service cid thunk)
  "fnn-owner-serialized for a peer's quantum (the :transit class): the push
and pull feeds, the BP node and its applications."
  (fnn-owner-serialized service cid thunk :transit))

(defun fnn-owner-consume-connection-fault (service operation)
  "Consume the private injection under the roster mutex, without a core step."
  (fnn-with-roster (service)
    (when (and (not (fnn-owner-service-stopping service))
               (eq operation
                   (fnn-owner-service-connection-fault-operation service)))
      (setf (fnn-owner-service-connection-fault-operation service) nil)
      t)))

(defun fnn-owner-connection-call (service operation thunk)
  "Run bounded socket/handler work that cannot mutate owner or Store state.

This is the production emitter of FNN-OWNER-CONNECTION-FAULT.  Store/core
conditions and process resource exhaustion retain their global meaning.  Only
an unexpected failure inside this named non-semantic scope is attributable to
the current connection."
  (handler-case
      (progn
        ;; A plain ERROR exercises this same production classifier; tests do
        ;; not signal FNN-OWNER-CONNECTION-FAULT directly.
        (when (fnn-owner-consume-connection-fault service operation)
          (error "injected connection handler failure"))
        (funcall thunk))
    ((or fnn-store-indeterminate fnn-store-fault fnn-store-error
         storage-condition fnn-owner-connection-fault) (condition)
      (error condition))
    (serious-condition (condition)
      (error 'fnn-owner-connection-fault
             :operation operation :cause condition))))

(defun fnn-owner-abandon-connection (service cid condition)
  "Apply the ACL2 connection-fault transition unless a global stop won first."
  (let ((reply (fnn-make-octets 0)))
    (fnn-owner-gated (service :control)
      (unless (fnn-owner-service-stopping service)
        (fnn-owner-shared-action-locked
         service cid
         (lambda ()
           ;; A refusal from this exact transition is a core fault, never a
           ;; connection refusal.  Convert it inside the shared boundary.
           (handler-case
               (let ((result (fnn-owner-action 'fn-owner-fault cid)))
                 (unless (member result '(:faulted :unknown))
                   (fnn-fault "owner fault transition returned ~a" result))
                 (when (eq result :faulted)
                   (setq reply (fnn-owner-octets-global 'fn-owner-output))))
             (fnn-store-error (nested)
               (fnn-fault "owner fault transition refused: ~a" nested)))))))
    (fnn-err "owner connection-local fault; service continues: ~a" condition)
    reply))

(defun fnn-owner-transit-groups ()
  "The memberships fn-owner-transit-decide computed for a transit take."
  (let ((groups (fnn-global 'fn-owner-transit-groups)))
    (unless (and (listp groups) (every #'fnn-octet-list-p groups))
      (fnn-fault "owner returned malformed submission groups"))
    (mapcar #'fnn-octets groups)))

;;; SubmissionTaken (books/owner-results.lisp fn-ores-take-result): WORD
;;; (:idle, :taken, :taken-control, :taken-transit), the submission's ID,
;;; MSGID, stored OCTETS and GROUPS, checked once by the recognizer (the
;;; octet fields are octet lists, the groups lists of them); read here.
(defun fnn-owner-take ()
  (fnn-owner-result 'fn-ores-submission-taken-p 'fn-owner-take))

(defun fnn-owner-taken-word (taken)
  (fnn-core 'fn-ores-taken-word taken))

(defun fnn-owner-taken-id (taken)
  (fnn-core 'fn-ores-taken-id taken))

(defun fnn-owner-taken-msgid (taken)
  (fnn-octets (fnn-core 'fn-ores-taken-msgid taken)))

(defun fnn-owner-taken-octets (taken)
  (fnn-octets (fnn-core 'fn-ores-taken-octets taken)))

(defun fnn-owner-taken-groups (taken)
  (mapcar #'fnn-octets (fnn-core 'fn-ores-taken-groups taken)))

(defun fnn-owner-refresh-compression (log)
  "The log's compression threshold from the owner's live configuration
(fn-owner-compress-min-octets: the `compress-min-octets' row, 0 off), read
where the batch bounds are read, so a reconfiguration applies from the next
record on (lane compression-extents-2)."
  (when log
    (setf (fnn-log-lz-min log) (fnn-nat (fnn-owner-core 'fn-owner-compress-min-octets)))))

(defun fnn-owner-publish-prepared (service label)
  "Publish and finish the one ACL2-prepared owner transaction."
  (let* ((store (fnn-owner-service-store service))
         (record (fnn-core-arena-state 'fn-owner-pending-octets))
         ;; The file is named from the staged record's own sequence, ACL2's
         ;; (fn-sbud-pending-sequence); the host keeps no count of its own.
         (sequence (fnn-pending-sequence
                    (fnn-owner-core 'fn-owner-pending-sequence))))
    (unless (fnn-octet-list-p record)
      (fnn-fault "owner returned malformed ~a transaction" label))
    (when (fnn-store-logp store) (fnn-owner-refresh-compression (fnn-store-log store)))
    (handler-case
        (fnn-publish store sequence (fnn-octets record))
      (fnn-store-indeterminate (e) (error e))
      (fnn-store-fault (e)
        ; A structural/core fault is never a capacity refusal.  Preserve the
        ; fence and propagate it to the service fault boundary.
        (setf (fnn-store-fenced store) t)
        (error e))
      (fnn-store-error (e)
        (unless (fnn-store-fenced store)
          (setf (fnn-store-fenced store) t)
          (unless (eq (fnn-owner-action 'fn-owner-known-abort) :aborted)
            (fnn-indeterminate "owner rejected known ~a abort" label))
          ; A known pre-publication refusal consumed the reservation.  It is
          ; the only error branch that reopens the writer without recovery.
          (setf (fnn-store-fenced store) nil))
        (error e)))
    (setf (fnn-store-fenced store) t)
    (fnn-finish store)
    ;; PRF-252: the committed delta wakes the consumer waits.
    (fnn-owner-signal-commit service)
    :durable))

(defun fnn-owner-preflight-publication (service kind)
  "Ask the owner whether one more record of KIND fits the Store's budget.

ACL2 decides it from the profile it was handed at open and the count of the
Store it carries (host/owner-host.lisp fn-owner-publication-verdict); the
host holds no count and no bound of its own here.  An article is not asked
here: its budget is part of its prepare (fn-owner-prepare)."
  (declare (ignore service))
  (unless (eq (fnn-owner-core 'fn-owner-publication-verdict kind) :admissible)
    (fnn-refuse "Store transaction budget refuses ~(~a~) transaction" kind))
  :admissible)

;; The Store refusal kinds relayed to fn-own-outcome, each named by the ACL2
;; step that refused (books/owner.lisp fn-own-refusal-wordp).  fn-owner-prepare
;; answers :invalid for inputs outside its domain; its other non-prepared
;; answers are D25's :duplicate / :conflict (books/store-intern.lisp fn-store-existing-action,
;; keyed on the poster's source through the injection inverse, D25), :clock-unusable,
;; :unaffordable (the Store's transaction budget, fn-sbud-refusal-kind), or
;; :refused.
(defun fnn-owner-prepare-refusal-word (prepared)
  (case prepared
    ((:duplicate :conflict :clock-unusable :refused :unaffordable :memberships
      :article-numbers-exhausted)
     prepared)
    (:invalid :malformed)
    (t (fnn-fault "owner prepare returned ~a" prepared))))

(defmacro fnn-owner-attempt-handlers (store &body body)
  "Classify one Store attempt's conditions into its outcome word.

A pre-publication write failure whose reservation ACL2 consumed is the
:storage-failed refusal; another typed Store refusal is :refused.  An
indeterminate commit is :uncertain.  An OS error that no Store step
classified is never a refusal: it may lie after publication (campaign W2), so
the store is fenced and the outcome is :uncertain, which stops the service for
recovery.  Every :uncertain names its reason once on the owner's stderr: the
reply to the peer or poster carries no reason, and the recovery stop that
follows is justified only by this line."
  `(handler-case (progn ,@body)
     (fnn-store-indeterminate (e)
       (fnn-err "Store outcome uncertain; the store needs recovery: ~a" e)
       :uncertain)
     (fnn-store-fault (e)
       (setf (fnn-store-fenced ,store) t)
       (error e))
     (fnn-store-io-refusal () :storage-failed)
     (fnn-store-error () :refused)
     (fnn-os-error (e)
       (setf (fnn-store-fenced ,store) t)
       (fnn-err "unclassified OS error in a Store attempt; outcome uncertain: ~a" e)
       :uncertain)))

(defun fnn-owner-attempt (service msgid payload groups evidence)
  "One Store attempt under the owner callbacks; return its observed word."
  (let ((store (fnn-owner-service-store service)))
    (fnn-owner-attempt-handlers store
        (let ((codes (fnn-owner-core
                      'fn-owner-group-codes
                      (mapcar #'fnn-octet-list groups)))
              (charge (fnn-charge (length payload))))
          (when (or (keywordp codes) (not (listp codes))
                    (/= (length codes) (length groups)))
            (fnn-refuse "unknown or duplicate configured group"))
          (let ((boundary (fnn-owner-core 'fn-owner-post-boundary (fnn-octet-list msgid)
                                          (length payload) (length codes) charge)))
            ;; Preserve ACL2's named placement refusal before buffer fill,
            ;; identity allocation or prepare.  The generic condition
            ;; handler would otherwise erase it into :refused.
            (when (eq boundary :mpx-saturated)
              (return-from fnn-owner-attempt boundary))
            (fnn-validate-post-boundary boundary))
          ;; The payload goes to the core in the octet buffer
          ;; (books/octets-stobj.lisp): filled once here from the byte
          ;; vector, read in place by the existing-article test and the
          ;; prepare (host/owner-host.lisp fn-owner-existing-action-buffer,
          ;; fn-owner-prepare-buffer), and the subject identity is digested
          ;; from it in place (fnn-metadata-buffer, fnn-subject-id-buffer;
          ;; books/subject-id-buffer.lisp).  Nothing between the fill and the
          ;; prepare writes the buffer; all of it runs under the service mutex.
          (fnn-octets-fill payload)
          (case (fnn-owner-buffer-arena-action 'fn-owner-existing-action-buffer
                                         (fnn-octet-list msgid) codes)
            (:duplicate (return-from fnn-owner-attempt :duplicate))
            (:conflict (return-from fnn-owner-attempt :conflict)))
          (let ((*fnn-observe-callback* #'fnn-owner-observe)
                (*fnn-finish-callback* #'fnn-owner-finish-submission))
            (fnn-advance-frontier store
                                  (fnn-nat (fnn-owner-core 'fn-owner-next-txid)))
            (multiple-value-bind (obligation subject ignored)
                (fnn-metadata-buffer msgid)
              (declare (ignore ignored))
              (let ((prepared
                      (fnn-owner-buffer-arena-action
                       'fn-owner-prepare-buffer (fnn-octet-list msgid) codes
                       (fnn-octet-list obligation) (fnn-octet-list subject)
                       (fnn-octet-list evidence) charge)))
                ;; The prepare reads the arena only; on acceptance it answers
                ;; :seal-buffer and the host seals the buffer's payload
                ;; (host/owner-host.lisp fn-owner-prepare-buffer).
                (when (eq prepared :seal-buffer)
                  (fnn-seal-live-buffer)
                  ;; Step 8: the catalog prepares the store's row, which names
                  ;; the handle just sealed (one seal per POST).
                  (setq prepared (fnn-owner-action 'fn-owner-cat-prepare-sealed)))
                (unless (eq prepared :prepared)
                  (setf (fnn-store-fenced store) t)
                  (unless (eq (fnn-owner-action 'fn-owner-refuse-reservation)
                              :refused)
                    (fnn-indeterminate "owner could not consume refused reservation"))
                  (setf (fnn-store-fenced store) nil)
                  (return-from fnn-owner-attempt
                    (fnn-owner-prepare-refusal-word prepared)))))
            (fnn-owner-publish-prepared service "article"))))))

;;; Which ingress check refused the transit attempt in flight, for the one
;;; service-log line fn-olog-transit-line renders.  Where ACL2 names the
;;; refusal (fn-pa-carrier-form, fn-pa-current-plan: `(:refused REASON)')
;;; its keyword is relayed unchanged; the other names say which host
;;; boundary check answered :refused.  It is a log detail, never an input
;;; to any decision.  Bound per submission by fnn-owner-drain-one.
(defvar *fnn-owner-transit-detail* nil)

;;; PKT-473 (PRF-184): the accepted arm's verdict (ACL2's
;;; fn-pcb-transit-verdict through fn-owner-transit-verdict), read before
;;; the kind-4 commit, for the same log line.  A log field only.  Bound per
;;; submission with the detail.
(defvar *fnn-owner-transit-verdict* nil)

;;; (PAYLOAD . OCTET-LIST) for the transit attempt in flight: its payload
;;; vector converted once (bound by fnn-owner-attempt-transit).  ACL2 never
;;; mutates an argument, so its calls share the one list; the parse carry
;;; (books/owner-parse-carried.lisp) compares it with the take's octets.
(defvar *fnn-owner-payload-list* nil)

(defun fnn-owner-payload-octets (payload)
  (if (and (consp *fnn-owner-payload-list*)
           (eq (car *fnn-owner-payload-list*) payload))
      (cdr *fnn-owner-payload-list*)
    (fnn-octet-list payload)))

(defun fnn-owner-note-transit-verdict (payload nntp-transit-p ed ml)
  (setq *fnn-owner-transit-verdict*
        (fnn-owner-core 'fn-owner-transit-verdict (fnn-owner-payload-octets payload)
                        (and nntp-transit-p t) ed ml)))

(defun fnn-owner-transit-refused (detail)
  (setq *fnn-owner-transit-detail*
        (if (and (consp detail) (eq (first detail) :refused)
                 (or (keywordp (second detail)) (consp (second detail))))
            (second detail)
          detail))
  :refused)

;;; PRF-099: on NNTP transit, a refusal of a present carrier is named by
;;; ACL2's class (books/peer-carriage.lisp fn-pcb-refusal-class through
;;; fn-owner-transit-refusal-class): no-local-binding, unsupported-profile,
;;; signature-failed or malformed.  ED and ML are the primitive outcomes
;;; when they were observed.  Other ingresses keep ACL2's plan reason.
(defun fnn-owner-transit-class (plan payload nntp-transit-p ed ml)
  (if (not nntp-transit-p) plan
    ;; PKT-433 (d): ACL2's (CLASS VERDICT); the log prints both.
    (let ((detail (fnn-owner-core 'fn-owner-transit-refusal-class
                                  (fnn-owner-payload-octets payload) t ed ml)))
      (if (and (consp detail) (keywordp (first detail)))
          (list :refused detail)
        plan))))

(defun fnn-owner-attempt-transit (service msgid payload groups evidence
                                  &optional nntp-transit-p)
  "One ingress decision for both NNTP and BP transit under the caller's
durable intent. ACL2 distinguishes carrier absence from present-invalid,
selects the B-local current enrollment, and constructs the exact kind-4
event. A carrier-absent article keeps the established legacy Store path.
NNTP-TRANSIT-P is true only for NNTP transit: ACL2 then also consults the
delivering boundary's carried-source list (D23) and, on its :carried arm,
builds the carried kind-4 event, which names no enrollment and claims no
verification.

First, for every ingress, ACL2's filing step (C1, fn-pa-filing-plan through
fn-owner-control-filing): a control article's groups become exactly its
control.<verb> filing group, or the attempt is refused with the plan's
reason before any Store call.  An ordinary article's groups are unchanged."
  ;; The payload's octet list, converted once for the ACL2 calls below
  ;; (fnn-owner-payload-octets): each call used to convert the vector
  ;; again, 16 bytes a cons per octet.
  (let ((*fnn-owner-payload-list* (cons payload (fnn-octet-list payload))))
  (let ((filing (fnn-owner-core 'fn-owner-control-filing
                                (fnn-owner-payload-octets payload)
                                (mapcar #'fnn-octet-list groups))))
    (unless (and (consp filing)
                 (member (first filing) '(:file :refused))
                 (consp (rest filing)))
      (fnn-fault "owner returned malformed control filing ~a" filing))
    (when (eq (first filing) :refused)
      (return-from fnn-owner-attempt-transit
        (fnn-owner-transit-refused filing)))
    (unless (and (listp (second filing))
                 (every #'fnn-octet-list-p (second filing)))
      (fnn-fault "owner returned malformed filed groups"))
    (setq groups (mapcar #'fnn-octets (second filing))))
  (let ((form (fnn-owner-core 'fn-owner-peer-carrier-form
                              (fnn-owner-payload-octets payload))))
    (cond
      ((eq form :absent)
       (fnn-owner-note-transit-verdict payload nntp-transit-p nil nil)
       (fnn-owner-attempt service msgid payload groups evidence))
      ((not (and (consp form) (eq (first form) :ok)))
       (fnn-owner-transit-refused
        (fnn-owner-transit-class form payload nntp-transit-p nil nil)))
      (t
       (fnn-owner-attempt-handlers (fnn-owner-service-store service)
           (let* ((store (fnn-owner-service-store service))
                  (codes (fnn-owner-core
                          'fn-owner-group-codes
                          (mapcar #'fnn-octet-list groups)))
                  (charge (fnn-charge (length payload))))
             (when (or (keywordp codes) (not (listp codes))
                       (/= (length codes) (length groups)))
               (return-from fnn-owner-attempt-transit
                 (fnn-owner-transit-refused :groups)))
             (let ((boundary (fnn-owner-core 'fn-owner-post-boundary (fnn-octet-list msgid)
                                             (length payload) (length codes) charge)))
               (when (eq boundary :mpx-saturated)
                 (return-from fnn-owner-attempt-transit boundary))
               (fnn-validate-post-boundary boundary))
             (case (fnn-owner-arena-action 'fn-owner-existing-action
                                     (fnn-octet-list msgid)
                                     (fnn-owner-payload-octets payload) codes)
               (:duplicate (return-from fnn-owner-attempt-transit :duplicate))
               (:conflict (return-from fnn-owner-attempt-transit
                            (fnn-owner-transit-refused :conflict))))
             (let ((plan (fnn-owner-core 'fn-owner-peer-carrier-plan
                                         (fnn-owner-payload-octets payload)
                                         (and nntp-transit-p t))))
               (when (and (consp plan) (eq (first plan) :carried))
                 (unless (eq (fnn-owner-advance-clock) :observed)
                   (return-from fnn-owner-attempt-transit :clock-unusable))
                 (multiple-value-bind (obligation subject ignored)
                     (fnn-metadata msgid payload)
                   (declare (ignore ignored))
                   (let* ((coordinates
                            (fnn-owner-core 'fn-owner-next-store-coordinates))
                          (event
                            (fnn-owner-core
                             'fn-owner-peer-carried-relay-event coordinates
                             (fnn-octet-list msgid) (fnn-owner-payload-octets payload)
                             codes (fnn-octet-list obligation)
                             (fnn-octet-list subject) (fnn-octet-list evidence)
                             charge)))
                     ;; PRF-099: the boundary's opaque-carriage budget,
                     ;; decided inside the event constructor over the
                     ;; owner-carried usage; a refusal names its bound.
                     (when (and (consp event) (eq (first event) :refused))
                       (return-from fnn-owner-attempt-transit
                         (fnn-owner-transit-refused event)))
                     (let ((boundary (fnn-owner-core
                                      'fn-owner-signed-event-boundary event)))
                       (unless (eq boundary :ok)
                         (return-from fnn-owner-attempt-transit
                           (fnn-owner-transit-refused boundary))))
                     ;; A log detail only (fn-olog-transit-line): the Store
                     ;; record's token, not an input to any decision.
                     (setq *fnn-owner-transit-detail* :carried)
                     (fnn-owner-note-transit-verdict payload nntp-transit-p
                                                     nil nil)
                     (return-from fnn-owner-attempt-transit
                       (fnn-owner-statement-committed
                        service event
                        (fnn-owner-identity-commit service event))))))
               ;; PRF-098: the :revoked arm (NNTP transit only) takes the
               ;; same two primitive observations as :ok, over the carrier's
               ;; keys, and commits fn-pa-revoked-event's composite.
               (unless (and (consp plan) (member (first plan) '(:ok :revoked)))
                 (return-from fnn-owner-attempt-transit
                   (fnn-owner-transit-refused
                    (fnn-owner-transit-class plan payload nntp-transit-p
                                             nil nil))))
             (unless (eq (fnn-owner-advance-clock) :observed)
               (return-from fnn-owner-attempt-transit :clock-unusable))
             (let* ((source (second plan))
                    (principal (third plan))
                    (keys (fourth plan))
                    (signatures (fifth plan))
                    (preimage
                      (fnn-core 'fn-hsig-host-preimage
                                principal keys source))
                    (observations
                      (and preimage
                           (fnn-hsig-observe-raw
                            (cdr (first keys)) (cdr (second keys))
                            preimage signatures)))
                    (ml-observation (second observations))
                    (observed-ml-key
                      (and (consp ml-observation)
                           (second ml-observation))))
               (unless (and observed-ml-key
                            (eq (first observations) :verified)
                            (eq (first ml-observation) :verified))
                 (return-from fnn-owner-attempt-transit
                   (fnn-owner-transit-refused
                    (fnn-owner-transit-class
                     (list :refused :signature) payload nntp-transit-p
                     (first observations)
                     (and observed-ml-key (first ml-observation))))))
               (multiple-value-bind (obligation subject ignored)
                   (fnn-metadata msgid payload)
                 (declare (ignore ignored))
                 (let* ((coordinates
                          (fnn-owner-core 'fn-owner-next-store-coordinates))
                        (event
                          (fnn-owner-core
                           (if (eq (first plan) :revoked)
                               'fn-owner-peer-revoked-event
                             'fn-owner-peer-carried-event)
                           coordinates
                           (fnn-octet-list msgid) (fnn-owner-payload-octets payload)
                           codes (fnn-octet-list obligation)
                           (fnn-octet-list subject) (fnn-octet-list evidence)
                           charge (coerce observed-ml-key 'list)
                           (first observations) (first ml-observation))))
                   ;; ACL2 names the refusal: :event when no composite
                   ;; was formed, :signed-record past the profile's R.
                   (let ((boundary (fnn-owner-core
                                    'fn-owner-signed-event-boundary event)))
                     (unless (eq boundary :ok)
                       (return-from fnn-owner-attempt-transit
                         (fnn-owner-transit-refused boundary))))
                   (when (eq (first plan) :revoked)
                     ;; A log detail only: the Store record's token.
                     (setq *fnn-owner-transit-detail* :revoked))
                   (fnn-owner-note-transit-verdict payload nntp-transit-p
                                                   (first observations)
                                                   (first ml-observation))
                   (fnn-owner-statement-committed
                    service event
                    (fnn-owner-identity-commit service event)))))))))))))

;;; PRF-098: the key-statement executor, run by the owner right after it
;;; committed a kind-4 composite (books/key-statements.lisp, through
;;; host/owner-host.lisp), whatever its verdict: ACL2 declines every
;;; composite whose stored verdict is not :verified
;;; (fn-ks-carried-or-revoked-statement-never-changes-a-keyring).  ACL2 names
;;; the one primitive observation (the proof of possession's D09 subject) or
;;; none, decides from the stored verdict, the live authorities rows and the
;;; Store's snapshots, and builds the kind-3 event at its own next
;;; generation; the host observes, commits and logs.  A composite that is no
;;; statement decides nothing.
;;;
;;; The answer is the key change's own outcome: :committed, :refused (the
;;; Store refused the kind-3 event; the statement article stays accepted),
;;; or nil (no change was attempted).  An uncertain kind-3 commit is not
;;; answered here: its condition propagates like any uncertain Store
;;; outcome and the open's recovery (fnn-owner-key-statement-recover)
;;; decides the statement again.
(defun fnn-owner-key-statement (service event &optional at-open)
  (let* ((request (fnn-owner-core 'fn-owner-key-statement-request event))
         (preimage (and request
                        (fnn-core 'fn-hsig-host-preimage (first request)
                                  (second request) (third request))))
         (observations (and preimage
                            (fnn-hsig-observe-raw
                             (cdr (first (second request)))
                             (cdr (second (second request)))
                             preimage (fourth request))))
         (ml-observation (second observations))
         (observed-ml-key (and (consp ml-observation) (second ml-observation)
                               (coerce (second ml-observation) 'list)))
         (ed (first observations))
         (ml (and (consp ml-observation) (first ml-observation)))
         (plan (fnn-owner-core 'fn-owner-key-statement-plan event
                               observed-ml-key ed ml (and at-open t))))
    (when plan
      (let* ((acting (and (consp plan) (member (first plan) '(:enroll :revoke))))
             (coordinates (and acting
                               (fnn-owner-core 'fn-owner-next-store-coordinates)))
             (kind3 (and acting
                         (fnn-owner-core 'fn-owner-key-statement-event event
                                         observed-ml-key ed ml coordinates
                                         (and at-open t))))
             (outcome
               (and kind3
                    (handler-case
                        (progn (fnn-owner-identity-commit service kind3)
                               :committed)
                      (fnn-store-indeterminate (e) (error e))
                      (fnn-store-fault (e) (error e))
                      (fnn-store-error () :refused)))))
        (fnn-owner-line-after-barrier
         (fnn-owner-core 'fn-owner-key-statement-log-line plan
                         outcome (and at-open t)))
        outcome))))

;;; The cut between the statement's commit and its key change's
;;; (books/key-statements.lisp fn-ks-cut).  A developer image started with
;;; FN_NATIVE_KEY_STATEMENT_FAULT=statement-committed:kill dies here, after a
;;; statement's kind-4 composite is durable (fnn-owner-statement-barrier
;;; returned) and before the executor runs; production has no injection
;;; branch.  tests/campaign/native_cuts.py STATEMENT_CUTS names it.
(defun fnn-owner-key-statement-cut ()
  (let ((raw (fnn-developer-selector "FN_NATIVE_KEY_STATEMENT_FAULT")))
    (when raw
      (unless (string= raw "statement-committed:kill")
        (fnn-fault "invalid FN_NATIVE_KEY_STATEMENT_FAULT (expected statement-committed:kill)"))
      (sb-posix:kill (sb-posix:getpid) sb-unix:sigkill)
      (fnn-fault "test SIGKILL did not terminate the process"))))

;;; A line that names a record committed in this step: inside the owner's
;;; batch quantum it waits for the batch's COMPLETE, after the barrier that
;;; persists the record (as fnn-owner-log's lines do); outside one the
;;; record's own barrier has returned (fnn-log-publish, a batch of one).
(defun fnn-owner-line-after-barrier (line)
  (unless (fnn-octet-list-p line)
    (fnn-fault "owner returned a malformed log line"))
  (if *fnn-owner-deferred*
      (push (cons :log line) (cdr *fnn-owner-deferred*))
    (fnn-log-line line)))

;;; Lane ack-before-barrier: the statement's own barrier.  Inside the owner's
;;; batch quantum (*fnn-log-batch*, fnn-owner-commit-start-locked) the
;;; statement's record is only in the log's open batch when its commit
;;; returns; the open batch -- the statement and every member drained before
;;; it -- is appended and fenced here (fnn-log-commit-open-batch, cuts
;;; log-written and log-fenced; behind a batch in flight it first awaits that
;;; batch's barrier), so the cut and the executor that follow run with the
;;; statement durable (books/owner-ack-after-barrier.lisp
;;; fn-oab-quantum-reports-after-its-barrier).  Those members' replies still
;;; leave only in their batch's COMPLETE.  Outside a quantum the commit was a
;;; batch of one, fenced before fnn-log-publish returned: nothing is open.
(defun fnn-owner-statement-barrier (service)
  (let* ((store (fnn-owner-service-store service))
         (log (fnn-store-log store)))
    (cond (*fnn-log-batch* (fnn-log-commit-open-batch store))
          ((and log (plusp (fnn-log-count log)))
           (fnn-fault "a statement committed outside a batch left its record unfenced")))))

;;; WORD is the kind-4 commit's outcome.  A durable composite that carries a
;;; key statement (ACL2's fn-oab-fence-before-change, through
;;; host/owner-host.lisp fn-owner-statement-fence) is fenced first, then the
;;; cut, then the executor; a refused key change leaves WORD (the article is
;;; accepted) and names the refusal in the transit detail, so the reported
;;; outcome names both.  Any other composite has no executor
;;; (fn-oab-plan-only-after-the-fence: the plan is nil).
(defun fnn-owner-statement-committed (service event word)
  (when (eq word :durable)
    (let ((fence (fnn-owner-core 'fn-owner-statement-fence event)))
      (unless (booleanp fence)
        (fnn-fault "owner returned a malformed statement fence ~a" fence))
      (when fence
        (fnn-owner-statement-barrier service)
        (fnn-owner-key-statement-cut)
        (when (eq (fnn-owner-key-statement service event) :refused)
          (setq *fnn-owner-transit-detail* :key-change-refused)))))
  word)

;;; The open's recovery (books/key-statements.lisp fn-ks-recover-recorded):
;;; the newest record the open read, when it is a statement, is decided
;;; under the grants in force at its own txid (packet 7; no policy switch),
;;; so a change the cut lost is made exactly as the acceptance would have
;;; made it whatever configuration was published since (PRF-140), a change
;;; already made is the newest record (no statement), and a declined
;;; statement declines again whatever grants were added since.
(defun fnn-owner-key-statement-recover (service records)
  (when records
    (let ((pending (fnn-owner-core 'fn-owner-key-statement-pending
                                   (fnn-octet-list (car (last records))))))
      (when pending
        (fnn-owner-key-statement service pending t)))))

;;; The served POST's attempt, and the bound local submission's.  The one
;;; ingress decision transit uses (fnn-owner-attempt-transit: ACL2's
;;; fn-pa-carrier-form and fn-pa-current-plan over these octets and this
;;; Store's enrollment, the primitive observation, fn-pa-authorized-event,
;;; the kind-4 identity commit) with the poster's outcome word chosen by
;;; ACL2 (fn-pa-served-word): a present carrier the plan refused carries the
;;; plan's reason to its own 441 line, and a carrier-absent article is the
;;; unsigned arm, fnn-owner-attempt, with its word unchanged.
;;;
;;; First, the posting policy's login gate (books/login-binding.lisp
;;; fn-lb-owner-gate through host/owner-host.lisp fn-owner-login-gate): under
;;; `posting-policy bound-logins' a bound login's article that is unsigned, or
;;; signed by another principal, is refused with the gate's reason
;;; (:login-unsigned, :login-not-bound) before any Store call; every other
;;; verdict continues into the unchanged attempt.  The verdict's log line
;;; names the login.
(defun fnn-owner-attempt-served (service msgid payload groups evidence)
  (setq *fnn-owner-transit-detail* nil
        *fnn-owner-transit-verdict* nil)
  (let ((gate (fnn-owner-core 'fn-owner-login-gate (fnn-octet-list payload))))
    (unless (and (consp gate) (member (first gate) '(:pass :refused)))
      (fnn-fault "owner returned malformed login gate ~a" gate))
    (fnn-owner-log 'fn-owner-login-log-line t)
    (let ((word (if (eq (first gate) :refused)
                    (fnn-owner-transit-refused gate)
                  (fnn-owner-attempt-transit service msgid payload groups
                                             evidence))))
      (fnn-owner-core 'fn-owner-served-post-word word
                      *fnn-owner-transit-detail*))))

(defun fnn-owner-retention-commit (service event)
  "Publish one ACL2-authored retention event through the normal Store path."
  (unless (and (listp event) (= (length event) 5)
               (member (first event) '(:undertake :release))
               (stringp (second event)) (stringp (third event))
               (stringp (fourth event)) (integerp (fifth event)))
    (fnn-fault "ACL2 returned malformed Store retention event"))
  (let ((store (fnn-owner-service-store service)))
    (fnn-owner-preflight-publication service (first event))
    (let ((*fnn-observe-callback* #'fnn-owner-observe)
          (*fnn-finish-callback* #'fnn-owner-finish))
      (fnn-advance-frontier store
                            (fnn-nat (fnn-owner-core 'fn-owner-next-txid)))
      (let ((prepared
             (fnn-owner-action
              'fn-owner-prepare-retention (first event)
              (fnn-octet-list (fnn-string-octets (second event)))
              (fnn-octet-list (fnn-string-octets (third event)))
              (fnn-octet-list (fnn-string-octets (fourth event)))
              (fifth event))))
        (unless (eq prepared :prepared)
          (unless (eq (fnn-owner-action 'fn-owner-refuse-reservation) :refused)
            (fnn-indeterminate "owner could not consume refused retention reservation"))
          (fnn-refuse "canonical Store refused retention event")))
      (fnn-owner-publish-prepared service "retention"))))

(defun fnn-owner-identity-commit (service event)
  "Publish one ACL2-constructed keyring snapshot or atomic acceptance event."
  (let ((store (fnn-owner-service-store service)))
    ;; ACL2's verdict over the event itself (host/owner-host.lisp
    ;; fn-owner-identity-publication-verdict): a composite is charged its
    ;; figure with its article's memberships.
    (unless (eq (fnn-owner-core 'fn-owner-identity-publication-verdict event)
                :admissible)
      (fnn-refuse "Store transaction budget refuses ~(~a~) transaction"
                  (fnn-core 'fn-wire-event-kind event)))
    (let ((*fnn-observe-callback* #'fnn-owner-observe)
          (*fnn-finish-callback* #'fnn-owner-finish))
      (fnn-advance-frontier store
                            (fnn-nat (fnn-owner-core 'fn-owner-next-txid)))
      ;; The entry stages the interned row and reads the arena only; when
      ;; the Store took a composite it names the article's payload and the
      ;; host seals exactly those octets (host/owner-host.lisp
      ;; fn-owner-prepare-identity, books/owner-identity-intern.lisp).
      (let ((prepared (fnn-core-arena-state 'fn-owner-prepare-identity event)))
        (when (and (consp prepared) (eq (first prepared) :seal))
          (unless (and (consp (rest prepared)) (null (cddr prepared))
                       (fnn-octet-list-p (second prepared)))
            (fnn-fault "ACL2 returned a malformed identity seal"))
          (fnn-seal-octets (second prepared))
          ;; The catalog's row for the article the event carries, after the
          ;; one seal (fn-owner-cat-prepare-sealed), completed by
          ;; fn-owner-finish-identity at the durable finish.
          (unless (eq (fnn-owner-action 'fn-owner-cat-prepare-sealed) :prepared)
            (fnn-fault "owner did not prepare the catalog row of the identity event"))
          (setq *fnn-finish-callback* #'fnn-owner-finish-identity)
          (setq prepared :prepared))
        (unless (keywordp prepared)
          (fnn-fault "owner returned non-action from fn-owner-prepare-identity"))
        (unless (eq prepared :prepared)
          (unless (eq (fnn-owner-action 'fn-owner-refuse-reservation) :refused)
            (fnn-indeterminate "owner could not consume refused identity reservation"))
          ;; The word names the refusal (:refused, or RFC 3977 section 6's
          ;; :article-numbers-exhausted, books/owner-prepare-served.lisp
          ;; fn-psrv-identity-refusal-kind).
          (fnn-refuse "canonical Store refused identity event (~(~a~))" prepared)))
      (fnn-owner-publish-prepared service "identity"))))

(defun fnn-owner-consumer-commit (service event)
  "Publish one ACL2-constructed consumer event through the durable Store gate."
  (let ((store (fnn-owner-service-store service)))
    (fnn-owner-preflight-publication service :consumer)
    (let ((*fnn-observe-callback* #'fnn-owner-observe)
          (*fnn-finish-callback* #'fnn-owner-finish))
      (fnn-advance-frontier store
                            (fnn-nat (fnn-owner-core 'fn-owner-next-txid)))
      (let ((prepared (fnn-owner-action 'fn-owner-prepare-consumer event)))
        (unless (eq prepared :prepared)
          (unless (eq (fnn-owner-action 'fn-owner-refuse-reservation) :refused)
            (fnn-indeterminate "owner could not consume refused consumer reservation"))
          (fnn-refuse "canonical Store refused consumer event")))
      (fnn-owner-publish-prepared service "consumer"))))

(defun fnn-owner-topic-commit (service event)
  "Publish one ACL2-constructed topic event through the Store durability gate."
  (let ((store (fnn-owner-service-store service)))
    (fnn-owner-preflight-publication service
                                     (fnn-core 'fn-store-event-kind event))
    (let ((*fnn-observe-callback* #'fnn-owner-observe)
          (*fnn-finish-callback* #'fnn-owner-finish))
      (fnn-advance-frontier store
                            (fnn-nat (fnn-owner-core 'fn-owner-next-txid)))
      (let ((prepared (fnn-owner-action 'fn-owner-prepare-topic event)))
        (unless (eq prepared :prepared)
          (unless (eq (fnn-owner-action 'fn-owner-refuse-reservation) :refused)
            (fnn-indeterminate "owner could not consume refused topic reservation"))
          (fnn-refuse "canonical Store refused topic event")))
      (fnn-owner-publish-prepared service "topic"))))

(defun fnn-owner-topic-local-serialized
    (service operation source-sequence quota observed-uid)
  "Use the OS-observed UID only as input to ACL2's installed-ID decision."
  (fnn-owner-serialized
   service nil
   (lambda ()
     (let* ((entropy-id
              (and (eq operation :install)
                   (fnn-csprng-octets 32 "topic installed ID")))
            (proposal
              (fnn-owner-core 'fn-owner-topic-propose
                              operation source-sequence observed-uid
                              entropy-id quota)))
       (cond
         ((and (eq operation :report)
               (consp proposal) (eq (first proposal) :replayed-historical)
               (consp (cdr proposal)))
          :replayed-historical)
         ((not (and (consp proposal) (eq (first proposal) :ok)
                    (consp (cdr proposal))))
          :refused)
         (t
          (unless (eq (fnn-owner-topic-commit service (second proposal))
                      :durable)
            (fnn-fault "topic publication lacked durable completion"))
          :accepted))))))

(defun fnn-owner-consumer-entropy-observation ()
  "Observe 64 OS entropy octets; ACL2 validates and owns the identities."
  (let ((bytes (make-array 64 :element-type '(unsigned-byte 8))))
    (handler-case
        (with-open-file (input "/dev/urandom" :direction :input
                               :element-type '(unsigned-byte 8))
          (unless (= (read-sequence bytes input) 64)
            (fnn-fault "short consumer identity entropy observation")))
      (error (condition)
        (fnn-fault "consumer identity entropy unavailable: ~a" condition)))
    (values (loop for i below 32 collect (aref bytes i))
            (loop for i from 32 below 64 collect (aref bytes i)))))

(defun fnn-owner-consumer-local-serialized (service operation first second)
  "Run one 0600 local-control consumer declaration under the owner mutex.

The ACL2 owner wrapper pins the local principal, query/view profile, epoch,
cursor scope and Store coordinates.  Raw Lisp transports only decoded octets
and publishes the exact ACL2 event.  A lost reply remains uncertain to the
client, which can issue POSITION after reconnecting."
  (fnn-owner-serialized
   service nil
   (lambda ()
     (let* ((proposal
              (case operation
                (:bootstrap
                 (multiple-value-bind (history incarnation)
                     (fnn-owner-consumer-entropy-observation)
                   (fnn-owner-core 'fn-owner-consumer-local-bootstrap
                                   history incarnation)))
                (:register
                 (fnn-owner-core 'fn-owner-consumer-local-register first second))
                (:ack
                 (fnn-owner-core 'fn-owner-consumer-local-ack first))
                (:position
                 (fnn-owner-core 'fn-owner-consumer-local-position first))
                (:status
                 (fnn-owner-core 'fn-owner-consumer-local-status first))
                (:poll
                 (fnn-core-arena-state 'fn-owner-consumer-local-poll first))
                ;; PRF-234: a consumer bound to an account; SECOND is the
                ;; account's password, which only ACL2 compares.
                (:bound-poll
                 (fnn-core-arena-state 'fn-owner-consumer-local-bound-poll
                                       first second))
                (:bound-ack
                 (fnn-owner-core 'fn-owner-consumer-local-bound-ack
                                 first second))
                (:unregister
                 (fnn-owner-core 'fn-owner-consumer-local-unregister first))
                (otherwise '(:refused :operation))))
            (kind (and (consp proposal) (first proposal))))
       (case kind
         (:refused
          ;; PKT-709: the refusal carries ACL2's reason, (:reason REPLY
          ;; REASON); a reasoned request (kind 22) gets it on the wire
          ;; (host/native/control.lisp), a plain one the reply alone.
          (list
           :reason
          (case operation
            (:status (list :consumer-status-reply :refused nil nil nil))
            ;; A refused poll answers on the poll reply kind
            ;; (fn-ncl-poll-reply-encode :refused), as the non-owner refusal
            ;; does.  PRF-234: before, a refused plain poll answered a kind-5
            ;; frame that the poll client cannot decode, so every refused
            ;; poll (an unknown consumer included) printed `uncertain' (exit
            ;; 3); a refusal is now `refused' (exit 1).
            ((:poll :bound-poll) (list :consumer-poll-reply :refused nil nil))
            (otherwise (list :consumer-reply :refused nil)))
           (second proposal)))
         (:position
          (let ((token (second proposal)))
            (unless (fnn-octet-list-p token)
              (fnn-fault "ACL2 returned malformed consumer position"))
            (list :consumer-reply :accepted token)))
         (:poll
          (let ((token (second proposal)) (report (third proposal)))
            (unless (and (fnn-octet-list-p token)
                         (fnn-octet-list-p report))
              (fnn-fault "ACL2 returned malformed consumer poll"))
            (list :consumer-poll-reply :accepted token report)))
         (:status
          (unless (and (= (length proposal) 4)
                       (every (lambda (value)
                                (and (integerp value) (not (minusp value))))
                              (rest proposal)))
            (fnn-fault "ACL2 returned malformed consumer status"))
          (list :consumer-status-reply :accepted
                (second proposal) (third proposal) (fourth proposal)))
         (:no-op
          (let ((token (fnn-core 'fn-cp-cursor-encode (second proposal))))
            (unless (fnn-octet-list-p token)
              (fnn-fault "ACL2 returned malformed idempotent cursor"))
            (list :consumer-reply :accepted token)))
         (:write
          (unless (eq (fnn-owner-consumer-commit service (second proposal))
                      :durable)
            (fnn-fault "consumer publication lacked durable completion"))
          (let ((token
                  (case operation
                    (:register
                     (let ((position
                             (fnn-owner-core 'fn-owner-consumer-local-position
                                             first)))
                       (unless (and (consp position)
                                    (eq (first position) :position))
                         (fnn-fault "durable registration has no position"))
                       (second position)))
                    ((:ack :bound-ack) first)
                    (:bootstrap nil)
                    (:unregister nil)
                    (otherwise
                     (fnn-fault "unexpected consumer write operation")))))
            (unless (fnn-octet-list-p token)
              (fnn-fault "ACL2 returned malformed durable cursor"))
            (list :consumer-reply :accepted token)))
         (otherwise (fnn-fault "ACL2 returned malformed consumer decision")))))))

(defun fnn-owner-consumer-poll-answer (answer)
  "Carry an ACL2 poll answer, (:poll TOKEN REPORT) or a refusal, as the poll reply."
  (case (and (consp answer) (first answer))
    (:poll
     (let ((token (second answer)) (report (third answer)))
       (unless (and (fnn-octet-list-p token) (fnn-octet-list-p report))
         (fnn-fault "ACL2 returned malformed consumer poll"))
       (list :consumer-poll-reply :accepted token report)))
    (:refused (list :reason (list :consumer-poll-reply :refused nil nil)
                    (second answer)))
    (otherwise (fnn-fault "ACL2 returned malformed consumer poll decision"))))

(defun fnn-owner-wait-elapsed-ms (start)
  (floor (* 1000 (max 0 (- (fnn-now) start))) internal-time-units-per-second))

(defun fnn-owner-consumer-local-wait (service operation consumer argument)
  "Answer one consumer WAIT (PRF-252): what a poll answers when it returns.

OPERATION is :wait (ARGUMENT the timeout in seconds) or :bound-wait (ARGUMENT
the list (SECONDS PASSWORD)).  ACL2 admits the waiter
(fn-owner-consumer-local-wait-admit) and decides each step
(fn-owner-consumer-local-wait-step, books/consumer-wait.lisp): the poll's
answer, or (:sleep MS) on an empty page before the deadline.  Between steps
this thread sleeps on the owner's commit signal (fnn-owner-signal-commit,
raised by every durable publication and by a stop) for at most MS, holding
no owner lock; a signal that came after the step's poll but before the
sleep is seen by the commit count, so none is lost.  It never spins: each
step follows a signal, a spurious wakeup or the sleep's end."
  (let* ((boundp (eq operation :bound-wait))
         (seconds (if boundp (first argument) argument))
         (secret (and boundp (second argument)))
         (lock (fnn-owner-service-wait-lock service))
         (queue (fnn-owner-service-wait-queue service))
         (start (fnn-now))
         (admission
           (fnn-owner-serialized
            service nil
            (lambda ()
              (sb-thread:with-mutex (lock)
                (let ((verdict (fnn-owner-core
                                'fn-owner-consumer-local-wait-admit
                                (fnn-owner-service-waiters service))))
                  (when (eq verdict :admit)
                    (incf (fnn-owner-service-waiters service)))
                  verdict))))))
    (unless (eq admission :admit)
      (unless (and (consp admission) (eq (first admission) :refused))
        (fnn-fault "ACL2 returned malformed wait admission"))
      (fnn-err "consumer wait refused: ~(~a~)" (second admission))
      (return-from fnn-owner-consumer-local-wait
        (list :reason (list :consumer-poll-reply :refused nil nil)
              (second admission))))
    (unwind-protect
         (loop
           (let* ((seen (sb-thread:with-mutex (lock)
                          (fnn-owner-service-commits service)))
                  (step (fnn-owner-serialized
                         service nil
                         (lambda ()
                           (fnn-core-arena-state 'fn-owner-consumer-local-wait-step
                                                 consumer secret
                                           (fnn-owner-wait-elapsed-ms start)
                                           seconds)))))
             (case (and (consp step) (first step))
               (:answer
                (return (fnn-owner-consumer-poll-answer (second step))))
               (:sleep
                (let ((ms (second step)))
                  (unless (and (integerp ms) (plusp ms))
                    (fnn-fault "ACL2 returned a malformed wait sleep"))
                  (sb-thread:grab-mutex lock)
                  (unwind-protect
                       (when (= seen (fnn-owner-service-commits service))
                         (sb-thread:condition-wait queue lock
                                                   :timeout (/ ms 1000.0d0)))
                    ;; A timed-out condition-wait may return without the mutex.
                    (when (sb-thread:holding-mutex-p lock)
                      (sb-thread:release-mutex lock)))))
               (otherwise (fnn-fault "ACL2 returned a malformed wait step")))))
      (sb-thread:with-mutex (lock)
        (decf (fnn-owner-service-waiters service))))))

(defun fnn-owner-transit-complete (cid kind reason word)
  "Feed a transit outcome to the owner and write its one service-log line.

The line is rendered by ACL2 (fn-olog-transit-line) from the owner before the
outcome consumes the submission, with the same KIND, REASON and WORD; a
refused or deferred peer transfer is never silent.  The outcome is fed the
word ACL2 chooses from WORD and the ingress detail (fn-pa-served-word, as
fnn-owner-attempt-served does for POST), so a relayed reason reaches the
peer on its 437 line (fn-osp-transit-refusal-renders-its-reason)."
  (fnn-owner-action 'fn-owner-transit-log-line cid kind reason word
                    *fnn-owner-transit-detail* *fnn-owner-transit-verdict*)
  (fnn-owner-action 'fn-owner-transit-outcome cid kind reason
                    (fnn-owner-core 'fn-owner-served-carried-word word
                                    *fnn-owner-transit-detail*))
  (fnn-owner-log))

(defun fnn-owner-drain-one (service)
  "Take and complete at most one queued served submission; return cid, the
completion reply (an ACL2 octet list, appended to the step's render plan),
whether the outcome was uncertain, and ACL2's outcome word (the attempt's,
:refused for a refusal before the attempt, :uncertain for a control fault),
which books/owner-commit-steps.lisp fn-ocs-member-releases reads."
  (setq *fnn-owner-transit-detail* nil
        *fnn-owner-transit-verdict* nil)
  (let* ((took (fnn-owner-take))
         (taken (fnn-owner-taken-word took)))
    (if (eq taken :idle)
        (values nil nil nil)
        (let* ((cid (fnn-nat (fnn-owner-taken-id took)))
               (msgid (fnn-owner-taken-msgid took))
               (payload (fnn-owner-taken-octets took)))
          (when (eq taken :taken-control)
            (fnn-owner-action 'fn-owner-fault cid)
            (return-from fnn-owner-drain-one
              (values cid (fnn-owner-list-global 'fn-owner-output) t :uncertain)))
          ;; The identities here serve the transfer decision only (the
          ;; obligation and subject fn-owner-transit-decide takes below); a
          ;; served POST derives them once, from the octet buffer, inside
          ;; fnn-owner-attempt (fnn-metadata-buffer), so the payload is not
          ;; converted and digested a second time per POST.
          (multiple-value-bind (obligation subject ignored)
              (if (eq taken :taken-transit)
                  (fnn-metadata msgid payload)
                (values nil nil nil))
            (declare (ignore ignored))
            (let* ((transitp (eq taken :taken-transit))
                   (transit-kind
                     (when transitp
                       (fnn-owner-action 'fn-owner-transit-decide
                                         (fnn-octet-list obligation)
                                         (fnn-octet-list subject))))
                   (transit-reason
                     (when transitp (fnn-owner-core 'fn-owner-transit-reason)))
                   ;; The payload the transfer decision staged is the one
                   ;; fn-owner-take left and the metadata above digested:
                   ;; fn-peer-relayed-octets of the received article.  A
                   ;; difference is a core fault, never a store attempt.
                   (transit-checked
                     (when (and transitp (eq transit-kind :want))
                       (unless (equalp payload
                                       (fnn-owner-octets-global
                                        'fn-owner-transit-payload))
                         (fnn-fault "owner transit payload differs from the staged one"))
                       t))
                   ;; Transit memberships are computed by the ACL2 transfer
                   ;; decision above; a served POST's are the take's.
                   (groups (if transitp
                               (fnn-owner-transit-groups)
                             (fnn-owner-taken-groups took)))
                   (evidence
                     (fnn-octets
                      (if transitp
                          (fnn-owner-core 'fn-owner-transit-evidence)
                        (fnn-owner-core 'fn-owner-prov-post))))
                 (generation (fnn-nat (fnn-owner-core 'fn-owner-config-generation)))
                 (txid (fnn-nat (fnn-owner-core 'fn-owner-next-txid)))
                 (intent-publication
                   (when (or (not transitp) (eq transit-kind :want))
                     (fnn-owner-feed-step 'fn-owner-submission-intent
                                          (fnn-octet-list evidence)
                                          generation txid)))
                 (intent (and intent-publication
                              (fnn-owner-feed-word intent-publication))))
            (declare (ignorable transit-checked))
            (if (and transitp (not (eq transit-kind :want)))
                (progn
                  (fnn-owner-transit-complete
                   cid transit-kind transit-reason :refused)
                  (values cid (fnn-owner-list-global 'fn-owner-output) nil :refused))
              (if (not (eq intent :ready))
                  ;; PRF-335: the refusal is named by ACL2 from the intent
                  ;; (fn-own-intent-refusal-word): a full peer feed queue is
                  ;; :feed-queue-full, never the unnamed :refused.
                  (let ((refusal (fnn-core 'fn-own-intent-refusal-word intent)))
                    (if transitp
                        (progn
                          (setq *fnn-owner-transit-detail* :intent)
                          (fnn-owner-transit-complete
                           cid :want transit-reason refusal))
                      (progn (fnn-owner-action 'fn-owner-outcome cid refusal)
                             (fnn-owner-log)))
                    (values cid (fnn-owner-list-global 'fn-owner-output) nil :refused))
                (progn
                  ;; Durable intent before the first Store mutation.  Empty is
                  ;; a complete plan when the ACL2 target set is empty.
                  (fnn-owner-feed-flush service intent-publication)
                  (let ((word (if transitp
                                  (fnn-owner-attempt-transit
                                   service msgid payload groups evidence t)
                                (fnn-owner-attempt-served
                                 service msgid payload groups evidence))))
                    (fnn-owner-feed-flush-after-barrier
                     service
                     (fnn-owner-feed-step 'fn-owner-submission-resolution
                                          word (fnn-octet-list evidence)
                                          generation txid))
                    ;; Inside a commit quantum: how this member's
                    ;; connection is answered if the batch's barrier fails
                    ;; (fnn-owner-commit-queued-locked), from the owner
                    ;; before its outcome is fed.
                    (when *fnn-owner-deferred*
                      (setq *fnn-owner-uncertain-render*
                            (list (fnn-owner-core 'fn-owner-snapshot)
                                  cid transitp :want transit-reason)))
                    (if transitp
                        (fnn-owner-transit-complete
                         cid :want transit-reason word)
                      (progn (fnn-owner-action 'fn-owner-outcome cid word)
                             (fnn-owner-log)))
                    (values cid (fnn-owner-list-global 'fn-owner-output)
                            (eq word :uncertain) word)))))))))))

;;; ---------------------------------------------------------------------------
;;; The commit quantum (lane commit-onto-log, design 2026-09-27
;;; section 3.3; PKT-688 (4)).
;;;
;;; A served POST's read queues its submission and returns :await
;;; (fnn-owner-handle-chunk); its mux connection holds the step and reads
;;; nothing more until its completion arrives.  The committer thread waits
;;; for a queued submission, enters the gate as the :commit class
;;; (books/owner-commit-class.lisp fn-ocm-next: admitted when no other class
;;; waits, or after its bound), and under the owner mutex:
;;;   1. drains every queued submission, each through the unchanged
;;;      fnn-owner-drain-one (take, intent, attempt, outcome), with
;;;      *fnn-log-batch* bound: each member's record joins the log's open
;;;      batch (fn-olr-take) and the member completes in memory in order --
;;;      the sequential machine's steps, one after another;
;;;   2. appends the batch and fences the segment ONCE (fnn-log-commit-open-
;;;      batch: cuts log-written, log-fenced), and the log kernel
;;;      acknowledges every member (fn-lgk-finish-one);
;;;   3. only then writes the members' service-log lines and feed resolutions
;;;      and hands each member's rendered completion to its connection.
;;; Nothing else runs between 1 and 3 (the mutex is held), so no reply, read,
;;; feed resolution or log line reveals a record before its barrier.  A
;;; member's uncertain outcome, or an append or barrier error, answers every
;;; member of the quantum with no reply (the connection closes: uncertain,
;;; never a refusal or an acceptance), fences the store and stops the service
;;; (exit 3); recovery decides from the log (T7).

(defun fnn-owner-note-queued (service)
  "A read step queued a submission: wake the committer."
  (sb-thread:with-mutex ((fnn-owner-service-commit-lock service))
    (incf (fnn-owner-service-queued service))
    (sb-thread:condition-notify (fnn-owner-service-commit-ready service))))

(defun fnn-owner-feed-flush-after-barrier (service publication)
  "A submission's feed resolution: flushed now, or, inside a commit quantum,
after the batch's barrier (its record is durable only then)."
  (if *fnn-owner-deferred*
      (push (cons :feed publication) (cdr *fnn-owner-deferred*))
    (fnn-owner-feed-flush service publication)))

(defun fnn-owner-deliver (service cid completion)
  "Hand CID's rendered COMPLETION (octets, or :uncertain) to its connection:
the mux connection waiting for it, or the DONE table until it registers."
  (let ((target nil))
    (sb-thread:with-mutex ((fnn-owner-service-commit-lock service))
      (setq target (gethash cid (fnn-owner-service-awaiting service)))
      (if target
          (remhash cid (fnn-owner-service-awaiting service))
        (setf (gethash cid (fnn-owner-service-done service)) completion)))
    (when target
      (funcall (car target) completion))))

(defun fnn-owner-take-done (service cid)
  "CID's completion from the DONE table (a logical connection committed in
its own quantum), removed; :uncertain when there is none."
  (sb-thread:with-mutex ((fnn-owner-service-commit-lock service))
    (multiple-value-bind (done present) (gethash cid (fnn-owner-service-done service))
      (remhash cid (fnn-owner-service-done service))
      (if present done :uncertain))))

(defun fnn-owner-awaiting-sockets (service cid)
  "The socket of CID's waiting connection, as a list (none when it has not
registered yet)."
  (sb-thread:with-mutex ((fnn-owner-service-commit-lock service))
    (let ((target (gethash cid (fnn-owner-service-awaiting service))))
      (and target (cdr target) (list (cdr target))))))

(defun fnn-owner-await-register (service cid deliver socket)
  "CID's connection (SOCKET) waits for its completion: DELIVER is called with
it once.  Returns the completion at once when the committer already produced
it."
  (sb-thread:with-mutex ((fnn-owner-service-commit-lock service))
    (multiple-value-bind (done present) (gethash cid (fnn-owner-service-done service))
      (cond (present (remhash cid (fnn-owner-service-done service)) done)
            (t (setf (gethash cid (fnn-owner-service-awaiting service))
                     (cons deliver socket))
               nil)))))

(defun fnn-owner-commit-start-locked (service &key (seal t))
  "START (books/owner-commit-pipeline.lisp): drain at most the operator's
batch bound of queued members into the log's open batch, each through its
sequential life; the caller holds the owner mutex.  With SEAL (the START of
an idle owner) the batch is then appended (fnn-log-seal-open-batch, cut
log-written) and is in flight: its barrier is the syncer's.  Without SEAL
(START-NEXT, behind a batch in flight) nothing is appended: the kernel
admits one batch in flight.  No reply leaves.  Returns (values MEMBERS
UNCERTAIN DEFERRED): MEMBERS in order, each (CID REPLY WORD RENDER): REPLY
the completion ACL2 rendered, WORD ACL2's outcome word, RENDER what ACL2's
uncertain reply for the member is rendered from (nil when it was refused
before its attempt); UNCERTAIN when a member's outcome was, or an observation
was indeterminate; DEFERRED the members' log lines and feed resolutions,
released by their COMPLETE.  MEMBERS is nil and UNCERTAIN
nil when nothing was queued (or the store does not commit through the log)."
  (let ((store (fnn-owner-service-store service))
        (deferred (list :deferred)))
    (unless (and (fnn-owner-service-batching service) (fnn-store-logp store))
      (return-from fnn-owner-commit-start-locked (values nil nil deferred)))
    (sb-thread:with-mutex ((fnn-owner-service-commit-lock service))
      (setf (fnn-owner-service-queued service) 0))
    (let ((members nil) (uncertain nil) (drained 0)
          (log (fnn-store-log store)))
      (destructuring-bind (bmax omax) (fnn-owner-core 'fn-owner-log-bounds)
        (setf (fnn-log-bmax log) bmax (fnn-log-omax log) omax))
      (fnn-owner-refresh-compression log)
      (let ((*fnn-log-batch* t)
            (*fnn-owner-deferred* deferred))
        (handler-case
            (progn
              ;; One START takes at most the operator's batch bound of
              ;; members (a work bound per step, D27); the rest stay queued
              ;; for the next batch.
              (loop repeat (fnn-log-bmax log) do
                (setq *fnn-owner-uncertain-render* nil)
                (let ((mark (cdr deferred)))
                  (multiple-value-bind (cid reply stop word) (fnn-owner-drain-one service)
                    (unless cid (return))
                    (incf drained)
                    (if (and (not stop) (fnn-core 'fn-ocs-told-at-drain-p word))
                        ;; PRF-354 (books/owner-commit-steps.lisp
                        ;; fn-ocs-told-at-drain-p): a refusal that wrote
                        ;; nothing is known now, whatever the batch's barrier
                        ;; does: its lines and feed resolution, then its
                        ;; rendered refusal, leave at once, and it is not a
                        ;; member of the batch.
                        (let ((mine (ldiff (cdr deferred) mark)))
                          (setf (cdr deferred) mark)
                          (dolist (item (reverse mine))
                            (if (eq (car item) :log)
                                (fnn-log-line (cdr item))
                              (fnn-owner-feed-flush service (cdr item))))
                          (fnn-owner-deliver service cid reply))
                      (progn
                        ;; A member ACL2 answered uncertain ends the START: the
                        ;; batch is not appended (its :started-uncertain).
                        (push (list cid reply word *fnn-owner-uncertain-render*) members)
                        (when stop (setq uncertain t) (return)))))))
              ;; The bound ended the drain: members may still be queued.
              ;; Keep the committer's wake-up count positive (host
              ;; bookkeeping: a START-NEXT or the next START that finds
              ;; nothing reports so), or the backlog would wait for a new
              ;; submission's wake-up.
              (when (and (= drained (fnn-log-bmax log)) (not uncertain))
                (sb-thread:with-mutex ((fnn-owner-service-commit-lock service))
                  (setf (fnn-owner-service-queued service)
                        (max 1 (fnn-owner-service-queued service)))))
              ;; Developer image only: the START's member count against
              ;; the operator's bound (the pipelined native cases).
              (when (fnn-developer-selector "FN_NATIVE_OWNER_TEST_PIPELINE_TRACE")
                (fnn-err "start: seal=~a bmax=~d members=~d" seal (fnn-log-bmax log)
                         (length members)))
              (when (and seal members (not uncertain))
                (fnn-log-seal-open-batch store)
                ;; Lane credits (books/owner-credits.lisp fn-mca-seal): the
                ;; taken members' credit is the batch in flight's until its
                ;; COMPLETE, whatever their connections do meanwhile.
                (fnn-owner-action 'fn-owner-credits-seal))
              ;; Nothing kept (every member a refusal told at its drain):
              ;; nothing of theirs is written or held (fn-mca-settle).
              (when (and (null members) (not uncertain))
                (fnn-owner-action 'fn-owner-credits-settle)))
          (fnn-store-indeterminate (e)
            (fnn-err "Store outcome uncertain; the store needs recovery: ~a" e)
            (setq uncertain t))))
      (values (nreverse members) uncertain deferred))))

(defun fnn-owner-commit-sync (service)
  "SYNC (books/owner-commit-pipeline.lisp): the sealed batch's barrier and
the kernel's fence (host/native/io.lisp fnn-log-sync-sealed-batch: the log
struct under its own lock, never an owner global).  Run by the syncer
thread with the owner RELEASED, or inline inside a quantum by
fnn-owner-commit-queued-locked.  Returns (values WORD CONDITION)."
  ;; Developer image only: hold the barrier open for the native test of the
  ;; in-flight regime (tests/test_native_owner_scheduler.py).
  (let ((ms (fnn-developer-selector "FN_NATIVE_OWNER_TEST_BARRIER_MS")))
    (when (and ms (every #'digit-char-p ms) (plusp (length ms)))
      (sleep (/ (parse-integer ms) 1000))))
  ;; Developer image only (lane time-model): a stalled device.  While the
  ;; named file exists the barrier does not proceed, as an fdatasync on a
  ;; device under maintenance does not return; removing it is the device
  ;; coming back (tests/test_native_slow_disk.py).
  (let ((stall (fnn-developer-selector "FN_NATIVE_TEST_DISK_STALL_FILE")))
    (when (and stall (plusp (length stall)))
      (loop while (probe-file stall) do (sleep 0.05))))
  (fnn-log-sync-sealed-batch (fnn-owner-service-store service)))

(defun fnn-owner-commit-start-event (members uncertain)
  "The START's observation for fn-ocs-commit-step, ACL2's
(books/owner-commit-steps.lisp fn-ocs-start-event): a member (or an
observation) was uncertain, the batch kept no member (nothing was queued, or
every member was a refusal told at its drain: PRF-354), or a batch was
staged."
  (let ((event (fnn-core 'fn-ocs-start-event (and uncertain t) (length members))))
    (unless (member event '(:started :started-none :started-uncertain))
      (fnn-fault "owner returned a malformed START event ~a" event))
    event))

(defun fnn-owner-commit-release-member (service member release)
  "Answer MEMBER (CID REPLY WORD RENDER) as ACL2's RELEASE for it
(books/owner-commit-steps.lisp fn-ocs-member-release) names."
  (destructuring-bind (cid reply word render) member
    (declare (ignore word))
    (fnn-owner-deliver
     service cid
     (case release
       (:rendered reply)
       (:own-uncertain (cons :close reply))
       (:uncertain-reply
        (let ((octets (ignore-errors
                       (apply #'fnn-core 'fn-owner-uncertain-reply-of render))))
          ;; ACL2's uncertain reply could not be rendered: the close alone
          ;; (still uncertain to its client, never an acceptance).
          (if (fnn-octet-list-p octets) (cons :close octets) :uncertain)))
       (:close :uncertain)
       (t (fnn-fault "owner named a malformed member release ~a" release))))))

(defun fnn-owner-commit-complete-locked (service action members deferred)
  "COMPLETE (books/owner-commit-steps.lisp), the caller holding the owner
mutex; ACTION is ACL2's step (fn-ocs-commit-step): :complete after a fenced
barrier -- the log kernel acknowledges the batch, the members' deferred log
lines and feed resolutions go out in order, and only then each member's
reply -- or :stop after an uncertain member or a failed barrier -- the
recovery event: the store is fenced, every member answered uncertain, and the
service stops (exit 3).  Each member is answered as ACL2's
fn-ocs-member-releases names (its own acceptance or refusal only in a
COMPLETE: fn-ocs-members-told-only-after-the-barrier).  Returns the number of
members."
  (let* ((store (fnn-owner-service-store service))
         (releases (fnn-core 'fn-ocs-member-releases action
                             (loop for m in members
                                   collect (list (third m) (and (fourth m) t))))))
    (unless (and (listp releases) (= (length releases) (length members)))
      (fnn-fault "owner returned malformed member releases ~a" releases))
    (case action
      (:stop
       ;; An indeterminate observation before the first member was kept
       ;; still stops: the store is fenced either way (lane log-2).
       (setf (fnn-store-fenced store) t)
       ;; Lane credits (fn-mca-stop): the service exits; nothing is admitted
       ;; again.
       (fnn-owner-action 'fn-owner-credits-stop)
       (fnn-err "a log batch of ~d member~:p is uncertain; the store needs recovery"
                (length members))
       ;; Each member is answered from the owner before the stop (campaign
       ;; W1: the poster is told before the connection closes).
       (let ((waiting (loop for m in members
                            append (fnn-owner-awaiting-sockets service (first m)))))
         ;; Added to, never replacing, a socket an earlier stop spared
         ;; (PKT-562).
         (sb-thread:with-mutex ((fnn-owner-service-commit-lock service))
           (setf (fnn-owner-service-sparing service)
                 (union waiting (fnn-owner-service-sparing service)))))
       (loop for m in members for r in releases
             do (fnn-owner-commit-release-member service m r))
       (fnn-owner-stop-service-locked service +fnn-exit-uncertain+))
      (:complete
       (fnn-log-batch-finish store)
       ;; Lane credits (fn-mca-batch-done): the barrier returned; the batch's
       ;; buffers are the syncer's no longer.
       (fnn-owner-action 'fn-owner-credits-batch-done)
       ;; After the barrier: the lines and the feed resolutions, in order.
       (dolist (item (reverse (cdr deferred)))
         (if (eq (car item) :log)
             (fnn-log-line (cdr item))
           (fnn-owner-feed-flush service (cdr item))))
       (loop for m in members for r in releases
             do (fnn-owner-commit-release-member service m r)))
      (t (fnn-fault "owner named ~a for a batch's COMPLETE" action)))
    (length members)))

(defun fnn-owner-commit-step-action (phase event)
  "ACL2's action for the commit's PHASE and EVENT (fn-ocs-commit-step), for
the inline commit, which holds no gate phase (only at an idle owner: while a
batch is in flight the gate admits no class that commits inline)."
  (let ((action (fnn-core 'fn-ocs-commit-step phase event)))
    (unless (member action '(:barrier :complete :stop :none :fault))
      (fnn-fault "owner returned a malformed commit step ~a" action))
    action))

(defun fnn-owner-commit-queued-locked (service)
  "The three steps in ONE quantum the caller already holds (a bound
submission's or a BP transit's, which commit what is queued before their own
record): START, the barrier inline, COMPLETE, each named by ACL2's
fn-ocs-commit-step.  Returns the number of members committed (0 when nothing
was queued)."
  (multiple-value-bind (members uncertain deferred)
      (fnn-owner-commit-start-locked service)
    (let ((action (fnn-owner-commit-step-action
                   :idle (fnn-owner-commit-start-event members uncertain))))
      (when (eq action :barrier)
        ;; START sealed the batch (fnn-owner-commit-start-locked): its SYNC
        ;; inline, then the syncer's collection.
        (multiple-value-bind (word condition) (fnn-owner-commit-sync service)
          (when condition (error condition))
          (fnn-log-sync-collected (fnn-store-log (fnn-owner-service-store service)))
          (setq action (fnn-owner-commit-step-action :staged word))))
      (case action
        ((:complete :stop)
         (fnn-owner-commit-complete-locked service action members deferred))
        (:none nil)
        (t (fnn-fault "owner named ~a for an inline commit" action))))
    (length members)))

(defun fnn-owner-reader-capture (event)
  "The reader view's capture at the committer's EVENT (host/owner-host.lisp
fn-owner-reader-views-capture, books/owner-reader-view.lisp fn-ocv-capture):
:start before a START's drain, :next before a START-NEXT's, :unnext after a
START-NEXT that took nobody, :complete after a COMPLETE's replies, :drop
after a START that took nobody or a stop.  The caller holds the owner."
  (fnn-owner-core 'fn-owner-reader-views-capture event))

(defun fnn-owner-commit-event (service event)
  "Apply the commit's EVENT to ACL2's scheduler value (books/owner-commit-pipeline.lisp
fn-ocp-commit-event) and return the ACTION it names; the gate's next pick
reads the phase it leaves.  Called inside the committer's :commit quanta."
  (let ((gate (fnn-owner-service-gate service)))
    (sb-thread:with-mutex ((fnn-owner-gate-mutex gate))
      (destructuring-bind (action sched)
          (fnn-call 'fn-otm-commit-event (fnn-owner-gate-sched gate) event)
        (unless (member action '(:sync :wait :complete :stop :none :fault))
          (fnn-fault "owner returned a malformed commit step ~a" action))
        (when (eq action :fault)
          (fnn-fault "owner refused the commit event ~a" event))
        (setf (fnn-owner-gate-sched gate) sched)
        action))))

(defun fnn-owner-commit-wake (service returned queued)
  "ACL2's wake for the committer while a batch is in flight
(fn-ocp-committer-wake): :collect, :start-next or :wait.  The gate's six
waiting counts go with the scheduler value, read under the gate mutex: a
waiting control, poster or transit request stops the pipeline from
preparing another batch (books/owner-commit-fairness.lisp)."
  (let ((gate (fnn-owner-service-gate service)))
    (let ((wake (multiple-value-bind (sched waiting)
                    (sb-thread:with-mutex ((fnn-owner-gate-mutex gate))
                      (values (fnn-owner-gate-sched gate)
                              (coerce (fnn-owner-gate-waiting gate) 'list)))
                  (progn
                    ;; Developer image only: the counts a wake read.
                    (when (and queued (not returned)
                               (fnn-developer-selector "FN_NATIVE_OWNER_TEST_PIPELINE_TRACE"))
                      (fnn-err "pipeline: wake waiting=~a" waiting))
                    (fnn-core 'fn-otm-committer-wake sched returned queued waiting)))))
      (unless (member wake '(:collect :start-next :wait))
        (fnn-fault "owner returned a malformed committer wake ~a" wake))
      wake)))

(defun fnn-owner-start-syncer (service gen)
  "Sync one sealed batch off owner lock. Roster ownership survives a failed
committer until actual shutdown joins this worker."
  (let ((result (list nil)))
    (setf (fnn-owner-service-synced service) nil)
    (fnn-with-roster (service)
      (let ((worker
              (sb-thread:make-thread
               (lambda ()
                 (unwind-protect
                      (progn
                        (multiple-value-bind (word condition)
                            (handler-case (fnn-owner-commit-sync service)
                              (serious-condition (e) (values :failed e)))
                          (setf (car result) (list* gen word condition)))
                        (sb-thread:with-mutex ((fnn-owner-service-commit-lock service))
                          (setf (fnn-owner-service-synced service) t)
                          (sb-thread:condition-notify (fnn-owner-service-commit-ready service))))
                   (fnn-with-roster (service)
                     (setf (fnn-owner-service-workers service)
                           (delete sb-thread:*current-thread*
                                   (fnn-owner-service-workers service) :test #'eq)))))
               :name "fn owner syncer")))
        (push worker (fnn-owner-service-workers service))
        (values worker result)))))

(defun fnn-owner-members-named (members cids)
  "The MEMBERS (CID REPLY WORD RENDER) whose cid ACL2 named in CIDS, in order."
  (unless (listp cids)
    (fnn-fault "owner returned a malformed connection list ~a" cids))
  (remove-if-not (lambda (m) (member (first m) cids)) members))

(defun fnn-owner-answer-early (ledger members)
  "Lane time-bars (PRF-384, books/owner-time-bars.lisp fn-otb-answer-early):
the MEMBERS of the request in flight answered before its completion (at the
stall, or at a stop's release): ACL2 names those not already told, each
once, and records them.  Returns (values MEMBERS-TO-TELL LEDGER')."
  (destructuring-bind (now ledger2)
      (fnn-core 'fn-otb-answer-early ledger (mapcar #'first members))
    (values (fnn-owner-members-named members now) ledger2)))

(defun fnn-owner-complete-generation (ledger gen members)
  "Lane time-bars (PRF-384, books/owner-time-bars.lisp fn-otb-complete): the
barrier's completion, reported with the generation GEN it was issued under,
consumed into the ledger: ACL2 names the MEMBERS it answers (those not told
early).  A completion that does not apply (another generation's, or one
already consumed) is a defect here: exactly one completion per issue.
Returns (values MEMBERS-TO-ANSWER LEDGER')."
  (destructuring-bind (verdict answer ledger2)
      (fnn-core 'fn-otb-complete ledger gen (mapcar #'first members))
    (unless (eq verdict :apply)
      (fnn-fault "owner refused the barrier's completion (generation ~a): ~a" gen verdict))
    (values (fnn-owner-members-named members answer) ledger2)))

(defun fnn-owner-stall-release (service members)
  "The stall (books/owner-time-model.lisp fn-otm-stall-releases): every
MEMBER (CID REPLY WORD RENDER) is answered as ACL2 names -- its uncertain
reply and a close, or the close alone; never its acceptance or refusal.
Returns the cids told."
  (let ((releases (fnn-core 'fn-otm-stall-releases
                            (loop for m in members
                                  collect (list (third m) (and (fourth m) t))))))
    (unless (and (listp releases) (= (length releases) (length members))
                 (every (lambda (r) (member r '(:own-uncertain :uncertain-reply :close)))
                        releases))
      (fnn-fault "owner returned malformed stall releases ~a" releases))
    (loop for m in members for r in releases
          do (fnn-owner-commit-release-member service m r))
    (mapcar #'first members)))

(defun fnn-owner-commit-pipeline (service)
  "Batches through ACL2's pipelined commit (books/owner-commit-pipeline.lisp
fn-ocp-commit-step): START (a :commit quantum; it seals the batch), the
SYNC in the syncer thread with the owner released, while it runs at most one
START-NEXT (a :commit quantum: the queued members behind the batch in
flight, not appended), then COMPLETE (a :commit quantum: the replies of the
batch in flight, then the seal of the next batch, which becomes the batch in
flight).  While any batch is in flight or open ACL2's pick admits only
:inspect and :commit (fn-ocp-next-open-only-in-flight); a batch's replies
leave only in its COMPLETE, after its barrier returned
(fn-ocp-complete-only-after-the-barrier)."
  (let ((members nil) (uncertain nil) (deferred nil) (action nil)
        (next nil) (next-deferred nil) (syncer nil) (result nil) (limits nil)
        (need nil)
        ;; Lane time-bars (PRF-384): ACL2's ledger of the request in
        ;; flight -- its generation, whether its completion is still owed,
        ;; and the connections told before it (at a stall or a stop), which
        ;; its completion never answers again -- and whether this barrier's
        ;; stall was answered.
        (ledger (fnn-core 'fn-otb-ledger-init)) (stall-told nil))
    (fnn-owner-serialized
     service nil
     (lambda ()
       ;; Lane time-model: the barrier's limits (D H C), from the
       ;; configuration generation current at the START
       ;; (fn-owner-barrier-limits).
       (setq limits (fnn-owner-core 'fn-owner-barrier-limits)
             ;; PRF-359: the space the next admissions are judged against.
             need (fnn-owner-core 'fn-owner-space-need))
       ;; ... and kept for the observations taken off the mutex
       ;; (fnn-owner-space-preobserve).
       (setf (fnn-owner-service-space-need service) need)
       ;; PKT-828: the view the readers read while this batch is in flight.
       (fnn-owner-reader-capture :start)
       (multiple-value-setq (members uncertain deferred)
         (fnn-owner-commit-start-locked service))
       (setq action (fnn-owner-commit-event
                     service (fnn-owner-commit-start-event members uncertain)))
       (case action
         (:sync nil)
         (:stop (fnn-owner-reader-capture :drop)
                (fnn-owner-commit-complete-locked service :stop members deferred))
         (:none (fnn-owner-reader-capture :drop))
         (t (fnn-fault "owner named ~a after a START" action))))
     :commit)
    (loop while (eq action :sync) do
      ;; PRF-359 (PKT-872): the free space at every barrier's issue, before
      ;; its append: the POSTs admitted from here on join the next batch, so
      ;; an observation per barrier keeps fn-otm-space-need's two batches
      ;; the only octets between the observation and the appends it admits.
      (fnn-owner-space-event service need)
      ;; Lane time-bars (PRF-384): the barrier is a request under a fresh
      ;; generation; its completion is consumed into that generation once.
      (destructuring-bind (issued gen ledger2) (fnn-core 'fn-otb-issue ledger)
        (unless (eq issued :issued)
          (fnn-fault "owner refused a barrier's issue: generation ~a is unresolved" gen))
        (setq ledger ledger2)
        (multiple-value-setq (syncer result) (fnn-owner-start-syncer service gen)))
      ;; Lane time-model (PRF-311): the barrier is a request with a
      ;; deadline; its issue is a disk event at this reading.
      (fnn-owner-disk-event service :issue limits)
      (setq action nil stall-told nil)
      ;; While the barrier runs: ACL2 wakes the committer to START-NEXT (a
      ;; queued member, no next batch open) or to COLLECT the barrier's word.
      ;; The wait is timed by ACL2 (fn-otm-wait-ms: to the deadline, then the
      ;; clock cadence); at each expiry the committer appends a clock event,
      ;; which enters the disk's :slow mode past the deadline.  A timeout
      ;; is never a failure: the batch stays in flight.
      (loop
        (let ((wake nil) (expired nil))
          (block waiting
            (sb-thread:with-mutex ((fnn-owner-service-commit-lock service))
              (loop
                (setq wake (fnn-owner-commit-wake
                            service (fnn-owner-service-synced service)
                            (plusp (fnn-owner-service-queued service))))
                (unless (eq wake :wait) (return-from waiting))
                ;; PKT-875: a stop's drain passed its deadline: release
                ;; below, once, as at a stall.
                (when (and (fnn-owner-service-drain-release service)
                           (not stall-told))
                  (return-from waiting))
                (let ((ms (fnn-owner-disk-wait-ms service)))
                  (unless (if ms
                              (sb-thread:condition-wait (fnn-owner-service-commit-ready service)
                                                        (fnn-owner-service-commit-lock service)
                                                        :timeout (/ ms 1000))
                            (sb-thread:condition-wait (fnn-owner-service-commit-ready service)
                                                      (fnn-owner-service-commit-lock service)))
                    ;; Timed out: SBCL returns without the mutex held, so
                    ;; leave WITH-MUTEX touching nothing it protects.
                    (setq expired t)
                    (return-from waiting))
                  ;; Lane time-model-2: woken before the wait expired --
                  ;; a clock event first, so the next wait is measured
                  ;; from the time of this wake, never from a stale one
                  ;; (the F4-W hypothesis, fn-otm-clock-run-okp).
                  (fnn-owner-disk-event service :clock)))))
          (when expired
            (fnn-owner-disk-event service :clock)
            (setq wake :expired))
          ;; Lane time-model-2 (PRF-311): past H the disk is :stalled (entered
          ;; by whichever clock event came first: this committer's, a served
          ;; read's, a status render's).  Once per barrier: every member of
          ;; the batch in flight and of the next batch is told the outcome
          ;; is uncertain -- never accepted, never refused; the bytes may
          ;; still land (books/owner-time-model.lisp
          ;; fn-otm-stall-tells-no-member-its-outcome) -- and the queued
          ;; POSTs behind them are refused try-later, nothing stored.
          ;; PKT-875 (books/owner-stop-drain.lisp): a graceful stop whose
          ;; drain deadline (H) passed releases them the same way, by
          ;; fn-otm-stall-releases: uncertain, never accepted or refused.
          (when (and (not (eq wake :collect)) (not stall-told)
                     (or (fnn-owner-disk-stalled-p service)
                         (sb-thread:with-mutex ((fnn-owner-service-commit-lock service))
                           (fnn-owner-service-drain-release service))))
            (setq stall-told t)
            (let ((told nil) (shed 0))
              (multiple-value-bind (tell ledger2)
                  (fnn-owner-answer-early ledger (append members next))
                (setq ledger ledger2
                      told (fnn-owner-stall-release service tell)))
              (fnn-owner-gated (service :reader)
                (fnn-owner-shared-action-locked
                 service nil
                 (lambda () (setq shed (fnn-owner-shed-queued-locked service)))))
              (fnn-owner-journal-note service (length told) shed)))
          (when (eq wake :collect)
            ;; The barrier's completion, observed: a disk event at this
            ;; reading (:recovered after a slow episode).
            (fnn-owner-disk-event service :return)
            (return))
          ;; :start-next
          (when (eq wake :start-next)
          (let ((step nil))
            (fnn-owner-gated (service :commit)
              (fnn-owner-shared-action-locked
               service nil
               (lambda ()
                 ;; Lane durability-bugs: the wake was decided before this
                 ;; quantum was admitted.  Asked again here, under the owner:
                 ;; a control, poster or transit request that arrived in
                 ;; between stops the START-NEXT, which then takes nobody
                 ;; (:next-none; books/owner-commit-fairness.lisp's
                 ;; fn-ocf-okp names :next-started only at a :start-next
                 ;; wake with the counts of the pick).
                 (if (not (eq (fnn-owner-commit-wake
                               service nil (plusp (fnn-owner-service-queued service)))
                              :start-next))
                     (setq step (fnn-owner-commit-event service :next-none))
                 (progn
                 ;; PKT-828: the next batch's reader view, taken before its
                 ;; members join the working view.
                 (fnn-owner-reader-capture :next)
                 (multiple-value-bind (m u d)
                     (fnn-owner-commit-start-locked service :seal nil)
                   (setq next m next-deferred d)
                   ;; Developer image only: the native test's evidence that
                   ;; a batch was prepared behind a barrier.
                   (when (and m (fnn-developer-selector "FN_NATIVE_OWNER_TEST_PIPELINE_TRACE"))
                     (fnn-err "pipeline: ~d member~:p prepared behind the barrier" (length m)))
                   (setq step (fnn-owner-commit-event
                               service (cond (u :next-uncertain)
                                             ((null m) :next-none)
                                             (t :next-started))))
                   (when (and (null m) (not u)) (fnn-owner-reader-capture :unnext))
                   (when (eq step :stop)
                     (fnn-owner-reader-capture :drop)
                     ;; Every member of both batches is uncertain; the owner
                     ;; stops (its COMPLETE below finds it stopping).
                     (multiple-value-bind (tell ledger2)
                         (fnn-owner-answer-early ledger (append members next))
                       (setq ledger ledger2)
                       (fnn-owner-commit-complete-locked service :stop tell deferred))
                     (setq members nil next nil))))))))))))
      (sb-thread:join-thread syncer :default nil)
      (destructuring-bind (rgen word . condition) (car result)
        ;; Lane time-bars (PRF-384): the late completion, consumed once into
        ;; its own generation; ACL2 names the members it answers (never one
        ;; told at the stall).  Only after this does the batch's buffer go
        ;; (fnn-log-sync-collected below).
        (multiple-value-bind (answer ledger2)
            (fnn-owner-complete-generation ledger rgen members)
          (setq ledger ledger2 members answer))
        ;; COMPLETE runs whatever the barrier observed, and the batch leaves
        ;; flight at its end whatever COMPLETE does, so a failure can never
        ;; leave the gate admitting only :inspect and :commit.
        (fnn-owner-gated (service :commit)
          (let ((done nil))
            (unwind-protect
                 (let ((step (fnn-owner-commit-event service word))
                       (store (fnn-owner-service-store service)))
                   ;; The next batch's barrier (sealed below) gets the
                   ;; limits of the configuration current now.
                   (setq limits (fnn-owner-core 'fn-owner-barrier-limits)
                         need (fnn-owner-core 'fn-owner-space-need))
                   (fnn-owner-shared-action-locked
                    service nil
                    (lambda ()
                      ;; A barrier that ended in a fault (not an indeterminate
                      ;; observation) is re-signalled here, under the owner,
                      ;; so the fault boundary classifies it (exit 4).
                      (when condition (error condition))
                      (fnn-log-sync-collected (fnn-store-log store))
                      (cond ((fnn-owner-service-stopping service)
                             ;; Stopped during the barrier: no member is
                             ;; answered (uncertain to its client).
                             (fnn-owner-reader-capture :drop)
                             (fnn-owner-action 'fn-owner-credits-stop)
                             (multiple-value-bind (tell ledger2)
                                 (fnn-owner-answer-early ledger next)
                               (setq ledger ledger2)
                               (dolist (m (append members tell))
                                 (fnn-owner-deliver service (first m) :uncertain))))
                            ((eq step :complete)
                             (fnn-owner-commit-complete-locked
                              service :complete members deferred)
                             ;; PKT-828: in the same quantum as the replies,
                             ;; the readers' view advances past this batch
                             ;; (to the next batch's capture, or the working
                             ;; view when none is open).
                             (fnn-owner-reader-capture :complete)
                             ;; The next batch, prepared behind the barrier,
                             ;; is sealed now and becomes the batch in flight.
                             (when next
                               (let ((*fnn-owner-deferred* next-deferred))
                                 (handler-case
                                     (progn (fnn-log-seal-open-batch store)
                                            ;; Lane credits: fn-mca-seal.
                                            (fnn-owner-action 'fn-owner-credits-seal))
                                   (fnn-store-indeterminate (e)
                                     (fnn-err "Store outcome uncertain; the store needs recovery: ~a" e)
                                     (fnn-owner-reader-capture :drop)
                                     (multiple-value-bind (tell ledger2)
                                         (fnn-owner-answer-early ledger next)
                                       (setq ledger ledger2)
                                       (fnn-owner-commit-complete-locked
                                        service :stop tell next-deferred))
                                     (setq next nil))))))
                            ((eq step :stop)
                             (fnn-owner-reader-capture :drop)
                             (multiple-value-bind (tell ledger2)
                                 (fnn-owner-answer-early ledger next)
                               (setq ledger ledger2)
                               (fnn-owner-commit-complete-locked
                                service :stop (append members tell) deferred))
                             (setq next nil))
                            (t (fnn-fault "owner named ~a after a barrier" step)))
                      (setq done t))))
              (setq action (fnn-owner-commit-event service :completed))
              (unless done (setq action :none))
              (when (fnn-owner-service-stopping service) (setq action :none))
              (if (and next (eq action :sync))
                  (setq members next deferred next-deferred next nil next-deferred nil)
                (setq members nil next nil)))))))))

(defun fnn-owner-loops-snapshot (service)
  "Per I/O loop, the pass count by which it will have polled (and stepped)
every connection ready now: the next pass when it sleeps in poll(2), the
pass after its current one otherwise.  Each loop is woken (its wake pipe),
so the pass comes at once, not at the poll's timeout."
  (loop for loop in (fnn-owner-service-mux service)
        collect (prog1 (+ (fnn-mux-loop-passes loop)
                          (if (fnn-mux-loop-polling loop) 1 2))
                  (fnn-mux-wake loop))))

(defun fnn-owner-loops-passed-p (service targets)
  "Every I/O loop reached its target pass, or completed the pass before it
and sleeps in poll(2) again (its wake byte may have been read by the pass
that was running when it was written): every connection that was ready at
the snapshot has been stepped, and its submission, if it had one, is
queued."
  (loop for loop in (fnn-owner-service-mux service)
        for n in targets
        always (let ((passes (fnn-mux-loop-passes loop)))
                 (or (>= passes n)
                     (and (fnn-mux-loop-polling loop) (>= passes (- n 1)))))))

(defun fnn-owner-committer-loop (service)
  "The committer thread: one commit quantum whenever a submission is queued,
requested once every I/O loop has finished the pass it was in (the batch is
every submission ready by then: the design's barrier-paced close, without a
timer)."
  (handler-case
      (loop
        (sb-thread:with-mutex ((fnn-owner-service-commit-lock service))
          (loop until (or (plusp (fnn-owner-service-queued service))
                          (fnn-owner-service-stopping service))
                do (sb-thread:condition-wait (fnn-owner-service-commit-ready service)
                                             (fnn-owner-service-commit-lock service)))
          (let ((targets (fnn-owner-loops-snapshot service)))
            (loop until (or (fnn-owner-service-stopping service)
                            (fnn-owner-loops-passed-p service targets))
                  do (sb-thread:condition-wait (fnn-owner-service-commit-ready service)
                                               (fnn-owner-service-commit-lock service)))))
        (when (fnn-owner-service-stopping service) (return))
        (fnn-owner-commit-pipeline service))
    (fnn-store-error ()
      ;; The service stopped between the wake-up and the gate.
      nil)
    (serious-condition (e)
      (fnn-owner-fault-service service nil e))))

(defun fnn-owner-start-committer (service)
  "Start the committer on a batching service."
  (when (fnn-owner-service-batching service)
    (setf (fnn-owner-service-committer service)
          (sb-thread:make-thread (lambda () (fnn-owner-committer-loop service))
                                 :name "fn owner committer"))))

(defun fnn-owner-bound-commit-word (commit-callback)
  "Classify a custom Store callback into the ordinary post's outcome words.

A known Store refusal has no ambiguous publication and can resolve the
in-flight submission.  An uncertain result must retain its unresolved intent;
core/Store faults and unclassified OS errors propagate to the serialized
owner's recovery fence."
  (let ((word (handler-case (funcall commit-callback)
                (fnn-store-indeterminate (e)
                  (fnn-err "Store outcome uncertain; the store needs recovery: ~a" e)
                  :uncertain)
                (fnn-store-fault (condition) (error condition))
                (fnn-store-error () :refused))))
    (unless (member word '(:durable :duplicate :conflict :malformed :unaffordable
                           :memberships :article-numbers-exhausted
                           :storage-failed :refused :clock-unusable :uncertain))
      (fnn-fault "owner bound commit returned ~a" word))
    word))

(defun fnn-owner-complete-bound-submission
    (service submit-callback msgid payload groups evidence generation txid
     &optional commit-callback name-conflict)
  "Complete one ACL2-admitted control submission while the owner mutex is held.

The interface callback is the sole admission event.  Local control and BP
applications then share this exact durable intent, Store attempt, resolution
and control-outcome sequence.

PAYLOAD is :INJECTED for the operator's submission: the octets stored are the
ones ACL2 injected (books/owner.lisp fn-own-operator-submit), read back from
the owner after the take, never the payload the host read from the file.
Every other caller submits exact authored octets and names them.

NAME-CONFLICT (the control callers: the operator post and hybrid-author)
answers a refusal whose completion word was D25's :conflict as the control
status :conflict (books/native-control.lisp
fn-native-control-completion-status, PKT-246); the BP application keeps its
own result vocabulary."
  (fnn-owner-commit-queued-locked service)
  (let ((submitted (funcall submit-callback)))
    (unless (member submitted '(:submitted :busy :refused))
      (fnn-fault "owner bound submit returned ~a" submitted))
    (unless (eq submitted :submitted)
      (return-from fnn-owner-complete-bound-submission submitted))
    (let* ((took (fnn-owner-take))
           (taken (fnn-owner-taken-word took)))
      (unless (eq taken :taken-control)
        (fnn-fault "owner bound take returned ~a" taken))
      (when (eq payload :injected)
        (setq payload (fnn-owner-taken-octets took)))
      (unless (and (equalp msgid (fnn-owner-taken-msgid took))
                   (equalp payload (fnn-owner-taken-octets took))
                   (equalp groups (fnn-owner-taken-groups took)))
        (fnn-fault "owner bound submission changed after admission"))
      (let ((intent-publication
              (fnn-owner-feed-step 'fn-owner-submission-intent
                                   (fnn-octet-list evidence) generation txid)))
        (unless (eq (fnn-owner-feed-word intent-publication) :ready)
          (let ((result
                  (fnn-owner-action 'fn-owner-control-outcome :refused)))
            (fnn-owner-log)
            (unless (eq result :refused)
              (fnn-fault "owner bound intent refusal changed outcome"))
            (return-from fnn-owner-complete-bound-submission result)))
        (fnn-owner-feed-flush service intent-publication)
        (let ((word (if commit-callback
                        ;; PKT-069: file first, here, not by the caller's
                        ;; convention.  The callback commits only when ACL2's
                        ;; filing plan files PAYLOAD in exactly GROUPS
                        ;; (fn-owner-bound-commit-gate, KEYSTONE
                        ;; fn-obc-commit-only-after-filing); otherwise the
                        ;; gate's refusal is the outcome and the Store is not
                        ;; touched.
                        (let ((gate (fnn-owner-core 'fn-owner-bound-commit-gate
                                                    (fnn-octet-list payload)
                                                    (mapcar #'fnn-octet-list groups))))
                          (cond ((eq gate :commit)
                                 (fnn-owner-bound-commit-word commit-callback))
                                ((and (consp gate) (eq (first gate) :refused))
                                 :refused)
                                (t (fnn-fault "owner returned malformed commit gate ~a"
                                              gate))))
                      (fnn-owner-attempt-served
                       service msgid payload groups evidence))))
          (fnn-owner-feed-flush
           service
           (fnn-owner-feed-step 'fn-owner-submission-resolution
                                word (fnn-octet-list evidence) generation txid))
          (let ((result (fnn-owner-action 'fn-owner-control-outcome word)))
            (fnn-owner-log)
            (unless (member result
                            '(:accepted :duplicate :refused :clock-unusable :uncertain))
              (fnn-fault "owner bound completion returned ~a" result))
            (when (eq result :uncertain)
              (fnn-indeterminate "owner bound Store outcome is uncertain"))
            (if name-conflict
                (fnn-core 'fn-native-control-completion-status result word)
              result)))))))

(defun fnn-owner-complete-bp-transit-submission
    (service submit-callback msgid raw stored groups evidence
             generation txid planned-id planned-subject)
  "Complete a BP-origin peer transit through the one owner writer and Store."
  (fnn-owner-commit-queued-locked service)
  (let ((submitted (funcall submit-callback)))
    (unless (member submitted '(:submitted :busy :refused))
      (fnn-fault "owner BP transit submit returned ~a" submitted))
    (unless (eq submitted :submitted)
      (return-from fnn-owner-complete-bp-transit-submission submitted))
    (let* ((took (fnn-owner-take))
           (taken (fnn-owner-taken-word took)))
      (unless (eq taken :taken-transit)
        (fnn-fault "owner BP transit take returned ~a" taken))
      (unless (and (equalp msgid (fnn-owner-taken-msgid took))
                   (equalp stored (fnn-owner-taken-octets took)))
        (fnn-fault "owner BP transit changed its pinned Store projection"))
      (multiple-value-bind (actual-id actual-subject ignored)
          (fnn-metadata msgid stored)
        (declare (ignore ignored))
        ;; fnn-metadata returns rendered text as octet vectors. The actual
        ;; fn-bpaj-transit-plan retains fn-record-octets-string results in
        ;; slots 8/9, so its globals are Lisp strings, not octet lists.
        (unless (and (stringp planned-id) (stringp planned-subject)
                     (equalp actual-id (fnn-string-octets planned-id))
                     (equalp actual-subject
                             (fnn-string-octets planned-subject)))
          (fnn-fault "owner BP transit changed projected identity"))
        (let ((kind (fnn-owner-action 'fn-owner-transit-decide
                                      (fnn-octet-list actual-id)
                                      (fnn-octet-list actual-subject))))
          (unless (eq kind :want)
            (fnn-owner-transit-refused
             (list :refused (fnn-owner-core 'fn-owner-transit-reason)))
            (fnn-owner-action 'fn-owner-bp-transit-outcome :refused)
            (return-from fnn-owner-complete-bp-transit-submission :refused))
          (unless (and (equalp stored
                               (fnn-owner-octets-global
                                'fn-owner-transit-payload))
                       (equalp groups (fnn-owner-transit-groups))
                       (equalp evidence
                               (fnn-octets
                                (fnn-owner-core 'fn-owner-transit-evidence))))
            (fnn-fault "owner BP transit decision disagrees with pinned plan"))
          (unless (equalp raw
                          (fnn-octets
                           (fnn-owner-core 'fn-owner-bp-transit-raw)))
            (fnn-fault "owner BP transit raw request changed"))
          (let ((intent-publication
                  (fnn-owner-feed-step 'fn-owner-submission-intent
                                       (fnn-octet-list evidence) generation txid)))
            (unless (eq (fnn-owner-feed-word intent-publication) :ready)
              (setq *fnn-owner-transit-detail* :submission-intent)
              (return-from fnn-owner-complete-bp-transit-submission
                (fnn-owner-action 'fn-owner-bp-transit-outcome :refused)))
            (fnn-owner-feed-flush service intent-publication)
            (let ((word (fnn-owner-attempt-transit
                         service msgid stored groups evidence)))
              (fnn-owner-feed-flush
               service
               (fnn-owner-feed-step 'fn-owner-submission-resolution
                                    word (fnn-octet-list evidence) generation txid))
              (let ((result
                      (fnn-owner-action 'fn-owner-bp-transit-outcome word)))
                (unless (member result '(:accepted :duplicate :refused
                                         :clock-unusable :uncertain))
                  (fnn-fault "owner BP transit completion returned ~a" result))
                (when (eq result :uncertain)
                  (fnn-indeterminate "owner BP transit Store outcome is uncertain"))
                result))))))))

;;; The developer-only uncertain outcome.
;;;
;;; `FN_NATIVE_CONTROL_FAULT=<cut>` selects one entry of +fnn-cli-faults+ --
;;; the same named table `store post --inject-fault` selects from -- and arms
;;; it on the owner's store for exactly one control submission.  It adds a
;;; reachable path to an existing model cut; it invents no fault point, no
;;; second action vocabulary and no outcome of its own.
;;;
;;; `postpublish` is the cut the uncertain outcome needs: FNN-STORE-INDETERMINATE
;;; is raised after the final publication, so the article is durable and its
;;; report is not.  fnn-owner-attempt answers :uncertain, ACL2's
;;; `fn-owner-control-outcome` keeps that word, fnn-owner-complete-bound-submission
;;; raises it again, fnn-owner-shared-action-locked fences this owner at exit 3,
;;; and the local-control reply carries ACL2's :uncertain status, which
;;; `fn-native-control-status-class` projects to exit 3 at the caller.  No word
;;; on that path is the host's.
;;;
;;; The variable is read through `fnn-developer-selector` (host/native/io.lisp),
;;; which answers NIL on a production image; a production image does not
;;; start with it set at all (`fnn-developer-selector-gate`).  An earlier
;;; version faulted here on a production image, inside fnn-owner-serialized,
;;; so an environment variable turned the next post into exit 3 with nothing
;;; written and stopped the node (campaign dabebb84, F5).
(defvar *fnn-owner-control-fault-consumed* nil)

(defun fnn-owner-control-test-fault ()
  (let ((raw (fnn-developer-selector "FN_NATIVE_CONTROL_FAULT")))
    (when (and raw (not *fnn-owner-control-fault-consumed*))
      (let ((fault (cdr (assoc raw +fnn-cli-faults+ :test #'string=))))
        (unless fault
          (fnn-fault "unknown FN_NATIVE_CONTROL_FAULT cut: ~a" raw))
        fault))))

(defun fnn-owner-control-arm-fault (store)
  "Arm the developer cut on STORE for one submission.

Answer NIL when none is armed, else the store fault it displaced (a list, so
never NIL), which `fnn-owner-control-disarm-fault' puts back: the owner's
own store fault from `fnn-post-entry-fault' survives a control fault.  The
caller holds the owner mutex, so the armed window cannot overlap another
submission, and the cut is consumed here rather than at each `fnn-at` so that
exactly one submission is affected even if the owner survives it."
  (let ((fault (fnn-owner-control-test-fault)))
    (when fault
      (setq *fnn-owner-control-fault-consumed* t)
      (prog1 (list (fnn-store-fault-point store) (fnn-store-fault-class store)
                   (fnn-store-fault-message store))
        (destructuring-bind (point class message) fault
          (setf (fnn-store-fault-point store) point
                (fnn-store-fault-class store) class
                (fnn-store-fault-message store) message))))))

(defun fnn-owner-control-disarm-fault (store displaced)
  (destructuring-bind (point class message) displaced
    (setf (fnn-store-fault-point store) point
          (fnn-store-fault-class store) class
          (fnn-store-fault-message store) message)))

(defun fnn-owner-moderation-serialized (service op login id reason)
  "PKT-657, PKT-575: one moderation or withdrawal request.

ACL2 decides it over the owner and the configuration it carries, after one
fresh clock reading (books/moderation-verbs.lisp fn-mvb-plan, through
host/owner-host.lisp fn-owner-moderation-plan), and names the steps; this
function runs them in order and answers the first that does not accept.  A
refusal carries ACL2's reason, as (:reason :refused REASON).  :submit hands
ACL2's article to the operator submission; :withdraw first publishes ACL2's
configuration vector through the live administration (the operator's
withdrawal row, code 26), then submits the cause article.  Each step decides
again under the owner mutex; nothing here computes a value."
  (let ((plan (fnn-owner-serialized
               service nil
               (lambda ()
                 (fnn-owner-advance-clock)
                 (fnn-owner-core 'fn-owner-moderation-plan op login id reason)))))
    (flet ((submit (msgid groups octets)
             (unless (and (fnn-octet-list-p msgid) (listp groups)
                          (every #'fnn-octet-list-p groups)
                          (fnn-octet-list-p octets))
               (fnn-fault "ACL2 returned a malformed moderation submission"))
             (fnn-owner-control-submit-serialized
              service (fnn-octets msgid) (mapcar #'fnn-octets groups)
              (fnn-octets octets))))
      (case (and (consp plan) (first plan))
        (:refused (list :reason :refused (second plan)))
        (:submit (submit (second plan) (third plan) (fourth plan)))
        (:withdraw
         (let* ((argv (second plan))
                (admin (if argv (fnn-owner-live-admin-serialized service argv)
                         :accepted))
                (word (if (consp admin) (second admin) admin)))
           (if (eq word :accepted)
               (submit (third plan) (fourth plan) (fifth plan))
             admin)))
        (t (fnn-fault "ACL2 returned a malformed moderation plan"))))))

(defun fnn-owner-control-submit-serialized (service msgid groups payload)
  "Inject, queue and drain the operator's article through the shared owner writer.

`fn operator CONFIG post' hands the owner a proto-article.  The owner injects
it (books/owner.lisp fn-own-operator-submit: Path, Injection-Date and
Injection-Info under the owner's posting configuration and clock) exactly as
it injects a served POST, so the article crosses to a peer that requires a
Path; until 2026-09-22 the payload was stored as read and INN refused it 437
(planning/evidence/inn-lab-dabebb84-2026-09-22.md).  One clock reading is
taken for this submission first, as fnn-owner-handle-chunk takes one per
read; a refused reading leaves the owner clock-less and the submission is
refused, not injected under a stale time (D10-a)."
  (fnn-owner-serialized
   service nil
   (lambda ()
     (let* ((store (fnn-owner-service-store service))
            (armed (fnn-owner-control-arm-fault store)))
       (unwind-protect
            (let ((evidence (fnn-octets (fnn-owner-core 'fn-owner-prov-post)))
                  (generation
                    (fnn-nat (fnn-owner-core 'fn-owner-config-generation)))
                  (txid (fnn-nat (fnn-owner-core 'fn-owner-next-txid))))
              (if (and (eq (fnn-owner-advance-clock) :observed)
                       (eq (fnn-owner-action 'fn-owner-stamp-status)
                           :usable))
                  (let ((status
                          (fnn-owner-complete-bound-submission
                           service
                           (lambda ()
                             (let ((submitted
                                     (fnn-owner-arena-action 'fn-owner-operator-submit
                                                       (fnn-octet-list msgid)
                                                       (mapcar #'fnn-octet-list groups)
                                                       (fnn-octet-list payload))))
                               ;; An article refused at admission never
                               ;; reaches an outcome line: ACL2 rendered its
                               ;; refusal line with the submit
                               ;; (fn-olog-control-refusal-line), NIL otherwise.
                               (fnn-owner-log 'fn-owner-log-line t)
                               submitted))
                           msgid :injected groups evidence generation txid
                           nil t)))
                    ;; A refusal carries ACL2's reason to the operator: the
                    ;; injection decision's reason, mapped to the control
                    ;; word by books/native-control.lisp
                    ;; fn-native-control-refusal-status (an article past
                    ;; the profile's A is article-exceeds-profile-bound).
                    ;; PKT-453 (a): the reason itself travels too, as
                    ;; (:reason STATUS REASON); a reasoned request's reply
                    ;; carries ACL2's word for it (books/native-control-
                    ;; reason.lisp fn-nctrl-reason-word), a plain one the
                    ;; status alone.
                    (if (eq status :refused)
                        ;; Row S10: a completion the Store refused names
                        ;; the Store's word (books/owner-control-post-reason
                        ;; fn-ocpr-reason, kept by fn-owner-control-outcome)
                        ;; when the admission decision names none.
                        (let ((reason (or (fnn-core-arena-state 'fn-owner-operator-refusal-reason
                                                          (fnn-octet-list msgid)
                                                          (mapcar #'fnn-octet-list groups)
                                                          (fnn-octet-list payload))
                                          (fnn-owner-core 'fn-owner-control-reason))))
                          (list :reason
                                (fnn-core 'fn-native-control-host-refusal-status reason)
                                reason))
                      status))
                :clock-unusable))
         (when armed (fnn-owner-control-disarm-fault store armed)))))
   :poster))

(defun fnn-owner-redeem-quantum (service cid)
  "PRF-164 (PKT-439), PKT-828 open item 2: an XREDEEM PASS's publication in
its own quantum of ACL2's publication class (books/owner-reader-read.lisp
fn-ocs-publication-class, the class the control socket's live
reconfiguration runs as), which the scheduler never admits while a batch is
in flight (fn-ocs-a-publication-waits-for-the-complete): the connection waits
for the COMPLETE in the gate, holding nothing, and the publication never runs
under a reader capture (fn-ocvp-reader-view-is-at-the-current-generation).
Its reply promises a durable credential (281 only after the configuration
record is durable), so it does not join the log's next batch: the record is
a configuration record, published by its own immutable publication.
Answers ACL2's rendered 281 or 482, or NIL when the connection no longer
waits."
  (let ((class (fnn-core 'fn-ocs-publication-class)))
    (unless (eq class :control)
      (fnn-fault "owner returned a malformed publication class ~a" class))
    (fnn-owner-serialized
     service cid
     (lambda ()
       (and (fnn-owner-core 'fn-acct-host-owner-redeem-waitingp cid)
            (fnn-octet-list (fnn-owner-account-redeem service cid))))
     class)))

(defun fnn-owner-handle-chunk (service cid incoming &optional socket (class :reader) peerp)
  "One served read (fnn-owner-handle-chunk-read, a quantum of CLASS) and,
when it left an XREDEEM PASS waiting, the publication's own quantum
(fnn-owner-redeem-quantum); the step's plan carries the redeem reply after
the read's effects, as when both ran in one quantum.  The values are
fnn-owner-handle-chunk-read's: (values PLAN CLOSING STARTTLS CONSUMED
REDEEMED SUBMITTED), (values :defer MS), or (values :await STEP REDEEM
CLOSING STARTTLS CONSUMED)."
  (let ((results (multiple-value-list
                  (fnn-owner-handle-chunk-read service cid incoming socket class peerp))))
    (case (first results)
      (:redeem
       (destructuring-bind (tag step completion closing starttls consumed submitted) results
         (declare (ignore tag))
         (let ((redeem (fnn-owner-redeem-quantum service cid)))
           (values (fnn-core 'fn-splan-step-plan step completion redeem)
                   closing starttls consumed (and redeem t) submitted))))
      (:await
       (destructuring-bind (tag step waiting closing starttls consumed) results
         (declare (ignore tag))
         (values :await step (and waiting (fnn-owner-redeem-quantum service cid))
                 closing starttls consumed)))
      (:fnn-extent-cold
       (fnn-owner-cold-line service cid incoming socket class peerp
                            (second results) (third results)))
      (:defer (values-list results))
      (t (fnn-owner-page-read-hold cid (first results))
         (values-list results)))))

;;; Developer image only (the resilience framework's `page-read-outstanding'
;;; point, planning/design-resilience-framework-2026-09-29.md section 5):
;;; FN_NATIVE_PAGE_READ_HOLD=MIN-OCTETS:RELEASE-FILE holds a served read
;;; AFTER its step ran against the reader's pinned view (the plan is built;
;;; the owner mutex is released) and BEFORE its reply is rendered and
;;; delivered, when ACL2's first render window of the plan
;;; (fn-splan-window-size) is at least MIN-OCTETS, so a scenario holds the
;;; ARTICLE it started and not the short status replies before it.  It
;;; prints `PAGE-READ held at=page-read-outstanding cid=N window=W' and waits
;;; until the release file exists; the scenario cancels the reader, retires
;;; the old generation (reclaim) and then creates the file, and the read is
;;; delivered (or meets its closed socket).  A SIGKILL during the hold is the
;;; death form.  Once the file exists every later read passes.
(defun fnn-owner-page-read-hold (cid plan)
  (let ((raw (fnn-developer-selector "FN_NATIVE_PAGE_READ_HOLD")))
    (when (and raw (plusp (length raw)))
      (let* ((colon (position #\: raw))
             (min (and colon (plusp colon)
                       (every #'digit-char-p (subseq raw 0 colon))
                       (parse-integer raw :end colon))))
        (unless (and min (< (1+ colon) (length raw)))
          (fnn-fault "invalid FN_NATIVE_PAGE_READ_HOLD (expected MIN-OCTETS:RELEASE-FILE)"))
        (let ((release (subseq raw (1+ colon))))
          (unless (probe-file release)
            (let ((size (fnn-core 'fn-splan-window-size plan)))
              (unless (and (integerp size) (>= size 0))
                (fnn-fault "owner returned a malformed render window size"))
              (when (and (plusp size) (>= size min))
                (fnn-err "PAGE-READ held at=page-read-outstanding cid=~d window=~d" cid size)
                (loop until (probe-file release) do (sleep 0.05))))))))))

;;; Row A4, option (c) (lane composed-owner-3; books/owner-cold-line.lisp,
;;; PRF-933).  The served read span is pure over its stobjs, so it runs with
;;; the extent realizer in its no-I/O mode (host/native/extent.lisp
;;; *fnn-extent-no-io*): a payload extent not in the realizer's cache throws
;;; the entry it needs and nothing of the span is kept.  Then the span is
;;; re-run limited to its FIRST LINE (ACL2's fn-oct-line-end): a warm first
;;; line is answered as its own read (the caller feeds the rest of INCOMING
;;; as the next read, exactly as after a submission's yield, PKT-600), so
;;; pipelined lines are answered in order.  A cold first line comes back as
;;; (:fnn-extent-cold FILE EOFF ELEN TRAILER).  The per-line re-run happens
;;; only after a cold abort: a warm span runs once, as before. Cache-off
;;; still enters admission; it cannot select unfunded synchronous I/O.
(defun fnn-owner-chunk-span-no-io (cid incoming sched)
  (flet ((try (end)
           (catch 'fnn-extent-cold
             (let ((*fnn-extent-no-io* t))
               (list :warm (fnn-core-buffer-state 'fn-owner-chunk-span cid 0 end sched))))))
    (if (not (fnn-extent-no-io-usable-p))
        (fnn-core-buffer-state 'fn-owner-chunk-span cid 0 (length incoming) sched)
      (let ((whole (try (length incoming))))
        (if (eq (car whole) :warm)
            (second whole)
          (let* ((line-end (first (fnn-call 'fn-oct-line-end 0 (fnn-live-octets))))
                 (first-line (try line-end)))
            (unless (and (integerp line-end) (< 0 line-end) (<= line-end (length incoming)))
              (fnn-fault "owner returned a malformed line end"))
            (if (eq (car first-line) :warm)
                (second first-line)
              (cons :fnn-extent-cold first-line))))))))

;;; The cold line's page, read OFF the owner mutex by its persistent worker
;;; (fnn-extent-prefetch: its pread holds no lock), waited for at most ACL2's
;;; dependency deadline (books/owner-time-bars.lisp fn-otb-dependency-step,
;;; `read-dependency-ms', 5,000 ms by default: the operator's limit row is not
;;; in the configuration yet, so the default is passed as nil).  :serve --
;;; the page came: the read runs again, warm.  :unavailable -- the line is
;;; answered by ACL2 (fnn-owner-unavailable-line): 403, the line consumed,
;;; the session unchanged; cancellation revokes cache publication, while the
;;; worker retains its buffer/fd ownership until its actual completion. A
;;; store fault (short read, digest mismatch) stops the owner even if late.
;;; Other connections are served meanwhile: nothing here
;;; holds the owner mutex or the realizer's lock.
(defun fnn-owner-cold-enqueue-locked (service read)
  (let ((tail (fnn-owner-service-cold-tail service)))
    (setf (fnn-owner-cold-read-prev read) tail
          (fnn-owner-cold-read-next read) nil
          (fnn-owner-cold-read-queuedp read) t)
    (if tail (setf (fnn-owner-cold-read-next tail) read)
      (setf (fnn-owner-service-cold-head service) read))
    (setf (fnn-owner-service-cold-tail service) read))
  read)

(defun fnn-owner-cold-remove-locked (service read)
  (when (fnn-owner-cold-read-queuedp read)
    (let ((prev (fnn-owner-cold-read-prev read))
          (next (fnn-owner-cold-read-next read)))
      (if prev (setf (fnn-owner-cold-read-next prev) next)
        (setf (fnn-owner-service-cold-head service) next))
      (if next (setf (fnn-owner-cold-read-prev next) prev)
        (setf (fnn-owner-service-cold-tail service) prev))
      (setf (fnn-owner-cold-read-prev read) nil
            (fnn-owner-cold-read-next read) nil
            (fnn-owner-cold-read-queuedp read) nil))))

(defun fnn-owner-cold-issue-locked (service cid entry)
  "Validated descriptor capture, owner mutex held, before retirement."
  (multiple-value-bind (token word worker) (apply #'fnn-extent-issue-read cid entry)
    (if (and word (not (eq word :admitted))) word
      (fnn-owner-cold-enqueue-locked
       service (%make-fnn-owner-cold-read :token token :worker worker)))))

(declaim (notinline fnn-owner-cold-transfer-result-locked))
(defun fnn-owner-cold-transfer-result-locked (read)
  "Private owner activation, owner and extent locks held. Transfer a verified
vector or discard it, then clear its slot. Return no vector/result-container
alias; the caller may refund only AFTER this activation has returned."
  (let* ((token (fnn-owner-cold-read-token read))
         (worker (fnn-owner-cold-read-worker read))
         (result (and worker (fnn-cold-worker-result worker)))
         (condition (and (typep result 'serious-condition) result))
         (verdict (if condition :error (if token (first result) :ok)))
         (octets (and (not condition) (second result)))
         (hold (fnn-developer-selector "FN_NATIVE_PAGE_IO_HOLD"))
         (mode (fnn-developer-selector "FN_NATIVE_PAGE_IO_RESULT"))
         (answer :stale) (settled-io nil) (cachedp nil) (evicted nil))
    (when (equal mode "stale")
      (fnn-err "PAGE-IO stale answer=~s" (fnn-extent-complete-read nil :ok)))
    (if token (multiple-value-setq (answer settled-io) (fnn-extent-complete-read token verdict))
      (setq answer :publish))
    (when hold (fnn-err "PAGE-IO settled token=~s answer=~s" token answer))
    (when (equal mode "duplicate")
      (fnn-err "PAGE-IO duplicate answer=~s" (fnn-extent-complete-read token verdict)))
    (when (and token (eq answer :publish))
      (destructuring-bind (id cid file eoff elen trailer) token
        (declare (ignore id cid))
        (multiple-value-setq (cachedp evicted)
          (fnn-extent-cache-store file eoff elen trailer octets token))))
    ;; No caller has received RESULT: readiness is a predicate, never a
    ;; borrowing getter. An exceptional transfer keeps the slot and charge.
    (when worker (setf (fnn-cold-worker-result worker) nil))
    (values answer settled-io cachedp evicted condition)))

(defun fnn-owner-cold-result-locked (service read)
  "The private worker and owner transfer activations relinquish their vector
before exact settlement releases a charge. Owner->extent serializes it."
  (when (fnn-owner-cold-read-settledp read)
    (return-from fnn-owner-cold-result-locked (fnn-owner-cold-read-outcome read)))
  (let ((token (fnn-owner-cold-read-token read))
        (condition nil) (answer :stale) (settled-io nil) (cachedp nil) (evicted nil))
    (sb-thread:with-mutex (*fnn-extent-lock* :wait-p t)
      (multiple-value-setq (answer settled-io cachedp evicted condition)
        (fnn-owner-cold-transfer-result-locked read))
      ;; The helper's vector-bearing activation is gone. Only a charged
      ;; cache owns a successful retained vector; cancelled/error data is gone.
      (fnn-owner-cold-remove-locked service read)
      (when token
        (when (eq answer :stale) (fnn-fault "returned cold job lost its exact I/O owner"))
        (fnn-extent-executor-commit (fnn-owner-cold-read-worker read) settled-io token cachedp))
      (setf (fnn-owner-cold-read-settledp read) t
            (fnn-owner-cold-read-worker read) nil)
      (fnn-extent-cache-release evicted))
    (when (and (consp answer) (eq (car answer) :fault))
      (unless condition
        (setq condition
              (make-condition 'fnn-extent-fault
                              :message (case (second answer)
                                         (:read "arena-extent-read: issued read was short")
                                         (:trailer "arena-extent-trailer: issued read commitment differs")
                                         (:digest "arena-extent-digest: issued read digest differs")
                                         (t "arena-extent-verdict: issued read failed")))))
      (incf (third *fnn-extent-stats*)))
    (setf (fnn-owner-cold-read-outcome read) (or condition t))
    (fnn-owner-release-pending-extents-locked)
    (when condition
      (unless *fnn-owner-last-fault*
        (setq *fnn-owner-last-fault*
              (format nil "owner core/store fault; process stopped: ~a" condition)))
      (fnn-err "owner core/store fault; process stopped: ~a" condition)
      (error condition))
    t))

(defun fnn-owner-cold-ready-p (read)
  "Owner held. Observe relinquishment without lending the result to a caller."
  (let ((worker (fnn-owner-cold-read-worker read)))
    (sb-thread:with-mutex (*fnn-extent-lock*)
      (and worker (fnn-extent-executor-observe-returned worker)))))

(defun fnn-owner-cold-settle-locked (service read)
  (if (fnn-owner-cold-read-settledp read)
      (fnn-owner-cold-read-outcome read)
    (when (or (null (fnn-owner-cold-read-token read)) (fnn-owner-cold-ready-p read))
      (fnn-owner-cold-result-locked service read))))

(defun fnn-owner-cold-settle (service read)
  "A returned job, not a timeout, can transfer its result and release credit."
  (handler-case
      (fnn-owner-serialized service nil
                            (lambda () (fnn-owner-cold-settle-locked service read)) :control)
    (serious-condition (condition)
      (ignore-errors (fnn-owner-fault-service service nil condition))
      condition)))

(defun fnn-owner-cold-reap (service)
  "One bounded round-robin quantum; no scan of all live or completed reads."
  (handler-case
      (dotimes (i (fnn-core 'fn-pio-reap-work))
        (declare (ignorable i))
        (fnn-owner-serialized
         service nil
         (lambda ()
           (let ((read (fnn-owner-service-cold-head service)))
             (when read
               (fnn-owner-cold-settle-locked service read)
               (when (fnn-owner-cold-read-queuedp read)
                 (fnn-owner-cold-remove-locked service read)
                 (fnn-owner-cold-enqueue-locked service read)))))
         :control))
    (fnn-store-error (condition)
      (unless (fnn-owner-service-stopping service)
        (fnn-owner-fault-service service nil condition)))
    (serious-condition (condition)
      (fnn-owner-fault-service service nil condition))))

(defun fnn-owner-cold-shutdown (service)
  "Clients have stopped. Join the persistent workers before shared close."
  (fnn-extent-executor-stop)
  ;; No worker activation can issue or touch a descriptor now. Its slot may
  ;; still own the private result until the following owner transfer returns.
  ;; All reads remain funded until this exact settlement, including errors.
  (loop for read = (fnn-owner-service-cold-head service) while read do
    (sb-thread:with-mutex ((fnn-owner-service-lock service))
      (unless (or (null (fnn-owner-cold-read-token read))
                  (fnn-extent-executor-returned-p (fnn-owner-cold-read-worker read)))
        (fnn-fault "cold worker exited without relinquishing its job"))
      (handler-case (fnn-owner-cold-settle-locked service read)
        (serious-condition (condition)
          (unless (fnn-owner-cold-read-settledp read) (error condition)))))))

(defun fnn-owner-cold-await (service read)
  "Await an already-captured read off owner lock. Return the core dependency
word and its clock observations; the caller retains its logical cursor/pin.
A refusal or timeout never authorizes releasing the physical I/O lease."
  (when (keywordp read) (return-from fnn-owner-cold-await (values read 0 0 nil)))
  (let* ((since (fnn-owner-monotonic-ms)) (limit nil)
         (token (fnn-owner-cold-read-token read))
         (worker (fnn-owner-cold-read-worker read)))
    (unless token
      (fnn-owner-cold-settle service read)
      (return-from fnn-owner-cold-await (values :serve since since limit)))
    (unwind-protect
         (loop
           (let* ((now (fnn-owner-monotonic-ms))
                  (done (or (fnn-owner-cold-read-settledp read)
                            (fnn-extent-executor-returned-p worker)))
                  (decision (fnn-core 'fn-otb-dependency-step since now limit done)))
             (cond ((eq decision :serve)
                    (let ((got (fnn-owner-cold-settle service read)))
                      (when (typep got 'serious-condition) (error got)))
                    (return (values :serve since now limit)))
                   ((eq decision :unavailable)
                    (fnn-extent-cancel-read token)
                    (return (values :unavailable since now limit)))
                   ((and (consp decision) (eq (car decision) :wait)
                         (integerp (second decision)) (plusp (second decision)))
                    (fnn-extent-executor-wait worker (/ (second decision) 1000)))
                   (t (fnn-fault "owner returned a malformed dependency step")))))
      (fnn-extent-cancel-read token))))

(defun fnn-owner-cold-line (service cid incoming socket class peerp entry read)
  (declare (ignore entry))
  (multiple-value-bind (word since now limit) (fnn-owner-cold-await service read)
    (case word
      (:serve (fnn-owner-handle-chunk service cid incoming socket class peerp))
      (:unavailable (fnn-owner-unavailable-line service cid incoming since now limit class))
      (otherwise (fnn-owner-resource-unavailable-line service cid incoming word class)))))

;;; ACL2's answer to the cold line past its deadline (host/owner-host.lisp
;;; fn-owner-unavailable-line-at over fn-ocln-unavailable-span), under the
;;; owner mutex; the values are fnn-owner-handle-chunk-read's.
(defun fnn-owner-unavailable-line (service cid incoming since now limit class)
  (fnn-owner-serialized
   service cid
   (lambda ()
     (fnn-octets-fill incoming)
     (let ((step (fnn-core-buffer-state 'fn-owner-unavailable-line-at cid 0 since now limit)))
       (when (eq step :unknown)
         (fnn-refuse "owner no longer knows connection ~d" cid))
       (unless (fnn-core 'fn-splan-step-p step)
         (fnn-fault "owner returned a malformed cold-line step ~a" step))
       (fnn-owner-refresh-read-octets service)
       (let ((consumed (fnn-core 'fn-splan-step-consumed step)))
         (unless (and (integerp consumed) (< 0 consumed) (<= consumed (length incoming)))
           (fnn-fault "owner returned a malformed cold-line count"))
         (values (fnn-core 'fn-splan-step-plan step nil nil)
                 (or (fnn-core 'fn-splan-step-closep step)
                     (fnn-core 'fn-splan-step-exposure-close step))
                 (fnn-core 'fn-splan-step-handshake-owed step)
                 consumed nil nil))))
   class))


(defun fnn-owner-resource-unavailable-line (service cid incoming word class)
  "ACL2's named admission refusal; never fabricate a deadline observation."
  (fnn-owner-serialized
   service cid
   (lambda ()
     (fnn-octets-fill incoming)
     (let ((step (fnn-core-buffer-state 'fn-owner-resource-unavailable-line-at cid 0 word)))
       (when (eq step :unknown) (fnn-refuse "owner no longer knows connection ~d" cid))
       (unless (fnn-core 'fn-splan-step-p step)
         (fnn-fault "owner returned a malformed resource refusal step ~a" step))
       (fnn-owner-refresh-read-octets service)
       (let ((consumed (fnn-core 'fn-splan-step-consumed step)))
         (unless (and (integerp consumed) (< 0 consumed) (<= consumed (length incoming)))
           (fnn-fault "owner returned a malformed resource refusal count"))
         (values (fnn-core 'fn-splan-step-plan step nil nil)
                 (or (fnn-core 'fn-splan-step-closep step)
                     (fnn-core 'fn-splan-step-exposure-close step))
                 (fnn-core 'fn-splan-step-handshake-owed step)
                 consumed nil nil))))
   class))


(defun fnn-owner-handle-chunk-read (service cid incoming socket class &optional peerp)
  "Run one owner read and its serial writer drain under the service mutex,
admitted by the gate as CLASS (:reader, or :transit for a peer connection;
PEERP: a peer connection's read, admitted as :reader while the disk sheds by
fnn-owner-peer-read-class).

Returns (values PLAN CLOSING STARTTLS CONSUMED REDEEMED SUBMITTED), PLAN the
immutable render plan of this step's whole reply (books/served-plan.lisp
fn-splan-step-plan: the step's effects, then the drain's completion, the
redeem reply and the exposure close), which the caller renders and writes
OFF the mutex (host/native/mux.lisp fnn-mux-queue-plan and fnn-mux-flush
through fnn-owner-render-next); or (values :defer MS) when ACL2's work
budget defers this step (PRF-161 fn-exp-charge, decided in the same critical
section as the step it admits: one gate pass per read, not two): the caller
waits MS and calls again with the same INCOMING.

SOCKET is this connection's own socket.  When the drained outcome is
uncertain the service stops here, under the mutex, but SOCKET is spared so
the caller can deliver the ACL2-rendered uncertain reply before closing it
(campaign W1, 2026-09-24: the stop shut this socket first, the reply met
EPIPE and the client saw a bare close)."
  (fnn-owner-serialized
   service cid
   (lambda ()
     (let ((admit :admit) (sched nil))
     (block step
       ;; One reading per read, before the transition that decides under it.
       ;; books/owner.lisp fn-own-open: "The injection clock is not pinned:
       ;; fn-own-read supplies the owner's current observation with every read,
       ;; so each submission is injected at its own time (RFC 5537 section
       ;; 3.4)."  Without this the owner's current observation is whatever the
       ;; process started with, and every article of a run carries one Date.
       (fnn-owner-advance-clock)
       ;; Lane time-model-2: the write admission at this read's recorded
       ;; time (the :served clock event above): while the disk sheds, the
       ;; read runs with posting not permitted (a POST command is answered
       ;; 440 before its article: host/owner-host.lisp fn-owner-chunk-span)
       ;; and a submitted POST is shed below (441).
       ;; Lane log-leftovers: the gate's value itself goes to the read
       ;; (fn-otm-read-span: the admission and the disk's reason lines are
       ;; ACL2's over it), read once here.
       (setq sched (fnn-owner-gate-sched-value service)
             admit (fnn-core 'fn-otm-admit-post sched))
       (unless (member admit '(:admit :shed))
         (fnn-fault "owner returned a malformed admission ~a" admit))
       ;; PKT-858: a peer's read admitted as :reader runs only while the disk
       ;; sheds (fn-otm-peer-read-proceeds-p): recovered since the class was
       ;; chosen, it is deferred and retried as transit (a reader-class read
       ;; of the live node without the posture could reveal the batch in
       ;; flight).
       (unless (or (not peerp) (fnn-core 'fn-otm-peer-read-proceeds-p class sched))
         (return-from step (values :defer 1)))
       ;; PRF-161: the work budget (books/public-exposure.lisp fn-exp-charge):
       ;; :proceed, or the milliseconds to wait.  Waiting reads nothing more
       ;; from this socket, so the client meets TCP backpressure and nothing
       ;; it sent is dropped or cut.
       (let ((charge (fnn-owner-core 'fn-owner-exposure-charge cid)))
         (cond ((eq charge :proceed))
               ((and (integerp charge) (> charge 0))
                (return-from step (values :defer charge)))
               (t (fnn-fault "owner returned a malformed exposure charge"))))
       ;; The observation goes to the core in the octet buffer
       ;; (books/octets-stobj.lisp): filled once here from the byte vector and
       ;; read in place by span (books/wire-span.lisp fn-wire-feed-span through
       ;; books/served-span.lisp fn-scar-ocfg-read-span), never as a list of
       ;; its octets.  The buffer is free here: the attempt below fills it
       ;; again for the payload after this read has returned, under the same
       ;; mutex (fnn-owner-attempt).  The reply is NOT rendered into it: the
       ;; step's typed result carries the effects, the plan the caller
       ;; renders off the mutex.
       (fnn-octets-fill incoming)
       (let ((step (fnn-owner-chunk-span-no-io cid incoming sched)))
         ;; Row A4 (c): the first line needs a page not in memory; its read
         ;; happens off the mutex (fnn-owner-handle-chunk, fnn-owner-cold-line).
         (when (and (consp step) (eq (car step) :fnn-extent-cold))
           (let ((entry (cdr step)))
             ;; Owner->extent lock order: issue at the validated capture,
             ;; before releasing the mutex that excludes file retirement.
             (return-from step
               (values :fnn-extent-cold entry
                       (fnn-owner-cold-issue-locked service cid entry)))))
         (when (eq step :unknown)
           (fnn-refuse "owner no longer knows connection ~d" cid))
         (fnn-owner-refresh-read-octets service)
         (unless (fnn-core 'fn-splan-step-p step)
           (fnn-fault "owner returned a malformed served step"))
         ;; Capture the response's lifetime before leaving this quantum.
         ;; Reclaim's swap excludes every live arena reader, including this
         ;; pin while a later cursor quantum still uses the original catalog.
         ;; :await and :redeem keep it too; their plans contain this STEP.
         (fnn-owner-response-pin service cid)
         ;; One ACL2-rendered line per 441 this read sends (books/owner-log.lisp
         ;; fn-olog-served-refusal-lines): a POST refused before it became a
         ;; submission has no outcome line of its own.
         (let ((lines (fnn-core 'fn-splan-step-refusal-lines step)))
           (unless (every #'fnn-octet-list-p lines)
             (fnn-fault "owner returned malformed refusal log lines"))
           (dolist (line lines) (fnn-log-line line)))
         (let ((closing (fnn-core 'fn-splan-step-closep step))
               ;; T: a TLS handshake owed (382); :DEFLATE: the COMPRESS layer
               ;; owed (206, RFC 8054), read off the session
               ;; (host/owner-host.lisp fn-owner-compress-owed).
               (starttls (or (and (fnn-core 'fn-splan-step-handshake-owed step) t)
                             (let ((alg (fnn-owner-core 'fn-owner-compress-owed cid)))
                               (unless (member alg '(nil :deflate))
                                 (fnn-fault "owner returned a malformed compression layer"))
                               alg)))
               (submitted (fnn-core 'fn-splan-step-submittedp step))
               (consumed (fnn-core 'fn-splan-step-consumed step))
               (completion nil)
               (uncertain nil)
               (redeem nil))
           (unless (and (integerp consumed) (<= 0 consumed (length incoming)))
             (fnn-fault "owner returned malformed receive-prefix count"))
           ;; Lane commit-onto-log: the submission stays queued
           ;; for the next commit quantum, which drains it with every other
           ;; queued one and fences the log once; this connection's reply
           ;; is built when its completion arrives (fnn-owner-await-done).
           ;; A logical connection (the pull feed: no socket) waits for
           ;; nothing: the queued submissions, its own last, are committed
           ;; now, in this quantum, and its completion read back.
           (when (and submitted (fnn-owner-service-batching service) (null socket))
             (fnn-owner-commit-queued-locked service)
             (let ((done (fnn-owner-take-done service cid)))
               (cond ((fnn-octet-list-p done) (setq completion done))
                     ((and (consp done) (eq (car done) :close))
                      (setq completion (cdr done) uncertain t))
                     (t (setq completion nil uncertain t))))
             (setq submitted nil))
           (when (and submitted (fnn-owner-service-batching service))
             ;; Lane time-model (PRF-311): while the disk is slow (a barrier
             ;; pending past its deadline at this quantum's recorded time,
             ;; books/owner-time-model.lisp fn-otm-admit-post), the queued
             ;; served POSTs -- this one included -- are refused try-later
             ;; with ACL2's reason line, nothing stored; each reply is
             ;; delivered as a completion (this connection's is taken at
             ;; once by its await).  Otherwise the submission waits for the
             ;; next batch, as before.
             (when (eq admit :shed)
               (fnn-owner-shed-queued-locked service))
             (fnn-owner-note-queued service)
             (return-from step
               (values :await step
                       (and (fnn-owner-core 'fn-acct-host-owner-redeem-waitingp cid) t)
                       closing starttls consumed)))
           (when submitted
             (multiple-value-bind (reply-cid done stop)
                 (multiple-value-prog1 (fnn-owner-drain-one service)
                   ;; Lane credits (fn-mca-settle): written synchronously.
                   (fnn-owner-action 'fn-owner-credits-settle))
               (when (and reply-cid (not (= reply-cid cid)))
                 (fnn-fault "writer drained a different connection"))
               (setq completion done uncertain stop)))
           ;; PRF-164: an XREDEEM PASS left this connection holding; the
           ;; owner plans and publishes, and only then renders 281 or 482 --
           ;; in its OWN quantum (fnn-owner-handle-chunk), not this reader's.
           (when (and (not uncertain)
                      (fnn-owner-core 'fn-acct-host-owner-redeem-waitingp cid))
             (setq redeem :pending))
           (when uncertain
             (fnn-owner-stop-service-locked service +fnn-exit-uncertain+ socket))
           ;; PRF-161: the step reached this address's failed-login limit
           ;; (fn-exp-observe): ACL2's 400 (the plan's last effect), then the
           ;; close.
           (when (fnn-core 'fn-splan-step-exposure-close step)
             (setq closing t))
           ;; PKT-600 (PRF-213): a read that emitted a submission yielded after
           ;; its article (books/served-tls-prefix.lisp fn-served-feed-counted,
           ;; the span fold books/served-span.lisp fn-scar-feed-span), so the
           ;; caller feeds the rest of INCOMING as the next read, after this
           ;; read's reply and the article's outcome are sent.
           (if (eq redeem :pending)
               (values :redeem step completion (or closing uncertain) starttls
                       consumed submitted)
             (values (fnn-core 'fn-splan-step-plan step completion nil)
                     (or closing uncertain) starttls consumed nil
                     submitted)))))))
   class))

(defun fnn-owner-exposure-idle (service cid &optional (class :reader))
  (let ((answer (fnn-owner-serialized
                 service cid
                 (lambda ()
                   (fnn-owner-advance-clock)
                   (fnn-owner-action 'fn-owner-exposure-idle cid))
                 class)))
    (unless (member answer '(:keep :close))
      (fnn-fault "owner returned a malformed idle decision"))
    answer))

(defun fnn-owner-receive (service fd channel seconds)
  "Read through the active transport.  Before TLS, MSG_PEEK is used only when
a loaded context makes STARTTLS reachable; ACL2 then chooses the exact prefix."
  (cond (channel (fnn-tls-read channel seconds))
        ((fnn-owner-service-tls-context service)
         (fnn-tls-peek-plaintext fd seconds))
        (t (fnn-recv fd seconds))))

(defun fnn-owner-send (fd channel octets seconds)
  (if channel
      (fnn-tls-send-all channel octets seconds)
    (fnn-send-all fd octets seconds)))

(defun fnn-owner-socket-address (service socket)
  "Return only the kernel family/address observation; ACL2 resolves its role."
  (multiple-value-bind (address port)
      (fnn-owner-connection-call
       service :peer-address
       (lambda () (sb-bsd-sockets:socket-peername socket)))
    (declare (ignore port))
    (unless (and (vectorp address)
                 (member (length address) '(4 16)))
      (fnn-fault "socket returned a malformed peer address"))
    (values (if (= (length address) 4) :inet :inet6)
            (coerce address 'list))))

;;; A connection is served by one of the service's I/O loops
;;; (host/native/mux.lisp fnn-mux-adopt), not a thread of its own: the
;;; worker this file used to start per connection held a control stack and
;;; runtime regions for the connection's whole life (PKT-605).  Everything
;;; the worker did, in its order and under its handlers, is the loop's
;;; connection record now.
(defun fnn-owner-launch-client (service socket &optional implicit-tls)
  "Register the socket with a loop before it can enter the owner core; while
the node retires (row S9), refuse it by name instead."
  (if (fnn-owner-service-retire service)
      (fnn-owner-retire-refuse socket implicit-tls)
    (fnn-mux-adopt service socket implicit-tls)))

;;; Row S9: while the node retires every new connection is refused by name
;;; (books/native-retire.lisp): on a plain listener RFC 3977's 502 greeting,
;;; written under a one-second deadline, then the close; on an implicit-TLS
;;; listener the close alone (no plaintext into a TLS port).  The log names
;;; each refusal.  A client gone before the line is written changes nothing.
(defun fnn-owner-retire-refuse (socket implicit-tls)
  (unwind-protect
       (unless implicit-tls
         (handler-case
             (fnn-send-all (fnn-socket-fd socket) (fnn-core 'fn-nret-refusal-line) 1)
           (error () nil)))
    (handler-case (sb-bsd-sockets:socket-close socket) (error () nil)))
  (fnn-log-line (fnn-core 'fn-nret-refused-log-line (and implicit-tls t))))

;;; Row S9: `retire [--drain SECONDS]' on the running owner.  The request
;;; (books/native-retire.lisp fn-nret-request) starts the retire: from then
;;; on new connections are refused by name (host/native/owner.lisp
;;; fnn-owner-launch-client), the pull service stops, and at each accept-loop
;;; tick ACL2 decides from a scheduler snapshot and the owner's feed table
;;; whether the drain goes on (books/owner-retire.lisp fn-oret-drain-step,
;;; which never waits past the window).  When it ends the owner takes its
;;; final checkpoint, writes ACL2's report to STORE/retire-report.txt (fenced
;;; before the stop, so the operator reads it from the stopped node) and
;;; stops as a SIGTERM stops it: the POSTs in flight answered first
;;; (fnn-owner-drain-service), then the fence.
(defun fnn-owner-retire-report-path (service)
  (fnn-join (fnn-store-root (fnn-owner-service-store service))
            (fnn-octets-string (fnn-octets (fnn-core 'fn-nret-report-file-name)))))

(defun fnn-owner-retire-begin (service seconds)
  (let* ((s0 (progn (fnn-owner-space-preobserve service t)
                    (fnn-owner-sched-snapshot service)))
         (answer
           (fnn-with-roster (service)
             (let ((a (fnn-core 'fn-nret-begin-answer
                                (and (fnn-owner-service-retire service) t))))
               (when (eq (first a) :accepted)
                 (setf (fnn-owner-service-retire service) (list s0 seconds)))
               a))))
    (unless (and (consp answer) (member (first answer) '(:accepted :refused)))
      (fnn-fault "owner returned a malformed retire answer ~a" answer))
    (when (eq (first answer) :accepted)
      ;; A report an earlier retire left (the node was started again) is
      ;; not this retire's.
      (handler-case (sb-posix:unlink (fnn-owner-retire-report-path service))
        (sb-posix:syscall-error () nil))
      ;; NEWNEWS pulling is an optional runtime extension: the DTN image
      ;; does not load pull-service.lisp. Stop its I/O only when that
      ;; extension is present; ACL2's retire decision is the same in both.
      (when (fboundp 'fnn-pull-service-wake)
        (funcall (symbol-function 'fnn-pull-service-wake) service))
      (fnn-log-line (fnn-core 'fn-nret-begin-log-line seconds)))
    (list :reason (first answer) (second answer))))

(defun fnn-owner-retire-write-report (service report)
  "Write REPORT (ACL2's octets) as STORE/retire-report.txt: staged, fenced,
renamed into place, the directory fenced."
  (unless (fnn-octet-list-p report)
    (fnn-fault "owner returned a malformed retire report"))
  (let* ((store (fnn-owner-service-store service))
         (final (fnn-owner-retire-report-path service))
         (stage (fnn-join (fnn-staging store)
                          (format nil ".retire-~d-~a" (sb-posix:getpid) (fnn-random-hex 12))))
         (fd (fnn-open stage (logior sb-posix:o-wronly sb-posix:o-creat sb-posix:o-excl) #o600)))
    (unwind-protect (progn (fnn-write-all fd (fnn-octets report))
                           (fnn-fsync-file fd))
      (fnn-close fd))
    (fnn-replace stage final)
    (fnn-fsync-dir (fnn-store-root store))))

(defun fnn-owner-maybe-retire (service)
  "One drain decision of a retiring owner (row S9), at an accept-loop tick."
  (let ((retire (fnn-owner-service-retire service)))
    (when (and retire (not *fnn-sigterm-requested*)
               (not (fnn-owner-service-stopping service)))
      (destructuring-bind (s0 seconds) retire
        (let* ((s (progn (fnn-owner-space-preobserve service t)
                         (fnn-owner-sched-snapshot service)))
               (step (fnn-owner-serialized
                      service nil
                      (lambda () (fnn-owner-core 'fn-owner-retire-step s0 s seconds))
                      :inspect)))
          (unless (member step '(:wait :drained :deadline))
            (fnn-fault "owner returned a malformed retire step ~a" step))
          (unless (eq step :wait)
            ;; The final checkpoint, as `store checkpoint' asks it.
            (fnn-owner-compaction-request service)
            (let ((report (fnn-owner-serialized
                           service nil
                           (lambda () (fnn-owner-core 'fn-owner-retire-report step))
                           :inspect)))
              (fnn-owner-retire-write-report service report)
              (fnn-log-line (fnn-core 'fn-nret-end-log-line step)))
            ;; The stop a SIGTERM takes (host/native/owner.lisp): the accept
            ;; loop returns, the POSTs in flight are answered, the fence.
            (setf *fnn-sigterm-requested* t)))))))

(defun fnn-owner-wait-workers (service)
  "Join client workers before closing any shared journal or Store object."
  (loop
    (let ((workers
            (fnn-with-roster (service)
              (copy-list (fnn-owner-service-workers service)))))
      (when (null workers) (return))
      (dolist (worker workers) (sb-thread:join-thread worker)))))

;;; Garbage between collections in the owner process.  SBCL's default
;;; trigger is 5% of the dynamic space the launcher reserves (32,000 MB,
;;; so 1,600 MiB): the heap census of 2026-09-25
;;; (planning/evidence/rep-heap-2026-09-25.md) found that headroom to be the
;;; largest term of the owner's resident set at every size measured, 1.4 to
;;; 1.6 GiB of dead objects on top of a live heap of 0.25 to 0.52 GB.  During
;;; recovery and a checkpoint publication the owner uses io.lisp's
;;; fnn-gc-nursery-octets (64 MiB, less at a reservation under 1 GiB).  This
;;; bounds collection work and dead memory, not data: the live heap is the
;;; store's and grows with it; only the garbage allowed to pile up between
;;; two collections is capped.  It decides nothing ACL2 decides.

;;; The trigger while the owner serves (HST-025, lane image-floor).  The open
;;; (recovery: the checkpoint decode and the suffix replay) and a checkpoint
;;; publication allocate in proportion to the retained history and keep
;;; fnn-gc-nursery-octets (PKT-316: a smaller trigger there slows the
;;; reopen).  A served command allocates in proportion to one request, so
;;; between accepts the garbage allowed to pile up is this much, and the
;;; owner's resident set is the live heap plus this, not plus 64 MiB.  It
;;; bounds dead memory and collection spacing, never data; it decides nothing
;;; ACL2 decides.
(defparameter +fnn-owner-service-nursery-octets+ (* 8 1024 1024))

(defun fnn-owner-service-nursery ()
  "Serving: the small trigger, unless a publication (which set the large one)
is running; the publication restores this one when it ends."
  (setf (sb-ext:bytes-consed-between-gcs) +fnn-owner-service-nursery-octets+))

(defun fnn-owner-release-recovery-garbage ()
  "Recovery is done and nothing is served yet: one full collection, after
which SBCL returns the pages the recovery's garbage occupied to the system
(a collection of the oldest generation remaps the free pages), so the
resident set the owner serves from is its live heap, not the recovery's
high-water mark.  Work proportional to the live heap, once per start."
  (sb-ext:gc :full t))

(defun fnn-owner-release-pending-extents-locked (&optional pin)
  "Release pending groups whose reader generations and issued I/O are clear.
Caller holds owner mutex; extent lock is acquired only after it."
  (let ((closed 0) (keep nil))
    (dolist (entry *fnn-extent-pending*)
      (if (fnn-arena-clear-p (car entry) pin)
          (multiple-value-bind (count owned) (fnn-extent-close (cdr entry))
            (incf closed count)
            (when owned (push (cons (car entry) owned) keep)))
        (push entry keep)))
    (setq *fnn-extent-pending* (nreverse keep))
    closed))

(defun fnn-owner-release-pending-extents (service)
  "Actual worker completion retries pending closes after dropping extent lock."
  (fnn-owner-gated (service :control)
    (fnn-owner-release-pending-extents-locked)))

(defun fnn-snapshot-source-root-acquire (service base-handle maintenance-lease)
  "Caller holds SERVICE's owner mutex while capturing BASE-HANDLE. Acquire
one exact checkpoint incarnation before releasing that mutex. The controller
already owns MAINTENANCE-LEASE; this token covers only physical retention."
  (declare (ignore service maintenance-lease))
  (sb-thread:with-mutex (*fnn-extent-lock*)
    (let ((file (fnn-core 'fn-hrs-h-file base-handle)))
      (destructuring-bind (word token &rest ignored)
          (fnn-core-page-read-pool 'fn-owner-page-file-pin file)
        (declare (ignore ignored))
        (unless (eq word :admitted) (fnn-refuse "snapshot root lease refused: ~a" word))
        token))))

(defun fnn-snapshot-source-root-ticket (service token)
  "Project the live root ticket through ACL2 while caller holds owner."
  (declare (ignore service))
  (sb-thread:with-mutex (*fnn-extent-lock*)
    (first (fnn-core-page-read-pool 'fn-owner-page-file-pin-ticket token))))

(defun fnn-snapshot-source-root-release (service token)
  "Controller has finished/joined all scans and relinquished their buffers.
Cancellation alone never invokes this release. Cleanup remains possible after
admission closes, so it takes the owner mutex directly rather than the gate."
  (sb-thread:with-mutex ((fnn-owner-service-lock service))
    (sb-thread:with-mutex (*fnn-extent-lock*)
      (unless (eq (first (fnn-core-page-read-pool 'fn-owner-page-file-unpin token)) :released)
        (fnn-fault "snapshot root lease release is stale")))
    (fnn-owner-release-pending-extents-locked)))

(define-condition fnn-snapshot-read-not-issued (fnn-store-io-refusal)
  ((word :initarg :word :reader fnn-snapshot-read-not-issued-word)
   (request :initarg :request :reader fnn-snapshot-read-not-issued-request)))

(define-condition fnn-snapshot-read-admission-uncertain (fnn-store-indeterminate)
  ((word :initarg :word :reader fnn-snapshot-read-admission-uncertain-word)
   (request :initarg :request :reader fnn-snapshot-read-admission-uncertain-request)
   (token :initarg :token :reader fnn-snapshot-read-admission-uncertain-token)))

(defun fnn-snapshot-source-issued-count (service root-token)
  "Caller holds owner; exact live root census, including legitimate zero."
  (declare (ignore service))
  (sb-thread:with-mutex (*fnn-extent-lock*)
    (fnn-core-page-read-pool 'fn-owner-page-file-issued-count root-token)))

(defun fnn-snapshot-source-read-page (service root-token request buffer-lease)
  "Read one exact page. Return vector, token, request, fresh ID, count, status.
Short/error observations remain owned for authcomplete's uncertain result;
BUFFER-LEASE is controller funding, never an independent refund right."
  (declare (ignore buffer-lease))
  (let ((fd nil) (offset nil) (count nil) (token nil) (base nil)
        (octets nil) (handed-off nil))
    (fnn-owner-gated (service :control)
      (sb-thread:with-mutex (*fnn-extent-lock*)
        (let ((file (first (fnn-core-page-read-pool 'fn-owner-page-file-pin-file root-token))))
          (setq base (gethash file *fnn-extent-bases*))
          (destructuring-bind (word read-file read-offset read-count read-token &rest ignored)
              (fnn-core-page-read-pool 'fn-owner-page-file-pin-read root-token request base)
            (declare (ignore ignored))
            (unless (eq word :admitted)
              (if (eq word :read-admission-uncertain)
                  (error 'fnn-snapshot-read-admission-uncertain :word word :request request
                         :token read-token :message "snapshot admitted read state is uncertain")
                (error 'fnn-snapshot-read-not-issued :word word :request request
                       :message "snapshot physical read not issued")))
            (setq token read-token offset read-offset count read-count
                  fd (gethash read-file *fnn-extent-fds*))))))
    (unwind-protect
         (progn
           (unless fd (fnn-fault "snapshot page lease lost its file"))
           (setq octets (make-array count :element-type '(unsigned-byte 8) :initial-element 0))
           (multiple-value-bind (got observed)
               (handler-case (values (fnn-extent-page-pread fd octets offset count) :ok)
                 (serious-condition () (values 0 :error)))
             (sb-thread:with-mutex (*fnn-extent-lock*)
               (destructuring-bind (word buffer-id result-count status)
                   (fnn-core-page-read-pool 'fn-owner-page-file-read-result
                                           root-token request base token got observed)
                 (unless (eq word :read-result)
                   (fnn-fault "snapshot page completion lost its exact lease"))
                 (setq handed-off t)
                 (values octets token request buffer-id result-count status)))))
      (unless handed-off
        ;; The syscall activation has returned; nothing has escaped to the
        ;; reader. Drop this alias before exact charged-buffer settlement.
        (setq octets nil)
        (sb-thread:with-mutex (*fnn-extent-lock*)
          (fnn-extent-discovery-release token))))))

(defun fnn-snapshot-source-page-release (token)
  "Auth/decoder cursor has cleared every vector alias before this call."
  (sb-thread:with-mutex (*fnn-extent-lock*)
    (fnn-extent-discovery-release token)))

(defun fnn-owner-release-extents (service store frames dropped-paths pin)
  "Give the disk blocks of the files a durable checkpoint publication dropped
back while serving (row Q16, PRF-930, books/extent-retire.lisp): register
the installed checkpoint with the extent realizer; per payload frame the
publication wrote (FRAMES, newest first: (EOFF ELEN HANDLES)), read the
frame's entry through the realizer (checked against its trailer) off the
mutex and reseat its payloads under the mutex (fn-xrt-reseat-checkpoint-
frame, KEYSTONE fn-xrt-reseat-frame-keeps-the-arena); retire the dropped
segments (DROPPED-PATHS) and the previous checkpoint.  Then, in ONE mutex
hold, the retired files ACL2 finds quiet (fn-xrt-quiet-files over the
arena's file count column, one read per file: KEYSTONE fn-xrt-quiet-files-
are-unnamed) become pending at a fresh arena-reader stamp S: a reader that
pins after S never sees an entry naming them.  Every pending group whose
stamp no other reader is pinned at or below (fnn-arena-clear-p S PIN, PIN
this thread's own pin) is closed.  Runs on a thread that is itself an
off-mutex arena reader pinned at PIN.  A failure leaves the files retired
or pending (closed by a later release) and serving continues."
  (let ((arena (fnn-live-arena)) (new-id nil) (reseated 0) (incomplete 0) (closed 0)
        (named-detail nil))
    (handler-case
        (progn
          (setq new-id (fnn-extent-register (fnn-state-checkpoint-path store)))
          (let ((drop-ids (fnn-extent-ids-of-paths dropped-paths)))
            (fnn-owner-gated (service :control)
              (setq *fnn-extent-retired*
                    (sort (remove-duplicates
                           (append drop-ids
                                   (and *fnn-extent-checkpoint-id*
                                        (list *fnn-extent-checkpoint-id*))
                                   *fnn-extent-retired*))
                          #'<)
                    *fnn-extent-checkpoint-id* new-id)))
          (dolist (f (reverse frames))
            (destructuring-bind (eoff elen handles) f
              ;; A fresh read (no descriptor names the frame yet): the frame
              ;; and its trailer, self-consistency checked; ACL2 makes the
              ;; descriptors from the frame's own trailer, held in the buffer
              ;; after the prefix (fn-xrt-reseat-one; lane extent-identity).
              (multiple-value-bind (octets lease)
                  (sb-thread:with-mutex (*fnn-extent-lock* :wait-p t)
                    (fnn-extent-entry-fresh new-id eoff elen))
                (unwind-protect
                     (fnn-owner-gated (service :control)
                       (let ((st (fnn-live-octets-pub)))
                         (setf (svref st 0) octets (svref st 1) (length octets))
                         (unwind-protect
                              (let ((answer (fnn-call 'fn-xrt-reseat-checkpoint-frame
                                                      handles new-id eoff elen st arena)))
                                (if (eq (first answer) t) (incf reseated) (incf incomplete)))
                           (setf (svref st 1) 0
                                 (svref st 0) (make-array 0 :element-type '(unsigned-byte 8))))))
                  ;; The publication buffer no longer aliases OCTETS. A
                  ;; scheduling refusal or reseat fault reaches this too.
                  (setq octets nil)
                  (sb-thread:with-mutex (*fnn-extent-lock* :wait-p t)
                    (fnn-extent-discovery-release lease))))))
          (fnn-owner-gated (service :control)
            ;; fnn-call answers the values as a list: the quiet set is its
            ;; first (the whole list was taken for the set once, so no
            ;; dropped file ever closed: KEYSTONE fn-xrt-dropped-file-is-
            ;; released says which do).
            (let ((quiet (first (fnn-call 'fn-xrt-quiet-files *fnn-extent-retired*
                                          (fnn-log-member-files (fnn-store-log store))
                                          arena))))
              (unless (and (listp quiet) (every #'integerp quiet))
                (fnn-fault "ACL2 returned a malformed quiet set"))
              (when quiet
                (setq *fnn-extent-pending*
                      (append *fnn-extent-pending* (list (cons (fnn-arena-stamp) quiet)))
                      *fnn-extent-retired* (set-difference *fnn-extent-retired* quiet)))
              (incf closed (fnn-owner-release-pending-extents-locked pin))
              ;; Each retired file still named, and by what: (ID COUNT LOG),
              ;; COUNT the extent column's entries naming it, LOG whether a
              ;; log member in flight or fenced names it.
              (let ((members (fnn-log-member-files (fnn-store-log store))))
                (setq named-detail
                      (loop for id in *fnn-extent-retired*
                            collect (list id (first (fnn-call 'fn-arx-file-count id arena))
                                          (if (member id members) 1 0)))))))
          (fnn-err "CHECKPOINT release reseated=~d incomplete=~d closed=~d retired=~d open=~d~@[ held=~(~a~)~]~@[ named=~{~{~d:~d:~d~}~^,~}~]"
                   reseated incomplete closed
                   (+ (length *fnn-extent-retired*)
                      (reduce #'+ *fnn-extent-pending* :key (lambda (e) (length (cdr e)))))
                   (fnn-extent-open-count)
                   (cond (*fnn-extent-retired* :named) (*fnn-extent-pending* :pending))
                   named-detail))
      (serious-condition (e)
        (fnn-err "CHECKPOINT release failed (files stay retired): ~a" e)))))

(defun fnn-owner-publish-captured (service captured &optional position pin)
  "The publication's thread: ACL2's fn-ock-next-checkpoint over the values
captured under the owner mutex (NEXT, the capture of the history at the
capture point: fn-ock-next-checkpoint-is-the-capture), then fn-ockp-setup
(books/owner-checkpoint-pipeline.lisp: the schema-3 tables of NEXT, the
file's length estimated from the metadata without encoding, and the
decision BY NAME before anything is allocated: past the profile's
checkpoint budget or the free space less the maintenance reserve the
publication is deferred, nothing is written, serving continues), then the
batch loop (fnn-checkpoint-write-steps: fn-ockp-step over the PUBLICATION
buffer fnn-live-octets-pub, its own stobj, each step's frames written
through fn-bs-scp-program's staged file before the next), all outside the
mutex; then fn-owner-sco-publication-done under it.  A failed write leaves
the old checkpoint (or, at and after the rename, the old or the new one:
the crash keystone) and serving continues."
  ;; The publication allocates in proportion to the history: the open's
  ;; trigger while it runs, the service trigger again when it ends.
  (setf (sb-ext:bytes-consed-between-gcs) (fnn-gc-nursery-octets))
  ;; It reads the live arena outside the owner's mutex: no staged page
  ;; retired while it runs is released until it ends (host/native/io.lisp
  ;; fnn-log-reseat-fenced, books/arena-reader-pins.lisp).  Its caller
  ;; pinned the generation PIN under the mutex, before this thread existed
  ;; (fnn-owner-maybe-publish); it is unpinned below.
  (unwind-protect
  (destructuring-bind (base configs records record-octets count suffix budget frontier free revision
                        base-payloads ident)
      captured
    (declare (ignore count))
    (let ((started (get-internal-real-time)) (next nil) (durablep nil) (verdict nil)
          (payloads nil) (dropped-paths nil) (image nil)
          ;; the payload frames the arena run writes, for the reseat after
          ;; the install (fnn-owner-release-extents)
          (*fnn-checkpoint-frames* nil)
          ;; the writer's segment: ACL2's choice under the record bound R the
          ;; capture handed over (fn-ockp-segment-octets, the verb's derivation)
          (segment (fnn-core 'fn-ockp-segment-octets record-octets
                             +fnn-checkpoint-batch-octets+)))
      (flet ((elapsed ()
               (round (* 1000 (- (get-internal-real-time) started))
                      internal-time-units-per-second)))
        (handler-case
            (let ((sequence (length records)))
              ;; Records-flip: NEXT is the capture of the captured rows'
              ;; canonical rows and the file opens with their canonical
              ;; payloads (host/owner-host.lisp fn-owner-sco-prepare, which
              ;; READS the live arena below the captured count).
              ;; NEXT (fn-owner-sco-next), the history image of NEXT's
              ;; records with its binding into the F row's position
              ;; (host/native/io.lisp fnn-history-image-build), then the
              ;; setup over that position and the space the image leaves
              ;; (fn-owner-sco-setup-of): fn-owner-sco-prepare in two halves.
              (destructuring-bind (setup prepared-next n arun)
                  (let ((prepared (fnn-core 'fn-owner-sco-next base base-payloads configs records
                                            (fnn-checkpoint-walk records) segment (fnn-live-arena))))
                    (multiple-value-bind (position2 image2)
                        (if prepared
                            (fnn-history-image-build (fnn-core 'fn-sco-records (first prepared))
                                                     (first ident) (second ident) position)
                            (values position nil))
                      (setq image image2)
                      (fnn-core 'fn-owner-sco-setup-of prepared frontier revision position2 segment
                                budget (fnn-core 'fn-his-stream-free free (fnn-history-image-np image)))))
                (unless (and (consp setup) (= (length setup) 7))
                  (fnn-fault "owner returned a malformed checkpoint setup"))
                (setq next prepared-next payloads n)
                (setq verdict (first setup))
                (cond
                  ((eq verdict :unencodable)
                   (fnn-err "CHECKPOINT auto refused=unencodable sequence=~d" sequence))
                  ((and (consp verdict) (eq (first verdict) :deferred)
                        (= (length verdict) 4) (keywordp (second verdict))
                        (integerp (third verdict)) (integerp (fourth verdict)))
                   (fnn-err "CHECKPOINT deferred reason=~(~a~) estimate=~d budget=~d sequence=~d ms=~d"
                            (second verdict) (third verdict) (fourth verdict) sequence
                            (elapsed)))
                  ((and (consp verdict) (eq (first verdict) :plan) (= (length verdict) 2)
                        (integerp (second verdict)))
                   (let ((octets (fnn-core 'fn-his-file-octets (fnn-history-image-np image)
                                           (second verdict)))
                         (steps 0)
                         (store (fnn-owner-service-store service)))
                     (handler-case
                         (progn
                           ;; The F row names the segment the capture rotated
                           ;; to: its name is made durable first (journal/'s
                           ;; fence, cut rotate-durable; io.lisp
                           ;; fnn-log-make-durable), off the owner mutex.
                           (fnn-log-make-durable (fnn-store-log store))
                           (unwind-protect
                                (fnn-state-checkpoint-write
                                 store
                                 (lambda (fd)
                                   (fnn-history-image-write fd image)
                                   (setq steps (fnn-checkpoint-write-steps
                                                fd setup segment sequence (fnn-store-config store)
                                                (fnn-live-octets-pub) arun))))
                             ;; the buffer's array back (PKT-PRS-2)
                             (fnn-octets-pub-release))
                           (setq durablep t)
                           ;; T8: the installed checkpoint covers the segments
                           ;; below its first suffix segment; they go now,
                           ;; off the mutex (none is the active one).
                           (let ((dropped (if position
                                              (let ((covered (fnn-log-covered-indices
                                                              store (first position))))
                                                (setq dropped-paths
                                                      (mapcar (lambda (k) (fnn-segment-path-at store k))
                                                              covered))
                                                (fnn-log-drop store covered))
                                            0)))
                             (fnn-err "CHECKPOINT auto sequence=~d suffix=~d octets=~d steps=~d ms=~d~@[ segment=~d~]~:[~; dropped=~d~]"
                                      sequence suffix octets steps (elapsed)
                                      (first position) position dropped)))
                       ((or fnn-store-io-refusal fnn-store-indeterminate) (e)
                         (fnn-err "CHECKPOINT auto failed sequence=~d: ~a" sequence e)))))
                  (t (fnn-fault "owner returned a malformed checkpoint verdict")))))
          (serious-condition (e)
            (fnn-err "CHECKPOINT auto failed: ~a" e))))
      (unwind-protect
           (progn
           (handler-case
               (fnn-owner-gated (service :control)
                 (when next
                   (let ((done (fnn-owner-core 'fn-owner-sco-publication-done
                                               next payloads durablep verdict)))
                     (when (and durablep (not (integerp done)))
                       (fnn-err "CHECKPOINT auto: owner refused the durable sequence")))))
             (serious-condition (e)
               (fnn-err "CHECKPOINT auto failed: ~a" e)))
          ;; Q16 (b): the dropped files' blocks back while serving.
          (when durablep
            (fnn-owner-release-extents service (fnn-owner-service-store service)
                                       *fnn-checkpoint-frames* dropped-paths pin)))
        (fnn-with-roster (service)
          (setf (fnn-owner-service-publisher service) nil
                (fnn-owner-service-workers service)
                (delete sb-thread:*current-thread*
                        (fnn-owner-service-workers service) :test #'eq))))))
    (when pin (fnn-arena-unpin pin))
    (fnn-owner-service-nursery))
  ;; PKT-583 (b): the publication finished; decide again from the newest
  ;; committed frontier now, not at the next accept (a load's tail has
  ;; none), so a coalesced request is served as soon as it can be and a
  ;; store that stopped posting is left with its suffix under K/2.
  ;; fnn-owner-maybe-publish takes the mutex itself and refuses while
  ;; stopping; at most one publication is in flight (fn-ock-one-
  ;; publication-in-flight).  After the service trigger is back, so a
  ;; publication it starts sets its own.
  (fnn-owner-maybe-publish service))

(defun fnn-owner-maybe-publish (service)
  "One publication decision (fnn-owner-maybe-publish-quantum), and when it
answers that the rotation's spare is missing, the spare made off the owner
mutex (host/native/io.lisp fnn-log-prepare-spare: create, preallocate, fence
in staging/) and the decision taken once more.  The rotation under the mutex
is then a rename.  A spare that cannot be made is a failed publication:
logged, serving continues."
  (let ((store (fnn-owner-service-store service)))
    (loop repeat 2 do
      (unless (eq (fnn-owner-maybe-publish-quantum service) :needs-spare)
        (return))
      (handler-case (fnn-log-prepare-spare store)
        ((or fnn-store-fault fnn-store-indeterminate) (e) (error e))
        (fnn-store-error (e)
          (fnn-err "CHECKPOINT auto failed: ~a" e)
          (return))))))

(defun fnn-log-rotation-ready-p (store)
  "Whether the rotation the capture performs can run as a rename now: the
active segment holds no record (ACL2's fn-lgc-rotate-needed-p: no rotation),
or the spare of ACL2's next segment is prepared."
  (let* ((log (fnn-store-log store))
         (ks (fnn-log-kernel log)))
    (or (not (fnn-core 'fn-lgc-rotate-needed-p ks))
        (let ((spare (fnn-log-spare log)))
          (and spare (eql (first spare)
                          (fnn-core 'fn-lgs-next-segment (fnn-log-index log))))))))

(defun fnn-owner-maybe-publish-quantum (service)
  "P3 owner publication (books/owner-checkpoint-open.lisp).  Between accepts
and when a publication finishes, never inside a command: when
fn-ock-publication-next says :due (fn-ock-publication-duep: the suffix since
the newest durable checkpoint reached half the profile's K; no deferred
publication is blocked on the profile's budget or the space, PKT-492; none in
flight, else the observation is the one coalesced request, PKT-583 (b)), ACL2
records the attempt and hands back the values the publication reads
(fn-owner-sco-capture) under the owner mutex, O(1): the record list by
pointer, the frontier, the free space the host observed by statvfs and the
source revision.  The tables, the decision and the batched write run on
their own thread, outside the mutex (fnn-owner-publish-captured), so served
commands and accepts continue; at most one publication runs at a time, and
the stop joins it with the client workers.  The owner state is only read
here, and written only through fn-owner-sco-publication-done.  The owner
reads run as a :control quantum; the thread's registration is the roster's."
  ;; The free space is observed once, off the owner mutex (statvfs is I/O),
  ;; before the quantum that decides with it; the due path and the capture
  ;; are handed the same reading.
  (let ((free (fnn-disk-free-octets (fnn-owner-service-store service))))
   (fnn-owner-gated (service :control)
    (unless (or (fnn-owner-service-stopping service)
                (fnn-with-roster (service) (fnn-owner-service-publisher service)))
      ;; The budget override is nil but on a developer image with
      ;; FN_NATIVE_CHECKPOINT_BUDGET_TEST set; ACL2 chooses between it and
      ;; the profile's (fn-owner-sco-budget) on the due path and at the
      ;; capture, so both see one budget.
      (progn
        (when (eq (fnn-owner-core 'fn-owner-sco-due
                                  (fnn-checkpoint-budget-test-override nil) free)
                  :due)
          ;; The capture rotates the log (fnn-log-rotate, under
          ;; the owner mutex: no batch is open in a :control quantum), so
          ;; the captured history is exactly the closed segments' records
          ;; and the checkpoint's F row names the new segment.  The
          ;; rotation is a rename of the spare made off the mutex; without
          ;; one this quantum answers :needs-spare and captures nothing.
          ;; A failed rotation is a failed publication: logged, serving
          ;; continues.
          (unless (fnn-log-rotation-ready-p (fnn-owner-service-store service))
            (return-from fnn-owner-maybe-publish-quantum :needs-spare))
          (let* ((store (fnn-owner-service-store service))
                 (position (handler-case (fnn-log-rotate store)
                             ((or fnn-store-fault fnn-store-indeterminate) (e) (error e))
                             (fnn-store-error (e)
                               (fnn-err "CHECKPOINT auto failed: ~a" e)
                               :failed)))
                 (captured (and (not (eq position :failed))
                                (fnn-owner-core 'fn-owner-sco-capture
                                                (fnn-checkpoint-budget-test-override nil)
                                                free (fnn-checkpoint-revision)))))
            (unless (or (eq position :failed)
                        (and (true-listp captured) (= (length captured) 12)))
              (fnn-fault "owner returned a malformed checkpoint capture"))
            ;; The publication reads the live arena outside the mutex, so it
            ;; pins the generation as such a reader here, under the mutex,
            ;; before its thread starts: pinned on its own thread, a commit
            ;; completing between this capture and that pin could release a
            ;; staged page it reads (fnn-log-reseat-fenced runs under the
            ;; mutex).  The thread unpins when it ends; a thread that was
            ;; never made unpins here.
            (fnn-with-roster (service)
              (let ((thread (and (not (eq position :failed))
                                 (let ((made nil) (pin (fnn-arena-pin)))
                                   (unwind-protect
                                        (setq made (sb-thread:make-thread
                                                    (lambda ()
                                                      ;; Lane scale-reads: the stop ends the
                                                      ;; publication at its next batch
                                                      ;; (io.lisp fnn-checkpoint-yield).
                                                      (let ((*fnn-checkpoint-stop-test*
                                                              (lambda ()
                                                                (fnn-with-roster (service)
                                                                  (fnn-owner-service-stopping
                                                                   service)))))
                                                        (fnn-owner-publish-captured
                                                         service captured position pin)))
                                                    :name "fn owner checkpoint"))
                                     (unless made (fnn-arena-unpin pin)))))))
                (setf (fnn-owner-service-publisher service) thread)
                (push thread (fnn-owner-service-workers service)))))))))))

(defstruct (fnn-snapshot-payload-view (:constructor fnn-make-snapshot-payload-view (token arena)))
  token arena)

(defun fnn-payload-lifecycle-start (service)
  "Owner mutex held; register before any core worker/thread is exposed."
  (sb-thread:with-mutex (*fnn-payload-lifecycle-lock*)
    (unless (eq (first (fnn-payload-lifecycle-answer :start)) :allowed)
      (fnn-fault "payload arena lifecycle refused owner startup"))
    (let ((answer (fnn-payload-lifecycle-answer
                   :start (fnn-core-state 'fn-owner-payload-view-owned-p))))
      (unless (eq (first answer) :allowed)
        (fnn-fault "payload arena lifecycle refused owner startup"))
      (setf *fnn-payload-lifecycle-arena* (fnn-live-arena)
            *fnn-payload-lifecycle-owner* service
            *fnn-payload-lifecycle-phase* (second answer)))))

(defun fnn-payload-lifecycle-drain (service)
  "Owner mutex held. Signal only; joining is always outside this exclusion."
  (sb-thread:with-mutex (*fnn-payload-lifecycle-lock*)
    (when (eq service *fnn-payload-lifecycle-owner*)
      (let ((answer (fnn-payload-lifecycle-answer :drain)))
        (when (eq (first answer) :allowed)
          (setf *fnn-payload-lifecycle-phase* (second answer)))))))

(defun fnn-payload-lifecycle-joined (service)
  "Owner mutex held AFTER definite worker, module, and buffer cleanup."
  (sb-thread:with-mutex (*fnn-payload-lifecycle-lock*)
    (when (eq service *fnn-payload-lifecycle-owner*)
      (let ((answer (fnn-payload-lifecycle-answer
                     :joined (fnn-core-state 'fn-owner-payload-view-owned-p) t)))
        (when (eq (first answer) :allowed)
          (setf *fnn-payload-lifecycle-phase* (second answer)
                *fnn-payload-lifecycle-owner* nil))))))

(defun fnn-snapshot-payload-view-acquire (service maintenance)
  "Owner capture mutex held; lifecycle exclusion covers instance and STATE."
  (sb-thread:with-mutex (*fnn-payload-lifecycle-lock*)
    (let ((permission (fnn-payload-lifecycle-answer :capture)))
      (unless (and (eq (first permission) :allowed)
                   (eq service *fnn-payload-lifecycle-owner*))
        (return-from fnn-snapshot-payload-view-acquire
          (values :refused '(:refused :arena-not-serving)))))
    (let* ((arena *fnn-payload-lifecycle-arena*)
           (answer (destructuring-bind (erp val &rest ignored)
                       (fnn-call 'fn-owner-payload-view-acquire maintenance arena *the-live-state*)
                     (declare (ignore ignored))
                     (when erp (fnn-fault "payload view acquire core error")) val)))
      (if (eq (first answer) :acquired)
          (values :acquired (fnn-make-snapshot-payload-view (second answer) arena))
        (values :refused answer)))))

(defun fnn-snapshot-payload-view-live-p (holder)
  "Owner mutex held; authorization to a captured source row is separate."
  (sb-thread:with-mutex (*fnn-payload-lifecycle-lock*)
    (and (eq (first (fnn-payload-lifecycle-answer :borrow)) :allowed)
         (eq (fnn-snapshot-payload-view-arena holder) *fnn-payload-lifecycle-arena*)
         (fnn-core-state 'fn-owner-payload-view-live-p
                         (fnn-snapshot-payload-view-token holder)))))

(defun fnn-snapshot-payload-view-release (holder settlement)
  "Owner mutex held after definite cleanup; uncertainty retains ownership."
  (sb-thread:with-mutex (*fnn-payload-lifecycle-lock*)
    (if (and (eq (first (fnn-payload-lifecycle-answer :borrow)) :allowed)
             (eq (fnn-snapshot-payload-view-arena holder) *fnn-payload-lifecycle-arena*))
        (fnn-core-state 'fn-owner-payload-view-release
                        (fnn-snapshot-payload-view-token holder) settlement)
      '(:refused :payload-view-instance))))

(defun fnn-snapshot-source-context ()
  "Observe scalar source admission context while the caller holds owner mutex."
  (fnn-owner-core 'fn-owner-osn-source-context))

(defun fnn-snapshot-source-begin (captured)
  "Initialize the source cursor from the funded controller's actual capture.
No based row is decoded and no suffix is reversed by this call."
  (let ((answer (fnn-core 'fn-owner-osn-source-begin captured)))
    (unless (eq (first answer) :source)
      (fnn-refuse "snapshot source refused: ~a" (second answer)))
    (second answer)))

(defun fnn-snapshot-prepare-configured-fold (configs records)
  "Resume the captured prefix's paused configuration fold one tick at a time.
Each continuation owns its unconsumed lists by pointer.  This is a preparer
component; the other checkpoint summary and history-image phases must also
be resumable and funded before the producer controller uses the result."
  (let ((cursor (fnn-core 'fn-osp-cpr-begin configs records)))
    (loop
      (fnn-checkpoint-yield "snapshot-prepare-configured" (fifth cursor))
      (let ((tick (fnn-core 'fn-osp-cpr-tick
                            (first cursor) (second cursor) (third cursor)
                            (fourth cursor) (fifth cursor))))
        (case (first tick)
          (:done (return (second tick)))
          (:continue (setq cursor (rest tick)))
          (otherwise (fnn-fault "invalid configured snapshot preparation tick")))))))

(defun fnn-snapshot-prepare-summary-folds (records)
  "Resume identity/consumer/topic/event-index summaries one event per tick.
The private cursor retains unconsumed captured records by pointer and the
four carried accumulators; it never copies an accumulated record prefix."
  (let ((cursor (fnn-core 'fn-osp-fold-begin records)))
    (loop
      (fnn-checkpoint-yield "snapshot-prepare-summaries" (sixth cursor))
      (let ((tick (fnn-core 'fn-osp-fold-tick cursor)))
        (case (first tick)
          (:done (return (second tick)))
          (:continue (setq cursor (second tick)))
          (:refused (fnn-refuse-io "snapshot summary preparation refused: ~a" (second tick)))
          (otherwise (fnn-fault "invalid summary snapshot preparation tick")))))))

(defun fnn-snapshot-prepare-canonical-rows (records)
  "Remap one retained row, then one reversal cell, per tick.
The fixed-shape remapper retains captured context/facts/verdict metadata and
borrows payload bytes through the separately pinned arena writer. No payload
is reparsed under a new key epoch and no suffix is validated in its guard."
  (let ((cursor (fnn-core 'fn-orm-begin records)))
    (loop
      (fnn-checkpoint-yield "snapshot-prepare-remap" (third cursor))
      (let ((tick (fnn-core 'fn-orm-tick cursor)))
        (case (first tick)
          (:done (return (second tick)))
          (:continue (setq cursor (second tick)))
          (:refused (fnn-refuse-io "snapshot canonical preparation refused: ~a" (second tick)))
          (otherwise (fnn-fault "invalid canonical snapshot preparation tick")))))))

(defun fnn-snapshot-prepare-capture (configs records)
  "Assemble the original checkpoint tuple from completed resumable phases.
No whole-history fn-sco-capture/fn-owner-sco-next is called by this path."
  (let ((canonical (fnn-snapshot-prepare-canonical-rows records)))
    (when (eq canonical :bad)
      (fnn-refuse-io "snapshot canonical rows refused"))
    (let ((configured (fnn-snapshot-prepare-configured-fold configs canonical))
          (summaries (fnn-snapshot-prepare-summary-folds canonical)))
      (fnn-core 'fn-osp-assemble canonical configured summaries))))

(defun fnn-snapshot-write-captured-checkpoint (target captured position profile)
  "Write the captured whole Store into TARGET's complete checkpoint.
Caller owns the shared publication scratch, pins the captured arena/version
and funds the old/new artifact demand BEFORE calling.  POSITION names the
empty suffix segment established by the source capture's rotation.  This
component neither publishes SNAPSHOT nor mutates the source checkpoint."
  (destructuring-bind (base configs records record-octets count suffix budget frontier free revision
                        base-payloads ident) captured
    (declare (ignore base suffix base-payloads))
    (let* ((segment (fnn-core 'fn-ockp-segment-octets record-octets
                             +fnn-checkpoint-batch-octets+))
           (prepared (fnn-core 'fn-owner-osn-prepared-run
                                (fnn-snapshot-prepare-capture configs records)
                                (fnn-checkpoint-walk records) segment))
           (image nil))
      (unwind-protect
           (multiple-value-bind (bound-position built-image)
               (if prepared
                   (fnn-history-image-build (fnn-core 'fn-sco-records (first prepared))
                                            (first ident) (second ident) position)
                 (values position nil))
             (setq image built-image)
             (destructuring-bind (setup next payloads arun)
                 (fnn-core 'fn-owner-sco-setup-of prepared frontier revision bound-position
                           segment budget
                           (fnn-core 'fn-his-stream-free free (fnn-history-image-np image)))
               (let ((verdict (first setup)))
                 (cond
                   ((eq verdict :unencodable)
                    (fnn-refuse-io "snapshot captured Store is unencodable as a checkpoint"))
                   ((and (consp verdict) (eq (first verdict) :deferred))
                    (fnn-refuse-io "snapshot deferred reason=~(~a~) estimate=~d budget=~d"
                                   (second verdict) (third verdict) (fourth verdict)))
                   ((and (consp verdict) (eq (first verdict) :plan))
                    (setf (fnn-store-config target) profile)
                    (fnn-state-checkpoint-write
                     target
                     (lambda (fd)
                       (fnn-history-image-write fd image)
                       (fnn-checkpoint-write-steps fd setup segment count profile
                                                   (fnn-live-octets-pub) arun)))
                    (values next payloads
                            (fnn-core 'fn-his-file-octets (fnn-history-image-np image)
                                      (second verdict))))
                   (t (fnn-fault "ACL2 returned a malformed snapshot checkpoint plan"))))))
        (fnn-octets-pub-release)
        ;; A cancelled/failed write may end before image-write released it.
        (fnn-call 'fn-his-release (fnn-live-hrecs))))))

;;; Row S3b (lane operability-7): `store export DIR' on the running owner
;;; (books/owner-export-request.lisp fn-oex-; SCN-210, PRF-988).  The export
;;; is a reader of the live arena, as the publication is: the capture under
;;; the owner mutex is O(1) (host/owner-host.lisp fn-owner-oex-capture: the
;;; record list by pointer, its count, the configuration history, the
;;; frontier), the archive is written on its own thread off the mutex in
;;; chunks of +fnn-export-chunk+ records, pinned at the arena generation the
;;; capture saw (fnn-arena-pin under the mutex, before the thread exists),
;;; joined by the stop with the client workers and ended by name at its next
;;; chunk when the owner stops (fnn-checkpoint-yield).  ACL2 decides the
;;; request (fn-oex-request-word over the two observations) and every
;;; archive entry and MANIFEST line (fn-sxp-export-head, fn-sxp-export-chunk:
;;; the entries the offline export writes, fn-sxp-stream-is-the-export);
;;; durability is fn-sxd-program's cuts, step for step as the offline verb
;;; (host/native/io.lisp fnn-command-store-export).  The export never
;;; excludes the publication: both read the arena under their pins, and the
;;; captured list is an immutable ACL2 value.

(defun fnn-owner-export-observation (service)
  "(INFLIGHTP OUTCOME DIR) under the roster: whether the exporter thread
runs, the last outcome and its DIR."
  (fnn-with-roster (service)
    (list (and (fnn-owner-service-exporter service) t)
          (fnn-owner-service-export-outcome service)
          (fnn-owner-service-export-dir service))))

(defun fnn-owner-export-start (service captured dir)
  "Under the owner mutex, an accepted request: pin the arena generation the
capture saw, make the thread and register it (the exporter slot; the
workers the stop joins).  A thread that was never made unpins here."
  (fnn-with-roster (service)
    (let ((made nil) (pin (fnn-arena-pin)))
      (unwind-protect
           (setq made (sb-thread:make-thread
                       (lambda ()
                         (let ((*fnn-checkpoint-stop-test*
                                 (lambda ()
                                   (fnn-with-roster (service)
                                     (fnn-owner-service-stopping service)))))
                           (fnn-owner-export-captured service captured dir pin)))
                       :name "fn owner export"))
        (unless made (fnn-arena-unpin pin)))
      (setf (fnn-owner-service-exporter service) made
            (fnn-owner-service-export-outcome service) nil
            (fnn-owner-service-export-dir service) dir)
      (push made (fnn-owner-service-workers service)))))

(defun fnn-owner-export-write (store records count configs frontier dir)
  "fnn-command-store-export's program over the captured values, without an
open: the head (config.json's octets, the captured frontier's frame, the
config/ files cut to the captured history's length: a record published
after the capture is a later file, never one of these), then the chunks off
the captured record list through the live arena (host/store-node-host.lisp
fn-store-sco-encode-chunk), each an ACL2 export step; then fn-sxd-program's
cuts.  A yield before each chunk ends the export by name when the owner
stops.  Answers the record count written."
  (let* ((fault (fnn-export-test-fault))
         (profile (fnn-octet-list (fnn-read-regular-bounded (fnn-config-path store) 16384)))
         (frontier-octets (fnn-octet-list (fnn-metadata-frontier-frame frontier)))
         (observation (fnn-config-record-observation store))
         (wanted (length configs)))
    (when (< (length observation) wanted)
      (fnn-refuse-io "the configuration directory holds ~d records, the captured history ~d"
                     (length observation) wanted))
    (let* ((config-pairs (mapcar (lambda (pair) (cons (car pair) (fnn-octet-list (cdr pair))))
                                 (subseq observation 0 wanted)))
           (head (fnn-core 'fn-sxp-export-head profile frontier-octets config-pairs))
           (staged (fnn-join dir "MANIFEST.partial"))
           (written 0) (batch 0))
      (unless (and (consp head) (consp (car head)))
        (fnn-fault "ACL2 returned a malformed archive"))
      (fnn-mkdir dir #o700)
      (fnn-mkdir (fnn-join dir "config") #o700)
      (fnn-mkdir (fnn-join dir "records") #o700)
      (let ((fd (fnn-open staged (logior sb-posix:o-wronly sb-posix:o-creat sb-posix:o-excl
                                         +fnn-o-nofollow+)
                          #o600)))
        (unwind-protect
             (let ((cursor records))
               (fnn-export-step dir fd head fault)
               (loop while (consp cursor)
                     do (fnn-checkpoint-yield "export" batch)
                        (destructuring-bind (octets-list rest)
                            (fnn-core 'fn-store-sco-encode-chunk cursor +fnn-export-chunk+
                                      (fnn-live-arena))
                          (unless (listp octets-list)
                            (fnn-fault "ACL2 returned a malformed export chunk"))
                          (let ((chunk (mapcar (lambda (octets)
                                                 (cons (fnn-bridge-record-sequence octets) octets))
                                               octets-list)))
                            (fnn-export-step dir fd (fnn-core 'fn-sxp-export-chunk chunk) fault)
                            (incf written (length chunk))
                            (incf batch)
                            (setq cursor rest))))
               (fnn-export-at fault "export-data-written")
               ;; :sync-all
               (fnn-export-sync-data dir)
               (fnn-export-at fault "export-data-durable")
               ;; fn-sxd-publish-program
               (fnn-fsync-file fd))
          (fnn-close fd)))
      (fnn-fsync-dir (fnn-join dir "records"))
      (fnn-fsync-dir (fnn-join dir "config"))
      (fnn-export-at fault "export-manifest-staged")
      (fnn-replace staged (fnn-join dir "MANIFEST"))
      (fnn-export-at fault "export-manifest-renamed")
      (fnn-fsync-dir dir)
      (fnn-export-at fault "export-durable")
      (unless (eql written count)
        (fnn-fault "the export wrote ~d records of a capture of ~d" written count))
      written)))

(defun fnn-owner-export-captured (service captured dir pin)
  "The export's thread: the archive under DIR from the captured values, the
outcome into the exporter slot, the log line.  A failure leaves no MANIFEST
(KEYSTONE fn-sxd-crash-is-incomplete-or-complete) and serving continues;
the stop's refusal at a chunk boundary is `owner-stopping'."
  (let ((started (get-internal-real-time)) (outcome nil))
    (unwind-protect
         (destructuring-bind (records count configs frontier) captured
           (handler-case
               (let ((written (fnn-owner-export-write (fnn-owner-service-store service)
                                                      records count configs frontier dir)))
                 (setq outcome (cons :done written))
                 (fnn-err "EXPORT done archive=~a records=~d configuration=~d ms=~d"
                          dir written (length configs)
                          (round (* 1000 (- (get-internal-real-time) started))
                                 internal-time-units-per-second)))
             (fnn-store-io-refusal (e)
               (setq outcome (cons :failed :owner-stopping))
               (fnn-err "EXPORT failed archive=~a reason=owner-stopping: ~a" dir e))
             (serious-condition (e)
               (setq outcome (cons :failed :archive-write))
               (fnn-err "EXPORT failed archive=~a reason=archive-write: ~a" dir e))))
      (fnn-with-roster (service)
        (setf (fnn-owner-service-exporter service) nil
              (fnn-owner-service-export-outcome service)
              (or outcome (cons :failed :archive-write))
              (fnn-owner-service-workers service)
              (delete sb-thread:*current-thread*
                      (fnn-owner-service-workers service) :test #'eq)))
      (fnn-arena-unpin pin))))

;;; Q16 (lane online-reclaim): `store reclaim --dry-run' on the running
;;; owner (books/owner-reclaim.lisp; host/owner-host.lisp fn-owner-orc-*).

(defun fnn-reclaim-counts-line (counts)
  (unless (and (listp counts) (= (length counts) 5)
               (every (lambda (n) (and (integerp n) (>= n 0))) counts))
    (fnn-fault "ACL2 returned malformed reclaim counts"))
  (destructuring-bind (reclaimable octets reclaimed freed held) counts
    (format nil "reclaimable=~d reclaimable-octets=~d held=~d reclaimed=~d freed-octets=~d"
            reclaimable octets held reclaimed freed)))

(defparameter +fnn-reclaim-chunk-rows+ 1024
  "Rows rewritten and folded per ACL2 call while a reclaim pass walks the
captured history (a work quantum per call, never a bound on the store).")

(defun fnn-owner-reclaim-walk (records ctx rewrite)
  "The pass over the captured RECORDS in chunks of +fnn-reclaim-chunk-rows+
(fn-owner-orc-chunk: fn-orc-chunk, whose rewrite is the offline rewrite and
whose fold is the offline fold, fn-orc-rewrite-rows-of-append and
fn-orc-fold-of-append joining the chunks).  Answers (values ACC REWRITTEN),
REWRITTEN the rewritten rows in order when REWRITE, else nil."
  (let ((acc (fnn-core 'fn-owner-orc-init)) (out nil) (rest records))
    (loop while rest do
      (let ((chunk (loop repeat +fnn-reclaim-chunk-rows+ while rest collect (pop rest))))
        (let ((r (fnn-core 'fn-owner-orc-chunk chunk ctx acc (fnn-live-arena))))
          (unless (and (consp r) (= (length r) 2) (listp (first r))
                       (= (length (first r)) (length chunk)))
            (fnn-fault "owner returned a malformed reclaim chunk"))
          (setq acc (second r))
          (when rewrite (push (first r) out)))))
    (values acc (and rewrite (let ((all nil))
                               (dolist (c out all) (setq all (nconc c all))))))))

(defun fnn-owner-reclaim-dry-run (service free)
  "The dry run on the running owner: under the owner mutex the capture
(fn-owner-orc-capture: the rows by pointer, the configuration and the
Store, the clock's stamp), then off it, on this thread, the context, the
walk (fnn-owner-reclaim-walk), the classes and the decision
(fn-owner-orc-decide: fn-lgr-decide-stream at the clock, as the offline
dry run), the report to the owner's log in the offline verb's words; then
the pass ends under the mutex (fn-owner-orc-finish).  Nothing is written.
The arena is read below the captured count only, and the pass is counted
as an off-mutex arena reader while it runs (no staged page is released
under it: its arena-reader pin, books/arena-reader-pins.lisp).  Answers
the reply word: :dry-run, or ACL2's refusal."
  (let ((clock (fnn-store-prepare-observation)) (captured nil) (pin nil))
    (unwind-protect
         (progn
           (fnn-owner-gated (service :control)
             (setq captured (fnn-owner-core 'fn-owner-orc-capture :dry-run clock
                                            (fnn-checkpoint-budget-test-override nil)
                                            free (fnn-checkpoint-revision)))
             (setq pin (fnn-arena-pin)))
           (unless (and (true-listp captured) (= (length captured) 12))
             (fnn-fault "owner returned a malformed reclaim capture"))
           (destructuring-bind (records count v s profile configs frontier budget free revision
                                now record-octets)
               captured
             (declare (ignore configs frontier budget free revision record-octets))
             (let* ((ctx (fnn-core 'fn-owner-orc-ctx :dry-run v s now (fnn-live-arena)))
                    (classes (fnn-core 'fn-owner-orc-classes ctx (fnn-live-arena)))
                    (acc (fnn-owner-reclaim-walk records ctx nil))
                    (decision (fnn-core 'fn-owner-orc-decide :dry-run profile v s now acc
                                        (fnn-live-arena)))
                    (expired (if (and (listp classes) (= (length classes) 6)
                                      (every (lambda (n) (and (integerp n) (>= n 0))) classes))
                                 (second classes)
                               (fnn-fault "ACL2 returned malformed reclaim classes"))))
               (unless (and (consp decision) (member (first decision) '(:refused :none :dry-run)))
                 (fnn-fault "ACL2 returned no reclaim decision"))
               (case (first decision)
                 (:refused
                  (fnn-err "RECLAIM dry-run refused: ~(~a~)" (second decision))
                  (second decision))
                 (:none
                  (fnn-err "RECLAIM dry-run records=~d would-reclaim=0 would-expire=~d ~a"
                           count expired (fnn-reclaim-counts-line (second decision)))
                  :dry-run)
                 (:dry-run
                  (destructuring-bind (msgids freed counts) (rest decision)
                    (fnn-err "RECLAIM dry-run records=~d would-reclaim=~d would-expire=~d freed-octets=~d ~a"
                             count (length msgids) expired freed
                             (fnn-reclaim-counts-line counts))
                    (dolist (m msgids)
                      (fnn-err "RECLAIM would-reclaim ~a"
                               (if (stringp m) m (fnn-fault "malformed msgid")))))
                  :dry-run)))))
      (when pin (fnn-arena-unpin pin))
      (when captured
        (fnn-owner-gated (service :control)
          (fnn-owner-core 'fn-owner-orc-finish))))))

;;; Q16 (a) (lane online-reclaim-3): `store reclaim --recorded' on the
;;; running owner INSTALLS (books/owner-reclaim-pass.lisp; host/owner-host.lisp
;;; fn-owner-orcp-*).  Every step is a named cut (FN_NATIVE_RECLAIM_FAULT=
;;; CUT:kill on a developer image, *fn-orcp-cuts*): before :installed a death
;;; leaves the old publication, from it the new one.

(defparameter +fnn-reclaim-cuts+
  '("captured" "rewritten" "staged" "interned" "rebuilt" "installed" "swapped" "released"))

(defparameter +fnn-reclaim-swap-rounds+ 8
  "Swap quanta a pass tries while the commit pipeline is busy or another
off-mutex reader holds the arena, before it defers by name.")

(defun fnn-reclaim-cut (cut)
  "The pass reached CUT (a keyword of *fn-orcp-cuts*): SIGKILL here when
FN_NATIVE_RECLAIM_FAULT names it."
  (let ((raw (fnn-developer-selector "FN_NATIVE_RECLAIM_FAULT")))
    (when raw
      (let ((colon (position #\: raw :from-end t)))
        (unless (and colon (string= (subseq raw (1+ colon)) "kill")
                     (member (subseq raw 0 colon) +fnn-reclaim-cuts+ :test #'string=))
          (fnn-fault "invalid FN_NATIVE_RECLAIM_FAULT (expected CUT:kill)"))
        (when (string-equal (subseq raw 0 colon) (symbol-name cut))
          (sb-posix:kill (sb-posix:getpid) sb-unix:sigkill)
          (fnn-fault "test SIGKILL did not terminate the process")))))
  ;; Developer image only (the HELD form of the same cuts, for the
  ;; resilience scenarios' interleavings; the held point is named
  ;; reclaim-CUT, e.g. reclaim-captured): FN_NATIVE_RECLAIM_HOLD=CUT:PATH
  ;; makes the pass, on reaching CUT, print `RECLAIM held at=CUT' and wait
  ;; until the release file PATH exists, so a scenario can take a new
  ;; independent hold (a reader on the candidate) between that cut and the
  ;; next step, then create PATH.
  (let ((raw (fnn-developer-selector "FN_NATIVE_RECLAIM_HOLD")))
    (when (and raw (plusp (length raw)))
      (let ((colon (position #\: raw)))
        (unless (and colon (< (1+ colon) (length raw))
                     (member (subseq raw 0 colon) +fnn-reclaim-cuts+ :test #'string=))
          (fnn-fault "invalid FN_NATIVE_RECLAIM_HOLD (expected CUT:RELEASE-FILE)"))
        (when (string-equal (subseq raw 0 colon) (symbol-name cut))
          (let ((release (subseq raw (1+ colon))))
            (fnn-err "RECLAIM held at=~(~a~)" cut)
            (loop until (probe-file release) do (sleep 0.05)))))))
  ;; Developer image only (Q16 item 5): while the file
  ;; FN_NATIVE_TEST_RECLAIM_STALL_FILE names exists, the pass waits at its
  ;; :rebuilt cut, off the owner mutex, so posts commit between the capture
  ;; and the swap and the swap word answers :delta
  ;; (tests/test_native_expiry.py, the continuous-posting case).
  (when (eq cut :rebuilt)
    (let ((stall (fnn-developer-selector "FN_NATIVE_TEST_RECLAIM_STALL_FILE")))
      (when (and stall (plusp (length stall)) (probe-file stall))
        (fnn-err "RECLAIM stalled at=rebuilt")
        (loop while (probe-file stall) do (sleep 0.05))))))

(defun fnn-fresh-stobj (name)
  "A fresh, empty instance of the live stobj NAME (fn-cat, fn-hist) for the
rebuild off the mutex: its creator's value, of the live instance's type.
The creator may be a macro (a defstobj's raw creator is), so it is called
by evaluating the form (CREATOR), once per pass."
  (let* ((creator (find-if #'fboundp
                           (list (intern (format nil "CREATE-~a" (symbol-name name)) "ACL2")
                                 (intern (format nil "CREATE-~a$C" (symbol-name name)) "ACL2"))))
         (fresh (and creator (eval (list creator))))
         (live (fnn-live-stobj name)))
    (unless (and fresh (equal (type-of fresh) (type-of live)))
      (fnn-fault "no fresh instance of the ~(~a~) stobj" name))
    fresh))

(defun fnn-install-stobj (name value)
  "Under the owner mutex: VALUE becomes the live stobj NAME (the host's
pointer and the live state's binding)."
  (let ((cell (assoc name (user-stobj-alist *the-live-state*))))
    (unless cell (fnn-fault "the ~(~a~) stobj is not in this image" name))
    (setf (cdr cell) value)
    (ecase name
      (fn-cat (setq *fnn-cat* value))
      (fn-hist (setq *fnn-hist* value)))))

(defun fnn-owner-reclaim-intern (service rows keyring generation)
  "The rewritten ROWS with their tombstoned records interned into the live
arena, +fnn-reclaim-chunk-rows+ rows per owner quantum (fn-owner-orcp-
intern-chunk).  NIL when ACL2 refused a record."
  (let ((out nil) (rest rows))
    (loop while rest do
      (let* ((chunk (loop repeat +fnn-reclaim-chunk-rows+ while rest collect (pop rest)))
             (done (fnn-owner-gated (service :control)
                     (first (fnn-call 'fn-owner-orcp-intern-chunk chunk keyring generation
                                      (fnn-live-arena))))))
        (when (eq done :bad) (return-from fnn-owner-reclaim-intern nil))
        (unless (and (listp done) (= (length done) (length chunk)))
          (fnn-fault "owner returned a malformed interned chunk"))
        (push done out)))
    (let ((all nil)) (dolist (c out all) (setq all (nconc c all))))))

;;; Q16 (a) (lane online-reclaim-5): the swapped owner is the owner the full
;;; open of the rewritten history installs, BEFORE the open's recovery
;;; barriers (its Store :recovering; books/owner-reclaim-ready.lisp).  The
;;; open's three (fnn-store-recovery-barriers), delivered as fnn-owner-install
;;; delivers them; without them the writer's take never takes and every POST
;;; after the swap waits forever (fn-orrd-the-swap-without-the-barriers-never-
;;; takes).  The publication is already installed: a barrier that fails, or
;;; an owner that is not :ready after them, is a recovery event.
(defun fnn-owner-reclaim-barriers (store)
  (let ((phase nil))
    (dolist (barrier (fnn-store-recovery-barriers store))
      (handler-case (funcall barrier)
        (fnn-os-error (e)
          (fnn-owner-observe :recovery-barrier :uncertain)
          (fnn-indeterminate "reclaim swap: recovery barrier failed after the install (~a): recovery required" e)))
      (setq phase (fnn-owner-observe :recovery-barrier :ok)))
    (unless (eq phase :ready)
      (fnn-indeterminate "reclaim swap: the swapped owner is ~(~a~) after the recovery barriers: recovery required"
                         phase))))

(defun fnn-owner-reclaim-pass (service free)
  "`store reclaim --recorded' on the running owner: the capture under the
mutex (the pass's credit reserved, refused by name; the log rotated as a
publication's capture rotates it; the pass the publication in flight), then
off it the walk with the rewrite, the decision, the reclaimed checkpoint
staged (the rewritten rows' tombstoned records are the writer's sources),
the tombstones interned in owner quanta, the rebuild (the open's recovery
over the rewritten rows) and the fresh catalog and history columns; then ONE
owner quantum takes the swap when fn-orcp-swap-word answers :swap (nothing
committed since the capture, the pipeline idle, no other off-mutex reader),
installs the staged checkpoint (the commit point) and swaps the owner, the
catalog and the history columns; then off it the covered segments dropped
and their blocks given back (fnn-owner-release-extents).  A failure after
the install is a recovery event (the service stops; the open reads the new
publication).  Answers the reply word."
  (let* ((store (fnn-owner-service-store service))
         (clock (fnn-store-prepare-observation))
         (answer nil) (captured nil) (pin nil) (position nil) (stage nil) (ident nil)
         (installed nil) (swapped nil) (word :failed) (*fnn-checkpoint-frames* nil)
         (image nil)
         (started (get-internal-real-time)))
    (flet ((ms () (round (* 1000 (- (get-internal-real-time) started))
                         internal-time-units-per-second))
           (deferred (reason &rest more)
             (fnn-err "RECLAIM deferred reason=~(~a~)~{ ~a~}" reason more)
             (setq word (intern (format nil "DEFERRED-~a" (symbol-name reason)) :keyword))))
      (unwind-protect
           (block pass
             (unless (fnn-log-rotation-ready-p store) (fnn-log-prepare-spare store))
             (fnn-owner-gated (service :control)
               (setq answer (fnn-owner-core 'fn-owner-orcp-capture :recorded clock
                                            (fnn-checkpoint-budget-test-override nil)
                                            free (fnn-checkpoint-revision)))
               (when (eq (first answer) :captured)
                 (setq captured (second answer))
                 (setq position (fnn-log-rotate store))
                 ;; the history image's binding: the store's node and salt
                 (setq ident (fnn-owner-core 'fn-store-genesis-ident))
                 ;; an off-mutex arena reader from here (arena-reader-pins)
                 (setq pin (fnn-arena-pin))))
             (unless captured
               (unless (and (eq (first answer) :deferred) (integerp (third answer)))
                 (fnn-fault "owner returned a malformed reclaim capture"))
               (deferred :credit (format nil "estimate=~d" (third answer)))
               (return-from pass))
             (unless (and (true-listp captured) (= (length captured) 12))
               (fnn-fault "owner returned a malformed reclaim capture"))
             (fnn-reclaim-cut :captured)
             (destructuring-bind (records count v s profile configs frontier budget free* revision
                                  now record-octets)
                 captured
               (declare (ignore now))
               (let* ((ctx (fnn-core 'fn-owner-orc-ctx :recorded v s nil (fnn-live-arena)))
                      (acc nil) (rows nil) (decision nil))
                 (multiple-value-setq (acc rows) (fnn-owner-reclaim-walk records ctx t))
                 (setq decision (fnn-core 'fn-owner-orc-decide :recorded profile v s nil acc
                                          (fnn-live-arena)))
                 (fnn-reclaim-cut :rewritten)
                 (case (and (consp decision) (first decision))
                   (:refused (fnn-err "RECLAIM refused: ~(~a~)" (second decision))
                    (setq word (second decision)) (return-from pass))
                   (:none (fnn-err "RECLAIM records=~d reclaimed=0 ~a" count
                                   (fnn-reclaim-counts-line (second decision)))
                    (setq word :none) (return-from pass))
                   (:reclaim nil)
                   (t (fnn-fault "ACL2 returned no reclaim decision")))
                 ;; the reclaimed checkpoint, staged off the mutex
                 (let ((segment (fnn-core 'fn-ockp-segment-octets record-octets
                                          +fnn-checkpoint-batch-octets+)))
                   ;; as a publication stages it (fnn-owner-publish-captured):
                   ;; NEXT, the history image of NEXT's records with its
                   ;; binding into the F row's position, then the setup
                   (destructuring-bind (setup next n arun)
                       (let ((prepared (fnn-core 'fn-owner-sco-next nil nil configs rows
                                                 (fnn-checkpoint-walk rows) segment
                                                 (fnn-live-arena))))
                         (multiple-value-bind (position2 image2)
                             (if prepared
                                 (fnn-history-image-build
                                  (fnn-core 'fn-sco-records (first prepared))
                                  (first ident) (second ident) position)
                                 (values position nil))
                           (setq image image2)
                           (fnn-core 'fn-owner-sco-setup-of prepared frontier revision position2
                                     segment budget
                                     (fnn-core 'fn-his-stream-free free*
                                               (fnn-history-image-np image)))))
                     (declare (ignore next n))
                     (let ((verdict (first setup)))
                       (cond ((and (consp verdict) (eq (first verdict) :plan)))
                             ((and (consp verdict) (eq (first verdict) :deferred))
                              (deferred (second verdict)) (return-from pass))
                             (t (deferred :unencodable) (return-from pass))))
                     (fnn-log-make-durable (fnn-store-log store))
                     (unwind-protect
                          (setq stage (fnn-state-checkpoint-stage
                                       store
                                       (lambda (fd)
                                         (fnn-history-image-write fd image)
                                         (fnn-checkpoint-write-steps
                                          fd setup segment (length rows) (fnn-store-config store)
                                          (fnn-live-octets-pub) arun))))
                       (fnn-octets-pub-release))))
                 (fnn-reclaim-cut :staged)
                 (destructuring-bind (keyring generation)
                     (fnn-core 'fn-owner-orcp-keyring s)
                   (setq rows (fnn-owner-reclaim-intern service rows keyring generation)))
                 (unless rows (deferred :unencodable) (return-from pass))
                 (fnn-reclaim-cut :interned)
                 (let* ((rebuilt (fnn-core 'fn-owner-orcp-rebuild rows configs frontier
                                           (third answer)))
                        (cat (fnn-fresh-stobj 'fn-cat))
                        (hist (fnn-fresh-stobj 'fn-hist)))
                   (when (eq (second rebuilt) :fault)
                     (deferred :rebuild) (return-from pass))
                   (fnn-call 'fn-owner-orcp-load-columns
                             (fnn-owner-core 'fn-owner-orcp-key)
                             rows
                             (fnn-core 'fn-owner-orcp-view-index (second rebuilt))
                             (fnn-owner-core 'fn-owner-orcp-salt)
                             (fnn-live-arena) cat hist)
                   (fnn-reclaim-cut :rebuilt)
                   (dotimes (round +fnn-reclaim-swap-rounds+)
                     (let ((sw (fnn-owner-gated (service :control)
                                 (let ((w (fnn-owner-core 'fn-owner-orcp-swap-word count frontier s
                                                          (1- (fnn-arena-reader-count))
                                                          rebuilt)))
                                   (when (eq w :swap)
                                     ;; the commit point, then the swap, in one quantum
                                     (fnn-state-checkpoint-install store stage)
                                     (setq installed t)
                                     (fnn-reclaim-cut :installed)
                                     (fnn-owner-core 'fn-owner-orcp-swap rebuilt)
                                     (fnn-install-stobj 'fn-cat cat)
                                     (fnn-install-stobj 'fn-hist hist)
                                     (setq swapped t)
                                     ;; The swapped owner is the open's owner
                                     ;; before its recovery barriers: :ready
                                     ;; only after them, in this quantum
                                     ;; (fn-orrd-a-post-after-the-swap-is-
                                     ;; taken-as-before).
                                     (fnn-owner-reclaim-barriers store))
                                   w))))
                       (case sw
                         (:swap (return))
                         (:delta (deferred :delta) (return-from pass))
                         (:unbound (deferred :unbound) (return-from pass))
                         ((:busy :readers)
                          (when (= round (1- +fnn-reclaim-swap-rounds+))
                            (deferred sw) (return-from pass))
                          (sb-thread:thread-yield))
                         (t (fnn-fault "owner returned a malformed swap word")))))
                   (fnn-reclaim-cut :swapped)
                   (setq word :installed)
                   (let* ((covered (fnn-log-covered-indices store (first position)))
                          (paths (mapcar (lambda (k) (fnn-segment-path-at store k)) covered))
                          (dropped (fnn-log-drop store covered)))
                     (fnn-err "RECLAIM installed records=~d reclaimed=~d dropped=~d ms=~d"
                              count (length (second decision)) dropped (ms))
                     (fnn-owner-release-extents service store *fnn-checkpoint-frames* paths pin))
                   (fnn-reclaim-cut :released)))))
        (when pin (fnn-arena-unpin pin))
        ;; Installed and not swapped: the durable publication is the new one
        ;; and the served state the old one -- never served on: a recovery
        ;; event (the service stops, the open reads the new publication).
        (when (and installed (not swapped))
          (fnn-indeterminate "reclaim swap failed after the install: recovery required"))
        (when (and stage (not installed))
          (ignore-errors (fnn-unlink stage)))
        (when (and captured (not swapped))
          (fnn-owner-gated (service :control)
            (fnn-owner-core 'fn-owner-orcp-finish)))))
    word))

;;; PKT-101: reopen `[log] path' when ACL2 says a SIGHUP is due
;;; (books/owner-log-reopen.lisp fn-olr-decide, through fn-owner-log-reopen).
;;; Append-only, created 0640, never through a symlink, as at run.  The
;;; descriptor is swapped under the log mutex, so every line lands whole in
;;; the renamed file or in the new one; the old descriptor is closed after.
(defun fnn-owner-journal-open (service)
  "Open STORE/decisions/decisions.fnj for append and offer this run's start
entry (fn-otm-start-line: the wall reading and whether it is usable; a
run's monotonic readings are its own clock domain).  A journal
that cannot be opened is reported and the run continues without it: the
journal records decisions that stored nothing, so its absence costs replay
of those decisions, never durable state."
  (let* ((root (fnn-store-root (fnn-owner-service-store service)))
         ;; Its own directory, never the record log's journal/: that holds
         ;; the log's segments and nothing else (batch AX: a file there broke
         ;; the log's segment listing in test_native_log_compaction).
         (dir (fnn-join root "decisions")))
    (handler-case
        (progn
          (handler-case (fnn-mkdir dir #o750)
            (fnn-os-error () nil))
          (setq *fnn-journal-fd* (fnn-owner-open-log (fnn-join dir "decisions.fnj")))
          ;; PKT-872: cut a torn last entry (a process that died mid-append)
          ;; back to the last whole one before this run appends after it,
          ;; and hand ACL2's writer that offset.
          (setq *fnn-journal-w*
                (fnn-core 'fn-otm-jw-init
                          (fnn-owner-journal-cut (fnn-join dir "decisions.fnj")
                                                 *fnn-journal-fd*)))
          (sb-thread:with-recursive-lock (*fnn-log-queue-mutex*)
            (setq *fnn-journal-dropped* nil))
          ;; Lane time-bars (PRF-384): the run's clock domain begins here;
          ;; the entry records the wall observation and whether it is usable,
          ;; never a monotonic origin (it means nothing in another process).
          (multiple-value-bind (wall has-wall) (fnn-owner-wall-milliseconds)
            (fnn-journal-line (fnn-core 'fn-otm-start-line wall (and has-wall t)))))
      (fnn-os-error (condition)
        (when *fnn-journal-fd* (ignore-errors (fnn-close *fnn-journal-fd*)))
        (setq *fnn-journal-fd* nil *fnn-journal-w* nil)
        (fnn-err "decision journal not opened (~a); decisions that store nothing are not journaled this run"
                 condition)))))

(defun fnn-owner-journal-read-at (fd start count)
  "COUNT octets of FD from START (a regular file; short reads continued)."
  (let ((data (fnn-make-octets count)) (at 0))
    (fnn-posix () (sb-posix:lseek fd start sb-posix:seek-set))
    (loop while (< at count) do
      (let* ((buffer (fnn-make-octets (- count at)))
             (n (fnn-read-fd fd buffer)))
        (when (zerop n) (fnn-fault "decision journal shrank while its last entry was read"))
        (replace data buffer :start1 at :end2 n)
        (incf at n)))
    data))

(defun fnn-owner-journal-cut (path fd)
  "PKT-872: the length of the journal's whole entries (ACL2's
fn-otm-jw-open-step over chunks read backwards from the end, each at most
fn-otm-jw-open-chunk octets), the file truncated to it through FD when a
torn last entry follows.  Answers the offset the writer resumes at."
  (let ((rfd (fnn-open path (logior sb-posix:o-rdonly +fnn-o-nofollow+))))
    (unwind-protect
         (let* ((size (sb-posix:stat-size (fnn-fstat rfd)))
                (end size)
                (start (fnn-core 'fn-otm-jw-open-first size)))
           (loop
             (unless (and (integerp start) (<= 0 start end))
               (fnn-fault "ACL2 returned a malformed journal chunk start ~a" start))
             (let ((step (fnn-core 'fn-otm-jw-open-step
                                   (fnn-octet-list (fnn-owner-journal-read-at rfd start (- end start)))
                                   start)))
               (case (first step)
                 (:cut
                  (let ((cut (second step)))
                    (unless (and (integerp cut) (<= 0 cut size))
                      (fnn-fault "ACL2 returned a malformed journal cut ~a" cut))
                    (when (< cut size)
                      (fnn-posix (path) (sb-posix:ftruncate fd cut))
                      (fnn-log-line (fnn-core 'fn-otm-jw-cut-line size cut)))
                    (return cut)))
                 (:more (setq end start start (second step)))
                 (t (fnn-fault "ACL2 returned a malformed journal open step ~a" step))))))
      (fnn-close rfd))))

(defun fnn-owner-journal-close ()
  "After the writer stopped: close the journal's descriptor."
  (let ((fd *fnn-journal-fd*))
    (setq *fnn-journal-fd* nil *fnn-journal-w* nil)
    (when fd (ignore-errors (fnn-close fd)))))

(defun fnn-owner-open-log (path)
  (fnn-open path
            (logior sb-posix:o-wronly sb-posix:o-append
                    sb-posix:o-creat +fnn-o-nofollow+)
            #o640))

(defvar *fnn-owner-log-handled* 0)

(defun fnn-owner-maybe-reopen-log (service)
  (let ((requested *fnn-sighup-count*))
    (unless (= requested *fnn-owner-log-handled*)
      (let ((decision (fnn-owner-serialized
                       service nil
                       (lambda ()
                         (fnn-owner-core 'fn-owner-log-reopen
                                         (and *fnn-owner-log-path* t)
                                         *fnn-owner-log-handled* requested)))))
        (unless (and (consp decision)
                     (member (first decision) '(:reopen :ignore :none))
                     (integerp (second decision)))
          (fnn-fault "owner returned malformed log reopen ~a" decision))
        (when (eq (first decision) :reopen)
          (handler-case
              (let ((fd (fnn-owner-open-log *fnn-owner-log-path*)))
                ;; PKT-508: through the writer's queue while it runs, so
                ;; the swap never waits on a write in progress.
                (fnn-log-swap-fd fd)
                (fnn-owner-log 'fn-owner-log-line))
            (error (condition)
              ;; The old descriptor stays: a failed reopen loses no line.
              (fnn-err "service log reopen failed: ~a" condition))))
        (setq *fnn-owner-log-handled* (second decision))))))

(defun fnn-owner-start-tls-accept (service listener &optional (implicit-tls t))
  "PRF-162: accept implicit-TLS clients on LISTENER until the service stops.
With IMPLICIT-TLS nil, a further plain listener's clients (NNT-041).  The
thread is a worker, so the stop joins it with the clients."
  (fnn-with-roster (service)
    (let ((thread
            (sb-thread:make-thread
             (lambda ()
               (unwind-protect
                    (handler-case
                        (loop
                          (when (or *fnn-sigterm-requested*
                                    (fnn-owner-service-stopping service))
                            (return))
                          (let ((socket (fnn-accept-observe listener 1)))
                            (unless (eq socket :timeout)
                              (fnn-owner-launch-client service socket implicit-tls))))
                      (sb-bsd-sockets:socket-error (condition)
                        (unless (or *fnn-sigterm-requested*
                                    (fnn-owner-service-stopping service))
                          (fnn-err "owner TLS listener: ~a" condition))))
                 (fnn-with-roster (service)
                   (setf (fnn-owner-service-workers service)
                         (delete sb-thread:*current-thread*
                                 (fnn-owner-service-workers service) :test #'eq)))))
             :name (if implicit-tls "fn owner TLS accept" "fn owner accept"))))
      (push thread (fnn-owner-service-workers service))
      thread)))

(defun fnn-owner-accept (service listener once)
  ;; Darwin does not reliably wake a blocking accept(2) when another context
  ;; calls shutdown(2) on the listener.  Keep accept itself nonblocking and
  ;; let the ordinary owner thread poll readiness so a signal request is
  ;; consumed within one second even when the raw shutdown is only advisory.
  ;; The signal handler still performs no allocation, locking, or core call.
  (loop
    (when (or *fnn-sigterm-requested*
              (fnn-owner-service-stopping service))
      (return))
    (handler-case
        (let ((socket (fnn-accept-observe listener 1)))
          (unless (eq socket :timeout)
            (if once
                (progn
                  (fnn-mux-serve-once service socket)
                  (return))
              (fnn-owner-launch-client service socket)))
          ;; Before the next accept: the owner's checkpoint publication,
          ;; and a log reopen a SIGHUP asked for (PKT-101).
          (fnn-owner-cold-reap service)
          (fnn-owner-maybe-publish service)
          (fnn-owner-maybe-reopen-log service)
          ;; Row S9: a retiring node's drain step (host/native/admin.lisp).
          (fnn-owner-maybe-retire service))
      (sb-bsd-sockets:socket-error (condition)
        (unless (or *fnn-sigterm-requested*
                    (fnn-owner-service-stopping service))
          (error condition))))))

;;; PKT-875: a graceful stop drains the POSTs in flight to their replies
;;; (books/owner-stop-drain.lisp, PRF-357).  After a SIGTERM the accept loops
;;; have returned and no I/O loop steps new input (fnn-mux-work); the loops
;;; keep delivering and the committer keeps committing.  Every observation
;;; is taken after a clock event (fnn-owner-sched-snapshot) and ACL2 decides
;;; from it: :wait, :release (the drain deadline H passed: the committer tells
;;; every member in flight uncertain and sheds the queue, as at a stall), or
;;; :stop (nothing is owed, or the release's grace passed).  Only then the
;;; fence (fnn-owner-stop-service), which ends every connection.

(defun fnn-owner-drain-observation (service)
  "(AWAITING UNSENT): the members waiting for a reply (the connections
registered for a completion and the queued submissions), and the replies the
I/O loops still owe (host/native/mux.lisp fnn-mux-unsent)."
  (list (sb-thread:with-mutex ((fnn-owner-service-commit-lock service))
          (+ (hash-table-count (fnn-owner-service-awaiting service))
             (fnn-owner-service-queued service)))
        (fnn-mux-unsent service)))

(defun fnn-owner-drain-log (word s0 s limits awaiting)
  (let ((line (fnn-core 'fn-osd-log-line word s0 s limits awaiting)))
    (when line (fnn-log-line line))))

(defun fnn-owner-drain-service (service)
  "Drain SERVICE before its stop, as ACL2's fn-osd-drain-next names (the step
and whether the release was made); returns when it answers :stop, within the
deadline and its grace for any connection state (PRF-357
fn-osd-drain-stops-by-the-deadline).  Nothing here compares times or counts."
  (when (and (not (fnn-owner-service-stopping service))
             (fnn-owner-service-mux service))
    (let* ((limits (handler-case
                       (fnn-owner-serialized
                        service nil
                        (lambda () (fnn-owner-core 'fn-owner-barrier-limits))
                        :inspect)
                     (error (condition)
                       ;; Stopped (a fault) before the drain began: the
                       ;; fence has ended it already.
                       (if (fnn-owner-service-stopping service)
                           (return-from fnn-owner-drain-service nil)
                         (error condition)))))
           (s0 (progn (fnn-owner-space-preobserve service t)
                      (fnn-owner-sched-snapshot service)))
           (poll (fnn-core 'fn-osd-poll-ms))
           (released nil))
      (unless (and (integerp poll) (plusp poll))
        (fnn-fault "owner returned a malformed drain poll ~a" poll))
      (fnn-owner-drain-log :start s0 s0 limits 0)
      (loop
        (when (fnn-owner-service-stopping service) (return))
        (destructuring-bind (awaiting unsent) (fnn-owner-drain-observation service)
          (let ((s (progn (fnn-owner-space-preobserve service t)
                          (fnn-owner-sched-snapshot service))))
            (destructuring-bind (step released2 &rest more)
                (fnn-call 'fn-osd-drain-next s0 s limits awaiting unsent released)
             (declare (ignore more))
             (setq released released2)
             (case step
              (:stop
               (fnn-owner-drain-log :stop s0 s limits awaiting)
               (return))
              (:release
               (fnn-owner-drain-log :release s0 s limits awaiting)
               (sb-thread:with-mutex ((fnn-owner-service-commit-lock service))
                 (setf (fnn-owner-service-drain-release service) t)
                 (sb-thread:condition-broadcast (fnn-owner-service-commit-ready service))))
              (:wait nil)
              (t (fnn-fault "owner returned a malformed drain step ~a" step))))))
        (sleep (/ poll 1000))))))

(defun fnn-owner-run (root port once max-connections
                      &optional fault address (family :inet) tls-context
                        connection-fault-operation tls-port more-addresses)
  "Run one service from already-normalized boundary values.
MORE-ADDRESSES are the (FAMILY . OCTETS) after the first of an ACL2-admitted
`[listener] host' list (NNT-041); each gets the same port and TLS port."
  (setf (sb-ext:bytes-consed-between-gcs) (fnn-gc-nursery-octets))
  (setq *fnn-owner-measure*
        (equal (sb-ext:posix-getenv "FN_OWNER_MEASURE") "1"))
  (let ((service nil) (listener nil) (tls-listener nil) (more-listeners nil)
        (old-active *fnn-sigterm-owner-active*)
        (old-requested *fnn-sigterm-requested*)
        (old-wakeup-fd *fnn-sigterm-wakeup-fd*))
    (unwind-protect
         (progn
           (setq *fnn-sigterm-owner-active* t
                 *fnn-sigterm-requested* nil
                 *fnn-sigterm-wakeup-fd* nil)
           ;; PKT-508 (PRF-187): from here until the service is closed, a
           ;; log line or diagnostic is offered to the writer's queue and
           ;; never waited on (host/native/io.lisp fnn-log-offer).
           (fnn-log-writer-start)
           (unwind-protect
                (progn
                  (setq service (fnn-owner-install root max-connections fault))
                  ;; Before any client/module starts, retire startup-only
                  ;; cache borrows; absent policy never gets a warm bypass.
                  (fnn-extent-end-recovery-cache)
                  ;; Lane time-model-2: the decision journal
                  ;; (books/owner-time-journal.lisp), a segment per run
                  ;; opened by its start entry; the served reads' clock
                  ;; readings are events on this service's gate from here.
                  (fnn-owner-journal-open service)
                  (setq *fnn-owner-time-service* service)
                  ;; PRF-359: the first NEED and observation, before serving.
                  (fnn-owner-space-prime service)
                  ;; PRF-161: the listener this run binds decides the default
                  ;; of every absent exposure row (fn-exp-address-publicp).
                  (unless (member (fnn-owner-action 'fn-owner-exposure-install-set
                                                    (cons (list family
                                                                (and address (coerce address 'list)))
                                                          (mapcar (lambda (more)
                                                                    (list (car more)
                                                                          (coerce (cdr more) 'list)))
                                                                  more-addresses)))
                                  '(:public :loopback))
                    (fnn-fault "owner refused the exposure install"))
                  (fnn-owner-refresh-read-octets service)
                  (setf (fnn-owner-service-tls-context service) tls-context
                        (fnn-owner-service-connection-fault-operation service)
                        connection-fault-operation)
                  ;; PKT-605 (PRF-223): the live capacity against this
                  ;; machine (books/connection-budget.lisp), refused by name
                  ;; before anything listens; then the I/O loops.
                  (fnn-mux-budget-install service tls-context)
                  (sb-thread:with-mutex ((fnn-owner-service-lock service))
                    (fnn-payload-lifecycle-start service))
                  (fnn-owner-start-committer service)
                  (fnn-mux-start service)
                  ;; PKT-283's native witness: the Store is recovered and
                  ;; its writer lock held, and no control socket listens
                  ;; yet (the startup hooks start it), so `health' must say
                  ;; starting.  Held until SIGTERM (or SIGKILL); a developer
                  ;; image only (fnn-developer-selector-gate).
                  (when (fnn-developer-selector
                         "FN_NATIVE_OWNER_TEST_PAUSE_BEFORE_LISTEN")
                    (fnn-out "OWNER-PAUSED-BEFORE-LISTEN")
                    (loop until *fnn-sigterm-requested* do (sleep 0.05)))
                  (fnn-owner-run-startup-hooks service)
                  ;; Deterministic native witness for the signal window in
                  ;; which recovery is complete but no listener fd or module
                  ;; resource exists yet.  The signal still travels through
                  ;; fnn-main's real handler; this branch supplies no shortcut
                  ;; to the stop machinery.
                  (when (string= (or (fnn-developer-selector
                                      "FN_NATIVE_OWNER_TEST_SIGTERM") "")
                                 "after-install")
                    (fnn-out "OWNER-PRELISTEN")
                    (sb-posix:kill (sb-posix:getpid) sb-unix:sigterm)
                    (loop repeat 1000
                          until *fnn-sigterm-requested*
                          do (sb-thread:thread-yield)))
                  (when *fnn-sigterm-requested*
                    (fnn-owner-stop-service service +fnn-exit-ok+)
                    (return-from fnn-owner-run +fnn-exit-ok+))
                  (multiple-value-bind (bound bound-port)
                      (fnn-listen port :address address :family family
                                       :backlog +fnn-owner-listen-backlog+)
                    (setf listener bound
                          (fnn-owner-service-listener service) bound
                          *fnn-sigterm-wakeup-fd*
                          (sb-bsd-sockets:socket-file-descriptor bound))
                    ;; A signal in the small post-install/pre-bind window set
                    ;; the flag but had no fd to wake.  Consume it here before
                    ;; any module resource starts.
                    (if *fnn-sigterm-requested*
                        (fnn-owner-stop-service service +fnn-exit-ok+)
                      (progn
                        (dolist (hook (fnn-owner-service-start-hooks service))
                          (funcall hook service))
                        ;; NNT-041: one more listener per further admitted
                        ;; address, on the port the first one bound, each
                        ;; with its own accept worker (as the TLS one).
                        (unless once
                          (dolist (more more-addresses)
                            (let ((extra (fnn-listen bound-port :address (cdr more)
                                                                :family (car more)
                                                                :backlog +fnn-owner-listen-backlog+)))
                              (push extra more-listeners)
                              (fnn-owner-start-tls-accept service extra nil))))
                        ;; Recovery is done: from here the owner serves.
                        (fnn-owner-release-recovery-garbage)
                        (fnn-owner-service-nursery)
                        (fnn-out "LISTENING ~d" bound-port)
                        ;; PRF-162: the implicit-TLS listener ACL2 offered
                        ;; (fn-native-operator-result-run-implicit-tls-port),
                        ;; on the same address, with its own accept thread.
                        (when (and tls-port tls-context (not once))
                          (multiple-value-bind (tls-bound tls-bound-port)
                              (fnn-listen tls-port :address address :family family
                                                   :backlog +fnn-owner-listen-backlog+)
                            (setq tls-listener tls-bound)
                            (fnn-owner-start-tls-accept service tls-bound)
                            (dolist (more more-addresses)
                              (let ((extra (fnn-listen tls-bound-port :address (cdr more)
                                                                      :family (car more)
                                                                      :backlog +fnn-owner-listen-backlog+)))
                                (push extra more-listeners)
                                (fnn-owner-start-tls-accept service extra)))
                            (fnn-out "LISTENING-TLS ~d" tls-bound-port)))
                        (fnn-owner-accept service listener once))))
                  (when *fnn-sigterm-requested*
                    ;; PKT-875: the POSTs in flight are answered first.
                    (fnn-owner-drain-service service)
                    (fnn-owner-stop-service service +fnn-exit-ok+))
                  (fnn-owner-service-exit-code service))
             (unwind-protect
                  (when service
                    ;; Cleanup itself is a stop boundary too: wake workers
                    ;; before joining, then close modules/FNFD/Store while the
                    ;; wake fd remains open and cannot be reused.
                    (fnn-owner-stop-service
                     service (fnn-owner-service-exit-code service))
                    (fnn-owner-wait-workers service)
                    (fnn-owner-cold-shutdown service)
                    (let ((committer (fnn-owner-service-committer service)))
                      (when committer
                        (ignore-errors (sb-thread:join-thread committer :default nil))))
                    ;; A failed committer can leave an in-flight syncer. No
                    ;; further syncer can start once the committer has returned.
                    (let ((worker (fnn-owner-service-committer service)))
                      (when (or (null worker) (not (sb-thread:thread-alive-p worker)))
                        (fnn-owner-wait-workers service)))
                    (fnn-owner-measure-report)
                    ;; Keep the captured listener fd live while the focused
                    ;; test delivers a repeated SIGTERM during cleanup.
                    (when (string= (or (fnn-developer-selector
                                        "FN_NATIVE_OWNER_TEST_PAUSE_CLEANUP") "")
                                   "1")
                      (fnn-out "OWNER-CLEANUP")
                      (sleep 2))
                    ;; Failed module cleanup is never evidence of quiescence.
                    (let ((modules-joined t))
                      (dolist (hook (fnn-owner-service-close-hooks service))
                        (handler-case (funcall hook service)
                          (serious-condition () (setq modules-joined nil))))
                      (fnn-owner-feed-close-all service)
                      (fnn-store-close (fnn-owner-service-store service))
                      (when (and modules-joined
                                 (null (fnn-with-roster (service)
                                         (fnn-owner-service-workers service)))
                                 (null (fnn-owner-service-cold-head service))
                                 (every (lambda (slot)
                                          (let ((worker (fnn-cold-worker-thread slot)))
                                            (or (null worker)
                                                (not (sb-thread:thread-alive-p worker)))))
                                        *fnn-cold-workers*)
                                 (let ((worker (fnn-owner-service-committer service)))
                                   (or (null worker) (not (sb-thread:thread-alive-p worker)))))
                        (sb-thread:with-mutex ((fnn-owner-service-lock service))
                          (fnn-payload-lifecycle-joined service)))))
               (setq *fnn-sigterm-wakeup-fd* nil)
               (dolist (extra more-listeners) (fnn-socket-shut extra))
               (when tls-listener (fnn-socket-shut tls-listener))
               (when listener (fnn-socket-shut listener)))))
      ;; Drain and stop the writer before the caller closes `[log] path'.
      (setq *fnn-owner-time-service* nil)
      (fnn-log-writer-stop)
      (fnn-owner-journal-close)
      (setq *fnn-sigterm-wakeup-fd* old-wakeup-fd
            *fnn-sigterm-requested* old-requested
            *fnn-sigterm-owner-active* old-active))))

(defun fnn-owner-run-normalized (store-octets listener-host-octets
                                 listener-port oncep max-connections &optional tls-context
                                 tls-port)
  "Operator callback over ACL2-normalized projections; no argv semantics."
  (unless (and (typep store-octets 'fnn-octets)
               (typep listener-host-octets 'fnn-octets)
               (integerp listener-port) (<= 0 listener-port 65535)
               (member oncep '(t nil))
               (integerp max-connections) (> max-connections 0)
               (or (null tls-context) (fnn-tls-context-p tls-context))
               (or (null tls-port)
                   (and tls-context (integerp tls-port) (< 0 tls-port 65536)
                        (/= tls-port listener-port) (not oncep))))
    (fnn-fault "malformed ACL2 owner run plan"))
  (let* ((root (fnn-octets-string store-octets))
         (projections
           (fnn-core 'fn-native-config-host-listener-addresses
                     (fnn-octet-list listener-host-octets))))
    ;; NNT-041 (PRF-197): ACL2 admitted every address and projected each to
    ;; the family and octets bound here; the host re-checks only the shape.
    (unless (and (consp projections) (listp projections)
                 (every (lambda (projection)
                          (and (listp projection) (= (length projection) 2)
                               (member (first projection) '(:inet :inet6))
                               (fnn-octet-list-p (second projection))
                               (= (length (second projection))
                                  (if (eq (first projection) :inet) 4 16))))
                        projections))
      (fnn-fault "ACL2 listener address projection is malformed"))
    (let ((family (first (first projections)))
          (address-list (second (first projections))))
      ;; The served owner is armed exactly as `store ROOT post' is: the same
      ;; function reads the same selectors into the same store slot, so a
      ;; developer image kills the served owner at every fnn-at coordinate
      ;; of the cut table (campaign dabebb84, F1).  The control fault is
      ;; validated here too, before the store opens.
      (fnn-owner-control-test-fault)
      ;; A developer image may instead arm one of fn-bs-scp-program's five
      ;; cuts, which only the owner's automatic publication reaches.
      (fnn-owner-run root listener-port oncep max-connections
                     (or (fnn-post-entry-fault nil) (fnn-state-checkpoint-test-fault))
                     (fnn-octets address-list)
                     family tls-context nil tls-port
                     (mapcar (lambda (projection)
                               (cons (first projection)
                                     (fnn-octets (second projection))))
                             (rest projections))))))

(defun fnn-command-owner (command args)
  "Private low-level test entry; public operators use the normalized callback."
  (unless (string= command "run")
    (error 'fnn-usage-error :message "unknown owner command"))
  (when (< (length args) 4)
    (error 'fnn-usage-error
           :message "owner run ROOT PORT ONCE MAX-CONNECTIONS"))
  (let* ((inject (fifth args))
         (connection-fault-operation
           (and inject (string= inject "connectionhandler") :receive))
         (fault (fnn-post-entry-fault
                 (and (null connection-fault-operation) inject))))
    (fnn-owner-run (first args) (parse-integer (second args))
                   (string= (third args) "1") (parse-integer (fourth args))
                   fault nil :inet nil connection-fault-operation)))

(fnn-register-developer-verb "owner" #'fnn-command-owner)
