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

(defstruct (fnn-owner-service (:constructor %make-fnn-owner-service))
  store lock listener stopping (exit-code +fnn-exit-ok+) (feeds nil)
  (workers nil) (clients nil) tls-context
  ;; The scheduler gate in front of LOCK (fnn-owner-gated), and the roster
  ;; mutex that protects WORKERS, CLIENTS, PUBLISHER and the stop flag's
  ;; publication to the accept threads: host lists, not owner state, so
  ;; their edits never queue at the gate.
  (gate nil) (roster (sb-thread:make-mutex :name "fn owner roster"))
  ;; The checkpoint publication's thread while one runs (fnn-owner-maybe-publish).
  (publisher nil)
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
  (commits 0) (waiters 0))

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
      (fnn-log-line line))))


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

(defun fnn-owner-render-next (plan)
  "Render the next window of PLAN: (values OCTETS PLAN-REST DONEP), OCTETS a
fresh vector (empty only when nothing remained), DONEP when nothing remains
after it."
  (let ((size (fnn-core 'fn-splan-window-size plan)))
    (unless (and (integerp size) (>= size 0))
      (fnn-fault "owner returned a malformed render window size"))
    (destructuring-bind (status rest buf)
        (fnn-call 'fn-splan-window plan size (fnn-make-render-buffer size))
      (unless (eq status :ok)
        (fnn-fault "owner returned non-octets in its served reply"))
      (let ((array (svref buf 0)) (fill (svref buf 1)))
        (values (if (= fill (length array))
                    (the fnn-octets array)
                  (subseq (the fnn-octets array) 0 fill))
                rest
                (and (fnn-core 'fn-splan-donep rest) t))))))

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
(defun fnn-owner-advance-clock ()
  "Hand the owner one fresh reading of this host's clocks.

The caller holds the owner mutex.  :refused is the model's answer to a
reading it cannot reconcile, not a host fault: a clock-less owner refuses to
inject, refuses to declare a group and answers DATE 503, each with its own
line, and the next reading is admitted whatever it says.  :invalid means this
function supplied no observation at all, which is a defect here."
  (multiple-value-bind (wall has-wall) (fnn-owner-wall-milliseconds)
    (let ((outcome (fnn-owner-action
                    'fn-owner-observe
                    (floor (* (get-internal-real-time) 1000)
                           internal-time-units-per-second)
                    wall +fnn-owner-wall-error-ms+ has-wall)))
      (when (eq outcome :invalid)
        (fnn-fault "owner was handed a malformed clock reading"))
      outcome)))

(defun fnn-owner-finish ()
  (fnn-owner-action 'fn-owner-finish))

(defun fnn-owner-finish-submission ()
  "The article completion's word, fn-ccar-own-finish's, which is fn-own-finish's (host/owner-host.lisp)."
  (fnn-owner-action 'fn-owner-finish-submission))

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
                  (:migration-required
                   (fnn-fault "FNFD migration required before legacy timing outcome: ~a"
                              path))
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
  (let* ((store (fnn-owner-service-store service))
         (peers (append configured (fnn-owner-feed-existing-peers store)))
         (opened nil))
    (handler-case
        (progn
          (dolist (peer (remove-duplicates peers :test #'string=))
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

(defun fnn-owner-recover-core (store records max-connections)
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
         (result (fnn-owner-core 'fn-owner-recover-from-store-open max-connections)))
    (unless (eq result :recovering)
      (fnn-fault "owner rejected committed history"))
    (unless (eq (fnn-owner-core 'fn-owner-sco-note-durable s) :noted)
      (fnn-fault "owner refused the durable checkpoint sequence"))
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
(defun fnn-owner-load-node-secret (store)
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
    (unless (eq (fnn-owner-core 'fn-owner-install-node-secret (cons current retained))
                :installed)
      (fnn-refuse "node secret files in ~a do not form a key ring (epochs must decrease from the current one)"
                  (fnn-node-secret-directory store)))))

(defun fnn-owner-install (root max-connections &optional fault)
  (multiple-value-bind (store records) (fnn-open-live-store root t fault)
    (let ((service nil))
      (handler-case
          (progn
            ;; PKT-648: the store's durability policy against its mount
            ;; (books/store-mount-identity.lisp fn-smid-start-verdict),
            ;; before the owner serves anything.
            (fnn-check-filesystem-identity store t)
            (fnn-owner-recover-core store records max-connections)
            (fnn-err "OWNER-OPEN ~a" (fnn-open-report store))
            ;; The persisted profile ACL2 decoded at open, handed back once:
            ;; the owner's transaction budget is derived from it there.
            (unless (eq (fnn-owner-core 'fn-owner-install-profile
                                        (fnn-store-config store))
                        :installed)
              (fnn-fault "owner refused the store profile"))
            ;; SEC-006: the node secret, handed to the owner after the
            ;; recovery that built it (fnn-owner-load-node-secret).
            (fnn-owner-load-node-secret store)
            ;; Five fresh namespace observations, now delivered to fn-owner.
            (let ((phase nil))
              (dolist (barrier
                       (list (lambda () (fnn-fsync-regular (fnn-config-path store)))
                             (lambda () (fnn-fsync-regular (fnn-frontier-path store)))
                             (lambda () (fnn-fsync-dir (fnn-transactions store)))
                             (lambda () (fnn-fsync-dir (fnn-store-root store)))
                             (lambda () (fnn-fsync-dir
                                         (fnn-parent (fnn-store-root store))))))
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
              (fnn-owner-key-statement-recover service records)
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
  (waiting (make-array 4 :initial-element 0))
  (next-ticket (make-array 4 :initial-element 0))
  (serving (make-array 4 :initial-element 0))
  (busy nil)
  (holder nil)
  (turn nil)
  (sched nil))

(defun fnn-make-owner-gate ()
  (%make-fnn-owner-gate :sched (fnn-core 'fn-osch-init)))

(defun fnn-owner-class-index (class)
  "The class's slot, ACL2's (fn-osch-class-index); a name ACL2 does not
recognise is a host fault."
  (unless (fnn-core 'fn-osch-classp class)
    (fnn-fault "unknown owner service class ~a" class))
  (let ((i (fnn-core 'fn-osch-class-index class)))
    (unless (and (integerp i) (<= 0 i 3))
      (fnn-fault "owner returned a malformed service class slot"))
    i))

(defun fnn-ms-since (started)
  (round (* 1000 (- (get-internal-real-time) started)) internal-time-units-per-second))

(defun fnn-owner-gate-pick (gate)
  "The owner is free and nobody was admitted: ask ACL2 which class runs
(nil when no class waits).  The caller holds the gate mutex."
  (destructuring-bind (class sched)
      (fnn-call 'fn-osch-next (fnn-owner-gate-sched gate)
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
          (fnn-core 'fn-osch-observe (fnn-owner-gate-sched gate) class hold-ms wait-ms))
    (fnn-owner-gate-pick gate)))

(defun fnn-owner-sched-snapshot (service)
  "ACL2's scheduler value, for `health' (fn-osch-health-lines)."
  (let ((gate (fnn-owner-service-gate service)))
    (sb-thread:with-mutex ((fnn-owner-gate-mutex gate))
      (fnn-owner-gate-sched gate))))

(defmacro fnn-owner-gated ((service class) &body body)
  "Run BODY under the owner mutex, admitted by the gate as CLASS."
  (let ((g (gensym "GATE")) (c (gensym "CLASS")) (w (gensym "WAITED"))
        (h (gensym "HELD")))
    `(let* ((,g (fnn-owner-service-gate ,service))
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
(fnn-owner-serialized refuses once STOPPING is set)."
  (fnn-with-roster (service)
    (unless (fnn-owner-service-stopping service)
      (setf (fnn-owner-service-stopping service) t
            (fnn-owner-service-exit-code service) exit-code)))
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
    (unless (eq socket answering)
      (ignore-errors
        (sb-bsd-sockets:socket-shutdown socket :direction :io))))
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

(defun fnn-owner-fault-service (service cid condition)
  "Contain an invalid core/store image, distinct from client refusal or EOF."
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
  (handler-case (funcall thunk)
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

(defun fnn-owner-publish-prepared (service label)
  "Publish and finish the one ACL2-prepared owner transaction."
  (let* ((store (fnn-owner-service-store service))
         (record (fnn-owner-core 'fn-owner-pending-octets))
         ;; The file is named from the staged record's own sequence, ACL2's
         ;; (fn-sbud-pending-sequence); the host keeps no count of its own.
         (sequence (fnn-pending-sequence
                    (fnn-owner-core 'fn-owner-pending-sequence))))
    (unless (fnn-octet-list-p record)
      (fnn-fault "owner returned malformed ~a transaction" label))
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
    (fnn-mark-committed store sequence)
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
;; answers are fn-pb-existing-action's :duplicate / :conflict (books/poster-bytes.lisp,
;; keyed on the poster's source through the injection inverse, D25), :clock-unusable,
;; :unaffordable (the Store's transaction budget, fn-sbud-refusal-kind), or
;; :refused.
(defun fnn-owner-prepare-refusal-word (prepared)
  (case prepared
    ((:duplicate :conflict :clock-unusable :refused :unaffordable) prepared)
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
          (fnn-validate-post-boundary
           (fnn-owner-core 'fn-owner-post-boundary (fnn-octet-list msgid)
                           (length payload) (length codes) charge))
          ;; The payload goes to the core in the octet buffer
          ;; (books/octets-stobj.lisp): filled once here from the byte
          ;; vector, read in place by the existing-article test and the
          ;; prepare (host/owner-host.lisp fn-owner-existing-action-buffer,
          ;; fn-owner-prepare-buffer), and the subject identity is digested
          ;; from it in place (fnn-metadata-buffer, fnn-subject-id-buffer;
          ;; books/sha256-buffer.lisp).  Nothing between the fill and the
          ;; prepare writes the buffer; all of it runs under the service mutex.
          (fnn-octets-fill payload)
          (case (fnn-owner-buffer-action 'fn-owner-existing-action-buffer
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
                      (fnn-owner-buffer-action
                       'fn-owner-prepare-buffer (fnn-octet-list msgid) codes
                       (fnn-octet-list obligation) (fnn-octet-list subject)
                       (fnn-octet-list evidence) charge)))
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

(defun fnn-owner-note-transit-verdict (payload nntp-transit-p ed ml)
  (setq *fnn-owner-transit-verdict*
        (fnn-owner-core 'fn-owner-transit-verdict (fnn-octet-list payload)
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
                                  (fnn-octet-list payload) t ed ml)))
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
  (let ((filing (fnn-owner-core 'fn-owner-control-filing
                                (fnn-octet-list payload)
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
                              (fnn-octet-list payload))))
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
             (fnn-validate-post-boundary
              (fnn-owner-core 'fn-owner-post-boundary (fnn-octet-list msgid)
                              (length payload) (length codes) charge))
             (case (fnn-owner-action 'fn-owner-existing-action
                                     (fnn-octet-list msgid)
                                     (fnn-octet-list payload) codes)
               (:duplicate (return-from fnn-owner-attempt-transit :duplicate))
               (:conflict (return-from fnn-owner-attempt-transit
                            (fnn-owner-transit-refused :conflict))))
             (let ((plan (fnn-owner-core 'fn-owner-peer-carrier-plan
                                         (fnn-octet-list payload)
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
                             (fnn-octet-list msgid) (fnn-octet-list payload)
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
                           (fnn-octet-list msgid) (fnn-octet-list payload)
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
                    (fnn-owner-identity-commit service event))))))))))))

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
        (fnn-log-line (fnn-owner-core 'fn-owner-key-statement-log-line plan
                                      outcome (and at-open t)))
        outcome))))

;;; The cut between the statement's commit and its key change's
;;; (books/key-statements.lisp fn-ks-cut).  A developer image started with
;;; FN_NATIVE_KEY_STATEMENT_FAULT=statement-committed:kill dies here, after a
;;; kind-4 composite is durable and before the executor runs; production has
;;; no injection branch.
(defun fnn-owner-key-statement-cut ()
  (let ((raw (fnn-developer-selector "FN_NATIVE_KEY_STATEMENT_FAULT")))
    (when raw
      (unless (string= raw "statement-committed:kill")
        (fnn-fault "invalid FN_NATIVE_KEY_STATEMENT_FAULT (expected statement-committed:kill)"))
      (sb-posix:kill (sb-posix:getpid) sb-unix:sigkill)
      (fnn-fault "test SIGKILL did not terminate the process"))))

;;; WORD is the kind-4 commit's outcome.  After a durable composite the
;;; executor runs; a refused key change leaves WORD (the article is
;;; accepted) and names the refusal in the transit detail, so the reported
;;; outcome names both.
(defun fnn-owner-statement-committed (service event word)
  (when (eq word :durable)
    (fnn-owner-key-statement-cut)
    (when (eq (fnn-owner-key-statement service event) :refused)
      (setq *fnn-owner-transit-detail* :key-change-refused)))
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
    (fnn-owner-preflight-publication
     service (fnn-core 'fn-store-event-kind event))
    (let ((*fnn-observe-callback* #'fnn-owner-observe)
          (*fnn-finish-callback* #'fnn-owner-finish))
      (fnn-advance-frontier store
                            (fnn-nat (fnn-owner-core 'fn-owner-next-txid)))
      (let ((prepared (fnn-owner-action 'fn-owner-prepare-identity event)))
        (unless (eq prepared :prepared)
          (unless (eq (fnn-owner-action 'fn-owner-refuse-reservation) :refused)
            (fnn-indeterminate "owner could not consume refused identity reservation"))
          (fnn-refuse "canonical Store refused identity event")))
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
                   (fnn-octet-list (fnn-anchor-csprng-nonce 32))))
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
                 (fnn-owner-core 'fn-owner-consumer-local-poll first))
                ;; PRF-234: a consumer bound to an account; SECOND is the
                ;; account's password, which only ACL2 compares.
                (:bound-poll
                 (fnn-owner-core 'fn-owner-consumer-local-bound-poll
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
          (case operation
            (:status (list :consumer-status-reply :refused nil nil nil))
            ;; A refused poll answers on the poll reply kind
            ;; (fn-ncl-poll-reply-encode :refused), as the non-owner refusal
            ;; does.  PRF-234: before, a refused plain poll answered a kind-5
            ;; frame that the poll client cannot decode, so every refused
            ;; poll (an unknown consumer included) printed `uncertain' (exit
            ;; 3); a refusal is now `refused' (exit 1).
            ((:poll :bound-poll) (list :consumer-poll-reply :refused nil nil))
            (otherwise (list :consumer-reply :refused nil))))
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
    (:refused (list :consumer-poll-reply :refused nil nil))
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
        (list :consumer-poll-reply :refused nil nil)))
    (unwind-protect
         (loop
           (let* ((seen (sb-thread:with-mutex (lock)
                          (fnn-owner-service-commits service)))
                  (step (fnn-owner-serialized
                         service nil
                         (lambda ()
                           (fnn-owner-core 'fn-owner-consumer-local-wait-step
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
completion reply (an ACL2 octet list, appended to the step's render plan)
and whether the outcome was uncertain."
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
              (values cid (fnn-owner-list-global 'fn-owner-output) t)))
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
                  (values cid (fnn-owner-list-global 'fn-owner-output) nil))
              (if (not (eq intent :ready))
                  (progn
                    (if transitp
                        (progn
                          (setq *fnn-owner-transit-detail* :intent)
                          (fnn-owner-transit-complete
                           cid :want transit-reason :refused))
                      (progn (fnn-owner-action 'fn-owner-outcome cid :refused)
                             (fnn-owner-log)))
                    (values cid (fnn-owner-list-global 'fn-owner-output) nil))
                (progn
                  ;; Durable intent before the first Store mutation.  Empty is
                  ;; a complete plan when the ACL2 target set is empty.
                  (fnn-owner-feed-flush service intent-publication)
                  (let ((word (if transitp
                                  (fnn-owner-attempt-transit
                                   service msgid payload groups evidence t)
                                (fnn-owner-attempt-served
                                 service msgid payload groups evidence))))
                    (fnn-owner-feed-flush
                     service
                     (fnn-owner-feed-step 'fn-owner-submission-resolution
                                          word (fnn-octet-list evidence)
                                          generation txid))
                    (if transitp
                        (fnn-owner-transit-complete
                         cid :want transit-reason word)
                      (progn (fnn-owner-action 'fn-owner-outcome cid word)
                             (fnn-owner-log)))
                    (values cid (fnn-owner-list-global 'fn-owner-output)
                            (eq word :uncertain))))))))))))

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
                                     (fnn-owner-action 'fn-owner-operator-submit
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
                        (let ((reason (fnn-owner-core 'fn-owner-operator-refusal-reason
                                                      (fnn-octet-list msgid)
                                                      (mapcar #'fnn-octet-list groups)
                                                      (fnn-octet-list payload))))
                          (list :reason
                                (fnn-core 'fn-native-control-host-refusal-status reason)
                                reason))
                      status))
                :clock-unusable))
         (when armed (fnn-owner-control-disarm-fault store armed)))))
   :poster))

(defun fnn-owner-handle-chunk (service cid incoming &optional socket (class :reader))
  "Run one owner read and its serial writer drain under the service mutex,
admitted by the gate as CLASS (:reader, or :transit for a peer connection).

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
     (block step
       ;; One reading per read, before the transition that decides under it.
       ;; books/owner.lisp fn-own-open: "The injection clock is not pinned:
       ;; fn-own-read supplies the owner's current observation with every read,
       ;; so each submission is injected at its own time (RFC 5537 section
       ;; 3.4)."  Without this the owner's current observation is whatever the
       ;; process started with, and every article of a run carries one Date.
       (fnn-owner-advance-clock)
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
       (let ((step (fnn-core-buffer-state 'fn-owner-chunk-span cid 0 (length incoming))))
         (when (eq step :unknown)
           (fnn-refuse "owner no longer knows connection ~d" cid))
         (unless (fnn-core 'fn-splan-step-p step)
           (fnn-fault "owner returned a malformed served step"))
         ;; One ACL2-rendered line per 441 this read sends (books/owner-log.lisp
         ;; fn-olog-served-refusal-lines): a POST refused before it became a
         ;; submission has no outcome line of its own.
         (let ((lines (fnn-core 'fn-splan-step-refusal-lines step)))
           (unless (every #'fnn-octet-list-p lines)
             (fnn-fault "owner returned malformed refusal log lines"))
           (dolist (line lines) (fnn-log-line line)))
         (let ((closing (fnn-core 'fn-splan-step-closep step))
               (starttls (fnn-core 'fn-splan-step-starttlsp step))
               (submitted (fnn-core 'fn-splan-step-submittedp step))
               (consumed (fnn-core 'fn-splan-step-consumed step))
               (completion nil)
               (uncertain nil)
               (redeem nil))
           (unless (and (integerp consumed) (<= 0 consumed (length incoming)))
             (fnn-fault "owner returned malformed receive-prefix count"))
           (when submitted
             (multiple-value-bind (reply-cid done stop)
                 (fnn-owner-drain-one service)
               (when (and reply-cid (not (= reply-cid cid)))
                 (fnn-fault "writer drained a different connection"))
               (setq completion done uncertain stop)))
           ;; PRF-164: an XREDEEM PASS left this connection holding; the
           ;; owner plans and publishes, and only then renders 281 or 482.
           (when (fnn-owner-core 'fn-acct-host-owner-redeem-waitingp cid)
             (setq redeem (fnn-octet-list (fnn-owner-account-redeem service cid))))
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
           (values (fnn-core 'fn-splan-step-plan step completion redeem)
                   (or closing uncertain) starttls consumed (and redeem t)
                   submitted)))))
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
  "Register the socket with a loop before it can enter the owner core."
  (fnn-mux-adopt service socket implicit-tls))

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

(defun fnn-owner-publish-captured (service captured)
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
  (unwind-protect
  (destructuring-bind (base configs records record-octets count suffix budget frontier free revision)
      captured
    (declare (ignore count))
    (let ((started (get-internal-real-time)) (next nil) (durablep nil) (verdict nil)
          ;; the writer's segment: ACL2's choice under the record bound R the
          ;; capture handed over (fn-ockp-segment-octets, the verb's derivation)
          (segment (fnn-core 'fn-ockp-segment-octets record-octets
                             +fnn-checkpoint-batch-octets+)))
      (flet ((elapsed ()
               (round (* 1000 (- (get-internal-real-time) started))
                      internal-time-units-per-second)))
        (handler-case
            (let ((sequence (length records)))
              (setq next (fnn-core 'fn-ock-next-checkpoint base configs records))
              (let ((setup (fnn-core 'fn-ockp-setup next frontier revision segment budget free)))
                (unless (and (consp setup) (= (length setup) 7))
                  (fnn-fault "owner returned a malformed checkpoint setup"))
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
                   (let ((octets (second verdict)) (steps 0)
                         (store (fnn-owner-service-store service)))
                     (handler-case
                         (progn
                           (fnn-state-checkpoint-write
                            store
                            (lambda (fd)
                              (setq steps (fnn-checkpoint-write-steps
                                           fd setup segment sequence (fnn-store-config store)
                                           (fnn-live-octets-pub)))))
                           (setq durablep t)
                           (fnn-err "CHECKPOINT auto sequence=~d suffix=~d octets=~d steps=~d ms=~d"
                                    sequence suffix octets steps (elapsed)))
                       ((or fnn-store-io-refusal fnn-store-indeterminate) (e)
                         (fnn-err "CHECKPOINT auto failed sequence=~d: ~a" sequence e)))))
                  (t (fnn-fault "owner returned a malformed checkpoint verdict")))))
          (serious-condition (e)
            (fnn-err "CHECKPOINT auto failed: ~a" e))))
      (unwind-protect
           (handler-case
               (fnn-owner-gated (service :control)
                 (when next
                   (let ((done (fnn-owner-core 'fn-owner-sco-publication-done
                                               next durablep verdict)))
                     (when (and durablep (not (integerp done)))
                       (fnn-err "CHECKPOINT auto: owner refused the durable sequence")))))
             (serious-condition (e)
               (fnn-err "CHECKPOINT auto failed: ~a" e)))
        (fnn-with-roster (service)
          (setf (fnn-owner-service-publisher service) nil
                (fnn-owner-service-workers service)
                (delete sb-thread:*current-thread*
                        (fnn-owner-service-workers service) :test #'eq))))))
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
  (fnn-owner-gated (service :control)
    (unless (or (fnn-owner-service-stopping service)
                (fnn-with-roster (service) (fnn-owner-service-publisher service)))
      ;; The budget override is nil but on a developer image with
      ;; FN_NATIVE_CHECKPOINT_BUDGET_TEST set; ACL2 chooses between it and
      ;; the profile's (fn-owner-sco-budget) on the due path and at the
      ;; capture, so both see one budget.  The free space is observed once
      ;; and handed to both.
      (let ((free (fnn-disk-free-octets (fnn-owner-service-store service))))
        (when (eq (fnn-owner-core 'fn-owner-sco-due
                                  (fnn-checkpoint-budget-test-override nil) free)
                  :due)
          (let ((captured (fnn-owner-core 'fn-owner-sco-capture
                                          (fnn-checkpoint-budget-test-override nil)
                                          free (fnn-checkpoint-revision))))
            (unless (and (true-listp captured) (= (length captured) 10))
              (fnn-fault "owner returned a malformed checkpoint capture"))
            (fnn-with-roster (service)
              (let ((thread (sb-thread:make-thread
                             (lambda () (fnn-owner-publish-captured service captured))
                             :name "fn owner checkpoint")))
                (setf (fnn-owner-service-publisher service) thread)
                (push thread (fnn-owner-service-workers service))))))))))

;;; PKT-101: reopen `[log] path' when ACL2 says a SIGHUP is due
;;; (books/owner-log-reopen.lisp fn-olr-decide, through fn-owner-log-reopen).
;;; Append-only, created 0640, never through a symlink, as at run.  The
;;; descriptor is swapped under the log mutex, so every line lands whole in
;;; the renamed file or in the new one; the old descriptor is closed after.
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
          (fnn-owner-maybe-publish service)
          (fnn-owner-maybe-reopen-log service))
      (sb-bsd-sockets:socket-error (condition)
        (unless (or *fnn-sigterm-requested*
                    (fnn-owner-service-stopping service))
          (error condition))))))

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
                  (setf (fnn-owner-service-tls-context service) tls-context
                        (fnn-owner-service-connection-fault-operation service)
                        connection-fault-operation)
                  ;; PKT-605 (PRF-223): the live capacity against this
                  ;; machine (books/connection-budget.lisp), refused by name
                  ;; before anything listens; then the I/O loops.
                  (fnn-mux-budget-install service tls-context)
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
                    (fnn-owner-measure-report)
                    ;; Keep the captured listener fd live while the focused
                    ;; test delivers a repeated SIGTERM during cleanup.
                    (when (string= (or (fnn-developer-selector
                                        "FN_NATIVE_OWNER_TEST_PAUSE_CLEANUP") "")
                                   "1")
                      (fnn-out "OWNER-CLEANUP")
                      (sleep 2))
                    (dolist (hook (fnn-owner-service-close-hooks service))
                      (ignore-errors (funcall hook service)))
                    (fnn-owner-feed-close-all service)
                    (fnn-store-close (fnn-owner-service-store service)))
               (setq *fnn-sigterm-wakeup-fd* nil)
               (dolist (extra more-listeners) (fnn-socket-shut extra))
               (when tls-listener (fnn-socket-shut tls-listener))
               (when listener (fnn-socket-shut listener)))))
      ;; Drain and stop the writer before the caller closes `[log] path'.
      (fnn-log-writer-stop)
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
