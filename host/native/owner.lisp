;;; host/native/owner.lisp -- the writable native owner service.
;;;
;;; This file is raw Common Lisp under the native host trust tag.  It owns
;;; scheduling, sockets and filesystem effects only.  Every protocol, owner,
;;; configuration, submission and outcome decision is a direct call to a
;;; host/owner-host.lisp wrapper through fnn-core/fnn-core-state.  All calls
;;; and Store mutations are serialized by one mutex because ACL2's live state
;;; and the exclusive Store writer are one process-owned machine; client
;;; sockets remain concurrent and never carry semantic state in raw Lisp.

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
;;; act on.  Sixteen is the depth host/native/control.lisp already uses.
(defconstant +fnn-owner-listen-backlog+ 16)

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
  (start-hooks nil) (stop-hooks nil) (close-hooks nil)
  ;; Private executable-test injection.  Production instances leave this NIL;
  ;; the value names a real connection envelope, not a second fault decision.
  (connection-fault-operation nil))

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

(defun fnn-owner-core (name &rest args)
  (apply #'fnn-core-state name args))

(defun fnn-owner-octets-global (name)
  (let ((value (fnn-global name)))
    (unless (fnn-octet-list-p value)
      (fnn-fault "owner returned non-octets in ~a" name))
    (fnn-octets value)))

(defun fnn-owner-bool-global (name)
  (let ((value (fnn-global name)))
    (unless (member value '(t nil))
      (fnn-fault "owner returned non-boolean in ~a" name))
    value))

(defun fnn-owner-action (name &rest args)
  (let ((value (apply #'fnn-owner-core name args)))
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

(defun fnn-owner-name-list (octets)
  "Split ACL2's LF-joined name projection; LF is excluded by the name grammar."
  (let ((names nil) (current nil))
    (unless (fnn-octet-list-p octets)
      (fnn-fault "owner returned a non-octet name table"))
    (dolist (octet octets)
      (if (= octet 10)
          (progn
            (push (fnn-octets-string (fnn-octets (nreverse current))) names)
            (setq current nil))
          (push octet current)))
    (when current
      (push (fnn-octets-string (fnn-octets (nreverse current))) names))
    (nreverse names)))

(defun fnn-owner-config-names (wrapper)
  (fnn-owner-name-list (fnn-owner-core wrapper)))

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
  (let ((peers (fnn-owner-core 'fn-owner-feed-configure)))
    (unless (fnn-octet-list-p peers)
      (fnn-fault "owner returned a malformed refreshed feed table"))
    (fnn-owner-feed-open-missing service (fnn-owner-name-list peers))))

(defun fnn-owner-feed-flush (service)
  "Persist the exact pending owner frame batch before its authorized effect."
  (let* ((raw-frames (fnn-global 'fn-owner-feed-frames))
         (peers (fnn-owner-name-list
                 (fnn-owner-core 'fn-owner-feed-record-peers))))
    (unless (listp raw-frames)
      (fnn-fault "owner returned malformed FNFD frame batch"))
    (unless (= (length raw-frames) (length peers))
      (fnn-fault "owner FNFD frame/peer count mismatch"))
    (loop for peer in peers for index from 0 do
      (let ((journal (cdr (assoc peer (fnn-owner-service-feeds service)
                                 :test #'string=)))
            (frame (fnn-owner-core 'fn-owner-feed-sealed-frame index)))
        (unless journal
          (fnn-fault "FNFD obligation has no journal for peer ~a" peer))
        (unless (fnn-octet-list-p frame)
          (fnn-fault "owner returned malformed sealed FNFD frame"))
        (fnn-owner-feed-append journal (fnn-octets frame))))))

(defun fnn-owner-feed-reconcile (service)
  (loop
    (let ((resolution (fnn-owner-action 'fn-owner-feed-reconcile-next)))
      (case resolution
        (:done (return))
        (:uncertain
         (fnn-indeterminate "feed intent cannot be resolved from recovered store"))
        ((:feed-commit :feed-abort)
         (fnn-owner-feed-flush service)
         (unless (eq (fnn-owner-action 'fn-owner-feed-reconcile-apply) :ok)
           (fnn-fault "owner refused recovered feed resolution")))
        (t (fnn-fault "unexpected feed reconciliation: ~a" resolution))))))

(defun fnn-owner-install (root max-connections &optional fault)
  (multiple-value-bind (store records) (fnn-open-live-store root t fault)
    (let ((service nil))
      (handler-case
          (let ((result (fnn-owner-core
                         'fn-owner-recover
                         (mapcar #'fnn-octet-list records)
                         (fnn-store-frontier store)
                         (mapcar #'fnn-octet-list (fnn-config-records store))
                         max-connections)))
            (unless (eq result :recovering)
              (fnn-fault "owner rejected committed history"))
            ;; The persisted profile ACL2 decoded at open, handed back once:
            ;; the owner's transaction budget is derived from it there.
            (unless (eq (fnn-owner-core 'fn-owner-install-profile
                                        (fnn-store-config store))
                        :installed)
              (fnn-fault "owner refused the store profile"))
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
            ;; fnn-owner-serve-client and fnn-owner-handle-chunk: this one is
            ;; not an anchor the run is dated against.
            (unless (eq (fnn-owner-advance-clock) :observed)
              (fnn-fault "owner refused its first clock observation"))
            (let ((peers (fnn-owner-core 'fn-owner-feed-configure)))
              (unless (fnn-octet-list-p peers)
                (fnn-fault "owner returned a malformed feed table"))
              (setq service
                    (%make-fnn-owner-service
                     :store store
                     :lock (sb-thread:make-mutex :name "fn owner/store")
                     :start-hooks *fnn-owner-start-hooks*
                     :stop-hooks *fnn-owner-stop-hooks*
                     :close-hooks *fnn-owner-close-hooks*
                     :stopping nil))
              (let ((configured (fnn-owner-name-list peers)))
                (setf (fnn-owner-service-feeds service)
                      (fnn-owner-feed-open-all service configured))
                (fnn-owner-feed-reconcile service)
                (when configured
                  (let ((count (fnn-owner-core 'fn-owner-feed-restart)))
                    (unless (and (integerp count) (>= count 0))
                      (fnn-fault "owner returned malformed feed restart count")))
                  (fnn-owner-feed-flush service)))
              service))
        (error (e)
          (when service (fnn-owner-feed-close-all service))
          (fnn-store-close store)
          (error e))))))

(defmacro fnn-with-owner ((service) &body body)
  `(sb-thread:with-mutex ((fnn-owner-service-lock ,service)) ,@body))

(defun fnn-owner-stop-service-locked (service exit-code &optional answering)
  "Fence while the owner mutex is held; the first terminal outcome wins.

ANSWERING is the socket of the connection whose own ACL2 reply reported the
stop, or nil.  It is not shut down here: its worker still owes that reply (the
uncertain `441 ... do not repost'), sends it after the mutex is released and
then closes the connection itself.  Setting STOPPING under this mutex is the
fence; no semantic action of any worker, that one included, can run after it
(fnn-owner-serialized refuses once STOPPING is set)."
  (unless (fnn-owner-service-stopping service)
    (setf (fnn-owner-service-stopping service) t
          (fnn-owner-service-exit-code service) exit-code))
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
  (dolist (socket (fnn-owner-service-clients service))
    (unless (eq socket answering)
      (ignore-errors
        (sb-bsd-sockets:socket-shutdown socket :direction :io))))
  ;; Hooks only signal external listeners/clients.  They run inside the same
  ;; first-terminal boundary and must be idempotent and nonblocking.
  (dolist (hook (fnn-owner-service-stop-hooks service))
    (ignore-errors (funcall hook service))))

(defun fnn-owner-stop-service (service exit-code)
  (fnn-with-owner (service)
    (fnn-owner-stop-service-locked service exit-code)))

(defun fnn-owner-fence-service (service)
  "Stop this owner image after an ambiguous Store or FNFD observation."
  (fnn-owner-stop-service service +fnn-exit-uncertain+))

(defun fnn-owner-fault-service (service cid condition)
  "Contain an invalid core/store image, distinct from client refusal or EOF."
  (fnn-with-owner (service)
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

(defun fnn-owner-serialized (service cid thunk)
  "Run one semantic action, fencing before its mutex can be released."
  (fnn-with-owner (service)
    (when (fnn-owner-service-stopping service)
      (fnn-refuse "owner service is stopping"))
    (fnn-owner-shared-action-locked service cid thunk)))

(defun fnn-owner-consume-connection-fault (service operation)
  "Consume the private injection under the owner mutex, without a core step."
  (fnn-with-owner (service)
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
    (fnn-with-owner (service)
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

(defun fnn-owner-submit-groups ()
  (let ((groups (fnn-global 'fn-owner-submit-groups)))
    (unless (and (listp groups) (every #'fnn-octet-list-p groups))
      (fnn-fault "owner returned malformed submission groups"))
    (mapcar #'fnn-octets groups)))

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
    (setf (fnn-store-fenced store) t)
    (fnn-finish store)
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
;; keyed on the poster's bytes, D25), :clock-unusable,
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
          (case (fnn-owner-action 'fn-owner-existing-action
                                  (fnn-octet-list msgid)
                                  (fnn-octet-list payload) codes)
            (:duplicate (return-from fnn-owner-attempt :duplicate))
            (:conflict (return-from fnn-owner-attempt :conflict)))
          (let ((*fnn-observe-callback* #'fnn-owner-observe)
                (*fnn-finish-callback* #'fnn-owner-finish-submission))
            (fnn-advance-frontier store
                                  (fnn-nat (fnn-owner-core 'fn-owner-next-txid)))
            (multiple-value-bind (obligation subject ignored)
                (fnn-metadata msgid payload)
              (declare (ignore ignored))
              (let ((prepared
                      (fnn-owner-action
                       'fn-owner-prepare (fnn-octet-list msgid)
                       (fnn-octet-list payload) codes
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

(defun fnn-owner-transit-refused (detail)
  (setq *fnn-owner-transit-detail*
        (if (and (consp detail) (eq (first detail) :refused)
                 (keywordp (second detail)))
            (second detail)
          detail))
  :refused)

(defun fnn-owner-attempt-transit (service msgid payload groups evidence)
  "One ingress decision for both NNTP and BP transit under the caller's
durable intent. ACL2 distinguishes carrier absence from present-invalid,
selects the B-local current enrollment, and constructs the exact kind-4
event. A carrier-absent article keeps the established legacy Store path."
  (let ((form (fnn-owner-core 'fn-owner-peer-carrier-form
                              (fnn-octet-list payload))))
    (cond
      ((eq form :absent)
       (fnn-owner-attempt service msgid payload groups evidence))
      ((not (and (consp form) (eq (first form) :ok)))
       (fnn-owner-transit-refused form))
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
                                         (fnn-octet-list payload))))
               (unless (and (consp plan) (eq (first plan) :ok))
                 (return-from fnn-owner-attempt-transit
                   (fnn-owner-transit-refused plan)))
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
                   (fnn-owner-transit-refused :signature)))
               (multiple-value-bind (obligation subject ignored)
                   (fnn-metadata msgid payload)
                 (declare (ignore ignored))
                 (let* ((coordinates
                          (fnn-owner-core 'fn-owner-next-store-coordinates))
                        (event
                          (fnn-owner-core
                           'fn-owner-peer-carried-event coordinates
                           (fnn-octet-list msgid) (fnn-octet-list payload)
                           codes (fnn-octet-list obligation)
                           (fnn-octet-list subject) (fnn-octet-list evidence)
                           charge (coerce observed-ml-key 'list)
                           (first observations) (first ml-observation))))
                   (unless event
                     (return-from fnn-owner-attempt-transit
                       (fnn-owner-transit-refused :event)))
                   (fnn-owner-identity-commit service event)))))))))))

;;; The served POST's attempt, and the bound local submission's.  The one
;;; ingress decision transit uses (fnn-owner-attempt-transit: ACL2's
;;; fn-pa-carrier-form and fn-pa-current-plan over these octets and this
;;; Store's enrollment, the primitive observation, fn-pa-authorized-event,
;;; the kind-4 identity commit) with the poster's outcome word chosen by
;;; ACL2 (fn-pa-served-word): a present carrier the plan refused carries the
;;; plan's reason to its own 441 line, and a carrier-absent article is the
;;; unsigned arm, fnn-owner-attempt, with its word unchanged.
(defun fnn-owner-attempt-served (service msgid payload groups evidence)
  (setq *fnn-owner-transit-detail* nil)
  (let ((word (fnn-owner-attempt-transit service msgid payload groups evidence)))
    (fnn-owner-core 'fn-owner-served-carried-word word
                    *fnn-owner-transit-detail*)))

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
                (:unregister
                 (fnn-owner-core 'fn-owner-consumer-local-unregister first))
                (otherwise '(:refused :operation))))
            (kind (and (consp proposal) (first proposal))))
       (case kind
         (:refused
          (if (eq operation :status)
              (list :consumer-status-reply :refused nil nil nil)
            (list :consumer-reply :refused nil)))
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
                    (:ack first)
                    (:bootstrap nil)
                    (:unregister nil)
                    (otherwise
                     (fnn-fault "unexpected consumer write operation")))))
            (unless (fnn-octet-list-p token)
              (fnn-fault "ACL2 returned malformed durable cursor"))
            (list :consumer-reply :accepted token)))
         (otherwise (fnn-fault "ACL2 returned malformed consumer decision")))))))

(defun fnn-owner-transit-complete (cid kind reason word)
  "Feed a transit outcome to the owner and write its one service-log line.

The line is rendered by ACL2 (fn-olog-transit-line) from the owner before the
outcome consumes the submission, with the same KIND, REASON and WORD; a
refused or deferred peer transfer is never silent."
  (fnn-owner-action 'fn-owner-transit-log-line cid kind reason word
                    *fnn-owner-transit-detail*)
  (fnn-owner-action 'fn-owner-transit-outcome cid kind reason word)
  (fnn-owner-log))

(defun fnn-owner-drain-one (service)
  "Take and complete at most one queued served submission; return cid/reply."
  (setq *fnn-owner-transit-detail* nil)
  (let ((taken (fnn-owner-action 'fn-owner-take)))
    (unless (member taken '(:idle :taken :taken-control :taken-transit))
      (fnn-fault "owner returned unexpected take result"))
    (if (eq taken :idle)
        (values nil (fnn-make-octets 0) nil)
        (let* ((cid (fnn-nat (fnn-global 'fn-owner-submit-id)))
               (msgid (fnn-owner-octets-global 'fn-owner-submit-msgid))
               (payload (fnn-owner-octets-global 'fn-owner-submit-octets)))
          (when (eq taken :taken-control)
            (fnn-owner-action 'fn-owner-fault cid)
            (return-from fnn-owner-drain-one
              (values cid (fnn-owner-octets-global 'fn-owner-output) t)))
          (multiple-value-bind (obligation subject ignored)
              (fnn-metadata msgid payload)
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
                   ;; decision above and installed in this same global.
                   (groups (fnn-owner-submit-groups))
                   (evidence
                     (fnn-octets
                      (if transitp
                          (fnn-owner-core 'fn-owner-transit-evidence)
                        (fnn-owner-core 'fn-owner-prov-post))))
                 (generation (fnn-nat (fnn-owner-core 'fn-owner-config-generation)))
                 (txid (fnn-nat (fnn-owner-core 'fn-owner-next-txid)))
                 (intent
                   (when (or (not transitp) (eq transit-kind :want))
                     (fnn-owner-action 'fn-owner-submission-intent
                                       (fnn-octet-list evidence)
                                       generation txid))))
            (declare (ignorable transit-checked))
            (if (and transitp (not (eq transit-kind :want)))
                (progn
                  (fnn-owner-transit-complete
                   cid transit-kind transit-reason :refused)
                  (values cid (fnn-owner-octets-global 'fn-owner-output) nil))
              (if (not (eq intent :ready))
                  (progn
                    (if transitp
                        (progn
                          (setq *fnn-owner-transit-detail* :intent)
                          (fnn-owner-transit-complete
                           cid :want transit-reason :refused))
                      (progn (fnn-owner-action 'fn-owner-outcome cid :refused)
                             (fnn-owner-log)))
                    (values cid (fnn-owner-octets-global 'fn-owner-output) nil))
                (progn
                  ;; Durable intent before the first Store mutation.  Empty is
                  ;; a complete batch when the ACL2 target set is empty.
                  (fnn-owner-feed-flush service)
                  (let ((word (if transitp
                                  (fnn-owner-attempt-transit
                                   service msgid payload groups evidence)
                                (fnn-owner-attempt-served
                                 service msgid payload groups evidence))))
                    (fnn-owner-action 'fn-owner-submission-resolution
                                      word (fnn-octet-list evidence)
                                      generation txid)
                    (fnn-owner-feed-flush service)
                    (if transitp
                        (fnn-owner-transit-complete
                         cid :want transit-reason word)
                      (progn (fnn-owner-action 'fn-owner-outcome cid word)
                             (fnn-owner-log)))
                    (values cid (fnn-owner-octets-global 'fn-owner-output)
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
     &optional commit-callback)
  "Complete one ACL2-admitted control submission while the owner mutex is held.

The interface callback is the sole admission event.  Local control and BP
applications then share this exact durable intent, Store attempt, resolution
and control-outcome sequence.

PAYLOAD is :INJECTED for the operator's submission: the octets stored are the
ones ACL2 injected (books/owner.lisp fn-own-operator-submit), read back from
the owner after the take, never the payload the host read from the file.
Every other caller submits exact authored octets and names them."
  (let ((submitted (funcall submit-callback)))
    (unless (member submitted '(:submitted :busy :refused))
      (fnn-fault "owner bound submit returned ~a" submitted))
    (unless (eq submitted :submitted)
      (return-from fnn-owner-complete-bound-submission submitted))
    (let ((taken (fnn-owner-action 'fn-owner-take)))
      (unless (eq taken :taken-control)
        (fnn-fault "owner bound take returned ~a" taken))
      (when (eq payload :injected)
        (setq payload (fnn-owner-octets-global 'fn-owner-submit-octets)))
      (unless (and (equalp msgid
                           (fnn-owner-octets-global 'fn-owner-submit-msgid))
                   (equalp payload
                           (fnn-owner-octets-global 'fn-owner-submit-octets))
                   (equalp groups (fnn-owner-submit-groups)))
        (fnn-fault "owner bound submission changed after admission"))
      (let ((intent
              (fnn-owner-action 'fn-owner-submission-intent
                                (fnn-octet-list evidence) generation txid)))
        (unless (eq intent :ready)
          (let ((result
                  (fnn-owner-action 'fn-owner-control-outcome :refused)))
            (fnn-owner-log)
            (unless (eq result :refused)
              (fnn-fault "owner bound intent refusal changed outcome"))
            (return-from fnn-owner-complete-bound-submission result)))
        (fnn-owner-feed-flush service)
        (let ((word (if commit-callback
                        (fnn-owner-bound-commit-word commit-callback)
                      (fnn-owner-attempt-served
                       service msgid payload groups evidence))))
          (fnn-owner-action 'fn-owner-submission-resolution
                            word (fnn-octet-list evidence) generation txid)
          (fnn-owner-feed-flush service)
          (let ((result (fnn-owner-action 'fn-owner-control-outcome word)))
            (fnn-owner-log)
            (unless (member result
                            '(:accepted :duplicate :refused :clock-unusable :uncertain))
              (fnn-fault "owner bound completion returned ~a" result))
            (when (eq result :uncertain)
              (fnn-indeterminate "owner bound Store outcome is uncertain"))
            result))))))

(defun fnn-owner-complete-bp-transit-submission
    (service submit-callback msgid raw stored groups evidence
             generation txid planned-id planned-subject)
  "Complete a BP-origin peer transit through the one owner writer and Store."
  (let ((submitted (funcall submit-callback)))
    (unless (member submitted '(:submitted :busy :refused))
      (fnn-fault "owner BP transit submit returned ~a" submitted))
    (unless (eq submitted :submitted)
      (return-from fnn-owner-complete-bp-transit-submission submitted))
    (let ((taken (fnn-owner-action 'fn-owner-take)))
      (unless (eq taken :taken-transit)
        (fnn-fault "owner BP transit take returned ~a" taken))
      (unless (and (equalp msgid
                           (fnn-owner-octets-global 'fn-owner-submit-msgid))
                   (equalp stored
                           (fnn-owner-octets-global 'fn-owner-submit-octets)))
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
            (fnn-owner-action 'fn-owner-bp-transit-outcome :refused)
            (return-from fnn-owner-complete-bp-transit-submission :refused))
          (unless (and (equalp stored
                               (fnn-owner-octets-global
                                'fn-owner-transit-payload))
                       (equalp groups (fnn-owner-submit-groups))
                       (equalp evidence
                               (fnn-octets
                                (fnn-owner-core 'fn-owner-transit-evidence))))
            (fnn-fault "owner BP transit decision disagrees with pinned plan"))
          (unless (equalp raw
                          (fnn-octets
                           (fnn-owner-core 'fn-owner-bp-transit-raw)))
            (fnn-fault "owner BP transit raw request changed"))
          (let ((intent
                  (fnn-owner-action 'fn-owner-submission-intent
                                    (fnn-octet-list evidence) generation txid)))
            (unless (eq intent :ready)
              (return-from fnn-owner-complete-bp-transit-submission
                (fnn-owner-action 'fn-owner-bp-transit-outcome :refused)))
            (fnn-owner-feed-flush service)
            (let ((word (fnn-owner-attempt-transit
                         service msgid stored groups evidence)))
              (fnn-owner-action 'fn-owner-submission-resolution
                                word (fnn-octet-list evidence) generation txid)
              (fnn-owner-feed-flush service)
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
                  (fnn-owner-complete-bound-submission
                   service
                   (lambda ()
                     (fnn-owner-action 'fn-owner-operator-submit
                                       (fnn-octet-list msgid)
                                       (mapcar #'fnn-octet-list groups)
                                       (fnn-octet-list payload)))
                   msgid :injected groups evidence generation txid)
                :clock-unusable))
         (when armed (fnn-owner-control-disarm-fault store armed)))))))

(defun fnn-owner-handle-chunk (service cid incoming &optional socket)
  "Run one owner read and its serial writer drain under the service mutex.

SOCKET is this connection's own socket.  When the drained outcome is
uncertain the service stops here, under the mutex, but SOCKET is spared so
the caller can deliver the ACL2-rendered uncertain reply before closing it
(campaign W1, 2026-09-24: the stop shut this socket first, the reply met
EPIPE and the client saw a bare close)."
  (fnn-owner-serialized
   service cid
   (lambda ()
     ;; One reading per read, before the transition that decides under it.
     ;; books/owner.lisp fn-own-open: "The injection clock is not pinned:
     ;; fn-own-read supplies the owner's current observation with every read,
     ;; so each submission is injected at its own time (RFC 5537 section
     ;; 3.4)."  Without this the owner's current observation is whatever the
     ;; process started with, and every article of a run carries one Date.
     (fnn-owner-advance-clock)
     (unless (eq (fnn-owner-action 'fn-owner-chunk cid
                                   (fnn-octet-list incoming)) :ok)
       (fnn-refuse "owner no longer knows connection ~d" cid))
     (let ((reply (fnn-owner-octets-global 'fn-owner-output))
           (closing (fnn-owner-bool-global 'fn-owner-closep))
           (starttls (fnn-owner-bool-global 'fn-owner-starttlsp))
           (consumed (fnn-global 'fn-owner-consumed))
           (uncertain nil))
       (unless (and (integerp consumed) (<= 0 consumed (length incoming)))
         (fnn-fault "owner returned malformed receive-prefix count"))
       (when (fnn-owner-bool-global 'fn-owner-submittedp)
         (multiple-value-bind (reply-cid completion stop)
             (fnn-owner-drain-one service)
           (when (and reply-cid (not (= reply-cid cid)))
             (fnn-fault "writer drained a different connection"))
           (setq reply (concatenate 'fnn-octets reply completion)
                 uncertain stop)))
       (when uncertain
         (fnn-owner-stop-service-locked service +fnn-exit-uncertain+ socket))
       (values reply (or closing uncertain) starttls consumed)))))

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

(defun fnn-owner-serve-client (service socket)
  ;; RETAINED is the part of the last socket read the served machine has not
  ;; consumed yet.  It is this connection's, never the service's, and the
  ;; socket is read only when it is empty, so it holds at most one
  ;; +fnn-max-read+ read minus one octet (host/native/io.lisp fnn-recv) and
  ;; cannot grow while a client keeps sending.
  (let ((fd (fnn-socket-fd socket)) (cid nil) (channel nil) (retained nil))
    (unwind-protect
         (handler-case
             (progn
               (multiple-value-bind (family address)
                   (fnn-owner-socket-address service socket)
                 (multiple-value-bind (opened greeting)
                   (fnn-owner-serialized
                    service nil
                    (lambda ()
                      ;; fn-own-open pins this reading into the connection as
                      ;; its READER environment (DATE, NEWGROUPS).  Taking it
                      ;; here is what makes DATE answer when the connection
                      ;; was accepted rather than when the process started.
                      (fnn-owner-advance-clock)
                      (let* ((peer
                               (fnn-owner-core
                                'fn-owner-peer-for-socket-address
                                family address))
                             (opened
                              (if peer
                                  (fnn-owner-core 'fn-owner-open-peer peer)
                                (fnn-owner-core 'fn-owner-open))))
                        (unless (or (null peer) (fnn-octet-list-p peer))
                          (fnn-fault "owner returned a malformed peer identity"))
                        (when opened (fnn-owner-log))
                        (values opened
                                (if opened (fnn-owner-octets-global 'fn-owner-output)
                                  (fnn-make-octets 0))))))
                   (unless (and opened (integerp opened))
                     (return-from fnn-owner-serve-client nil))
                   (setq cid opened)
                   (when (> (length greeting) 0)
                     (fnn-owner-connection-call
                      service :send-greeting
                      (lambda () (fnn-owner-send fd channel greeting 10))))))
               (loop
                 ;; ONCE serves this client on the accept thread itself.  It
                 ;; must consume the signal flag here too, or an idle/partial
                 ;; command prevents that thread from reaching service stop.
                 (when (or *fnn-sigterm-requested*
                           (fnn-owner-service-stopping service))
                   (return))
                 (let ((incoming
                         (or retained
                             (fnn-owner-connection-call
                              service :receive
                              (lambda ()
                                (let ((value (fnn-owner-receive service fd channel 1)))
                                  (unless (or (eq value :timeout)
                                              (typep value 'fnn-octets))
                                    (error "malformed connection receive result"))
                                  value))))))
                   ;; Whatever this step does not consume is set again below;
                   ;; nothing carried here is ever read from the socket twice.
                   (setq retained nil)
                   (cond ((eq incoming :timeout) nil)
                         ((zerop (length incoming)) (return))
                         (t (multiple-value-bind (reply closing starttls consumed)
                                (fnn-owner-handle-chunk service cid incoming socket)
                              (cond
                                (channel
                                 ;; Once protected, no transport suffix may be
                                 ;; reclassified as a second TLS handshake.
                                 (unless (= consumed (length incoming))
                                   (fnn-fault "protected owner read left a TLS suffix")))
                                ((fnn-owner-service-tls-context service)
                                 ;; The worker is the sole socket reader.  A
                                 ;; failed/short consume closes this connection;
                                 ;; the ACL2 transition is never replayed.
                                 (fnn-tls-consume-plaintext
                                  fd (subseq incoming 0 consumed) 10))
                                ((/= consumed (length incoming))
                                 ;; The suffix is the next step's input, and
                                 ;; it is already in hand.  The served machine
                                 ;; stops at the octet that closed the wire:
                                 ;; an article over fn-own-body-limit
                                 ;; (books/owner.lisp, the record codec's
                                 ;; *fn-record-max-payload* = 32768) makes fn-wire-after-line answer
                                 ;; (fn-wire-close ... :body-overlimit)
                                 ;; (books/wire.lisp), and
                                 ;; fn-served-feed-counted
                                 ;; (books/served-tls-prefix.lisp) consumes no
                                 ;; further octet, which
                                 ;; fn-served-tls-prefix-suffix-accounting
                                 ;; states as the partition this line honours.
                                 ;; A client that sends a long article breaks
                                 ;; no invariant: the 441 below and the close
                                 ;; that follows it are the answer, and this
                                 ;; used to stop the whole process instead.
                                 ;;
                                 ;; A step that consumes nothing and neither
                                 ;; closes nor hands the transport over IS a
                                 ;; broken invariant: the same octets fed
                                 ;; again cannot make progress.
                                 (when (and (zerop consumed)
                                            (not closing) (not starttls))
                                   (fnn-fault
                                    "owner consumed no octets and left the connection open"))
                                 (setq retained (subseq incoming consumed))))
                              (when (> (length reply) 0)
                                (fnn-owner-connection-call
                                 service :send-reply
                                 (lambda ()
                                   (fnn-owner-send fd channel reply 10))))
                              (when starttls
                                (when channel
                                  (fnn-fault "owner requested STARTTLS on a protected channel"))
                                (unless (fnn-owner-service-tls-context service)
                                  (fnn-fault "owner requested STARTTLS without a TLS context"))
                                ;; Only successful SSL_accept makes the ACL2
                                ;; session protected.  Pipelined ClientHello
                                ;; bytes remained unread after exact consume.
                                (setq channel
                                      (fnn-tls-accept
                                       (fnn-owner-service-tls-context service)
                                       fd 10))
                                (fnn-owner-serialized
                                 service cid
                                 (lambda ()
                                   (unless (eq (fnn-owner-action
                                                'fn-owner-tls-established cid)
                                               :ok)
                                     (fnn-fault "owner rejected established TLS")))))
                              (when closing
                                (unless channel
                                  (fnn-owner-connection-call
                                   service :graceful-close
                                   (lambda () (fnn-graceful-close fd))))
                                (return))))))))
           (fnn-store-indeterminate (e)
             ;; The shared boundary has already stopped mutation; prevent the
             ;; unwind cleanup from attempting a later close transition.
             (setq cid nil)
             (fnn-owner-fence-service service)
             (fnn-err "owner uncertain; recovery required: ~a" e))
           (fnn-store-fault (e)
             (let ((faulted-cid cid))
               (setq cid nil)
               (fnn-owner-fault-service service faulted-cid e)))
           (fnn-owner-connection-fault (e)
             ;; Clear CID before any secondary send failure.  Exactly one ACL2
             ;; fault transition owns semantic cleanup for this connection.
             (let ((faulted-cid cid))
               (setq cid nil)
               (handler-case
                   (let ((reply (and faulted-cid
                                     (fnn-owner-abandon-connection
                                      service faulted-cid e))))
                     (when (and reply (> (length reply) 0))
                       (ignore-errors (fnn-owner-send fd channel reply 10))))
                 ;; A failure of the core fault transition is shared.  Its
                 ;; serialized boundary already fenced before unlocking; this
                 ;; nested handler keeps the worker available to join cleanly.
                 (fnn-store-indeterminate (nested)
                   (fnn-owner-fence-service service)
                   (fnn-err "owner uncertain while abandoning connection: ~a"
                            nested))
                 (serious-condition (nested)
                   (fnn-owner-fault-service service nil nested)))))
           ((or fnn-store-error fnn-os-error sb-bsd-sockets:socket-error) (e)
             (fnn-err "owner connection: ~a" e))
           (fnn-tls-error (e)
             ;; Certificate/handshake/record failure is scoped to this peer.
             ;; The owner connection is removed in the unwind cleanup and the
             ;; listener and shared TLS context remain live.
             (fnn-err "owner TLS connection: ~a" e))
           (serious-condition (e)
             (let ((faulted-cid cid))
               (setq cid nil)
               (fnn-owner-fault-service service faulted-cid e))))
      (when cid
        (ignore-errors
          (fnn-owner-serialized
           service cid (lambda () (fnn-owner-action 'fn-owner-close cid)))))
      (when channel (fnn-tls-close-channel channel))
      (fnn-socket-shut socket))))

(defun fnn-owner-client-done (service socket)
  (fnn-with-owner (service)
    (setf (fnn-owner-service-clients service)
          (delete socket (fnn-owner-service-clients service) :test #'eq)
          (fnn-owner-service-workers service)
          (delete sb-thread:*current-thread*
                  (fnn-owner-service-workers service) :test #'eq))))

(defun fnn-owner-launch-client (service socket)
  "Register the socket and worker before either can enter the owner core."
  (fnn-with-owner (service)
    (if (fnn-owner-service-stopping service)
        (progn (ignore-errors (fnn-socket-shut socket)) nil)
      (progn
        (push socket (fnn-owner-service-clients service))
        (let ((worker
                (sb-thread:make-thread
                 (lambda ()
                   (unwind-protect (fnn-owner-serve-client service socket)
                     (fnn-owner-client-done service socket)))
                 :name "fn owner client")))
          (push worker (fnn-owner-service-workers service))
          worker)))))

(defun fnn-owner-wait-workers (service)
  "Join client workers before closing any shared journal or Store object."
  (loop
    (let ((workers
            (fnn-with-owner (service)
              (copy-list (fnn-owner-service-workers service)))))
      (when (null workers) (return))
      (dolist (worker workers) (sb-thread:join-thread worker)))))

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
                  (fnn-owner-serve-client service socket)
                  (return))
              (fnn-owner-launch-client service socket))))
      (sb-bsd-sockets:socket-error (condition)
        (unless (or *fnn-sigterm-requested*
                    (fnn-owner-service-stopping service))
          (error condition))))))

(defun fnn-owner-run (root port once max-connections
                      &optional fault address (family :inet) tls-context
                        connection-fault-operation)
  "Run one service from already-normalized boundary values."
  (let ((service nil) (listener nil)
        (old-active *fnn-sigterm-owner-active*)
        (old-requested *fnn-sigterm-requested*)
        (old-wakeup-fd *fnn-sigterm-wakeup-fd*))
    (unwind-protect
         (progn
           (setq *fnn-sigterm-owner-active* t
                 *fnn-sigterm-requested* nil
                 *fnn-sigterm-wakeup-fd* nil)
           (unwind-protect
                (progn
                  (setq service (fnn-owner-install root max-connections fault))
                  (setf (fnn-owner-service-tls-context service) tls-context
                        (fnn-owner-service-connection-fault-operation service)
                        connection-fault-operation)
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
                        (fnn-out "LISTENING ~d" bound-port)
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
               (when listener (fnn-socket-shut listener)))))
      (setq *fnn-sigterm-wakeup-fd* old-wakeup-fd
            *fnn-sigterm-requested* old-requested
            *fnn-sigterm-owner-active* old-active))))

(defun fnn-owner-run-normalized (store-octets listener-host-octets
                                 listener-port oncep max-connections &optional tls-context)
  "Operator callback over ACL2-normalized projections; no argv semantics."
  (unless (and (typep store-octets 'fnn-octets)
               (typep listener-host-octets 'fnn-octets)
               (integerp listener-port) (<= 0 listener-port 65535)
               (member oncep '(t nil))
               (integerp max-connections) (> max-connections 0)
               (or (null tls-context) (fnn-tls-context-p tls-context)))
    (fnn-fault "malformed ACL2 owner run plan"))
  (let* ((root (fnn-octets-string store-octets))
         (projection
           (fnn-core 'fn-native-config-host-listener-address
                     (fnn-octet-list listener-host-octets))))
    (unless (and (listp projection) (= (length projection) 2))
      (fnn-fault "ACL2 listener address projection is malformed"))
    (let ((family (first projection)) (address-list (second projection)))
      (unless (or (and (eq family :inet) (fnn-octet-list-p address-list)
                       (= (length address-list) 4))
                  (and (eq family :inet6) (fnn-octet-list-p address-list)
                       (= (length address-list) 16)))
        (fnn-fault "ACL2 listener address projection is malformed"))
      ;; The served owner is armed exactly as `store ROOT post' is: the same
      ;; function reads the same selectors into the same store slot, so a
      ;; developer image kills the served owner at every fnn-at coordinate
      ;; of the cut table (campaign dabebb84, F1).  The control fault is
      ;; validated here too, before the store opens.
      (fnn-owner-control-test-fault)
      (fnn-owner-run root listener-port oncep max-connections
                     (fnn-post-entry-fault nil) (fnn-octets address-list)
                     family tls-context))))

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
