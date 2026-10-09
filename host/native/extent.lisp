;;; fn native host: the payload arena's EXTENT realizer (lane arena-offheap-2,
;;; 2026-09-27; PRF-281; design planning/evidence/arena-offheap-2026-09-27.md
;;; section 3; identity: lane extent-identity, 2026-09-29, PRF-994).  Loaded
;;; after io.lisp by host/native/build.lisp.
;;;
;;; A-DURABLE-EXTENT (books/assumptions.lisp) constrains the realizer
;;; `fn-durable-realize-octet' to answer the durable octet; this file is its
;;; raw definition, the trust boundary's one read path for an extent handle
;;; (books/payload-arena-extent.lisp fn-arena$x-get / -payload call it).
;;;
;;; What the host does, and nothing else: it holds a read-only descriptor per
;;; durable file an extent names (a log segment or an installed checkpoint;
;;; an id is never reused within the process and an unlinked file stays
;;; readable through its descriptor until the file is RETIRED and ACL2's close
;;; decision names it: see the end of this file), preads an entry's protected
;;; prefix and its trailer into a bounded cache (ACL2's
;;; fn-arx-read-cache-entries entries), and asks ACL2 for the VERDICT of that
;;; read against the descriptor's commitment (fn-arx-entry-verdict-buffer,
;;; books/payload-extent-read.lisp, over its own octet buffer fn-octets-rd):
;;; the trailer recorded after the prefix must be the descriptor's trailer
;;; (KEYSTONE fn-arx-entry-verdict-buffer-ok-is-the-commitment) and the
;;; prefix's frame digest must be that trailer.  Each verdict but :ok is
;;; refused by name -- arena-extent-trailer (the recorded trailer is not the
;;; descriptor's: another well-formed entry at this offset, a wrong offset,
;;; an entry of another store or generation), arena-extent-digest (the
;;; prefix's digest is not its trailer), arena-extent-read (no file, a short
;;; read) -- as a store fault (a recovery event: the store is fenced); the
;;; octet is never answered.  pread, not mmap: portable (Linux, OpenBSD), no
;;; SIGBUS on a zeroed or truncated tail, one copy.
;;;
;;; IDENTITY.  A cached entry is keyed by the whole descriptor identity --
;;; the file id, the prefix's offset and length and the expected trailer --
;;; and a hit answers only a read that was verified under exactly that
;;; identity.  The file id is this process's name for one durable INCARNATION
;;; of a file: the (device, inode) pair `fnn-extent-register' records from the
;;; descriptor it opened, never reused within the process, dropped (with every
;;; cached entry of it) by `fnn-extent-close'.  It is never persisted: every
;;; descriptor is re-derived at the open from the file the open itself read
;;; and checked, so no process-local id crosses a restart, and the identity
;;; that does cross a restart is the commitment (the entry's trailer, which
;;; the open's chain check established).  A transient OS descriptor number is
;;; not an identity here: it is looked up under the id, never compared.

(in-package "ACL2")

(define-condition fnn-extent-fault (fnn-store-fault) ())

(defun fnn-extent-page-observation (control &rest args)
  "Developer-only primitive observations for the held native-I/O scenario.
Never print a private buffer or derive a model verdict here. Missing log
lines make a trace incomplete; this diagnostic queue is not a proof oracle."
  (when (fnn-developer-selector "FN_NATIVE_PAGE_IO_HOLD")
    (let ((*print-pretty* nil))
      (apply #'fnn-err (concatenate 'string "PAGE-IO observed " control) args))))

(defmacro fnn-extent-native-observe (label actor-p &rest args)
  "Developer-only literal primitive projection; arguments stay unevaluated
when the collector is absent. No buffer or condition is a model result.
Missing wait/pin/other owner edges leave full PageIO replay unavailable."
  `(when *fnn-native-observer*
     (handler-case
         (fnn-native-observe
          ,(if actor-p `(list ,label *fnn-native-actor-identity* ,@args)
             `(list ,label ,@args)))
       (serious-condition ()
         ;; Observation failure never becomes a service verdict or cleanup.
         (setf (fnn-native-observation-valid *fnn-native-observer*) nil
               (fnn-native-observation-reason *fnn-native-observer*) :observer-fault)))))

(defvar *fnn-extent-lock* (sb-thread:make-mutex :name "fn extent realizer"))
(defvar *fnn-extent-fds* (make-hash-table))   ; (file id -> fd)
(fnn-guarded-by *fnn-extent-fds* *fnn-extent-lock*)
(defvar *fnn-extent-paths* (make-hash-table)) ; (file id -> path)
(fnn-guarded-by *fnn-extent-paths* *fnn-extent-lock*)
(defvar *fnn-extent-incarnations* (make-hash-table))
(fnn-guarded-by *fnn-extent-incarnations* *fnn-extent-lock*)
;; (file id -> (device . inode) of the file opened)
(defvar *fnn-extent-bases* (make-hash-table)) ; (file id -> page 0's offset)
(fnn-guarded-by *fnn-extent-bases* *fnn-extent-lock*)
(defvar *fnn-extent-next-id* nil)
(defvar *fnn-extent-cache* nil)
(defvar *fnn-extent-cache-tokens* (make-hash-table :test #'eq))
(fnn-guarded-by *fnn-extent-cache-tokens* *fnn-extent-lock*)
;; (every reader and writer: fnn-extent-cache-
;; forget/-store, both "Extent lock held", and the pool install under it).
;; Verified vector -> immutable charged token. Capacity is a static pool
;; allowance, not a per-entry credit that eviction pretends to reclaim.
;; ((file eoff elen trailer . octets) ...), most recent first: the verified
;; entries, each under the descriptor identity it was verified for
(defvar *fnn-extent-stats* (list 0 0 0))      ; hits, misses (preads), refusals
(defvar *fnn-extent-issued* nil)
(fnn-guarded-by *fnn-extent-issued* *fnn-extent-lock*)
;; ACL2's issued table (books/page-read-direct.lisp
;; fn-pio-issuedp: an alist TOKEN -> ownership row, PRF-1057), kept exactly as
;; ACL2 returns it and written only through its helpers (fn-pio-issued-put /
;; -remove, fn-pio-direct-admit / -cancel / -settle); at most the worker count
;; long.  A row is removed only by actual worker completion, never a request's
;; timeout.
(defvar *fnn-extent-file-holds* nil)
(fnn-guarded-by *fnn-extent-file-holds* *fnn-extent-lock*)
;; ACL2's holds table (def-holder fn-pio-file-holds,
;; books/page-read-direct.lisp): per file incarnation the tokens of the direct
;; reads that pin it; fnn-extent-close asks fn-pio-direct-quiet-p of it (one
;; lookup) instead of walking the issued rows (KEYSTONE
;; fn-pio-direct-quiet-is-clear).

;; Mirror of the generated *fn-pio-file-holds-cuts* (books/def-holder.lisp,
;; table fn-holder-cuts): the selector's vocabulary.  tests/campaign/native_cuts.py
;; verify_holder_cut_map checks this list against the declarations both ways
;; (tools/native_program_check.py), tools/holder_check.py the markers.
(defparameter +fnn-holder-cuts+
  '("fn-pio-file-holds-decided" "fn-pio-file-holds-released"))

(defun fnn-holder-cut (cut)
  "A holder release reached CUT (a keyword of a declared holder's *NAME-cuts*,
books/def-holder.lisp): SIGKILL here when FN_NATIVE_HOLDER_FAULT names it
(CUT:kill on a developer image).  The effect is process-local: the tables
are memory, rebuilt at fnn-extent-direct-start."
  (let ((raw (fnn-developer-selector "FN_NATIVE_HOLDER_FAULT")))
    (when raw
      (let ((colon (position #\: raw :from-end t)))
        (unless (and colon (string= (subseq raw (1+ colon)) "kill")
                     (member (subseq raw 0 colon) +fnn-holder-cuts+ :test #'string=))
          (fnn-fault "invalid FN_NATIVE_HOLDER_FAULT (expected CUT:kill)"))
        (when (string-equal (subseq raw 0 colon) (symbol-name cut))
          (sb-posix:kill (sb-posix:getpid) sb-unix:sigkill)
          (fnn-fault "test SIGKILL did not terminate the process"))))))

(defun fnn-extent-pool-storage-start (file-capacity worker-capacity cache-capacity)
  "Install the admitted fixed peak capacities before any live registration.
ACL2 supplied capacities include cache insertion overlap; table backing is
permanent baseline, never refunded when an association is removed."
  (declare (ignorable worker-capacity))
  (fnn-with-observed-mutex (*fnn-extent-lock* :extent)
    (unless (and (zerop (hash-table-count *fnn-extent-fds*))
                 (zerop (hash-table-count *fnn-extent-paths*))
                 (zerop (hash-table-count *fnn-extent-incarnations*))
                 (zerop (hash-table-count *fnn-extent-bases*))
                 (null *fnn-extent-issued*)
                 (null *fnn-extent-file-holds*)
                 (zerop (hash-table-count *fnn-extent-cache-tokens*))
                 (null *fnn-extent-cache*))
      (fnn-fault "cold pool installation follows physical registration"))
    (setf *fnn-extent-fds* (make-hash-table :size file-capacity :rehash-threshold 1.0 :rehash-size 1)
          *fnn-extent-paths* (make-hash-table :size file-capacity :rehash-threshold 1.0 :rehash-size 1)
          *fnn-extent-incarnations* (make-hash-table :size file-capacity :rehash-threshold 1.0 :rehash-size 1)
          *fnn-extent-bases* (make-hash-table :size file-capacity :rehash-threshold 1.0 :rehash-size 1)
          ;; the issued and holds tables are ACL2 values bounded by the worker
          ;; count (admission needs an idle worker): no backing to size
          *fnn-extent-cache-tokens* (make-hash-table :test #'eq :size cache-capacity :rehash-threshold 1.0 :rehash-size 1))))

(defun fnn-extent-register (path &optional (open-path path))
  "Reserve ACL2's fresh incarnation name and funded path lease before open.
Failed constructors spend the name; refund only after definite OS release.
The core explicitly distinguishes an unfunded offline registration.
OPEN-PATH, when not PATH, is the file the descriptor opens while PATH is
the name it is registered (and later dropped) under: the writable open's
copy of the active segment, registered before it is renamed onto PATH
(fnn-log-recover)."
  (let ((id nil) (funded nil))
    (fnn-with-observed-mutex (*fnn-extent-lock* :extent)
      (destructuring-bind (word next issued)
          (fnn-core-page-read-pool 'fn-owner-page-file-issue *fnn-extent-next-id*)
        (unless (member word '(:issued :unfunded-offline))
          (fnn-fault (format nil "extent incarnation refused: ~a" word)))
        (setf *fnn-extent-next-id* next id issued)
        (when (eq word :issued)
          (let ((registered
                  (first (fnn-core-page-read-pool 'fn-owner-page-read-register-path id path))))
            (unless (eq registered :registered)
              (fnn-fault (format nil "extent incarnation resources refused: ~a" registered)))
            (setq funded t)))))
    (let ((fd nil) (installed nil))
      (unwind-protect
           (progn
             (setq fd (fnn-open open-path (logior sb-posix:o-rdonly +fnn-o-nofollow+)))
             (let* ((st (fnn-fstat fd))
                    (incarnation (cons (sb-posix:stat-dev st) (sb-posix:stat-ino st))))
               (fnn-with-observed-mutex (*fnn-extent-lock* :extent)
                 (setf (gethash id *fnn-extent-fds*) fd
                       (gethash id *fnn-extent-paths*) path
                       (gethash id *fnn-extent-incarnations*) incarnation
                       installed t)
                 (fnn-extent-page-observation "fd-open file=~d fd=~d dev=~d ino=~d"
                                              id fd (car incarnation) (cdr incarnation))
                 (fnn-extent-native-observe :fd-open t id fd)))
             id)
        (unless installed
          ;; An ambiguous close aborts this cleanup before any credit refund.
          (when fd (fnn-close fd))
          (fnn-with-observed-mutex (*fnn-extent-lock* :extent)
            ;; A failed table installation may have installed a prefix.
            ;; Purge it only after the descriptor is definitely released.
            (remhash id *fnn-extent-fds*)
            (remhash id *fnn-extent-paths*)
            (remhash id *fnn-extent-incarnations*)
            (remhash id *fnn-extent-bases*)
            (when funded
              (unless (eq (first (fnn-core-page-read-pool 'fn-owner-page-read-close id)) :closed)
                (fnn-fault "failed extent constructor retained its resource lease")))))))))

(defun fnn-extent-incarnation (file)
  "The (device . inode) file id FILE opened, or NIL.  Called with the
realizer's lock held."
  (gethash file *fnn-extent-incarnations*))

(defun fnn-extent-where (file eoff)
  "The refusal's naming of the entry at EOFF of FILE: its path and durable
incarnation.  Called with the realizer's lock held."
  (let ((inc (fnn-extent-incarnation file)))
    (format nil "~a (file ~a~@[, dev ~a ino ~a~]) at ~a"
            (gethash file *fnn-extent-paths*) file (car inc) (cdr inc) eoff)))

(defun fnn-extent-register-at (path base)
  "A new file id for PATH whose page A the page fill reads at BASE + 16 KiB * A
(the history image region of the state checkpoint's file: books/history-image-
snapshot.lisp); a read-only descriptor held for the process's life, so the
file stays readable after a later checkpoint replaces its name."
  (let ((id (fnn-extent-register path)))
    (fnn-with-observed-mutex (*fnn-extent-lock* :extent)
      (setf (gethash id *fnn-extent-bases*) base))
    id))

(defun fnn-extent-read-stall ()
  "Developer image only (lane composed-owner-3, row A4): a stalled read
device.  While the named file exists a pread does not return, as a read from
a device under maintenance does not (tests/test_native_slow_disk.py).  Every
physical payload pread passes here: the whole-extent realizer's
(fnn-extent-pread) and the window workers' (fnn-extent-window-pread, raw and
decoded).  The cold reads (the served line's and the peer feed reply's, both
issued under the owner mutex and read by a worker: fnn-extent-prefetch) and
the window workers' hold neither lock.  The synchronous realizer miss
(fnn-extent-entry-direct, reached with *fnn-extent-no-io* unbound) does hold
both (e.g. the history refresh, LOCK-R2-PGS-FILL-REALIZE-REENTRY)."
  (let ((stall (fnn-developer-selector "FN_NATIVE_TEST_READ_STALL_FILE")))
    (when (and stall (plusp (length stall)))
      (loop while (probe-file stall) do (sleep 0.05)))))

(defun fnn-extent-pread (fd octets offset)
  "Fill OCTETS from OFFSET of FD; the count read (short at end of file)."
  (fnn-extent-read-stall)
  (let ((n (length octets)) (done 0))
    (loop while (< done n) do
      (let ((got (sb-sys:with-pinned-objects (octets)
                   (sb-alien:alien-funcall
                    (sb-alien:extern-alien "pread"
                                           (function sb-alien:long sb-alien:int
                                                     sb-alien:system-area-pointer
                                                     sb-alien:unsigned-long sb-alien:long))
                    fd (sb-sys:sap+ (sb-sys:vector-sap octets) done) (- n done) (+ offset done)))))
        (cond ((plusp got) (incf done got))
              ((zerop got) (return))
              (t (return)))))
    done))

(defun fnn-extent-cache-limit ()
  "ACL2's bound on the verified entries the realizer keeps
(fn-arx-read-cache-entries); 0 on a developer image started with
FN_NATIVE_EXTENT_CACHE_TEST_OFF=1 (the matched measurement's cache-off arm)."
  (if (equal (fnn-developer-selector "FN_NATIVE_EXTENT_CACHE_TEST_OFF") "1")
      0
    (fnn-core 'fn-arx-read-cache-entries)))

(defvar *fnn-octets-rd* nil)

(defun fnn-live-octets-rd ()
  (or *fnn-octets-rd*
      (setq *fnn-octets-rd*
            (or (cdr (assoc 'fn-octets-rd (user-stobj-alist *the-live-state*)))
                (fnn-fault "the realizer's buffer stobj is not in this image")))))

(defvar *fnn-page-read-pool* nil)

(defun fnn-live-page-read-pool ()
  (or *fnn-page-read-pool*
      (setq *fnn-page-read-pool*
            (or (cdr (assoc 'fn-page-read-pool (user-stobj-alist *the-live-state*)))
                (fnn-fault "the cold pool stobj is not in this image")))))

(defun fnn-core-page-read-pool (name &rest arguments)
  "The extent mutex serializes the pool; never acquire owner from here."
  (apply #'fnn-call name (append arguments (list (fnn-live-page-read-pool)))))

;;; Stage 0 (planning/design-store-representation-2026-10-01.md section 4;
;;; MODE 2026-10-01 section 3).  The pool stobj starts :uninitialized and
;;; nothing installed it, so fn-owner-page-file-issue answered
;;; :read-resources-unavailable and every registration (replay, each log
;;; commit, every checkpoint) faulted.  Until the funded baseline is
;;; installed from the profile (section 4, stage 6; route A's M1:
;;; fn-ncfg-cold-resources -> fn-crv-pool-budget ->
;;; fn-owner-page-read-install-baseline -> fnn-extent-pool-storage-start ->
;;; fnn-extent-executor-start, before fnn-open-live-store in
;;; fnn-owner-install), every store open enters the pool's :offline context
;;; here (fn-owner-page-read-open-context, host/page-read-host.lisp): ACL2
;;; still issues every file incarnation (fn-pio-file-issue), registration is
;;; :unfunded-offline, a miss is read and cached directly
;;; (fnn-extent-entry-direct's :offline arm) under the realizer's cache bound
;;; (fn-arx-read-cache-entries), and the served cold line issues each miss to
;;; a bounded set of persistent workers under an fn-pio row that pins its file
;;; incarnation until the worker returns (fnn-extent-issue-direct, books/
;;; page-read-direct.lisp; lane cold-read-ownership replaced the 7aad444ce
;;; thread per miss, Codex r31 F1/F2).  Admission, the ledger and its
;;; settlement stay in this module, entered only once the pool is funded
;;; (fnn-extent-pool-funded-p).
(defun fnn-extent-pool-open-context ()
  "Enter the pool's unfunded context once per process; idempotent."
  (fnn-with-observed-mutex (*fnn-extent-lock* :extent)
    (let ((mode (first (fnn-core-page-read-pool 'fn-owner-page-read-open-context))))
      (unless (member mode '(:offline :served))
        (fnn-fault (format nil "page pool context refused: ~a" mode)))
      mode)))

(defun fnn-extent-pool-funded-p ()
  "Whether cold reads go through the funded pool (admission, the executor)."
  (fnn-with-observed-mutex (*fnn-extent-lock* :extent)
    (eq (first (fnn-core-page-read-pool 'fn-owner-page-read-direct-mode)) :funded-pool)))

 ; These macros add no per-job host list construction beyond the dedicated
; call itself. Quoted subjects remain visible to the host source inventory.
(defmacro fnn-core-cold-values (name &rest arguments)
  `(fnn-cold-call ,name ,@arguments))
(defmacro fnn-core-cold-single (name &rest arguments)
  `(first (fnn-cold-call ,name ,@arguments)))
(defmacro fnn-core-cold-pool (name &rest arguments)
  `(fnn-cold-call ,name ,@arguments (fnn-live-page-read-pool)))

(defstruct (fnn-cold-worker (:constructor %make-fnn-cold-worker))
  row thread token result phase next decoded decoded-storage scope
  span ; the span borrow's copy of the window, see fnn-extent-window-span-at
  (ready (sb-thread:make-waitqueue :name "fn cold job")))

;; Allocated only after the installed baseline covers every persistent
;; thread/stack, waitqueue and slot. NEXT is an intrusive idle-slot stack;
;; removing a job never pretends to release native stack-cache storage.
(defvar *fnn-cold-workers* nil)
(defvar *fnn-cold-free* nil)
(defvar *fnn-cold-stopping* nil)

;;; Window jobs retain the complete typed token in the existing slot. No
;;; private buffer leaves the scalar borrow API. Admission remains staged
;;; until the selected native demand and served descriptor join are installed.
(defun fnn-extent-window-p (token)
  (fn-pwx-tokenp token))

(defun fnn-extent-window-pread (fd input offset count)
  "One physical syscall, using ACL2's exact offset/count and fixed input."
  (fnn-extent-read-stall)
  (let* ((octets (svref input 0))
         (got (sb-sys:with-pinned-objects (octets)
                (sb-alien:alien-funcall
                 (sb-alien:extern-alien "pread"
                   (function sb-alien:long sb-alien:int sb-alien:system-area-pointer
                             sb-alien:unsigned-long sb-alien:long))
                 fd (sb-sys:vector-sap octets) count offset))))
    (setf (svref input 1) (if (minusp got) 0 got))
    (if (minusp got) :error :ok)))

(defun fnn-extent-window-observation (control &rest args)
  "fnn-extent-page-observation for a protected window job: the same
developer-only primitive observations, under the window's own prefix."
  (when (fnn-developer-selector "FN_NATIVE_PAGE_IO_HOLD")
    (let ((*print-pretty* nil))
      (apply #'fnn-err (concatenate 'string "WINDOW-IO observed " control) args))))

(defun fnn-extent-job-observation (token control &rest args)
  "A shared executor observation (physical return, join) under the prefix
of TOKEN's kind: WINDOW-IO for a protected window job, PAGE-IO otherwise."
  (if (fnn-extent-window-p token)
      (apply #'fnn-extent-window-observation control args)
    (apply #'fnn-extent-page-observation control args)))

(defun fnn-extent-window-run (worker token)
  "Actual core digest trajectory; only the fixed private window is retained.
The result is (PLAN WINDOW) whenever the job ran: a cancelled job keeps the
plan it reached, so a read that failed before the cancellation was seen is
still the core's fault (fn-pwr-outcome; specs/storage.md PRF-1057)."
  (destructuring-bind (kind ticket file eoff elen poff plen offset expected) token
    (declare (ignore kind))
    (unless (fnn-core-cold-single 'fn-crw-supportedp (cddr token) ticket)
      (fnn-fault "window descriptor is not representable by the selected native ABI"))
    (let ((fd nil) (incarnation nil) (plan nil)
          (input (fn-octets$c-reserve (fn-profile-limit :read-span-octets)
                                      (create-fn-octets$c)))
          (answer :continue)
          (hash (create-pgs-digest-state)) (window (create-fn-ew-buffer))
          (hold (fnn-developer-selector "FN_NATIVE_PAGE_IO_HOLD"))
          (mode (fnn-developer-selector "FN_NATIVE_PAGE_IO_RESULT")))
      (fnn-with-observed-mutex (*fnn-extent-lock* :extent)
        (setq fd (gethash file *fnn-extent-fds*)
              incarnation (gethash file *fnn-extent-incarnations*)))
      (unless (and fd incarnation) (fnn-fault "window issued file closed"))
      (fnn-extent-window-observation "fd-capture token=~s file=~d fd=~d" token file fd)
      (destructuring-bind (next hash1)
          (fnn-core-cold-values 'fn-ews-begin file eoff elen poff plen offset ticket incarnation token expected hash)
        (setq plan next hash hash1))
      (loop
        ;; A cancelled worker finishes its current bounded core operation,
        ;; then relinquishes its activation without publishing a window.
        (unless (fnn-with-observed-mutex (*fnn-extent-lock* :extent)
                  (first (fnn-core-cold-pool 'fn-owner-page-window-work-permittedp
                            (fnn-cold-worker-row worker) token)))
          (return (list plan window)))
        ;; One span per iteration (books/extent-window-span.lisp): the core
        ;; digests every block of the span read, and runs to the next I/O
        ;; need, inside one call.  A :READ answer from the span read is that
        ;; need, so the tick is skipped; any other answer goes through
        ;; FN-EWS-TICK-TO-IO, which resumes a spent tick quantum (:CONTINUE)
        ;; or reports the stream's terminal status.
        (destructuring-bind (status next hash1)
            (if (eq answer :read)
                (list :read plan hash)
              (fnn-core-cold-values 'fn-ews-tick-to-io plan hash))
          (setq plan next hash hash1)
          (case status
            (:continue (setq answer :continue))
            (:read
             ;; :READ status requests I/O; :READ plan phase is terminal.
             (let ((effect (fnn-core-cold-single 'fn-ews-span-effect plan hash)))
               (unless effect (return (list plan window)))
               ;; Developer observation gate (PRF-1057, SCN-216; as the
               ;; decoded controller's, SCN-1129): the core has selected this
               ;; physical read and the token/fd/private buffers stay owned
               ;; while the test device holds it, off owner and extent
               ;; exclusion.  Released, the read completes and its literal
               ;; result is observed before the next cancellation check.
               (when (and hold (plusp (length hold)) (not (probe-file hold)))
                 (let ((*print-pretty* nil))
                   (fnn-err "WINDOW-IO held token=~s file=~d" token file))
                 (loop until (probe-file hold) do (sleep 0.05)))
               (fnn-extent-native-observe :io-begin t token)
               (when (equal mode "error")
                 (error 'fnn-extent-fault :message "arena-extent-read: injected pread error"))
               (when (equal mode "runtime-error")
                 ;; A condition that actually retains the private input.
                 (error 'type-error :datum input :expected-type 'null))
               (let ((io-status (if (equal mode "short")
                                    (progn (setf (svref input 1) 0) :ok)
                                  (fnn-extent-window-pread fd input (fifth effect) (sixth effect)))))
                 (fnn-extent-window-observation
                  "read-return token=~s fd=~d offset=~d count=~d got=~d status=~s injected=~s"
                  token fd (fifth effect) (sixth effect) (svref input 1) io-status
                  (equal mode "short"))
                 (destructuring-bind (answer1 next hash1 window1)
                     (fnn-core-cold-values 'fn-ews-read-span effect io-status plan input hash window)
                   (setq answer answer1 plan next hash hash1 window window1)))))
            (otherwise (return (list plan window)))))))))

(defun fnn-extent-executor-actual-return (worker)
  "Extent lock held; job activation has returned, or dead thread was joined."
  (let ((token (fnn-cold-worker-token worker)))
    (destructuring-bind (word row &rest ignored)
        (if (fnn-extent-window-p token)
            (fnn-core-cold-pool 'fn-owner-page-window-executor-return
                                    (fnn-cold-worker-row worker) token)
          (fnn-call 'fn-pxe-return (fnn-cold-worker-row worker) token))
      (declare (ignore ignored))
      (unless (eq word :returned) (fnn-fault "cold worker returned a different job"))
      (setf (fnn-cold-worker-row worker) row
            (fnn-cold-worker-phase worker) :returned)
      ;; The job activation has unwound. This is distinct from the owner's
      ;; later ledger settlement; a persistent executor thread stays alive.
      (fnn-extent-job-observation token "physical-return token=~s row=~s" token row)
      (when (fnn-cold-worker-scope worker)
        (fnn-err "DECODED-WINDOW physical token=~s scope=~s" token (fnn-cold-worker-scope worker)))
      (when *fnn-native-observer*
        (unless (fn-pwz-tokenp token)
          (fnn-extent-native-observe :return t token))))))

(defun fnn-extent-window-byte (worker token i)
  "Borrow one scalar after physical return, retaining every window credit."
  (fnn-with-observed-mutex (*fnn-extent-lock* :extent)
    (unless (fnn-extent-executor-observe-returned worker)
      (return-from fnn-extent-window-byte (values :pending nil)))
    (unless (fnn-core-cold-single 'fn-pwx-boundp
                     (fnn-core-cold-single 'fn-owner-page-read-ledger (fnn-live-page-read-pool))
                     (fnn-cold-worker-row worker) token :returned)
      (return-from fnn-extent-window-byte (values :stale-job nil)))
    (let ((result (fnn-cold-worker-result worker)))
      (when (typep result 'condition) (error result))
      (destructuring-bind (plan window) result
        (destructuring-bind (word byte)
            (fnn-core-cold-pool 'fn-owner-page-window-byte
                                    (fnn-cold-worker-row worker) token plan i window)
          (values word byte))))))

(declaim (notinline fnn-extent-window-outcome))
(defun fnn-extent-window-outcome (worker token)
  "Scalar-only terminal disposition; integrity failure is never a new miss.
:pending, :ready, :cancelled, (:fault V) -- the core's (fn-pwr-outcome:
a cancelled job's own failure is its fault) -- or the retained condition of
a job that signalled, cancelled or not.  Nothing here settles or signals."
  (when (fn-pwz-tokenp token)
    (return-from fnn-extent-window-outcome
      (fnn-extent-decoded-window-outcome worker token)))
  (fnn-with-observed-mutex (*fnn-extent-lock* :extent)
    (unless (fnn-extent-executor-observe-returned worker)
      (return-from fnn-extent-window-outcome :pending))
    (let ((result (fnn-cold-worker-result worker)))
      (if (typep result 'condition) result
        (first (fnn-core-cold-pool 'fn-owner-page-window-outcome
                 (fnn-cold-worker-row worker) token (first result)))))))

(defun fnn-extent-window-byte-at (worker token file eoff elen poff plen trailer i)
  "Original arena payload coordinate goes unchanged to the core scalar join."
  (fnn-with-observed-mutex (*fnn-extent-lock* :extent)
    (unless (fnn-extent-executor-observe-returned worker)
      (return-from fnn-extent-window-byte-at (values :pending nil)))
    (unless (fnn-core-cold-single 'fn-pwx-boundp
                     (fnn-core-cold-single 'fn-owner-page-read-ledger (fnn-live-page-read-pool))
                     (fnn-cold-worker-row worker) token :returned)
      (return-from fnn-extent-window-byte-at
        (values (first (fnn-core-cold-pool 'fn-owner-page-window-outcome
                         (fnn-cold-worker-row worker) token nil)) nil)))
    (let ((result (fnn-cold-worker-result worker)))
      (when (typep result 'condition) (error result))
      (destructuring-bind (plan window) result
        (destructuring-bind (word byte)
            (fnn-core-cold-pool 'fn-owner-page-window-byte-at
              (fnn-cold-worker-row worker) token plan file eoff elen poff plen trailer i window)
          (values word byte))))))

;;; Future owner quantum bindings retain the exact charged cold row. These
;;; are thread-dynamic references, not a second window cache or a new map.
;;; No served caller binds them until allocator and owner lifetime joins land.
;;; THE SPAN BORROW (books/page-window-span.lisp; host row
;;; fn-owner-page-window-span-at).  The arena reads a payload one octet at a
;;; time; each octet was a scalar borrow, a lock and three ACL2 calls (about
;;; 6 us, PERF-REGRESSION-20261005).  A miss now borrows one SPAN: one lock,
;;; one ACL2 decision, the octets copied into a buffer this host owns (a
;;; fn-ew-span of its own, never an alias of the private window), and the
;;; octets that follow are read from the copy.  ACL2 decides every span
;;; (KEYSTONE fn-owner-page-window-span-at-is-the-scalar-borrows: each octet
;;; is what the scalar borrow of its own coordinate answers; a span refuses
;;; wherever the scalar does); the host only chooses where a span starts and
;;; ends, and when ACL2 refuses it asks the scalar exactly as before.
(defstruct (fnn-window-span (:constructor make-fnn-window-span (token key base len dst)))
  token key base len dst)

(defconstant +fnn-extent-span-capacity+ 16384)

(defun fnn-extent-window-span-at (worker token file eoff elen poff plen trailer i dst)
  "One lock, one ACL2 call: copy the window's octets from payload coordinate I
to the end of the window (at most the buffer, never past PLEN) into DST.
(values WORD J): :span and the exclusive end, or the scalar borrow's word."
  (fnn-with-observed-mutex (*fnn-extent-lock* :extent)
    (unless (fnn-extent-executor-observe-returned worker)
      (return-from fnn-extent-window-span-at (values :pending nil)))
    (unless (fnn-core-cold-single 'fn-pwx-boundp
                     (fnn-core-cold-single 'fn-owner-page-read-ledger (fnn-live-page-read-pool))
                     (fnn-cold-worker-row worker) token :returned)
      (return-from fnn-extent-window-span-at (values :stale-job nil)))
    (let ((result (fnn-cold-worker-result worker)))
      (when (typep result 'condition) (error result))
      (destructuring-bind (plan window) result
        ;; The window's end is a hint only: ACL2 refuses a span that is not
        ;; exactly inside the window.
        (let ((j (and (integerp (eighth token)) (integerp (nth 5 plan))
                      (min plen (+ i +fnn-extent-span-capacity+) (+ (eighth token) (nth 5 plan))))))
          (if (and j (< (1+ i) j))
              (values (first (fnn-core-page-read-pool 'fn-owner-page-window-span-at
                               (fnn-cold-worker-row worker) token plan file eoff elen poff plen
                               trailer i j window dst))
                      j)
              (values :unavailable nil)))))))

(defun fnn-extent-window-span-octet (worker token file eoff elen poff plen trailer i)
  "Octet I of the borrowed window: from this worker's span copy when it covers
I, else borrow a span from I and read it, else the scalar borrow."
  (let ((span (fnn-cold-worker-span worker))
        (key (list file eoff elen poff plen trailer)))
    (when (and span (eq (fnn-window-span-token span) token)
               (eq (fnn-cold-worker-phase worker) :returned)
               (<= (fnn-window-span-base span) i)
               (< i (+ (fnn-window-span-base span) (fnn-window-span-len span)))
               (equal (fnn-window-span-key span) key))
      (return-from fnn-extent-window-span-octet
        (values :byte (fn-ew-span-bytesi (- i (fnn-window-span-base span))
                                         (fnn-window-span-dst span)))))
    (let ((dst (if span (fnn-window-span-dst span) (create-fn-ew-span))))
      (multiple-value-bind (word j)
          (fnn-extent-window-span-at worker token file eoff elen poff plen trailer i dst)
        (if (eq word :span)
            (progn
              (setf (fnn-cold-worker-span worker) (make-fnn-window-span token key i (- j i) dst))
              (values :byte (fn-ew-span-bytesi 0 dst)))
            (fnn-extent-window-byte-at worker token file eoff elen poff plen trailer i))))))

(defvar *fnn-extent-window-mode* nil)
(defvar *fnn-extent-window-worker* nil)
(defvar *fnn-extent-window-token* nil)

(defun fnn-extent-window-realize-octet (file eoff elen poff plen trailer i)
  "Staged realizer: scalar success or the core's complete cold descriptor."
  (multiple-value-bind (word byte)
      (if *fnn-extent-window-worker*
          (fnn-extent-window-span-octet *fnn-extent-window-worker* *fnn-extent-window-token*
                                    file eoff elen poff plen trailer i)
        (values :unavailable nil))
    (cond ((eq word :byte) byte)
          ((member word '(:cancelled :stale-job))
           (throw 'fnn-extent-window-refused (values word nil nil nil)))
          ((eq word :unavailable)
           ;; Not in the borrowed window: a verified cached window, else the
           ;; core's complete cold descriptor.
           (or (fnn-extent-window-cache-byte file eoff elen poff plen trailer i)
               (throw 'fnn-extent-cold
                 (fnn-core-cold-single 'fn-pwr-cold-descriptor file eoff elen poff plen trailer i))))
          (t (error 'fnn-extent-fault
                    :message "arena-extent-read: window was not an authenticated returned result")))))

;;; THE RENDERER'S SPAN (row 21, ARTICLE-RENDER-WALKS-FROM-WINDOW; books/
;;; assumptions-durable.lisp fn-durable-realize-span, books/article-stream.lisp).
;;; The ARTICLE render asks for the octets it is about to render, a span at a
;;; time, and no octet is read by a call of its own.  The host only chooses
;;; where each borrow ends (the window's end, the request's end, the buffer);
;;; ACL2 decides each one (fn-owner-page-window-span-at: KEYSTONE
;;; fn-owner-page-window-span-at-is-the-scalar-borrows), a window it refuses
;;; is asked of the verified-window cache (fn-owner-page-window-cache-span-at),
;;; and what neither holds is the core's cold descriptor, as the scalar path
;;; answers its octet.
;; The verified-window cache (below, THE VERIFIED-WINDOW CACHE); defined before
;; fnn-extent-window-cache-run reads it.
(defvar *fnn-extent-window-cache* nil)
(fnn-guarded-by *fnn-extent-window-cache* *fnn-extent-lock*)
(defvar *fnn-extent-run-dst* nil) ; the run's one buffer
(fnn-guarded-by *fnn-extent-run-dst* *fnn-extent-lock*)

(defun fnn-extent-copy-span (dst count)
  (let ((acc nil))
    (loop for k of-type fixnum from (1- count) downto 0
          do (push (fn-ew-span-bytesi k dst) acc))
    acc))

(defun fnn-extent-window-run-at (worker token file eoff elen poff plen trailer p end
                                 &optional sink)
  "One lock, one ACL2 decision: the borrowed window's octets from P to END, or
to the window's end.  (values WORD OCTETS COUNT): :span, or the borrow's word.
With SINK, the run's bytes are not listed: (funcall SINK DST COUNT) reads them
from the fn-ew-span stobj DST under the lock, and OCTETS is T."
  (fnn-with-observed-mutex (*fnn-extent-lock* :extent)
    (unless (fnn-extent-executor-observe-returned worker)
      (return-from fnn-extent-window-run-at (values :pending nil nil)))
    (unless (fnn-core-cold-single 'fn-pwx-boundp
                     (fnn-core-cold-single 'fn-owner-page-read-ledger (fnn-live-page-read-pool))
                     (fnn-cold-worker-row worker) token :returned)
      (return-from fnn-extent-window-run-at (values :stale-job nil nil)))
    (let ((result (fnn-cold-worker-result worker)))
      (when (typep result 'condition) (error result))
      (destructuring-bind (plan window) result
        (let ((j (and (integerp (eighth token)) (integerp (nth 5 plan))
                      (min end plen (+ p +fnn-extent-span-capacity+) (+ (eighth token) (nth 5 plan))))))
          (if (and j (< p j))
              (let ((dst (or *fnn-extent-run-dst* (setq *fnn-extent-run-dst* (create-fn-ew-span)))))
                (let ((word (first (fnn-core-page-read-pool 'fn-owner-page-window-span-at
                                     (fnn-cold-worker-row worker) token plan file eoff elen poff plen
                                     trailer p j window dst))))
                  (if (eq word :span)
                      (values :span
                              (if sink
                                  (progn (funcall sink dst (- j p)) t)
                                (fnn-extent-copy-span dst (- j p)))
                              (- j p))
                    (values word nil nil))))
            (values :unavailable nil nil)))))))

(defun fnn-extent-window-cache-run (file eoff elen poff plen trailer p end &optional sink)
  "The cached window's octets from P to END or the window's end, decided by
ACL2 (fn-owner-page-window-cache-span-at); (values OCTETS COUNT), or NIL.
SINK as in fnn-extent-window-run-at (OCTETS is then T)."
  (fnn-with-observed-mutex (*fnn-extent-lock* :extent)
    (dolist (entry *fnn-extent-window-cache* nil)
      (destructuring-bind (token plan window) entry
        (when (and (eq (first token) :window)
                   (eql (third token) file) (eql (fourth token) eoff)
                   (eql (fifth token) elen) (eql (sixth token) poff)
                   (eql (seventh token) plen) (eql (ninth token) trailer)
                   (integerp (eighth token)) (<= (eighth token) p)
                   (integerp (nth 5 plan)))
          (let ((j (min end plen (+ p +fnn-extent-span-capacity+) (+ (eighth token) (nth 5 plan)))))
            (when (< p j)
              (let ((dst (or *fnn-extent-run-dst* (setq *fnn-extent-run-dst* (create-fn-ew-span)))))
                (when (eq (first (fnn-core-page-read-pool 'fn-owner-page-window-cache-span-at
                                    token plan file eoff elen poff plen trailer p j window dst))
                          :span)
                  (incf (first *fnn-extent-stats*) (- j p))
                  (unless (eq entry (first *fnn-extent-window-cache*))
                    (setq *fnn-extent-window-cache*
                          (cons entry (delete entry *fnn-extent-window-cache* :test #'eq))))
                  (return (values (if sink
                                      (progn (funcall sink dst (- j p)) t)
                                    (fnn-extent-copy-span dst (- j p)))
                                  (- j p))))))))))))

(defun fnn-extent-window-realize-run (file eoff elen poff plen trailer p end &optional sink)
  "(values OCTETS COUNT) for a stretch starting at P and ending at or before END.
SINK as in fnn-extent-window-run-at (OCTETS is then T)."
  (multiple-value-bind (word octets count)
      (if *fnn-extent-window-worker*
          (fnn-extent-window-run-at *fnn-extent-window-worker* *fnn-extent-window-token*
                                    file eoff elen poff plen trailer p end sink)
        (values :unavailable nil nil))
    (cond ((eq word :span) (values octets count))
          ((member word '(:cancelled :stale-job))
           (throw 'fnn-extent-window-refused (values word nil nil nil)))
          ((eq word :unavailable)
           (multiple-value-bind (cached n)
               (fnn-extent-window-cache-run file eoff elen poff plen trailer p end sink)
             (if cached
                 (values cached n)
               (throw 'fnn-extent-cold
                 (fnn-core-cold-single 'fn-pwr-cold-descriptor file eoff elen poff plen trailer p)))))
          (t (error 'fnn-extent-fault
                    :message "arena-extent-read: window was not an authenticated returned result")))))

(defun fnn-extent-window-realize-span (file eoff elen poff plen trailer i n)
  "The N octets from I: each stretch one borrow, the first octet no stretch
holds the core's cold descriptor."
  (let ((acc nil) (p i) (end (+ i n)))
    (loop while (< p end)
          do (multiple-value-bind (octets count)
                 (fnn-extent-window-realize-run file eoff elen poff plen trailer p end)
               (setq acc (revappend octets acc))
               (incf p count)))
    (nreverse acc)))

(defun fnn-extent-window-current-acquire (view h i)
  "Caller holds owner mutex and provider captured-row authorization for H/I.
Live logical VIEW supplies its bound arena; selection/admission precede unlock."
  (unless (fnn-snapshot-payload-view-live-p view)
    (return-from fnn-extent-window-current-acquire (values :stale-view nil nil nil)))
  (let ((arena (fnn-snapshot-payload-view-arena view)))
  (catch 'fnn-extent-window-refused
    (let ((descriptor
            (let ((*fnn-extent-window-mode* t)
                  (*fnn-extent-window-worker* nil)
                  (*fnn-extent-window-token* nil))
              (catch 'fnn-extent-cold
                (return-from fnn-extent-window-current-acquire
                  (values :byte
                    (first (fnn-core-cold-values 'fn-owner-page-window-current-octet h i arena))
                    nil nil))))))
      ;; The dynamic scalar activation has unwound; no buffer alias escaped.
      (multiple-value-bind (token word worker) (fnn-extent-issue-window descriptor)
        (values word nil token worker))))))

;;; THE VERIFIED-WINDOW CACHE (lane window-read; books/page-window-read.lisp
;;; fn-pwc-*).  A raw window job whose publication was read is, at its last
;;; borrow's release, moved into this cache instead of freed: ACL2's
;;; fn-pwc-cache admits only a :ready outcome and turns the job's ledger row
;;; into a :cached row charged the buffer alone; the entry keeps the job's
;;; token, its plan and its window buffer.  A later scalar read of the same
;;; window borrows from the entry (fn-pwc-byte-at, KEYSTONE
;;; fn-pwc-a-hit-is-the-published-window: exactly the byte the job's own
;;; borrow gave) with no worker, pread or owner settlement -- the window
;;; route's warm path.  At most fnn-extent-cache-limit entries (ACL2's
;;; fn-arx-read-cache-entries, the bound books/cold-line-quanta.lisp's
;;; quanta are shaped to); the oldest is evicted, and its exact :cached row
;;; released (fn-prl-evict), on insertion and when its file retires
;;; (fnn-extent-cache-drop-files).  Each entry is (TOKEN PLAN WINDOW); the
;;; variable is defined above the renderer's span, its first reader.
(defvar *fnn-extent-lz-last* nil)             ; (key dict . octets)

(defun fnn-extent-window-cache-insert (token plan window)
  "Extent lock held, the :cached row already ACL2's.  Front insertion; the
tokens of the entries evicted past the bound (the caller releases them)."
  (push (list token plan window) *fnn-extent-window-cache*)
  (let ((limit (fnn-extent-cache-limit)))
    (when (> (length *fnn-extent-window-cache*) limit)
      (let ((evicted (mapcar #'first (nthcdr limit *fnn-extent-window-cache*))))
        (setq *fnn-extent-window-cache* (subseq *fnn-extent-window-cache* 0 limit))
        evicted))))

(defvar *fnn-extent-cache-span* nil)  ; (entry key base len)
(fnn-guarded-by *fnn-extent-cache-span* *fnn-extent-lock*)
(defvar *fnn-extent-cache-span-dst* nil) ; the span's one buffer
(fnn-guarded-by *fnn-extent-cache-span-dst* *fnn-extent-lock*)

(defun fnn-extent-window-cache-byte (file eoff elen poff plen trailer i)
  "A cached window's payload byte I of this exact descriptor, or NIL.  The
host only selects candidates by the token's own descriptor and requested
offset; ACL2 decides the hit (fn-owner-page-window-cache-byte-at).  A hit is
decided as a SPAN (fn-owner-page-window-cache-span-at, KEYSTONE
fn-owner-page-window-cache-span-at-is-the-cached-bytes): the window's octets
from I on are copied once into this host's buffer and the octets after I are
read from the copy, valid while its entry is still in the cache."
  (fnn-with-observed-mutex (*fnn-extent-lock* :extent)
    (let ((span *fnn-extent-cache-span*)
          (key (list file eoff elen poff plen trailer)))
      (when (and span (equal (second span) key)
                 (<= (third span) i) (< i (+ (third span) (fourth span)))
                 (member (first span) *fnn-extent-window-cache* :test #'eq))
        (incf (first *fnn-extent-stats*))
        (return-from fnn-extent-window-cache-byte
          (fn-ew-span-bytesi (- i (third span)) *fnn-extent-cache-span-dst*))))
    (dolist (entry *fnn-extent-window-cache* nil)
      (destructuring-bind (token plan window) entry
        (when (and (eq (first token) :window)
                   (eql (third token) file) (eql (fourth token) eoff)
                   (eql (fifth token) elen) (eql (sixth token) poff)
                   (eql (seventh token) plen) (eql (ninth token) trailer)
                   (integerp (eighth token)) (<= (eighth token) i))
          (let ((j (and (integerp (nth 5 plan))
                        (min plen (+ i +fnn-extent-span-capacity+) (+ (eighth token) (nth 5 plan))))))
            (when (and j (< (1+ i) j))
              (let ((dst (or *fnn-extent-cache-span-dst*
                             (setq *fnn-extent-cache-span-dst* (create-fn-ew-span)))))
                (when (eq (first (fnn-core-page-read-pool 'fn-owner-page-window-cache-span-at
                                    token plan file eoff elen poff plen trailer i j window dst))
                          :span)
                  (setq *fnn-extent-cache-span* (list entry (list file eoff elen poff plen trailer) i (- j i)))
                  (incf (first *fnn-extent-stats*))
                  (unless (eq entry (first *fnn-extent-window-cache*))
                    (setq *fnn-extent-window-cache*
                          (cons entry (delete entry *fnn-extent-window-cache* :test #'eq))))
                  (return (fn-ew-span-bytesi 0 dst))))))
          (destructuring-bind (word byte)
              (fnn-core-page-read-pool 'fn-owner-page-window-cache-byte-at
                                       token plan file eoff elen poff plen trailer i window)
            (when (eq word :byte)
              (incf (first *fnn-extent-stats*))
              (unless (eq entry (first *fnn-extent-window-cache*))
                (setq *fnn-extent-window-cache*
                      (cons entry (delete entry *fnn-extent-window-cache* :test #'eq))))
              (return byte))))))))

(defun fnn-extent-window-release (worker token &optional cachep)
  "Caller holds no buffer aliases. Drop the sole retained result BEFORE refund.
CACHEP: a published raw window's buffer moves into the verified-window cache
(ACL2's fn-pwc-cache) when it admits it; otherwise, and for every other job,
the job is released.  Values :released (or a stale word) and whether cached."
  (fnn-with-observed-mutex (*fnn-extent-lock* :extent)
    (unless (and (fnn-extent-executor-observe-returned worker)
                 (fnn-core-cold-single 'fn-pwx-boundp
                           (fnn-core-cold-single 'fn-owner-page-read-ledger (fnn-live-page-read-pool))
                           (fnn-cold-worker-row worker) token :returned))
      (return-from fnn-extent-window-release :stale-job))
    (when (and (fnn-cold-worker-decoded worker)
               (eq (fnn-decoded-activation-stage (fnn-cold-worker-decoded worker)) :calling))
      (fnn-fault "decoded torn semantic step retains its cold debit"))
    (let ((scope (fnn-cold-worker-scope worker))
          (result (fnn-cold-worker-result worker))
          (cached nil) (evicted nil) (decoded-attempt nil))
      ;; A returned decoded job whose window ACL2 admits (fn-dwj-cache: its
      ;; outcome is :ready, KEEP is funded) is retired and cached in ONE
      ;; ACL2 step; the buffer moves out of the persistent worker below.
      (when (and cachep (fnn-cold-worker-decoded worker) (plusp (fnn-extent-cache-limit)))
        (setq decoded-attempt (fnn-extent-decoded-window-cache-attempt worker token)))
      ;; A torn reset or settlement must never be retried or offered as idle.
      (setf (fnn-cold-worker-phase worker) :retiring)
      (when (and (fnn-cold-worker-decoded worker) (not decoded-attempt))
        (fnn-extent-decoded-storage-retire worker token))
      (setf (fnn-cold-worker-phase worker) :releasing)
      (setf (fnn-cold-worker-decoded worker) nil)
      (setf (fnn-cold-worker-result worker) nil
            (fnn-cold-worker-span worker) nil)
      (destructuring-bind (word row &rest ignored)
          (let ((attempt
                  (and cachep (not decoded-attempt) (fnn-extent-window-p token)
                       (plusp (fnn-extent-cache-limit))
                       (consp result) (true-listp (first result))
                       (fnn-core-page-read-pool 'fn-owner-page-window-executor-cache
                                                (fnn-cold-worker-row worker) token (first result)))))
            (cond
              (decoded-attempt
               (setq cached t evicted (third decoded-attempt))
               (fnn-extent-window-observation "window-cached token=~s evicted=~s" token evicted)
               (list :released (second decoded-attempt)))
              ((and attempt (eq (first attempt) :cached))
                (progn (setq cached t
                             evicted (fnn-extent-window-cache-insert
                                      token (first result) (second result)))
                       (fnn-extent-window-observation "window-cached token=~s evicted=~s"
                                                      token evicted)
                       (list :released (second attempt))))
              (t (fnn-core-cold-pool 'fn-owner-page-window-executor-release
                                     (fnn-cold-worker-row worker) token))))
        (declare (ignore ignored))
        (unless (eq word :released) (fnn-fault "window release lost exact returned job"))
        (setf (fnn-cold-worker-row worker) row
              (fnn-cold-worker-token worker) nil
              (fnn-cold-worker-scope worker) nil
              (fnn-cold-worker-phase worker) :idle)
        (when (and (not *fnn-cold-stopping*)
                   (sb-thread:thread-alive-p (fnn-cold-worker-thread worker)))
          (setf (fnn-cold-worker-next worker) *fnn-cold-free*
                *fnn-cold-free* worker))
        ;; The evicted buffers are gone from the cache: release their rows.
        (fnn-extent-cache-release evicted)
        ;; This is the literal returned semantic release after actual
        ;; physical return and last scalar borrow, not a close inference.
        (when scope
          (fnn-err "DECODED-WINDOW release token=~s scope=~s word=~s" token scope word))
        (values word cached)))))

; Staged cancellation never refunds, never terminates a thread, and never
; borrows its output. Extent mutex serializes revocation with scalar reads.
(defun fnn-extent-window-cancel (worker token)
  (fnn-with-observed-mutex (*fnn-extent-lock* :extent)
    (when (member (fnn-cold-worker-phase worker) '(:issuing :binding-fault :retiring :releasing))
      (fnn-fault "cold semantic escape retains cancellation authority"))
    (destructuring-bind (word row &rest ignored)
        (fnn-core-cold-pool 'fn-owner-page-window-executor-cancel
                                (fnn-cold-worker-row worker) token)
      (declare (ignore ignored))
      (when (eq word :cancelled) (setf (fnn-cold-worker-row worker) row))
      (when (fnn-developer-selector "FN_NATIVE_PAGE_IO_HOLD")
        (let ((*print-pretty* nil))
          (if (fn-pwz-tokenp token)
              (fnn-err "DECODED-WINDOW cancel token=~s word=~s" token word)
            (fnn-err "WINDOW-IO cancelled token=~s word=~s" token word))))
      word)))

(defun fnn-extent-window-settle-fault (worker token)
  "A returned job whose outcome is the core's fault or a retained condition:
drop the result and release its charge by the transition its phase names --
the ordinary release (:returned) or the cancelled settlement
(:cancelled-returned).  :released, else what the transition answered.  The
caller then stops the owner with the fault."
  (if (fnn-with-observed-mutex (*fnn-extent-lock* :extent)
        (fnn-core-cold-single 'fn-pwx-boundp
                              (fnn-core-cold-single 'fn-owner-page-read-ledger
                                                    (fnn-live-page-read-pool))
                              (fnn-cold-worker-row worker) token :cancelled-returned))
      (fnn-extent-window-settle-cancelled worker token)
    (fnn-extent-window-release worker token)))

(defun fnn-extent-window-settle-cancelled (worker token)
  "After actual return/join and last scalar borrow. Drop result before refund."
  (fnn-with-observed-mutex (*fnn-extent-lock* :extent)
    (unless (and (fnn-extent-executor-observe-returned worker)
                 (fnn-core-cold-single 'fn-pwx-boundp
                           (fnn-core-cold-single 'fn-owner-page-read-ledger (fnn-live-page-read-pool))
                           (fnn-cold-worker-row worker) token :cancelled-returned))
      (return-from fnn-extent-window-settle-cancelled :stale-job))
    (when (and (fnn-cold-worker-decoded worker)
               (eq (fnn-decoded-activation-stage (fnn-cold-worker-decoded worker)) :calling))
      (fnn-fault "decoded torn semantic step retains its cancelled debit"))
    (let ((scope (fnn-cold-worker-scope worker)))
      ;; A torn reset or settlement must never be retried or offered as idle.
      (setf (fnn-cold-worker-phase worker) :retiring)
      (when (fnn-cold-worker-decoded worker)
        (fnn-extent-decoded-storage-retire worker token))
      (setf (fnn-cold-worker-phase worker) :releasing)
      (setf (fnn-cold-worker-decoded worker) nil)
      (setf (fnn-cold-worker-result worker) nil
            (fnn-cold-worker-span worker) nil)
      (destructuring-bind (word row &rest ignored)
        (fnn-core-cold-pool 'fn-owner-page-window-executor-settle-cancelled
                                (fnn-cold-worker-row worker) token)
      (declare (ignore ignored))
      (unless (eq word :released) (fnn-fault "cancelled window lost exact returned job"))
      (setf (fnn-cold-worker-row worker) row
            (fnn-cold-worker-token worker) nil
            (fnn-cold-worker-scope worker) nil
            (fnn-cold-worker-phase worker) :idle)
      (when (and (not *fnn-cold-stopping*)
                 (sb-thread:thread-alive-p (fnn-cold-worker-thread worker)))
        (setf (fnn-cold-worker-next worker) *fnn-cold-free*
              *fnn-cold-free* worker))
        (when scope
          (fnn-err "DECODED-WINDOW release token=~s scope=~s word=~s" token scope word))
        word))))

(declaim (notinline fnn-extent-executor-job))
(defun fnn-extent-executor-job (worker)
  "Publish a private result, but do not yet announce relinquishment."
  (let* ((token (fnn-cold-worker-token worker))
         (result
           (handler-case
               (if (equal (fnn-developer-selector "FN_NATIVE_PAGE_IO_RESULT") "launch-error")
                   (progn
                     (let ((*print-pretty* nil))
                       (fnn-err "~a dispatch-failed token=~s worker=retained buffer=none"
                                (if (fnn-extent-window-p token) "WINDOW-IO" "PAGE-IO") token))
                     (error 'fnn-extent-fault :message "arena-extent-read: injected job dispatch error"))
                 (cond ((fn-pwz-tokenp token)
                        (fnn-extent-decoded-window-run worker token))
                       ((fnn-extent-window-p token)
                        (fnn-extent-window-run worker token))
                       (t (fnn-extent-prefetch token))))
             ;; Our extent faults carry a diagnostic string. An arbitrary
             ;; runtime condition may retain its datum/arguments, including
             ;; the private vector. Do not let that alias escape in RESULT.
             (fnn-extent-fault (condition) condition)
             (serious-condition (condition)
               (declare (ignore condition))
               (make-condition 'fnn-extent-fault
                               :message "arena-extent-read: cold executor runtime failure")))))
    (fnn-with-observed-mutex (*fnn-extent-lock* :extent)
      (setf (fnn-cold-worker-result worker) result)
      (when (fnn-developer-selector "FN_NATIVE_PAGE_IO_HOLD")
        ;; A window job's stored result: the plan's phase, never its bytes.
        (when (fnn-extent-window-p token)
          (fnn-extent-window-observation "job-result token=~s condition=~s phase=~s"
                                         token (typep result 'condition)
                                         (and (consp result) (consp (first result))
                                              (first (first result))))
          (when (and *fnn-native-observer* (consp result))
            (fnn-extent-native-observe :job-result t token
                                       (and (consp (first result)) (first (first result))))))
        (unless (or (fn-pwz-tokenp token) (fnn-extent-window-p token))
          (fnn-extent-page-observation "job-result token=~s condition=~s verdict=~s"
                                       token (typep result 'condition)
                                       (and (not (typep result 'condition)) (first result))
          ;; A stored job result is distinct from a device request/result.
          ;; Cache/no-pread outcomes must not invent an io-complete event.
          ;; Conditions stay unclassified until the owner's later boundary.
          (when (and *fnn-native-observer* (not (typep result 'condition)))
            (fnn-extent-native-observe :job-result t token (first result)))))))
    ;; The activation returns no buffer-bearing value to the loop. Only the
    ;; retained worker field owns the result when actual return is announced.
    nil))

(defun fnn-extent-executor-loop (worker)
  (loop
    ;; The shared wait producer records actual release/reacquire without
    ;; pretending a sleeping executor continuously holds E.
    (fnn-with-observed-mutex (*fnn-extent-lock* :extent)
      (loop until (eq (fnn-cold-worker-phase worker) :queued) do
        (when *fnn-cold-stopping* (return-from fnn-extent-executor-loop nil))
        (fnn-observed-condition-wait (fnn-cold-worker-ready worker) *fnn-extent-lock* :extent))
      (setf (fnn-cold-worker-phase worker) :working))
    ;; This call has returned before RETURNED is made observable. No worker
    ;; activation still consumes the token/fd/vector when owner takes it.
    (fnn-extent-executor-job worker)
    (fnn-with-observed-mutex (*fnn-extent-lock* :extent)
      (fnn-extent-executor-actual-return worker)
      (sb-thread:condition-broadcast (fnn-cold-worker-ready worker)))))

(defun fnn-extent-executor-start (workers &optional plan)
  "Baseline-backed scratch is created once, before a worker is offered.
Legacy direct startup has no decoded scratch and cannot borrow this grant."
  (when *fnn-cold-workers* (fnn-fault "cold executor already installed"))
  (when plan
    (unless (and (fnn-core 'fn-prstartup-planp plan)
                 (eql workers (fnn-core 'fn-prstartup-decoded-workers plan)))
      (fnn-fault "cold executor lacks its admitted baseline plan")))
  (setq *fnn-cold-stopping* nil)
  (handler-case
      (dotimes (slot workers)
        (let ((worker (%make-fnn-cold-worker :row (fnn-core 'fn-pxe-new slot)
                                            :phase :initializing)))
          ;; Publish before constructor/reserve/maker: partial backing remains
          ;; discoverable and never causes an uncharged replacement allocation.
          (push worker *fnn-cold-workers*)
          ;; Both slot checks are owner-thread startup calls, once per slot,
          ;; like fn-pxe-new above: the ordinary entry guard, not the funded
          ;; per-job cold cache (books/cold-guard-bootstrap.lisp roster).
          (when plan
            (fnn-with-observed-mutex (*fnn-extent-lock* :extent)
              (unless (first (fnn-core-page-read-pool
                               'fn-owner-page-read-default-worker-constructionp slot))
                (fnn-fault "decoded backing lacks its installed slot reservation")))
            (fnn-extent-decoded-storage-start worker))
          (setf (fnn-cold-worker-thread worker)
                (sb-thread:make-thread
                 (fnn-native-observed-thread-thunk (lambda () (fnn-extent-executor-loop worker)))
                 :name "fn cold executor"))
          (fnn-with-observed-mutex (*fnn-extent-lock* :extent)
            (when plan
              (unless (eq (first (fnn-core-page-read-pool
                                   'fn-owner-page-read-default-worker-ready slot)) :ready)
                (fnn-fault "cold worker backing was not acknowledged"))
              (fnn-err "DECODED-WINDOW storage-ready slot=~s scope=:persistent-partial-fixed-storage" slot))
            (setf (fnn-cold-worker-phase worker) :idle
                  (fnn-cold-worker-next worker) *fnn-cold-free*
                  *fnn-cold-free* worker))))
    (serious-condition (condition)
      (fnn-extent-executor-stop)
      (error condition))))

(defun fnn-extent-executor-discard-idle-locked ()
  "E held. Joining proves physical end, not token/result/reset settlement.
Retain every unsettled or torn slot as independent terminal-debt custody."
  (setf *fnn-cold-free* nil
        *fnn-cold-workers*
        (remove-if
         (lambda (worker)
           (let ((thread (fnn-cold-worker-thread worker))
                 (storage (fnn-cold-worker-decoded-storage worker)))
             (and (or (null thread) (not (sb-thread:thread-alive-p thread)))
                  (member (fnn-cold-worker-phase worker) '(:idle :initializing))
                  (null (fnn-cold-worker-token worker))
                  (null (fnn-cold-worker-result worker))
                  (null (fnn-cold-worker-decoded worker))
                  (or (null storage)
                      (eq (fnn-decoded-activation-stage storage) :idle)))))
         *fnn-cold-workers*)))

(defun fnn-extent-executor-discard-idle ()
  (fnn-with-observed-mutex (*fnn-extent-lock* :extent)
    (fnn-extent-executor-discard-idle-locked)))

(defun fnn-extent-executor-drained-p ()
  "Physical retained-custody observation, not a typed settlement receipt.
A joined thread or normal stop return alone cannot discharge roster debt."
  (fnn-with-observed-mutex (*fnn-extent-lock* :extent)
    (null *fnn-cold-workers*)))

(defun fnn-extent-executor-stop ()
  "Stop clients first. Join every worker before closing any shared file.
No cancellation, timeout or thread termination releases a job or baseline."
  (fnn-with-observed-mutex (*fnn-extent-lock* :extent)
    (setq *fnn-cold-stopping* t)
    (dolist (worker *fnn-cold-workers*)
      ;; Stop revokes future bounded window steps but never manufactures
      ;; physical return or last-borrow settlement. Legacy jobs stay distinct.
      (let ((token (fnn-cold-worker-token worker)))
        (when (and (fn-pwx-tokenp token)
                   (not (member (fnn-cold-worker-phase worker) '(:issuing :binding-fault :retiring :releasing))))
          (destructuring-bind (word row &rest ignored)
              (fnn-core-cold-pool 'fn-owner-page-window-executor-cancel
                                  (fnn-cold-worker-row worker) token)
            (declare (ignore ignored))
            (when (eq word :cancelled) (setf (fnn-cold-worker-row worker) row)))))
      (sb-thread:condition-broadcast (fnn-cold-worker-ready worker))))
  (dolist (worker *fnn-cold-workers*)
    (let ((thread (fnn-cold-worker-thread worker))
          (token (fnn-cold-worker-token worker)))
      (when thread
        ;; These are actual call/return observations outside E; a call-site
        ;; marker does not claim an internal SBCL waiting state or success.
        (when (fnn-developer-selector "FN_NATIVE_PAGE_IO_HOLD")
          (fnn-extent-job-observation token "executor-join-call token=~s alive=~s"
                                       token (sb-thread:thread-alive-p thread)))
        (sb-thread:join-thread thread :default nil)
        (when (fnn-developer-selector "FN_NATIVE_PAGE_IO_HOLD")
          (fnn-extent-job-observation token "executor-join-return token=~s alive=~s"
                                       token (sb-thread:thread-alive-p thread))))))
  ;; Physical joins never discard the sole reference to unsettled draws,
  ;; private results or torn constructor/reset/settlement activations.
  (fnn-extent-executor-discard-idle))

(defun fnn-extent-executor-enqueue (worker row token &optional retain)
  "Extent lock held; ACL2 already assigned this exact funded physical slot."
  (setq *fnn-cold-free* (fnn-cold-worker-next worker))
  (setf (fnn-cold-worker-row worker) row
        (fnn-cold-worker-token worker) token
        (fnn-cold-worker-next worker) nil
        (fnn-cold-worker-result worker) nil
        (fnn-cold-worker-span worker) nil
        (fnn-cold-worker-phase worker) :binding)
  ;; The owning activation retains the exact token before this physical
  ;; executor can run, even if notification subsequently signals.
  (when retain (funcall retain worker token))
  (setf (fnn-cold-worker-phase worker) :queued)
  (sb-thread:condition-broadcast (fnn-cold-worker-ready worker))
  worker)

(defun fnn-extent-issue-window (descriptor &optional retain)
  "One SAME-pool issue. Decoded default storage scope is explicitly partial;
modern complete installations still refuse their unpriced operation."
  (let ((decodedp (eq (fnn-core 'fn-owner-page-decoded-window-price-status descriptor)
                      :unpriced-decoded-window)))
    (fnn-with-observed-mutex (*fnn-extent-lock* :extent)
      (let ((worker *fnn-cold-free*))
        (unless (and worker (not *fnn-cold-stopping*))
          (return-from fnn-extent-issue-window (values nil :read-resources-unavailable nil)))
        ;; Reserve the native custody envelope before the semantic issuer.
        ;; A torn draw cannot put this worker back on the free roster.
        (setq *fnn-cold-free* (fnn-cold-worker-next worker))
        (setf (fnn-cold-worker-phase worker) :issuing
              (fnn-cold-worker-scope worker) (and decodedp :partial-fixed-storage))
        ;; Publish native custody before the semantic draw. On a torn draw
        ;; the caller still knows which reserved worker must not be reused.
        (when retain (funcall retain worker nil))
        (let* ((reply
                 (if decodedp
                     (fnn-call 'fn-owner-page-decoded-window-acquire-projected
                       (fnn-cold-worker-row worker) descriptor (fnn-live-page-read-pool))
                   (fnn-core-cold-pool 'fn-owner-page-window-executor-acquire-funded
                     (fnn-cold-worker-row worker) descriptor)))
               (word (first reply)) (row (second reply)) (token (third reply))
               (scope (and decodedp (fourth reply))))
          (unless (eq word :assigned)
            ;; An admitted-but-unbound token stays charged. Never construct
            ;; or invent a physical no-child refund after a torn binding.
            (when token
              (setf (fnn-cold-worker-token worker) token (fnn-cold-worker-row worker) row
                    (fnn-cold-worker-scope worker) scope (fnn-cold-worker-phase worker) :binding-fault)
              (when retain (funcall retain worker token))
              (fnn-fault "window admitted but its exact worker binding failed"))
            (setf (fnn-cold-worker-phase worker) :idle (fnn-cold-worker-scope worker) nil
                  *fnn-cold-free* worker)
            (return-from fnn-extent-issue-window (values nil word nil)))
          (setf (fnn-cold-worker-scope worker) scope)
          ;; The literal descriptor the owner captured, not one read back
          ;; from the token; before the worker can run.
          (fnn-extent-window-observation "window-admit token=~s row=~s descriptor=~s"
                                         token row descriptor)
          (fnn-extent-native-observe :issue t descriptor)
          (let ((issued (fnn-extent-executor-enqueue worker row token retain)))
            (when decodedp
              (fnn-err "DECODED-WINDOW issue token=~s scope=~s" token scope))
            (values token :admitted issued)))))))

(defun fnn-extent-executor-acquire (token)
  "Extent lock held; the ledger already funded this exact job."
  (let ((worker *fnn-cold-free*))
    (unless (and worker (not *fnn-cold-stopping*))
      (fnn-fault "admitted cold job lacks its funded executor slot"))
    (destructuring-bind (word row &rest ignored)
        (if (fnn-extent-window-p token)
            (fnn-core-cold-pool 'fn-owner-page-window-executor-acquire
                                    (fnn-cold-worker-row worker) token)
          (fnn-core-page-read-pool 'fn-owner-page-executor-acquire
                                  (fnn-cold-worker-row worker) token))
      (declare (ignore ignored))
      (unless (eq word :assigned) (fnn-fault "cold executor refused admitted job ~a" word))
      (fnn-extent-executor-enqueue worker row token))
    worker))

(defun fnn-extent-executor-observe-returned (worker)
  "Extent lock held. An unexpected death requires a real join before failure
settlement; the dead executor is never reused for another admitted job."
  (when (member (fnn-cold-worker-phase worker) '(:issuing :binding-fault :retiring :releasing))
    (fnn-fault "cold terminal semantic call was already entered"))
  (unless (eq (fnn-cold-worker-phase worker) :returned)
    (when (eq (fnn-core 'fn-pio-worker-death-step
                        (not (sb-thread:thread-alive-p (fnn-cold-worker-thread worker)))) :settle)
      (sb-thread:join-thread (fnn-cold-worker-thread worker) :default nil)
      (fnn-extent-executor-actual-return worker)
      (setf (fnn-cold-worker-result worker)
            (make-condition 'fnn-extent-fault :message "arena-extent-read: cold executor died"))))
  (eq (fnn-cold-worker-phase worker) :returned))

(defun fnn-extent-executor-returned-p (worker)
  "Physical observation only; ACL2 still decides exact settlement."
  (fnn-with-observed-mutex (*fnn-extent-lock* :extent)
    (fnn-extent-executor-observe-returned worker)))

(defun fnn-extent-executor-wait (worker seconds)
  ;; A timed-out wait may return unlocked; the shared wrapper records that
  ;; actual release and does not synthesize a final unlock.
  (fnn-with-observed-mutex (*fnn-extent-lock* :extent)
    (unless (eq (fnn-cold-worker-phase worker) :returned)
      (fnn-observed-condition-wait (fnn-cold-worker-ready worker) *fnn-extent-lock* :extent :timeout seconds))))

(defun fnn-extent-executor-commit (worker io token cachedp)
  "Extent lock held, worker relinquished and cache transfer already done."
  (destructuring-bind (word row &rest ignored)
      (fnn-core-page-read-pool 'fn-owner-page-executor-commit
                               (fnn-cold-worker-row worker) io token cachedp)
    (declare (ignore ignored))
    (unless (eq word :committed) (fnn-fault "cold executor settlement refused ~a" word))
    (setf (fnn-cold-worker-row worker) row
          (fnn-cold-worker-token worker) nil
          (fnn-cold-worker-result worker) nil
          (fnn-cold-worker-span worker) nil
          (fnn-cold-worker-phase worker) :idle)
    (when (and (not *fnn-cold-stopping*)
               (sb-thread:thread-alive-p (fnn-cold-worker-thread worker)))
      (setf (fnn-cold-worker-next worker) *fnn-cold-free*
            *fnn-cold-free* worker))))

(defun fnn-extent-cache-release (tokens)
  "After physical eviction, release only ACL2's exact cached charge."
  (dolist (token tokens)
    (unless (eq (first (fnn-core-page-read-pool 'fn-owner-page-cache-evict token)) :evicted)
      (fnn-fault "cold cache eviction lacks its exact resource binding"))))

(defmacro fnn-with-octets-rd ((st octets fill) &body body)
  "BODY with the realizer's buffer ST holding OCTETS (its array) at FILL;
the buffer lets go of OCTETS afterwards.  Called with the realizer's lock
held."
  `(let ((,st (fnn-live-octets-rd)))
     (setf (svref ,st 0) ,octets
           (svref ,st 1) ,fill)
     (unwind-protect
          (progn ,@body)
       (setf (svref ,st 1) 0
             (svref ,st 0) (make-array 0 :element-type '(unsigned-byte 8))))))

(defun fnn-extent-entry-verdict (octets elen trailer)
  "ACL2's verdict of the entry read into OCTETS (its protected prefix, ELEN
octets, then its 32-octet trailer) against the descriptor's expected
TRAILER: the realizer's own buffer fn-octets-rd holds the prefix in place
(its array is OCTETS, its fill ELEN) and fn-arx-entry-verdict-buffer
(books/payload-extent-read.lisp, KEYSTONE
fn-arx-entry-verdict-buffer-ok-is-the-commitment) answers :ok, :trailer or
:digest.  Called with the realizer's lock held."
  (fnn-with-octets-rd (st octets elen)
    (first (fnn-call 'fn-arx-entry-verdict-buffer trailer (coerce (subseq octets elen) 'list) st))))

(defun fnn-extent-entry-ok (octets elen)
  "ACL2's self-consistency check of the entry read into OCTETS (its
protected prefix, ELEN octets, then its 32-octet trailer):
fn-arx-entry-ok-buffer (books/payload-extent-read.lisp, KEYSTONE
fn-arx-entry-ok-buffer-is-the-frame-check) compares the frame digest of the
prefix with the trailer read after it.  For a read that has no descriptor
yet (fnn-extent-entry-fresh); a read of an accepted extent is decided
against the descriptor's trailer by fnn-extent-entry-verdict.  Called with
the realizer's lock held."
  (fnn-with-octets-rd (st octets elen)
    (first (fnn-call 'fn-arx-entry-ok-buffer (coerce (subseq octets elen) 'list) st))))

(defun fnn-extent-read-entry (file eoff elen)
  "One pread of the entry at [EOFF, EOFF+ELEN+32) of FILE into a fresh
array; refused by name (arena-extent-read) when no such file is registered
or the file holds fewer octets.  Called with the realizer's lock held."
  (let ((fd (gethash file *fnn-extent-fds*))
        (octets (make-array (+ elen 32) :element-type '(unsigned-byte 8))))
    (incf (second *fnn-extent-stats*))
    (unless fd
      (incf (third *fnn-extent-stats*))
      (error 'fnn-extent-fault
             :message (format nil "arena-extent-read: no durable file ~a is registered" file)))
    (unless (= (fnn-extent-pread fd octets eoff) (+ elen 32))
      (incf (third *fnn-extent-stats*))
      (error 'fnn-extent-fault
             :message (format nil "arena-extent-read: ~a holds fewer than ~a octets"
                              (fnn-extent-where file eoff) (+ elen 32))))
    octets))

;;; Row A4 (option (c), lane composed-owner-3; books/owner-cold-line.lisp):
;;; the served read span runs with *fnn-extent-no-io* bound true (host/native/
;;; owner.lisp fnn-owner-chunk-span-no-io).  A miss then reads nothing: it
;;; THROWS the entry it needs to the tag fnn-extent-cold (a throw, not a
;;; condition: fnn-call turns every condition into a store fault), the span (pure over its
;;; stobjs) is discarded, and the host reads the entry OUTSIDE the owner mutex
;;; (fnn-extent-prefetch) within ACL2's dependency deadline
;;; (fn-otb-dependency-step).  A hit is a hit either way: the warm path does
;;; no more work than before. Diagnostic cache-off refuses a cold command
;;; through ACL2 resource admission; it never enables an unfunded fallback.
(defvar *fnn-extent-no-io* nil)

(defun fnn-extent-no-io-usable-p ()
  ;; Every served miss enters ACL2 admission, including diagnostic cache-off.
  t)

(defun fnn-extent-cache-forget (entries)
  "Extent lock held. Forget exact vector bindings, returning eviction tokens
for the core resource ledger. No timeout or cancellation invokes this."
  (let ((tokens nil))
    (dolist (entry entries)
      (let* ((octets (cddddr entry))
             (token (gethash octets *fnn-extent-cache-tokens*)))
        (when token (push token tokens))
        (remhash octets *fnn-extent-cache-tokens*)))
    (nreverse tokens)))

(defun fnn-extent-cache-store (file eoff elen trailer octets &optional token)
  "Extent lock held. Return keptp and exact tokens of evicted buffers."
  (let ((limit (fnn-extent-cache-limit)) (evicted nil))
    (when (plusp limit)
      (push (list* file eoff elen trailer octets) *fnn-extent-cache*)
      (when token (setf (gethash octets *fnn-extent-cache-tokens*) token))
      (when (> (length *fnn-extent-cache*) limit)
        (setq evicted (fnn-extent-cache-forget (nthcdr limit *fnn-extent-cache*)))
        (setq *fnn-extent-cache* (subseq *fnn-extent-cache* 0 limit))))
    (values (plusp limit) evicted)))

(defun fnn-extent-cache-yield-oldest ()
  "Extent lock held.  The caches hold pool charge only for speed: when a read
cannot be admitted for want of the pool's octets, the least recently used
cached buffer gives its charge back (the whole-extent entries first, then the
verified windows) -- ACL2's exact eviction (fn-owner-page-cache-evict), never a
guess about what is free.  T when one was evicted, NIL when no cache holds
anything: the pool is then genuinely out."
  (let ((entry (car (last *fnn-extent-cache*))))
    (cond (entry
           (setq *fnn-extent-cache* (butlast *fnn-extent-cache*))
           (fnn-extent-cache-release (fnn-extent-cache-forget (list entry)))
           t)
          (*fnn-extent-window-cache*
           (let ((window (car (last *fnn-extent-window-cache*))))
             (setq *fnn-extent-window-cache* (butlast *fnn-extent-window-cache*))
             (fnn-extent-cache-release (list (first window))))
           t)
          (t nil))))

(defun fnn-extent-cache-drop-files (files)
  "Extent lock held. Remove physical buffers and return their exact tokens:
the whole-extent cache's and the verified-window cache's (a window token
names its file third)."
  (let ((keep nil) (drop nil) (wkeep nil) (wdrop nil))
    (dolist (entry *fnn-extent-cache*)
      (if (member (first entry) files) (push entry drop) (push entry keep)))
    (setq *fnn-extent-cache* (nreverse keep))
    (dolist (entry *fnn-extent-window-cache*)
      (if (member (third (first entry)) files) (push (first entry) wdrop) (push entry wkeep)))
    (setq *fnn-extent-window-cache* (nreverse wkeep))
    (append (fnn-extent-cache-forget (nreverse drop)) (nreverse wdrop))))

(defun fnn-extent-end-recovery-cache ()
  "Before serving, drop startup-only borrows and every direct/offline cache.
No recovery activation remains. Retained decoder array highwater is separate."
  (fnn-with-observed-mutex (*fnn-extent-lock* :extent)
    (let ((tokens (append (fnn-extent-cache-forget *fnn-extent-cache*)
                          (mapcar #'first *fnn-extent-window-cache*))))
      (setq *fnn-extent-cache* nil *fnn-extent-lz-last* nil *fnn-extent-window-cache* nil)
      (fnn-extent-cache-release tokens))))

(defun fnn-extent-read-verified (file eoff elen trailer)
  "Synchronous private read/verifier activation. Caller already owns a lease
or explicitly selected offline mode; extent lock remains held."
  (let* ((octets (fnn-extent-read-entry file eoff elen))
         (verdict (fnn-extent-entry-verdict octets elen trailer)))
        (unless (eq verdict :ok)
          (incf (third *fnn-extent-stats*))
          (error 'fnn-extent-fault
                 :message
                 (case verdict
                   (:trailer
                    (format nil "arena-extent-trailer: the entry at ~a is not the extent's: its recorded trailer is not the descriptor's"
                            (fnn-extent-where file eoff)))
                   (:digest
                    (format nil "arena-extent-digest: the entry at ~a does not match its trailer"
                            (fnn-extent-where file eoff)))
                   (t
                    (format nil "arena-extent-verdict: ACL2 answered ~s for the entry at ~a"
                            verdict (fnn-extent-where file eoff))))))
    octets))

(defun fnn-extent-sync-settle (row token verdict cachedp)
  "The synchronous read activation returned or unwound before this call.
The local exact I/O row belongs only to this activation, under extent lock."
  (destructuring-bind (settled answer) (fnn-call 'fn-pio-complete row token verdict)
    (declare (ignore settled))
    (when (eq answer :stale) (fnn-fault "synchronous cold completion lost its token"))
    (unless (eq (first (fnn-core-page-read-pool 'fn-owner-page-read-settle token cachedp)) :settled)
      (fnn-fault "synchronous cold completion lost its resource lease"))))

(defun fnn-extent-read-refused (what word)
  "A synchronous read refused by WORD (no lease taken).  Under a stage that
decides its own reads (host/native/io.lisp fnn-extent-with-read-refusal) the
word goes back to it; elsewhere the refusal is raised here, as before."
  (if *fnn-extent-read-refusal*
      (throw 'fnn-extent-read-refused word)
    (fnn-refuse "extent ~a refused: ~a" what word)))

(defun fnn-extent-entry-direct (file eoff elen trailer)
  "A synchronous miss reserves before allocation. Its execution slot is
conservatively charged while the persistent native worker baseline stays put.
A served result transfers to the cache before the caller borrows the vector."
  (let ((mode (first (fnn-core-page-read-pool 'fn-owner-page-read-direct-mode))))
    (when (eq mode :offline)
      (let ((octets (fnn-extent-read-verified file eoff elen trailer)))
        (multiple-value-bind (cachedp evicted)
            (fnn-extent-cache-store file eoff elen trailer octets)
          (declare (ignore cachedp))
          (fnn-extent-cache-release evicted))
        (return-from fnn-extent-entry-direct octets)))
    (unless (eq mode :funded-pool) (fnn-extent-read-refused "read" mode))
    (let ((cache-mode (fnn-core 'fn-pxe-cache-mode (plusp (fnn-extent-cache-limit)))))
      (unless (eq cache-mode :ready) (fnn-extent-read-refused "read" cache-mode)))
    (destructuring-bind (word token &rest ignored)
        (let ((admitted (fnn-core-page-read-pool 'fn-owner-page-read-admit 0 file eoff elen trailer)))
          ;; The pool is out of octets while the caches hold some: they yield,
          ;; oldest first, and the read is asked again.  Only a pool the caches
          ;; cannot relieve refuses the read.
          (loop while (and (eq (first admitted) :read-resources-unavailable)
                           (fnn-extent-cache-yield-oldest))
                do (setq admitted
                         (fnn-core-page-read-pool 'fn-owner-page-read-admit 0 file eoff elen trailer)))
          admitted)
      (declare (ignore ignored))
      (unless (eq word :admitted)
        (fnn-extent-read-refused "read" word))
      (let ((row (fnn-core 'fn-pio-own-admitted-token token))
            (octets nil) (transferring nil))
        (unless row (fnn-fault "synchronous admitted token lacks its owned read"))
        (unwind-protect
             (progn
               (setq octets (fnn-extent-read-verified file eoff elen trailer))
               ;; Once cache mutation begins, an exceptional transfer retains
               ;; the lease: uncertainty about an alias never authorizes refund.
               (setq transferring t)
               (multiple-value-bind (cachedp evicted)
                   (fnn-extent-cache-store file eoff elen trailer octets token)
                 (unless cachedp (fnn-fault "funded synchronous result has no cache owner"))
                 (fnn-extent-cache-release evicted)
                 (fnn-extent-sync-settle row token :ok t))
               octets)
          (unless transferring
            ;; Read/verifier stack and its buffer-stobj alias have unwound.
            (setq octets nil)
            (fnn-extent-sync-settle row token :error nil)))))))

(defun fnn-extent-entry (file eoff elen trailer)
  "The verified vector under the complete descriptor identity. Called with
extent lock held; caller keeps that lock until its final vector borrow ends."
  (let ((hit (find-if (lambda (e) (and (eql (first e) file) (eql (second e) eoff)
                                       (eql (third e) elen) (eql (fourth e) trailer)))
                      *fnn-extent-cache*)))
    (if hit
        (progn (incf (first *fnn-extent-stats*))
               (unless (eq hit (first *fnn-extent-cache*))
                 (setq *fnn-extent-cache* (cons hit (delete hit *fnn-extent-cache* :test #'eq))))
               (cddddr hit))
      (if *fnn-extent-no-io*
          (throw 'fnn-extent-cold (list file eoff elen trailer))
        (fnn-extent-entry-direct file eoff elen trailer)))))

(defun fnn-extent-discovery-release (token)
  "Extent lock held. Caller relinquished the exact unverified buffer lease."
  (when token
    (unless (eq (first (fnn-core-page-read-pool 'fn-owner-page-read-discovery-release token)) :released)
      (fnn-fault "discovery buffer lost its exact resource lease"))))

(defun fnn-extent-entry-fresh (file eoff elen)
  "Return the self-consistent vector AND its discovery lease. The caller
keeps that lease until its last buffer borrow ends. Extent lock held."
  (let ((mode (first (fnn-core-page-read-pool 'fn-owner-page-read-direct-mode)))
        (token nil) (octets nil) (handed-off nil))
    (case mode
      (:offline nil)
      (:funded-pool
       (destructuring-bind (word lease &rest ignored)
           (fnn-core-page-read-pool 'fn-owner-page-read-discovery-admit file eoff elen)
         (declare (ignore ignored))
         (unless (eq word :admitted) (fnn-extent-read-refused "discovery" word))
         (setq token lease)))
      (otherwise (fnn-extent-read-refused "discovery" mode)))
    (unwind-protect
         (progn
           (setq octets (fnn-extent-read-entry file eoff elen))
           (unless (eq (fnn-extent-entry-ok octets elen) t)
             (incf (third *fnn-extent-stats*))
             (error 'fnn-extent-fault
                    :message (format nil "arena-extent-digest: the entry at ~a does not match its trailer"
                                     (fnn-extent-where file eoff))))
           (setq handed-off t)
           (values octets token))
      (unless handed-off
        ;; The synchronous pread and verifier have returned/unwound; their
        ;; private vector is no longer borrowed, even on allocation failure.
        (setq octets nil)
        (fnn-extent-discovery-release token)))))

;;; The entry a cold span needs, read into the cache (a store fault is
;;; signalled as always: the caller re-signals it in the owner's thread).
;;; Called OFF the owner mutex, from a thread of its own.  The pread runs
;;; WITHOUT the realizer's lock, so a stalled disk holds only this thread:
;;; cached reads on every other connection proceed (the lock is taken to find
;;; the descriptor, and again to decide the entry -- ACL2's verdict uses the
;;; realizer's one buffer -- and keep it).  The entry is decided against the
;;; descriptor's TRAILER (fnn-extent-entry-verdict) and cached under that
;;; identity, exactly as fnn-extent-entry decides and caches it.
(defun fnn-extent-issue-read (cid file eoff elen trailer)
  "Acquire the cold worker's ownership BEFORE launching it. NIL means warm."
  (fnn-with-observed-mutex (*fnn-extent-lock* :extent :wait-p t)
    (let ((mode (fnn-core 'fn-pxe-cache-mode (plusp (fnn-extent-cache-limit)))))
      (unless (eq mode :ready) (return-from fnn-extent-issue-read (values nil mode))))
    (when (find-if (lambda (e) (and (eql (first e) file) (eql (second e) eoff)
                                   (eql (third e) elen) (eql (fourth e) trailer)))
                  *fnn-extent-cache*)
      (return-from fnn-extent-issue-read nil))
    (unless (gethash file *fnn-extent-fds*)
      (error 'fnn-extent-fault
             :message (format nil "arena-extent-read: no durable file ~a is registered" file)))
    (destructuring-bind (word token &rest ignored)
        (fnn-core-page-read-pool 'fn-owner-page-read-admit cid file eoff elen trailer)
      (declare (ignore ignored))
      (unless (eq word :admitted)
        (return-from fnn-extent-issue-read (values nil word)))
      (let ((row (fnn-core 'fn-pio-own-admitted-token token)))
        (unless row (fnn-fault "admitted cold token lacks its owned read"))
        ;; the funded arm's row: in the issued table, protected at close by
        ;; the ledger's close-preview (:read-file-held), not by the holds
        ;; table (the funded arm is not installed: fn-owner-page-read-direct-mode)
        (setq *fnn-extent-issued* (fnn-core 'fn-pio-issued-put token row *fnn-extent-issued*))
        (values token :admitted (fnn-extent-executor-acquire token))))))

(defun fnn-extent-cancel-read (token)
  "Revoke this request's publication right; the worker still owns its fd,
the file and (direct arm) its hold: ACL2's fn-pio-direct-cancel."
  (when token
    (fnn-with-observed-mutex (*fnn-extent-lock* :extent :wait-p t)
      (let ((before *fnn-extent-issued*))
        (setq *fnn-extent-issued* (fnn-core 'fn-pio-direct-cancel token *fnn-extent-issued*))
        (fnn-extent-native-observe :cancel t token)
        (when (and (not (eq before *fnn-extent-issued*))
                   (fnn-developer-selector "FN_NATIVE_PAGE_IO_HOLD"))
          (fnn-err "PAGE-IO cancelled token=~s" token))))))

(defun fnn-extent-complete-read (token verdict)
  "ACL2's completion decision, with the extent lock held. Only actual I/O
settlement calls this. A missing/stale token has no publish or release."
  (destructuring-bind (row answer)
      (fnn-call 'fn-pio-complete (fnn-core 'fn-pio-issued-row token *fnn-extent-issued*)
                token verdict)
    (unless (eq answer :stale)
      (setq *fnn-extent-issued* (fnn-core 'fn-pio-issued-remove token *fnn-extent-issued*)))
    (values answer row)))

(defun fnn-extent-prefetch (token)
  "Read and verify TOKEN, off owner mutex. Return its private verified result;
only observed worker relinquishment allows owner settlement/publication."
  (unless token (return-from fnn-extent-prefetch (list :ok nil)))
  (destructuring-bind (id cid file eoff elen trailer) token
    (declare (ignore id cid))
    (let ((fd nil)
          (octets (make-array (+ elen 32) :element-type '(unsigned-byte 8)))
          (hold (fnn-developer-selector "FN_NATIVE_PAGE_IO_HOLD"))
          (mode (fnn-developer-selector "FN_NATIVE_PAGE_IO_RESULT")))
      (fnn-with-observed-mutex (*fnn-extent-lock* :extent :wait-p t)
        (setq fd (gethash file *fnn-extent-fds*))
        (incf (second *fnn-extent-stats*)))
      (unless fd
        (error 'fnn-extent-fault :message "arena-extent-read: issued file closed"))
      (fnn-extent-page-observation "fd-capture token=~s file=~d fd=~d" token file fd)
      (fnn-extent-native-observe :io-begin t token)
      (when (and hold (plusp (length hold)) (not (probe-file hold)))
        (fnn-err "PAGE-IO held token=~s file=~d" token file)
        (loop until (probe-file hold) do (sleep 0.05)))
      (when (equal mode "error")
        (error 'fnn-extent-fault :message "arena-extent-read: injected pread error"))
      (when (equal mode "runtime-error")
        ;; Exercise a condition that actually retains the private array.
        (error 'type-error :datum octets :expected-type 'null))
      (let ((got (if (equal mode "short") 0 (fnn-extent-pread fd octets eoff))))
        (fnn-extent-page-observation "read-return token=~s fd=~d count=~d injected=~s"
                                     token fd got (equal mode "short"))
        (fnn-with-observed-mutex (*fnn-extent-lock* :extent :wait-p t)
          (list (if (= got (+ elen 32))
                    (fnn-extent-entry-verdict octets elen trailer) :read)
                octets))))))

;;; THE UNFUNDED COLD LINE (lane cold-read-ownership; Codex r31 F1/F2;
;;; books/page-read-direct.lisp).  While the page pool runs in its :offline
;;; context the served cold line uses the same issued rows, persistent
;;; workers and owner settlement as the funded pool, without the ledger:
;;; fn-pio-direct-admit binds an idle worker to an fn-pio row naming the file
;;; incarnation, kept in *fnn-extent-issued* until the worker ACTUALLY
;;; returns, so fnn-extent-close (fn-pio-file-clear-p) never closes the
;;; descriptor under its pread; a timeout only cancels the row
;;; (fnn-extent-cancel-read); a miss with every worker busy is refused by
;;; name (:read-resources-unavailable: the 403 of books/owner-resource-line.lisp),
;;; never given a thread; fn-pio-direct-settle
;;; settles once (:publish, :cancelled, (:fault V) or :stale).  The worker
;;; count is ACL2's (fn-pio-direct-workers, a profile-limits row the
;;; launcher's thread reservation counts).
(defvar *fnn-extent-direct-next* nil)
(fnn-guarded-by *fnn-extent-direct-next* *fnn-extent-lock*)
;; (the direct read counter, advanced only by
;; fn-pio-direct-admit)

(defun fnn-extent-direct-start ()
  "Before serving: install the unfunded cold line's persistent workers, once
per run, unless the funded pool already started its executor."
  (unless (or *fnn-cold-workers* (fnn-extent-pool-funded-p))
    (let ((workers (fnn-core 'fn-pio-direct-workers)))
      (unless (and (integerp workers) (plusp workers))
        (fnn-fault "owner returned a malformed cold worker count"))
      ;; the two tables start as ACL2's initial (both empty): the effect of
      ;; a release is process-local and this is its rebuild
      (fnn-with-observed-mutex (*fnn-extent-lock* :extent :wait-p t)
        (destructuring-bind (issued holds) (fnn-call 'fn-pio-direct-initial)
          (setq *fnn-extent-issued* issued *fnn-extent-file-holds* holds)))
      (fnn-extent-executor-start workers))))

(defun fnn-extent-issue-direct (cid file eoff elen trailer)
  "Owner mutex held (retirement excluded), unfunded pool: issue the read's
row and bind an idle worker before the mutex is released.  NIL: warm.
Otherwise (values TOKEN WORD WORKER): WORD :admitted, or ACL2's refusal."
  (fnn-with-observed-mutex (*fnn-extent-lock* :extent :wait-p t)
    (let ((mode (fnn-core 'fn-pxe-cache-mode (plusp (fnn-extent-cache-limit)))))
      (unless (eq mode :ready) (return-from fnn-extent-issue-direct (values nil mode nil))))
    (when (find-if (lambda (e) (and (eql (first e) file) (eql (second e) eoff)
                                   (eql (third e) elen) (eql (fourth e) trailer)))
                  *fnn-extent-cache*)
      (return-from fnn-extent-issue-direct nil))
    (unless (gethash file *fnn-extent-fds*)
      (error 'fnn-extent-fault
             :message (format nil "arena-extent-read: no durable file ~a is registered" file)))
    (let ((worker (and (not *fnn-cold-stopping*) *fnn-cold-free*)))
      (destructuring-bind (word next token row worker-row issued holds)
          (fnn-call 'fn-pio-direct-admit *fnn-extent-direct-next* cid file eoff elen trailer
                    (and worker (fnn-cold-worker-row worker))
                    *fnn-extent-issued* *fnn-extent-file-holds*)
        (fnn-extent-native-observe :issue t cid file eoff elen trailer)
        (unless (eq word :admitted)
          ;; Every worker busy is ACL2's named refusal; any other word means
          ;; the host offered a row ACL2 does not recognize as idle and fresh
          ;; (:hold-refused: a token already held or issued, an invariant
          ;; breach).
          (unless (eq word :read-resources-unavailable)
            (fnn-fault (format nil "cold worker binding refused: ~a" word)))
          (return-from fnn-extent-issue-direct (values nil word nil)))
        (fnn-extent-page-observation
         "direct-admit token=~s previous-next=~s next=~s row=~s cid=~s inc=~s eoff=~s elen=~s trailer=~s"
         token *fnn-extent-direct-next* next worker-row cid file eoff elen trailer)
        (setq *fnn-extent-direct-next* next
              *fnn-extent-issued* issued
              *fnn-extent-file-holds* holds)
        (values token :admitted (fnn-extent-executor-enqueue worker worker-row token))))))

(defun fnn-extent-direct-settle (worker token verdict)
  "Owner and extent locks held, WORKER observed returned: ACL2's settlement
of the issued row and the worker together.  (values ANSWER SETTLED-ROW).
Anything but :stale removes the row (the file pin) and idles the worker."
  (destructuring-bind (answer row worker-row issued holds)
      (fnn-call 'fn-pio-direct-settle token (fnn-cold-worker-row worker) verdict
                *fnn-extent-issued* *fnn-extent-file-holds*)
    (fnn-extent-native-observe :settle t token)
    (when (eq answer :unheld)
      ;; the row is issued but no hold carries its token: the tables
      ;; disagree, never a silent settle
      (fnn-fault (format nil "issued read ~s is held by no token" token)))
    (fnn-extent-page-observation "direct-settle token=~s verdict=~s answer=~s"
                                 token verdict answer)
    (unless (eq answer :stale)
      ;; decided (ACL2 answered) ... released (the row gone, the hold
      ;; dropped, the worker idle): the holder's two cuts, *fn-pio-file-holds-cuts*
      (fnn-holder-cut :fn-pio-file-holds-decided)
      (setq *fnn-extent-issued* issued *fnn-extent-file-holds* holds)
      (setf (fnn-cold-worker-row worker) worker-row
            (fnn-cold-worker-token worker) nil
            (fnn-cold-worker-phase worker) :idle)
      (when (and (not *fnn-cold-stopping*)
                 (sb-thread:thread-alive-p (fnn-cold-worker-thread worker)))
        (setf (fnn-cold-worker-next worker) *fnn-cold-free*
              *fnn-cold-free* worker))
      (fnn-holder-cut :fn-pio-file-holds-released))
    (values answer row)))

;;; The realizer (A-DURABLE-EXTENT's constrained function), raw and *1*.
;;; The descriptor's guard (books/payload-arena-extent-logic.lisp
;;; fn-arn-extent-guardp: EOFF <= POFF, POFF+PLEN <= EOFF+ELEN) places the
;;; payload slice inside the verified prefix; the arena's invariant
;;; (fn-arena$x-wfp) carries it to every call.
(defun fn-durable-realize-octet (file eoff elen poff plen trailer i)
  (when *fnn-extent-window-mode*
    (return-from fn-durable-realize-octet
      (fnn-extent-window-realize-octet file eoff elen poff plen trailer i)))
  (fnn-with-observed-mutex (*fnn-extent-lock* :extent :wait-p t)
    (aref (fnn-extent-entry file eoff elen trailer) (+ (- poff eoff) i))))

(defun acl2_*1*_acl2::fn-durable-realize-octet (file eoff elen poff plen trailer i)
  (fn-durable-realize-octet file eoff elen poff plen trailer i))

;;; The span (A-DURABLE-EXTENT's fn-durable-realize-span, books/assumptions-
;;; durable.lisp): the N octets from I.  In the window route the borrowed
;;; windows and the verified-window cache answer it a stretch at a time; the
;;; synchronous route copies them from the verified entry under the one lock.
(defun fn-durable-realize-span (file eoff elen poff plen trailer i n)
  (when *fnn-extent-window-mode*
    (return-from fn-durable-realize-span
      (fnn-extent-window-realize-span file eoff elen poff plen trailer i n)))
  (fnn-with-observed-mutex (*fnn-extent-lock* :extent :wait-p t)
    (let ((entry (fnn-extent-entry file eoff elen trailer))
          (start (+ (- poff eoff) i))
          (acc nil))
      (declare (type (simple-array (unsigned-byte 8) (*)) entry)
               (type fixnum start n))
      (loop for k of-type fixnum from (+ start n -1) downto start do
        (push (aref entry k) acc))
      acc)))

(defun acl2_*1*_acl2::fn-durable-realize-span (file eoff elen poff plen trailer i n)
  (fn-durable-realize-span file eoff elen poff plen trailer i n))

;;; A-ARENA-SPAN-INTO (books/assumptions-durable-spans.lisp): the same N octets
;;; appended to the octet buffer, no list.  FN-ARENA is the concrete
;;; fn-arena-extent object and FN-OCTETS the concrete fn-octets$c (or a
;;; congruent clone's: field 0 the ub8 array, field 1 the fill; io.lisp
;;; fnn-octets-append-vector writes it the same way).  The window [AT, AT+N)
;;; is checked against the payload length at entry.  An extent entry runs the
;;; run loop of fnn-extent-window-realize-span with one REPLACE per decided
;;; run, from the fn-ew-span array under the lock that decided it; the
;;; synchronous route copies one REPLACE from the trailer-verified entry
;;; (fnn-extent-entry) under the one lock.  The fill moves once, after the last
;;; run, so a cold throw or refusal leaves the buffer as it was.  Every other
;;; entry kind appends the arena's own span.
(defun fn-arena-get-span-into (h at n fn-arena fn-octets)
  (unless (and (integerp h) (<= 0 h) (< h (fn-arena$x-count fn-arena))
               (integerp at) (<= 0 at) (integerp n) (<= 0 n)
               (<= (+ at n) (fn-arena$x-payload-len h fn-arena)))
    (error 'fnn-extent-fault
           :message (format nil "arena-span-into: window [~a, ~a+~a) of handle ~a is not inside its payload"
                            at at n h)))
  (let ((e (fn-arena$x-exti h fn-arena)))
    (if (not (fn-arn-extentp e))
        (fn-oct-write-list (fn-arena$x-get-span h at n fn-arena) fn-octets)
      (let ((fill (svref fn-octets 1)))
        (declare (type fixnum fill n))
        (fn-octets$c-reserve (+ fill n) fn-octets)
        (destructuring-bind (file eoff elen poff plen trailer) e
          (cond
           ((zerop n))
           (*fnn-extent-window-mode*
            (let ((pos fill) (p at) (end (+ at n)))
              (declare (type fixnum pos p end))
              (flet ((sink (dst count)
                       (declare (type fixnum count))
                       (replace (the fnn-octets (svref fn-octets 0))
                                (the fnn-octets (svref dst 0))
                                :start1 pos :end2 count)
                       (incf pos count)))
                (declare (dynamic-extent #'sink))
                (loop while (< p end)
                      do (multiple-value-bind (octets count)
                             (fnn-extent-window-realize-run file eoff elen poff plen trailer
                                                            p end #'sink)
                           (declare (ignore octets))
                           (incf p count))))))
           (t
            (fnn-with-observed-mutex (*fnn-extent-lock* :extent :wait-p t)
              (let ((entry (fnn-extent-entry file eoff elen trailer))
                    (start (+ (- poff eoff) at)))
                (declare (type fnn-octets entry))
                (replace (the fnn-octets (svref fn-octets 0)) entry
                         :start1 fill :start2 start :end2 (+ start n)))))))
        (setf (svref fn-octets 1) (+ fill n))))
    fn-octets))

(defun acl2_*1*_acl2::fn-arena-get-span-into (h at n fn-arena fn-octets)
  (fn-arena-get-span-into h at n fn-arena fn-octets))

;;; The whole payload in one call (fn-durable-realize-octets): one lock, one
;;; cache lookup or one pread and one verdict, one list of PLEN octets built
;;; from the verified buffer.
(defun fn-durable-realize-octets (file eoff elen poff plen trailer)
  ;; Keep this vector borrow under the cache lock: an eviction may release
  ;; its lease only after the last borrowed byte has been copied. The caller
  ;; still owes the resulting list's separate response/maintenance budget.
  (fnn-with-observed-mutex (*fnn-extent-lock* :extent :wait-p t)
    (let ((entry (fnn-extent-entry file eoff elen trailer))
          (start (- poff eoff))
          (acc nil))
      (declare (type (simple-array (unsigned-byte 8) (*)) entry)
               (type fixnum start plen))
      (loop for i of-type fixnum from (+ start plen -1) downto start do
        (push (aref entry i) acc))
      acc)))

(defun acl2_*1*_acl2::fn-durable-realize-octets (file eoff elen poff plen trailer)
  (fn-durable-realize-octets file eoff elen poff plen trailer))

;;; A-DURABLE-LZ (books/assumptions.lisp; lane compression-extents, PRF-326):
;;; the realizer of a COMPRESSED extent.  It reads the block C through the
;;; extent realizer above (the entry decided by ACL2 against the
;;; descriptor's trailer), runs ACL2's DEFLATE payload decoder over it
;;; (host/native/deflate.lisp fnn-pzd-decode: fn-zpl-decode-bufs over pooled
;;; buffers; KEYSTONE fn-zpl-decode-bufs-is-the-lz-value,
;;; books/deflate-pool.lisp: an :ok answer is the value the constraint names)
;;; and answers ACL2's octets.  A decode that fails is refused by name
;;; (arena-extent-lz-decode, a store fault: a recovery event) and nothing is
;;; answered.  One decoded payload is kept (the last one read) so a reader
;;; that reads octet by octet (fn-arena$x-get) decodes once; the key is the
;;; whole descriptor identity (file, entry, expected trailer, block, length)
;;; and the dictionary's identity (EQ: one shared list per dictionary).
;;; (*fnn-extent-lz-last*, the one decoded payload kept, is declared with the other extent caches.)

(defun fn-durable-realize-lz (file eoff elen poff plen trailer n dict)
  (when *fnn-extent-window-mode*
    (throw 'fnn-extent-window-refused
      (values (fnn-core-cold-single 'fn-owner-page-window-decoded-refusal) nil nil nil)))
  (let* ((key (list file eoff elen trailer poff plen n))
         (hit (fnn-with-observed-mutex (*fnn-extent-lock* :extent :wait-p t)
                (let ((last *fnn-extent-lz-last*))
                  (and last (equal (first last) key) (eq (second last) dict)
                       (cddr last))))))
    (or hit
        (let* ((c (fn-durable-realize-octets file eoff elen poff plen trailer))
               (r (funcall 'fnn-pzd-decode dict c n)))
          (unless (and (consp r) (eq (first r) :ok) (eql (length (rest r)) n))
            ;; The path is read under the lock that guards the table: another
            ;; thread may be registering a file (fnn-extent-register).
            (let ((where (fnn-with-observed-mutex (*fnn-extent-lock* :extent :wait-p t)
                           (incf (third *fnn-extent-stats*))
                           (fnn-extent-where file poff))))
              (error 'fnn-extent-fault
                     :message (format nil "arena-extent-lz-decode: the block at ~a does not decode to its ~a octets"
                                      where n))))
          (let ((octets (rest r)))
            (fnn-with-observed-mutex (*fnn-extent-lock* :extent :wait-p t)
              (setq *fnn-extent-lz-last* (list* key dict octets)))
            octets)))))

(defun acl2_*1*_acl2::fn-durable-realize-lz (file eoff elen poff plen trailer n dict)
  (fn-durable-realize-lz file eoff elen poff plen trailer n dict))

;;; Octet I of the decoded payload, from the generated buffer fn-dlz
;;; (books/decoded-payload-buffer.lisp, def-representation :scalar
;;; (:octet-seq fn-octets)).  The decode writes into ACL2's pooled output
;;; buffer (fnn-pzd-decode-into) and fn-dlz-fill-from, a generated index loop,
;;; makes fn-dlz hold those octets: no octet list of the decoded payload is
;;; built.  KEYSTONE fn-dlz-decode-into-is-the-lz-value
;;; (books/decoded-payload-decode-into.lisp): after an :ok decode, the filled
;;; buffer is the value A-DURABLE-LZ names; reads are fn-dlz-nth
;;; (fn-dlz-nth-is-nth).  The buffer holds the last payload read, keyed as
;;; *fnn-extent-lz-last* is (descriptor identity and the dictionary's EQ
;;; identity), under the extent lock.  Every call here comes through
;;; fn-durable-realize-lz-octet, whose ACL2 guard is a natural index; its
;;; one caller, fn-arena$x-get (books/payload-arena-extent.lisp), has that
;;; guard.  RULING 1 (2026-10-06, RULINGS-20261006.md) authorises this edit to
;;; a forbidden-zone file.
(defvar *fnn-extent-lz-buffer-key* nil)       ; (key . dict) fn-dlz holds
(fnn-guarded-by *fnn-extent-lz-buffer-key* *fnn-extent-lock*)
(defvar *fnn-dlz* nil)

(defun fnn-live-dlz ()
  (or *fnn-dlz*
      (setq *fnn-dlz*
            (or (cdr (assoc 'fn-dlz (user-stobj-alist *the-live-state*)))
                (fnn-fault "the decoded-payload buffer stobj is not in this image")))))

(defun fnn-extent-lz-buffer-octet (file eoff elen poff plen trailer n dict i)
  (let ((key (list file eoff elen trailer poff plen n)))
    (loop
      (multiple-value-bind (hit octet)
          (fnn-with-observed-mutex (*fnn-extent-lock* :extent :wait-p t)
            (let ((held *fnn-extent-lz-buffer-key*))
              (if (and held (equal (car held) key) (eq (cdr held) dict))
                  (values t (fn-dlz-nth i (fnn-live-dlz)))
                  (values nil nil))))
        (when hit (return octet)))
      (let* ((c (fn-durable-realize-octets file eoff elen poff plen trailer))
             (r (funcall 'fnn-pzd-decode-into dict c n
                         (lambda (out)
                           (fnn-with-observed-mutex (*fnn-extent-lock* :extent :wait-p t)
                             (let ((st (fnn-live-dlz)))
                               (setq *fnn-extent-lz-buffer-key* nil)
                               (fn-dlz-fill-from out st)
                               (setq *fnn-extent-lz-buffer-key* (cons key dict))))))))
        (unless (eq r :ok)
          (let ((where (fnn-with-observed-mutex (*fnn-extent-lock* :extent :wait-p t)
                         (incf (third *fnn-extent-stats*))
                         (fnn-extent-where file poff))))
            (error 'fnn-extent-fault
                   :message (format nil "arena-extent-lz-decode: the block at ~a does not decode to its ~a octets"
                                    where n))))))))

;;; The arena scalar export consumes this seam. Window mode may only borrow
;;; the authenticated returned decoded window; it never falls back to the
;;; full-payload realizer. The physical decoded worker installs that leaf.
(defun fn-durable-realize-lz-octet (file eoff elen poff compressed trailer decoded dict i)
  (if *fnn-extent-window-mode*
      (if (fboundp 'fnn-extent-decoded-window-realize-octet)
          (fnn-extent-decoded-window-realize-octet
           file eoff elen poff compressed trailer decoded dict i)
        (throw 'fnn-extent-window-refused
          (values (fnn-core-cold-single 'fn-owner-page-window-decoded-refusal)
                  nil nil nil)))
    (fnn-extent-lz-buffer-octet file eoff elen poff compressed trailer decoded dict i)))

(defun acl2_*1*_acl2::fn-durable-realize-lz-octet
    (file eoff elen poff compressed trailer decoded dict i)
  (fn-durable-realize-lz-octet file eoff elen poff compressed trailer decoded dict i))

;;; A-ARENA-STORED (books/assumptions-stored.lisp; lane compress-5, NNT-055):
;;; handle H's payload AS IT IS STORED, for XFN-ZARTICLE
;;; (books/nntp-zarticle.lisp fn-zar-stored).  The live fn-arena is the
;;; concrete arena of books/payload-arena-extent.lisp; EXT[H] names H's
;;; extent.  For a COMPRESSED extent (FILE EOFF ELEN POFF PLEN TRAILER N
;;; DICT) the answer is (DICT C N), C the block's durable octets read through
;;; the extent realizer above (one pread, ACL2's trailer check); nothing is
;;; decoded.  Any other handle (resident, staged, a plain extent, past the
;;; array) answers NIL, and ACL2 then answers as ARTICLE does.
(defun fn-arena-stored (h fn-arena)
  (let ((e (and (integerp h) (<= 0 h)
                (< h (fn-arena$x-ext-length fn-arena))
                (fn-arena$x-exti h fn-arena))))
    (if (fn-arn-lz-extentp e)
        (list (nth 7 e)
              (fn-durable-realize-octets (nth 0 e) (nth 1 e) (nth 2 e)
                                         (nth 3 e) (nth 4 e) (nth 5 e))
              (nth 6 e))
      nil)))

(defun acl2_*1*_acl2::fn-arena-stored (h fn-arena)
  (fn-arena-stored h fn-arena))

;;; A-PGS-HOST-IO's page fill, in place (books/assumptions-pgs-host-io.lisp
;;; `fn-pgs-fill-frame'; lane arena-store-7 2026-09-28, in place since lane
;;; s-frame-fill 2026-10-06).  Page ADDR of the page file FILE (a file id from
;;; `fnn-extent-register') is read by ONE pread of its 16 KiB into the calling
;;; thread's stationary page buffer, the generated octet buffer `fn-pgb'
;;; (books/def-buffer.lisp), whose array is allocated once per thread and
;;; reused for every fill; then ACL2's `fn-pgb-frame-put' stores the buffer's
;;; 2048 little-endian words into the selected array of pgs-mem, a word at a
;;; time from the buffer's array into the stobj's.  No list of the page's words
;;; or of its octets is built; the word order is a theorem
;;; (fn-pgb-frame-put-is-frame-put-of-words), not a promise of this file.  A
;;; short read or an unknown file is refused by name (history-page-read: a
;;; store fault, a recovery event), never answered with made-up words, and the
;;; selector and range are checked before anything is read, so nothing is
;;; written outside the range.  Whether the words are the page the committed
;;; table names is ACL2's digest check (books/history-records-disk.lisp: the
;;; lazy decode of the committed history image `fn-hrs-disk-history', and
;;; fn-hrecs's retry loop).
(defvar *fnn-pgb-table* (make-hash-table :test 'eq :weakness :key :synchronized t)
  "thread -> its page buffer stobj (a live fn-pgb, array of 16384 octets)")

(defun fnn-live-pgb ()
  "The calling thread's page buffer, made on its first fill."
  (let ((thread sb-thread:*current-thread*))
    (or (gethash thread *fnn-pgb-table*)
        (setf (gethash thread *fnn-pgb-table*)
              ;; the concrete octet stobj's live object: a two-slot vector, the
              ;; array and the fill (as fnn-with-octets-rd sets them)
              (vector (make-array 16384 :element-type '(unsigned-byte 8)) 16384)))))

(defun fn-pgs-fill-frame (file addr sel base pgs-mem)
  (unless (and (member sel '(0 1 2)) (integerp base) (<= 0 base)
               (<= (+ base 2048) (fn-pgs-frame-len sel pgs-mem)))
    (error 'fnn-extent-fault
           :message (format nil "history-page-read: frame ~a at word ~a is outside the page store"
                            sel base)))
  (let ((st (fnn-live-pgb)))
    ;; R3: the pread runs inside the extent-lock region that looked up its
    ;; descriptor, so a page file closed or replaced under the lock cannot
    ;; hand this read a descriptor number the kernel has reused.  A caller
    ;; already inside the extent lock (the limit and live reconfiguration
    ;; quanta reach this through ACL2's history refresh) reads under its own
    ;; hold: with-mutex is not recursive.  The short-read fault names the
    ;; path from the same region, for the same reason.
    (flet ((read-page ()
             (let ((fd (gethash file *fnn-extent-fds*))
                   (base-off (gethash file *fnn-extent-bases* 0)))
               (unless (and fd (integerp addr) (<= 0 addr))
                 (error 'fnn-extent-fault
                        :message (format nil "history-page-read: no page file ~a (page ~a)"
                                         file addr)))
               (let ((got (fnn-extent-pread fd (svref st 0) (+ base-off (* addr 16384)))))
                 (unless (= got 16384)
                   (error 'fnn-extent-fault
                          :message (format nil "history-page-read: page ~a of ~a: ~a of 16384 octets"
                                           addr (gethash file *fnn-extent-paths*) got)))))))
      (if (sb-thread:holding-mutex-p *fnn-extent-lock*)
          (read-page)
        (fnn-with-observed-mutex (*fnn-extent-lock* :extent :wait-p t)
          (read-page))))
    (fn-pgb-frame-put sel base st pgs-mem)))

(defun acl2_*1*_acl2::fn-pgs-fill-frame (file addr sel base pgs-mem)
  (fn-pgs-fill-frame file addr sel base pgs-mem))

;;; Online disk release (lane online-reclaim-2, row Q16, PRF-930;
;;; books/extent-retire.lisp).  A descriptor is no longer held for the
;;; process's life: once a checkpoint publication has reseated the live
;;; payloads at the installed checkpoint's frames, the files it dropped (the
;;; covered log segments, the previous checkpoint) are RETIRED, and a retired
;;; file waits until ACL2 finds it quiet (fn-xrt-quiet-files: its count in
;;; the arena's file column is 0 and no log member in flight names it), is
;;; then pending at the arena-reader generation stamped there, and its
;;; descriptor closes once no off-mutex arena reader pinned at or below that
;;; stamp still runs (fnn-arena-clear-p, books/arena-reader-pins.lisp).
;;; Closing the last descriptor of an unlinked file gives its blocks back
;;; while the owner serves.  host/native/owner.lisp fnn-owner-release-extents
;;; drives it.

(defvar *fnn-extent-retired* nil)
(fnn-guarded-by *fnn-extent-retired* (fnn-owner-service-lock))
;; (file ids not yet found quiet)
(defvar *fnn-extent-pending* nil)
(fnn-guarded-by *fnn-extent-pending* (fnn-owner-service-lock))
;; ((S . IDS) ...: quiet file ids waiting for
;; the readers pinned at or below the stamp S)
(defvar *fnn-extent-checkpoint-id* nil)
(fnn-guarded-by *fnn-extent-checkpoint-id* (fnn-owner-service-lock))
;; (the realizer id of the installed checkpoint
;; the last reseat pointed payloads at)
;; *fnn-extent-image-id* is declared in host/native/io.lisp, which sets it first and loads before this file.

(defun fnn-extent-ids-of-paths (paths)
  "The registered file ids whose path is one of PATHS."
  (fnn-with-observed-mutex (*fnn-extent-lock* :extent)
    (let ((ids nil))
      (maphash (lambda (id path) (when (member path paths :test #'equal) (push id ids)))
               *fnn-extent-paths*)
      (sort ids #'<))))

(defun fnn-extent-close (ids)
  "Physical retirement: workers keep descriptors; cache credits release on
actual eviction, descriptor credits only after successful OS close."
  (fnn-with-observed-mutex (*fnn-extent-lock* :extent)
    (let ((closed 0) (keep nil))
      (dolist (id ids)
        ;; the direct arm's reads: one lookup of the holds table (KEYSTONE
        ;; fn-pio-direct-quiet-is-clear: under the carried agreement it is the
        ;; walk of the issued rows this used to run); the funded arm's rows
        ;; are the ledger's, answered :read-file-held by the close-preview
        (if (fnn-core 'fn-pio-direct-quiet-p id *fnn-extent-file-holds*)
            (progn
              (fnn-extent-cache-release (fnn-extent-cache-drop-files (list id)))
              (when (and *fnn-extent-lz-last* (eql (first (first *fnn-extent-lz-last*)) id))
                (setq *fnn-extent-lz-last* nil))
              (let* ((word (first (fnn-core-page-read-pool 'fn-owner-page-read-close-preview id)))
                     (fd (gethash id *fnn-extent-fds*)))
                (case word
                  ((:closable :unfunded-offline :stale)
                   (when (and fd (eq word :stale))
                     (fnn-fault "registered incarnation lacks its resource lease"))
                   ;; From the attempted OS close through settlement/table
                   ;; removal, any error is uncertain, never a retry/refusal.
                   ;; The owner fences while it still holds its mutex. No
                   ;; refund or table removal runs after a failed close.
                   (handler-case
                       (progn
                         (when fd
                           (let ((fault (fnn-developer-selector "FN_NATIVE_EXTENT_CLOSE_FAULT")))
                             (when (equal fault "before-close") (fnn-os-fail 5))
                             (fnn-close fd)
                             (when (equal fault "after-close") (fnn-os-fail 5)))
                           (fnn-extent-page-observation "fd-close file=~d fd=~d" id fd)
                           (fnn-extent-native-observe :close t id)
                           (incf closed))
                         (unless (eq word :unfunded-offline)
                           (let ((settled (first (fnn-core-page-read-pool 'fn-owner-page-read-close id))))
                             (unless (member settled '(:closed :stale))
                               (fnn-fault "closed incarnation still has a resource owner"))))
                         (remhash id *fnn-extent-fds*)
                         (remhash id *fnn-extent-paths*)
                         (remhash id *fnn-extent-incarnations*)
                         (remhash id *fnn-extent-bases*)
                         (when (and fd (fnn-developer-selector "FN_NATIVE_PAGE_IO_HOLD"))
                           (fnn-err "PAGE-IO closed file=~d" id)))
                     (serious-condition (e)
                       ;; Developer observation of the retained descriptor and
                       ;; ACL2 lease after the failure, before the owner fence.
                       (unwind-protect
                            (when (fnn-developer-selector "FN_NATIVE_EXTENT_CLOSE_FAULT")
                              (fnn-err "EXTENT close uncertain file=~d registered=~a lease=~a"
                                       id (not (null (gethash id *fnn-extent-fds*)))
                                       (first (fnn-core-page-read-pool 'fn-owner-page-read-close-preview id))))
                         (if fd
                             (fnn-indeterminate "extent close ~d: recovery required: ~a" id e)
                           (error e))))))
                  (:read-file-held
                   ;; The funded window route's holds are the ledger's: a
                   ;; worker that still owns the descriptor is observed the
                   ;; way the direct arm's table observed it.
                   (push id keep)
                   (when (fnn-developer-selector "FN_NATIVE_PAGE_IO_HOLD")
                     (fnn-err "PAGE-IO close-held file=~d" id)))
                  (otherwise (fnn-fault "invalid incarnation close preview ~a" word)))))
          (progn
            (push id keep)
            (when (fnn-developer-selector "FN_NATIVE_PAGE_IO_HOLD")
              (fnn-err "PAGE-IO close-held file=~d" id)))))
      (values closed (nreverse keep)))))

(defun fnn-extent-open-count ()
  "The descriptors the realizer holds (the natives' observation)."
  (fnn-with-observed-mutex (*fnn-extent-lock* :extent)
    (hash-table-count *fnn-extent-fds*)))

(defun fnn-extent-stats-line ()
  "The realizer's counters (the natives' observation): hits, preads,
refusals."
  (fnn-with-observed-mutex (*fnn-extent-lock* :extent)
    (format nil "extent-cache hits=~d misses=~d refusals=~d"
            (first *fnn-extent-stats*) (second *fnn-extent-stats*) (third *fnn-extent-stats*))))
