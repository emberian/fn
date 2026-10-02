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

(defvar *fnn-extent-lock* (sb-thread:make-mutex :name "fn extent realizer"))
(defvar *fnn-extent-fds* (make-hash-table))   ; guarded-by: *fnn-extent-lock* (file id -> fd)
(defvar *fnn-extent-paths* (make-hash-table)) ; guarded-by: *fnn-extent-lock* (file id -> path)
(defvar *fnn-extent-incarnations* (make-hash-table))
;; guarded-by: *fnn-extent-lock* (file id -> (device . inode) of the file opened)
(defvar *fnn-extent-bases* (make-hash-table)) ; guarded-by: *fnn-extent-lock* (file id -> page 0's offset)
(defvar *fnn-extent-next-id* nil)
(defvar *fnn-extent-cache* nil)
(defvar *fnn-extent-cache-tokens* (make-hash-table :test #'eq))
;; Verified vector -> immutable charged token. Capacity is a static pool
;; allowance, not a per-entry credit that eviction pretends to reclaim.
;; ((file eoff elen trailer . octets) ...), most recent first: the verified
;; entries, each under the descriptor identity it was verified for
(defvar *fnn-extent-stats* (list 0 0 0))      ; hits, misses (preads), refusals
(defvar *fnn-extent-issued* (make-hash-table :test #'equal))
;; guarded-by: *fnn-extent-lock*. Token -> ACL2 ownership row (PRF-1057).
;; Removed only by actual worker completion, never a request's timeout.

(defun fnn-extent-pool-storage-start (file-capacity worker-capacity cache-capacity)
  "Install the admitted fixed peak capacities before any live registration.
ACL2 supplied capacities include cache insertion overlap; table backing is
permanent baseline, never refunded when an association is removed."
  (sb-thread:with-mutex (*fnn-extent-lock*)
    (unless (and (zerop (hash-table-count *fnn-extent-fds*))
                 (zerop (hash-table-count *fnn-extent-paths*))
                 (zerop (hash-table-count *fnn-extent-incarnations*))
                 (zerop (hash-table-count *fnn-extent-bases*))
                 (zerop (hash-table-count *fnn-extent-issued*))
                 (zerop (hash-table-count *fnn-extent-cache-tokens*))
                 (null *fnn-extent-cache*))
      (fnn-fault "cold pool installation follows physical registration"))
    (setf *fnn-extent-fds* (make-hash-table :size file-capacity :rehash-threshold 1.0 :rehash-size 1)
          *fnn-extent-paths* (make-hash-table :size file-capacity :rehash-threshold 1.0 :rehash-size 1)
          *fnn-extent-incarnations* (make-hash-table :size file-capacity :rehash-threshold 1.0 :rehash-size 1)
          *fnn-extent-bases* (make-hash-table :size file-capacity :rehash-threshold 1.0 :rehash-size 1)
          *fnn-extent-issued* (make-hash-table :test #'equal :size worker-capacity :rehash-threshold 1.0 :rehash-size 1)
          *fnn-extent-cache-tokens* (make-hash-table :test #'eq :size cache-capacity :rehash-threshold 1.0 :rehash-size 1))))

(defun fnn-extent-register (path)
  "Reserve ACL2's fresh incarnation name and funded path lease before open.
Failed constructors spend the name; refund only after definite OS release.
The core explicitly distinguishes an unfunded offline registration."
  (let ((id nil) (funded nil))
    (sb-thread:with-mutex (*fnn-extent-lock*)
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
             (setq fd (fnn-open path (logior sb-posix:o-rdonly +fnn-o-nofollow+)))
             (let* ((st (fnn-fstat fd))
                    (incarnation (cons (sb-posix:stat-dev st) (sb-posix:stat-ino st))))
               (sb-thread:with-mutex (*fnn-extent-lock*)
                 (setf (gethash id *fnn-extent-fds*) fd
                       (gethash id *fnn-extent-paths*) path
                       (gethash id *fnn-extent-incarnations*) incarnation
                       installed t)))
             id)
        (unless installed
          ;; An ambiguous close aborts this cleanup before any credit refund.
          (when fd (fnn-close fd))
          (sb-thread:with-mutex (*fnn-extent-lock*)
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
    (sb-thread:with-mutex (*fnn-extent-lock*)
      (setf (gethash id *fnn-extent-bases*) base))
    id))

(defun fnn-extent-pread (fd octets offset)
  "Fill OCTETS from OFFSET of FD; the count read (short at end of file)."
  ;; Developer image only (lane composed-owner-3, row A4): a stalled read
  ;; device.  While the named file exists a pread does not return, as a read
  ;; from a device under maintenance does not (tests/test_native_slow_disk.py).
  (let ((stall (fnn-developer-selector "FN_NATIVE_TEST_READ_STALL_FILE")))
    (when (and stall (plusp (length stall)))
      (loop while (probe-file stall) do (sleep 0.05))))
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
  (sb-thread:with-mutex (*fnn-extent-lock*)
    (let ((mode (first (fnn-core-page-read-pool 'fn-owner-page-read-open-context))))
      (unless (member mode '(:offline :served))
        (fnn-fault (format nil "page pool context refused: ~a" mode)))
      mode)))

(defun fnn-extent-pool-funded-p ()
  "Whether cold reads go through the funded pool (admission, the executor)."
  (sb-thread:with-mutex (*fnn-extent-lock*)
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
  row thread token result phase next
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
  (let* ((octets (svref input 0))
         (got (sb-sys:with-pinned-objects (octets)
                (sb-alien:alien-funcall
                 (sb-alien:extern-alien "pread"
                   (function sb-alien:long sb-alien:int sb-alien:system-area-pointer
                             sb-alien:unsigned-long sb-alien:long))
                 fd (sb-sys:vector-sap octets) count offset))))
    (setf (svref input 1) (if (minusp got) 0 got))
    (if (minusp got) :error :ok)))

(defun fnn-extent-window-run (worker token)
  "Actual core digest trajectory; only the fixed private window is retained."
  (destructuring-bind (kind ticket file eoff elen poff plen offset expected) token
    (declare (ignore kind))
    (unless (fnn-core-cold-single 'fn-crw-supportedp (cddr token) ticket)
      (fnn-fault "window descriptor is not representable by the selected native ABI"))
    (let ((fd nil) (incarnation nil) (plan nil)
          (input (fn-octets$c-reserve 64 (create-fn-octets$c)))
          (hash (create-pgs-digest-state)) (window (create-fn-ew-buffer)))
      (sb-thread:with-mutex (*fnn-extent-lock*)
        (setq fd (gethash file *fnn-extent-fds*)
              incarnation (gethash file *fnn-extent-incarnations*)))
      (unless (and fd incarnation) (fnn-fault "window issued file closed"))
      ;; Developer observation gate: the real token/fd/private fixed buffers
      ;; remain owned while the test device delays actual worker completion.
      (let ((hold (fnn-developer-selector "FN_NATIVE_PAGE_IO_HOLD")))
        (when (and hold (plusp (length hold)) (not (probe-file hold)))
          (fnn-err "WINDOW-IO held token=~s file=~d" token file)
          (loop until (probe-file hold) do (sleep 0.05))))
      (destructuring-bind (next hash1)
          (fnn-core-cold-values 'fn-ews-begin file eoff elen poff plen offset ticket incarnation token expected hash)
        (setq plan next hash hash1))
      (loop
        ;; A cancelled worker finishes its current bounded core operation,
        ;; then relinquishes its activation without publishing a window.
        (unless (sb-thread:with-mutex (*fnn-extent-lock*)
                  (first (fnn-core-cold-pool 'fn-owner-page-window-work-permittedp
                            (fnn-cold-worker-row worker) token)))
          (return nil))
        (destructuring-bind (status next hash1) (fnn-core-cold-values 'fn-ews-tick plan hash)
          (setq plan next hash hash1)
          (case status
            (:continue nil)
            (:read
             ;; :READ status requests I/O; :READ plan phase is terminal.
             (let ((effect (fnn-core-cold-single 'fn-ews-effect plan hash)))
               (unless effect (return (list plan window)))
               (let ((io-status (fnn-extent-window-pread fd input (fifth effect) (sixth effect))))
                 (destructuring-bind (answer next hash1 window1)
                     (fnn-core-cold-values 'fn-ews-read effect io-status plan input hash window)
                   (declare (ignore answer))
                   (setq plan next hash hash1 window window1)))))
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
            (fnn-cold-worker-phase worker) :returned))))

(defun fnn-extent-window-byte (worker token i)
  "Borrow one scalar after physical return, retaining every window credit."
  (sb-thread:with-mutex (*fnn-extent-lock*)
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
  "Scalar-only terminal disposition; integrity failure is never a new miss."
  (sb-thread:with-mutex (*fnn-extent-lock*)
    (unless (fnn-extent-executor-observe-returned worker)
      (return-from fnn-extent-window-outcome :pending))
    (when (eq (first (fnn-core-cold-pool 'fn-owner-page-window-outcome
                       (fnn-cold-worker-row worker) token nil)) :cancelled)
      (return-from fnn-extent-window-outcome :cancelled))
    (let ((result (fnn-cold-worker-result worker)))
      (when (typep result 'condition) (error result))
      (first (fnn-core-cold-pool 'fn-owner-page-window-outcome
               (fnn-cold-worker-row worker) token (first result))))))

(defun fnn-extent-window-byte-at (worker token file eoff elen poff plen trailer i)
  "Original arena payload coordinate goes unchanged to the core scalar join."
  (sb-thread:with-mutex (*fnn-extent-lock*)
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
(defvar *fnn-extent-window-mode* nil)
(defvar *fnn-extent-window-worker* nil)
(defvar *fnn-extent-window-token* nil)

(defun fnn-extent-window-realize-octet (file eoff elen poff plen trailer i)
  "Staged realizer: scalar success or the core's complete cold descriptor."
  (multiple-value-bind (word byte)
      (if *fnn-extent-window-worker*
          (fnn-extent-window-byte-at *fnn-extent-window-worker* *fnn-extent-window-token*
                                    file eoff elen poff plen trailer i)
        (values :unavailable nil))
    (cond ((eq word :byte) byte)
          ((member word '(:cancelled :stale-job))
           (throw 'fnn-extent-window-refused (values word nil nil nil)))
          ((eq word :unavailable)
           (throw 'fnn-extent-cold
             (fnn-core-cold-single 'fn-pwr-cold-descriptor file eoff elen poff plen trailer i)))
          (t (error 'fnn-extent-fault
                    :message "arena-extent-read: window was not an authenticated returned result")))))

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

(defun fnn-extent-window-release (worker token)
  "Caller holds no buffer aliases. Drop the sole retained result BEFORE refund."
  (sb-thread:with-mutex (*fnn-extent-lock*)
    (unless (and (fnn-extent-executor-observe-returned worker)
                 (fnn-core-cold-single 'fn-pwx-boundp
                           (fnn-core-cold-single 'fn-owner-page-read-ledger (fnn-live-page-read-pool))
                           (fnn-cold-worker-row worker) token :returned))
      (return-from fnn-extent-window-release :stale-job))
    (setf (fnn-cold-worker-result worker) nil)
    (destructuring-bind (word row &rest ignored)
        (fnn-core-cold-pool 'fn-owner-page-window-executor-release
                                (fnn-cold-worker-row worker) token)
      (declare (ignore ignored))
      (unless (eq word :released) (fnn-fault "window release lost exact returned job"))
      (setf (fnn-cold-worker-row worker) row
            (fnn-cold-worker-token worker) nil
            (fnn-cold-worker-phase worker) :idle)
      (when (and (not *fnn-cold-stopping*)
                 (sb-thread:thread-alive-p (fnn-cold-worker-thread worker)))
        (setf (fnn-cold-worker-next worker) *fnn-cold-free*
              *fnn-cold-free* worker))
      word)))

; Staged cancellation never refunds, never terminates a thread, and never
; borrows its output. Extent mutex serializes revocation with scalar reads.
(defun fnn-extent-window-cancel (worker token)
  (sb-thread:with-mutex (*fnn-extent-lock*)
    (destructuring-bind (word row &rest ignored)
        (fnn-core-cold-pool 'fn-owner-page-window-executor-cancel
                                (fnn-cold-worker-row worker) token)
      (declare (ignore ignored))
      (when (eq word :cancelled) (setf (fnn-cold-worker-row worker) row))
      word)))

(defun fnn-extent-window-settle-cancelled (worker token)
  "After actual return/join and last scalar borrow. Drop result before refund."
  (sb-thread:with-mutex (*fnn-extent-lock*)
    (unless (and (fnn-extent-executor-observe-returned worker)
                 (fnn-core-cold-single 'fn-pwx-boundp
                           (fnn-core-cold-single 'fn-owner-page-read-ledger (fnn-live-page-read-pool))
                           (fnn-cold-worker-row worker) token :cancelled-returned))
      (return-from fnn-extent-window-settle-cancelled :stale-job))
    (setf (fnn-cold-worker-result worker) nil)
    (destructuring-bind (word row &rest ignored)
        (fnn-core-cold-pool 'fn-owner-page-window-executor-settle-cancelled
                                (fnn-cold-worker-row worker) token)
      (declare (ignore ignored))
      (unless (eq word :released) (fnn-fault "cancelled window lost exact returned job"))
      (setf (fnn-cold-worker-row worker) row
            (fnn-cold-worker-token worker) nil
            (fnn-cold-worker-phase worker) :idle)
      (when (and (not *fnn-cold-stopping*)
                 (sb-thread:thread-alive-p (fnn-cold-worker-thread worker)))
        (setf (fnn-cold-worker-next worker) *fnn-cold-free*
              *fnn-cold-free* worker))
      word)))

(declaim (notinline fnn-extent-executor-job))
(defun fnn-extent-executor-job (worker)
  "Publish a private result, but do not yet announce relinquishment."
  (let* ((token (fnn-cold-worker-token worker))
         (result
           (handler-case
               (if (equal (fnn-developer-selector "FN_NATIVE_PAGE_IO_RESULT") "launch-error")
                   (progn
                     (fnn-err "PAGE-IO dispatch-failed token=~s worker=retained buffer=none" token)
                     (error 'fnn-extent-fault :message "arena-extent-read: injected job dispatch error"))
                 (cond ((fn-pwz-tokenp token)
                        (fnn-core-cold-single 'fn-owner-page-window-decoded-refusal)
                        (fnn-fault "decoded executor funding is not installed"))
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
    (sb-thread:with-mutex (*fnn-extent-lock*)
      (setf (fnn-cold-worker-result worker) result))
    ;; The activation returns no buffer-bearing value to the loop. Only the
    ;; retained worker field owns the result when actual return is announced.
    nil))

(defun fnn-extent-executor-loop (worker)
  (loop
    (sb-thread:with-mutex (*fnn-extent-lock*)
      (loop until (eq (fnn-cold-worker-phase worker) :queued) do
        (when *fnn-cold-stopping* (return-from fnn-extent-executor-loop nil))
        (sb-thread:condition-wait (fnn-cold-worker-ready worker) *fnn-extent-lock*))
      (setf (fnn-cold-worker-phase worker) :working))
    ;; This call has returned before RETURNED is made observable. No worker
    ;; activation still consumes the token/fd/vector when owner takes it.
    (fnn-extent-executor-job worker)
    (sb-thread:with-mutex (*fnn-extent-lock*)
      (fnn-extent-executor-actual-return worker)
      (sb-thread:condition-broadcast (fnn-cold-worker-ready worker)))))

(defun fnn-extent-executor-start (workers)
  "Called once after ACL2 baseline installation, before recovery/listen."
  (when *fnn-cold-workers* (fnn-fault "cold executor already installed"))
  (setq *fnn-cold-stopping* nil)
  (handler-case
      (dotimes (slot workers)
        (let ((worker (%make-fnn-cold-worker :row (fnn-core 'fn-pxe-new slot) :phase :idle)))
          ;; Keep partially constructed slots for definite cleanup on failure.
          (push worker *fnn-cold-workers*)
          (setf (fnn-cold-worker-thread worker)
                (sb-thread:make-thread (lambda () (fnn-extent-executor-loop worker))
                                       :name "fn cold executor"))
          (sb-thread:with-mutex (*fnn-extent-lock*)
            (setf (fnn-cold-worker-next worker) *fnn-cold-free*
                  *fnn-cold-free* worker))))
    (serious-condition (condition)
      (fnn-extent-executor-stop)
      (error condition))))

(defun fnn-extent-executor-stop ()
  "Stop clients first. Join every worker before closing any shared file.
No cancellation, timeout or thread termination releases a job or baseline."
  (sb-thread:with-mutex (*fnn-extent-lock*)
    (setq *fnn-cold-stopping* t)
    (dolist (worker *fnn-cold-workers*)
      ;; Stop revokes future bounded window steps but never manufactures
      ;; physical return or last-borrow settlement. Legacy jobs stay distinct.
      (let ((token (fnn-cold-worker-token worker)))
        (when (fn-pwx-tokenp token)
          (destructuring-bind (word row &rest ignored)
              (fnn-core-cold-pool 'fn-owner-page-window-executor-cancel
                                  (fnn-cold-worker-row worker) token)
            (declare (ignore ignored))
            (when (eq word :cancelled) (setf (fnn-cold-worker-row worker) row)))))
      (sb-thread:condition-broadcast (fnn-cold-worker-ready worker))))
  (dolist (worker *fnn-cold-workers*)
    (when (fnn-cold-worker-thread worker)
      (sb-thread:join-thread (fnn-cold-worker-thread worker) :default nil)))
  ;; Every worker has actually returned and exited: no slot can be offered
  ;; again (fnn-extent-direct-start may install a fresh set in a later run).
  (sb-thread:with-mutex (*fnn-extent-lock*)
    (setq *fnn-cold-free* nil *fnn-cold-workers* nil)))

(defun fnn-extent-executor-enqueue (worker row token)
  "Extent lock held; ACL2 already assigned this exact funded physical slot."
  (setq *fnn-cold-free* (fnn-cold-worker-next worker))
  (setf (fnn-cold-worker-row worker) row
        (fnn-cold-worker-token worker) token
        (fnn-cold-worker-next worker) nil
        (fnn-cold-worker-result worker) nil
        (fnn-cold-worker-phase worker) :queued)
  (sb-thread:condition-broadcast (fnn-cold-worker-ready worker))
  worker)

(defun fnn-extent-issue-window (descriptor)
  "Staged only: core ticket, demand, typed lease and exact slot in one call.
The served caller must await complete demand/allocator and descriptor joins."
  (sb-thread:with-mutex (*fnn-extent-lock*)
    (let ((worker *fnn-cold-free*))
      (unless (and worker (not *fnn-cold-stopping*))
        (return-from fnn-extent-issue-window (values nil :read-resources-unavailable nil)))
      (destructuring-bind (word row token &rest ignored)
          (fnn-core-cold-pool 'fn-owner-page-window-executor-acquire-funded
                                  (fnn-cold-worker-row worker) descriptor)
        (declare (ignore ignored))
        (unless (eq word :assigned)
          (when token (fnn-fault "window admitted but its exact worker binding failed"))
          (return-from fnn-extent-issue-window (values nil word nil)))
        (values token :admitted (fnn-extent-executor-enqueue worker row token))))))

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
  (sb-thread:with-mutex (*fnn-extent-lock*)
    (fnn-extent-executor-observe-returned worker)))

(defun fnn-extent-executor-wait (worker seconds)
  (sb-thread:with-mutex (*fnn-extent-lock*)
    (unless (eq (fnn-cold-worker-phase worker) :returned)
      (sb-thread:condition-wait (fnn-cold-worker-ready worker) *fnn-extent-lock* :timeout seconds))))

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

(defun fnn-extent-cache-drop-files (files)
  "Extent lock held. Remove physical buffers and return their exact tokens."
  (let ((keep nil) (drop nil))
    (dolist (entry *fnn-extent-cache*)
      (if (member (first entry) files) (push entry drop) (push entry keep)))
    (setq *fnn-extent-cache* (nreverse keep))
    (fnn-extent-cache-forget (nreverse drop))))

(defun fnn-extent-end-recovery-cache ()
  "Before serving, drop startup-only borrows and every direct/offline cache.
No recovery activation remains. Retained decoder array highwater is separate."
  (sb-thread:with-mutex (*fnn-extent-lock*)
    (let ((tokens (fnn-extent-cache-forget *fnn-extent-cache*)))
      (setq *fnn-extent-cache* nil *fnn-extent-lz-last* nil)
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
    (unless (eq mode :funded-pool) (fnn-refuse "extent read refused: ~a" mode))
    (let ((cache-mode (fnn-core 'fn-pxe-cache-mode (plusp (fnn-extent-cache-limit)))))
      (unless (eq cache-mode :ready) (fnn-refuse "extent read refused: ~a" cache-mode)))
    (destructuring-bind (word token &rest ignored)
        (fnn-core-page-read-pool 'fn-owner-page-read-admit 0 file eoff elen trailer)
      (declare (ignore ignored))
      (unless (eq word :admitted) (fnn-refuse "extent read refused: ~a" word))
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
         (unless (eq word :admitted) (fnn-refuse "extent discovery refused: ~a" word))
         (setq token lease)))
      (otherwise (fnn-refuse "extent discovery refused: ~a" mode)))
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
  (sb-thread:with-mutex (*fnn-extent-lock* :wait-p t)
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
        (setf (gethash token *fnn-extent-issued*) row)
        (values token :admitted (fnn-extent-executor-acquire token))))))

(defun fnn-extent-cancel-read (token)
  "Revoke this request's publication right; the worker still owns its fd."
  (when token
    (sb-thread:with-mutex (*fnn-extent-lock* :wait-p t)
      (let ((row (gethash token *fnn-extent-issued*)))
        (when row
          (setf (gethash token *fnn-extent-issued*) (fnn-core 'fn-pio-cancel row token))
          (when (fnn-developer-selector "FN_NATIVE_PAGE_IO_HOLD")
            (fnn-err "PAGE-IO cancelled token=~s" token)))))))

(defun fnn-extent-complete-read (token verdict)
  "ACL2's completion decision, with the extent lock held. Only actual I/O
settlement calls this. A missing/stale token has no publish or release."
  (destructuring-bind (row answer)
      (fnn-call 'fn-pio-complete (gethash token *fnn-extent-issued*) token verdict)
    (unless (eq answer :stale)
      (setf (gethash token *fnn-extent-issued*) row)
      (remhash token *fnn-extent-issued*))
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
      (sb-thread:with-mutex (*fnn-extent-lock* :wait-p t)
        (setq fd (gethash file *fnn-extent-fds*))
        (incf (second *fnn-extent-stats*)))
      (unless fd
        (error 'fnn-extent-fault :message "arena-extent-read: issued file closed"))
      (when (and hold (plusp (length hold)) (not (probe-file hold)))
        (fnn-err "PAGE-IO held token=~s file=~d" token file)
        (loop until (probe-file hold) do (sleep 0.05)))
      (when (equal mode "error")
        (error 'fnn-extent-fault :message "arena-extent-read: injected pread error"))
      (when (equal mode "runtime-error")
        ;; Exercise a condition that actually retains the private array.
        (error 'type-error :datum octets :expected-type 'null))
      (let ((got (if (equal mode "short") 0 (fnn-extent-pread fd octets eoff))))
        (sb-thread:with-mutex (*fnn-extent-lock* :wait-p t)
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
;; guarded-by: *fnn-extent-lock* (the direct read counter, advanced only by
;; fn-pio-direct-admit)

(defun fnn-extent-direct-start ()
  "Before serving: install the unfunded cold line's persistent workers, once
per run, unless the funded pool already started its executor."
  (unless (or *fnn-cold-workers* (fnn-extent-pool-funded-p))
    (let ((workers (fnn-core 'fn-pio-direct-workers)))
      (unless (and (integerp workers) (plusp workers))
        (fnn-fault "owner returned a malformed cold worker count"))
      (fnn-extent-executor-start workers))))

(defun fnn-extent-issue-direct (cid file eoff elen trailer)
  "Owner mutex held (retirement excluded), unfunded pool: issue the read's
row and bind an idle worker before the mutex is released.  NIL: warm.
Otherwise (values TOKEN WORD WORKER): WORD :admitted, or ACL2's refusal."
  (sb-thread:with-mutex (*fnn-extent-lock* :wait-p t)
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
      (destructuring-bind (word next token row worker-row)
          (fnn-call 'fn-pio-direct-admit *fnn-extent-direct-next* cid file eoff elen trailer
                    (and worker (fnn-cold-worker-row worker)))
        (unless (eq word :admitted)
          ;; Every worker busy is ACL2's named refusal; any other word means
          ;; the host offered a row ACL2 does not recognize as idle and fresh.
          (unless (eq word :read-resources-unavailable)
            (fnn-fault (format nil "cold worker binding refused: ~a" word)))
          (return-from fnn-extent-issue-direct (values nil word nil)))
        (setq *fnn-extent-direct-next* next)
        (setf (gethash token *fnn-extent-issued*) row)
        (values token :admitted (fnn-extent-executor-enqueue worker worker-row token))))))

(defun fnn-extent-direct-settle (worker token verdict)
  "Owner and extent locks held, WORKER observed returned: ACL2's settlement
of the issued row and the worker together.  (values ANSWER SETTLED-ROW).
Anything but :stale removes the row (the file pin) and idles the worker."
  (destructuring-bind (answer row worker-row)
      (fnn-call 'fn-pio-direct-settle (gethash token *fnn-extent-issued*)
                (fnn-cold-worker-row worker) token verdict)
    (unless (eq answer :stale)
      (remhash token *fnn-extent-issued*)
      (setf (fnn-cold-worker-row worker) worker-row
            (fnn-cold-worker-token worker) nil
            (fnn-cold-worker-phase worker) :idle)
      (when (and (not *fnn-cold-stopping*)
                 (sb-thread:thread-alive-p (fnn-cold-worker-thread worker)))
        (setf (fnn-cold-worker-next worker) *fnn-cold-free*
              *fnn-cold-free* worker)))
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
  (sb-thread:with-mutex (*fnn-extent-lock* :wait-p t)
    (aref (fnn-extent-entry file eoff elen trailer) (+ (- poff eoff) i))))

(defun acl2_*1*_acl2::fn-durable-realize-octet (file eoff elen poff plen trailer i)
  (fn-durable-realize-octet file eoff elen poff plen trailer i))

;;; The whole payload in one call (fn-durable-realize-octets): one lock, one
;;; cache lookup or one pread and one verdict, one list of PLEN octets built
;;; from the verified buffer.
(defun fn-durable-realize-octets (file eoff elen poff plen trailer)
  ;; Keep this vector borrow under the cache lock: an eviction may release
  ;; its lease only after the last borrowed byte has been copied. The caller
  ;; still owes the resulting list's separate response/maintenance budget.
  (sb-thread:with-mutex (*fnn-extent-lock* :wait-p t)
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
(defvar *fnn-extent-lz-last* nil)             ; (key dict . octets)

(defun fn-durable-realize-lz (file eoff elen poff plen trailer n dict)
  (when *fnn-extent-window-mode*
    (throw 'fnn-extent-window-refused
      (values (fnn-core-cold-single 'fn-owner-page-window-decoded-refusal) nil nil nil)))
  (let* ((key (list file eoff elen trailer poff plen n))
         (hit (sb-thread:with-mutex (*fnn-extent-lock* :wait-p t)
                (let ((last *fnn-extent-lz-last*))
                  (and last (equal (first last) key) (eq (second last) dict)
                       (cddr last))))))
    (or hit
        (let* ((c (fn-durable-realize-octets file eoff elen poff plen trailer))
               (r (funcall 'fnn-pzd-decode dict c n)))
          (unless (and (consp r) (eq (first r) :ok) (eql (length (rest r)) n))
            ;; The path is read under the lock that guards the table: another
            ;; thread may be registering a file (fnn-extent-register).
            (let ((where (sb-thread:with-mutex (*fnn-extent-lock* :wait-p t)
                           (incf (third *fnn-extent-stats*))
                           (fnn-extent-where file poff))))
              (error 'fnn-extent-fault
                     :message (format nil "arena-extent-lz-decode: the block at ~a does not decode to its ~a octets"
                                      where n))))
          (let ((octets (rest r)))
            (sb-thread:with-mutex (*fnn-extent-lock* :wait-p t)
              (setq *fnn-extent-lz-last* (list* key dict octets)))
            octets)))))

(defun acl2_*1*_acl2::fn-durable-realize-lz (file eoff elen poff plen trailer n dict)
  (fn-durable-realize-lz file eoff elen poff plen trailer n dict))

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

;;; A-PGS-HOST-IO's page fill (books/assumptions.lisp `fn-pgs-fill-realize';
;;; lane arena-store-7, 2026-09-28): the 2048 little-endian u64 words page
;;; ADDR of the page file FILE holds, FILE a file id from
;;; `fnn-extent-register'.  One pread of the 16 KiB page; a short read or an
;;; unknown file is refused by name (history-page-read: a store fault, a
;;; recovery event), never answered with made-up words.  Whether the words
;;; are the page the committed table names is ACL2's digest check
;;; (books/history-records-disk.lisp: the lazy decode of the committed
;;; history image `fn-hrs-disk-history', and fn-hrecs's retry loop).
(defun fn-pgs-fill-realize (file addr)
  (multiple-value-bind (fd base)
      (sb-thread:with-mutex (*fnn-extent-lock* :wait-p t)
        (values (gethash file *fnn-extent-fds*) (gethash file *fnn-extent-bases* 0)))
   (let ((octets (make-array 16384 :element-type '(unsigned-byte 8))))
    (unless (and fd (integerp addr) (<= 0 addr))
      (error 'fnn-extent-fault
             :message (format nil "history-page-read: no page file ~a (page ~a)" file addr)))
    (let ((got (fnn-extent-pread fd octets (+ base (* addr 16384)))))
      (unless (= got 16384)
        (let ((path (sb-thread:with-mutex (*fnn-extent-lock* :wait-p t)
                      (gethash file *fnn-extent-paths*))))
          (error 'fnn-extent-fault
                 :message (format nil "history-page-read: page ~a of ~a: ~a of 16384 octets"
                                  addr path got)))))
    (let ((acc nil))
      (declare (type (simple-array (unsigned-byte 8) (16384)) octets))
      (loop for k of-type fixnum from 2047 downto 0 do
        (let ((w 0) (base (* 8 k)))
          (loop for b of-type fixnum from 7 downto 0 do
            (setq w (logior (ash w 8) (aref octets (+ base b)))))
          (push w acc)))
      acc))))

(defun acl2_*1*_acl2::fn-pgs-fill-realize (file addr)
  (fn-pgs-fill-realize file addr))

;;; A-PGS-HOST-IO's frame form (books/assumptions-pgs-host-io.lisp
;;; `fn-pgs-fill-frame', codex-pagefix): page ADDR of FILE into words BASE ..
;;; BASE+2047 of the pgs-mem array SEL selects.  Until this definition the
;;; image left the constrained function unattached, so every history-records
;;; read (store export, fn-store-sco-image-open) faulted on it.  It is the
;;; constraint's own right-hand side, `fn-pgs-frame-put' of the page's words,
;;; over the one pread above (a short read or an unknown file refused by name
;;; there; the guard's selector and range are ACL2's, checked here again so a
;;; raw caller cannot write outside the range).  Forward (D27): pread straight
;;; into the selected array's storage at word BASE (sb-sys:vector-sap,
;;; A-PGS-LE) instead of through the 2048-word list.
(defun fn-pgs-fill-frame (file addr sel base pgs-mem)
  (unless (and (member sel '(0 1 2)) (integerp base) (<= 0 base)
               (<= (+ base 2048) (fn-pgs-frame-len sel pgs-mem)))
    (error 'fnn-extent-fault
           :message (format nil "history-page-read: frame ~a at word ~a is outside the page store"
                            sel base)))
  (fn-pgs-frame-put sel base (fn-pgs-fill-realize file addr) pgs-mem))

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
;; guarded-by: the owner mutex (file ids not yet found quiet)
(defvar *fnn-extent-pending* nil)
;; guarded-by: the owner mutex ((S . IDS) ...: quiet file ids waiting for
;; the readers pinned at or below the stamp S)
(defvar *fnn-extent-checkpoint-id* nil)
;; guarded-by: the owner mutex (the realizer id of the installed checkpoint
;; the last reseat pointed payloads at)

(defun fnn-extent-ids-of-paths (paths)
  "The registered file ids whose path is one of PATHS."
  (sb-thread:with-mutex (*fnn-extent-lock*)
    (let ((ids nil))
      (maphash (lambda (id path) (when (member path paths :test #'equal) (push id ids)))
               *fnn-extent-paths*)
      (sort ids #'<))))

(defun fnn-extent-close (ids)
  "Physical retirement: workers keep descriptors; cache credits release on
actual eviction, descriptor credits only after successful OS close."
  (sb-thread:with-mutex (*fnn-extent-lock*)
    (let ((closed 0) (keep nil)
          (rows (loop for row being the hash-values of *fnn-extent-issued* collect row)))
      (dolist (id ids)
        (if (fnn-core 'fn-pio-file-clear-p id rows)
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
                  (:read-file-held (push id keep))
                  (otherwise (fnn-fault "invalid incarnation close preview ~a" word)))))
          (progn
            (push id keep)
            (when (fnn-developer-selector "FN_NATIVE_PAGE_IO_HOLD")
              (fnn-err "PAGE-IO close-held file=~d" id)))))
      (values closed (nreverse keep)))))

(defun fnn-extent-open-count ()
  "The descriptors the realizer holds (the natives' observation)."
  (sb-thread:with-mutex (*fnn-extent-lock*)
    (hash-table-count *fnn-extent-fds*)))

(defun fnn-extent-stats-line ()
  "The realizer's counters (the natives' observation): hits, preads,
refusals."
  (sb-thread:with-mutex (*fnn-extent-lock*)
    (format nil "extent-cache hits=~d misses=~d refusals=~d"
            (first *fnn-extent-stats*) (second *fnn-extent-stats*) (third *fnn-extent-stats*))))
