;;; Actual stored-DEFLATE window dispatcher. Loaded after extent.lisp by
;;; the physical integration, which admits and owns every supplied buffer.
;;; This driver does not admit jobs or allocate a whole compressed payload.
(in-package "ACL2")

(defun fnn-extent-decoded-window-realize-octet (file eoff elen poff compressed trailer decoded dict i)
  "The actual scalar getter either borrows a returned decoded byte or throws
its full core-selected cold descriptor while the captured owner is held."
  (let* ((descriptor (fnn-core 'fn-pwz-cold-descriptor
                       file eoff elen poff compressed trailer decoded dict i))
         (dict-id (fnn-core 'fn-pwz-nth 8 descriptor)))
    (multiple-value-bind (word byte)
        (if *fnn-extent-window-worker*
            (fnn-extent-decoded-window-byte-at
              *fnn-extent-window-worker* *fnn-extent-window-token*
              file eoff elen poff compressed trailer decoded dict-id i)
          (values :unavailable nil))
      (cond ((eq word :byte) byte)
            ((member word '(:cancelled :stale-job))
             ;; WW-DIAG (lane w-window, temporary): a borrow that answers a
             ;; refusal word never reaches the cache arm.
             (fnn-err "WW-DIAG realize refused word=~s i=~s borrowed=~s"
                      word i (if *fnn-extent-window-worker* t nil))
             (throw 'fnn-extent-window-refused (values word nil nil nil)))
            ((eq word :unavailable)
             ;; Not in the borrowed window: a verified cached window, else the
             ;; core's complete cold descriptor.
             ;; WW-DIAG (lane w-window, temporary)
             (fnn-err "WW-DIAG realize miss i=~s borrowed=~s cache-entries=~d"
                      i (if *fnn-extent-window-worker* t nil)
                      (length *fnn-extent-window-cache*))
             (let ((hit (fnn-extent-decoded-window-cache-byte
                         file eoff elen poff compressed trailer decoded dict-id i)))
               (fnn-err "WW-DIAG realize miss resolved=~s" (not (null hit)))
               (or hit (throw 'fnn-extent-cold descriptor))))
            (t (error 'fnn-extent-fault
                      :message "arena-extent-read: decoded window was not an authenticated returned result"))))))

;;; The native envelope is published on the existing worker before the
;;; sanctioned private creator runs. It preserves partial construction and
;;; torn semantic calls; it is never a second file/token directory.
(defstruct fnn-decoded-activation job (stage :constructing))

(defmacro fnn-decoded-semantic ((activation) &body body)
  (let ((saved (gensym "DECODED-ACTIVATION-"))
        (answer (gensym "DECODED-ANSWER-")))
    `(let ((,saved ,activation))
       (unless (member (fnn-decoded-activation-stage ,saved) '(:constructing :idle))
         (fnn-fault "decoded private semantic step was already entered"))
       (setf (fnn-decoded-activation-stage ,saved) :calling)
       (let ((,answer (progn ,@body)))
         (setf (fnn-decoded-activation-stage ,saved) :idle)
         ,answer))))

(defun fnn-extent-decoded-window-pread (fd input token effect)
  "Delay only an already selected physical read, off owner/extent exclusion.
The developer hold retains the actual pending effect/private activation; it
does not issue, revoke or settle work. No private bytes enter diagnostics."
  (let ((hold (fnn-developer-selector "FN_NATIVE_PAGE_IO_HOLD")))
    (when (and hold (plusp (length hold)) (not (probe-file hold)))
      (let ((*print-pretty* nil))
        (fnn-err "DECODED-WINDOW held token=~s file=~d fd=~d offset=~d count=~d"
                 token (second effect) fd (fifth effect) (sixth effect)))
      (loop until (probe-file hold) do (sleep 0.05)))
    (let ((status (fnn-extent-window-pread fd input (fifth effect) (sixth effect))))
      (when hold
        (let ((*print-pretty* nil))
          (fnn-err "DECODED-WINDOW read-return token=~s status=~s" token status)))
      status)))

(defun fnn-extent-decoded-storage-start (worker)
  "Actual persistent constructor, authorized by the installed startup baseline."
  (let ((activation (make-fnn-decoded-activation)))
    (setf (fnn-cold-worker-decoded-storage worker) activation)
    (setf (fnn-decoded-activation-job activation)
          (fnn-decoded-semantic (activation) (fnn-core 'create-fn-decoded-job)))
    (setf (fnn-decoded-activation-job activation)
          (fnn-decoded-semantic (activation)
            (fnn-core 'fn-dwj-reserve (fnn-decoded-activation-job activation))))
    activation))

(defun fnn-extent-decoded-storage-retire (worker token)
  "E held after final borrow. Clear current authority before token settlement;
keep baseline backing charged through idle, and quarantine every torn reset."
  (let ((activation (fnn-cold-worker-decoded worker)))
    (when activation
      (unless (eq activation (fnn-cold-worker-decoded-storage worker))
        (fnn-fault "decoded activation is not the baseline scratch"))
      (destructuring-bind (word job &rest ignored)
          (fnn-decoded-semantic (activation)
            (fnn-call 'fn-owner-page-decoded-job-retire
              (fnn-cold-worker-row worker) token
              (fnn-decoded-activation-job activation) (fnn-live-page-read-pool)))
        (declare (ignore ignored))
        (setf (fnn-decoded-activation-job activation) job)
        (unless (eq word :reusable)
          (fnn-fault "decoded scratch still retains operation authority"))
        (fnn-err "DECODED-WINDOW backing token=~s word=~s scope=:persistent-partial-fixed-storage"
                 token word)))))

;;; THE VERIFIED-WINDOW CACHE FOR A DECODED WINDOW (lane w-window; the raw
;;; window's is fnn-extent-window-release's CACHEP arm and books/page-window-read.lisp
;;; fn-pwc-*).  A returned decoded job is, at its last borrow's release, retired
;;; and cached in ONE ACL2 step (fn-owner-page-decoded-job-cache: its outcome is
;;; :ready, KEEP is funded, its authority is retired).  The host then MOVES the
;;; job's window buffer into the cache and gives the persistent worker a fresh
;;; one: the buffer was charged to the pool as the worker's persistent backing,
;;; the new one replaces it under that same charge, and the cache's buffer is
;;; the new KEEP charge (the ledger row ACL2 just made).  The entry is
;;; (TOKEN NIL WINDOW), the raw window cache's shape with no plan: a published
;;; decoded window's extent is a function of its token
;;; (books/decoded-window-read.lisp fn-pwz-token-window-length).
;;; The inline single-array child IS the array it holds: the slot contains the
;;; fn-ew-buffer's (simple-array (unsigned-byte 8) (16384)) directly, not a
;;; field vector around it. Measured on the developer image (3e53d7bc5, run
;;; w-window/native-ww-diag-c on hbox, lane w-window 2026-10-05): (svref job 7)
;;; is a rank-1 array of exactly 16384 octets, element type (unsigned-byte 8),
;;; simple-vector-p NIL. The defconstant below keeps its original bytes: its
;;; expansion is compiled into the image's callers.
(defconstant +fnn-decoded-job-window-slot+ 7
  "The fn-dwj-window child of the fn-decoded-job stobj object (books/decoded-worker-job.lisp:
carry 0, input 1, hash 2, zin 3, win 4, tab 5, out 6, window 7; the input is (svref job 1) above).")

(defun fnn-extent-decoded-window-movable-p (job)
  (and (simple-vector-p job) (> (length job) +fnn-decoded-job-window-slot+)
       (typep (svref job +fnn-decoded-job-window-slot+)
              '(simple-array (unsigned-byte 8) (16384)))))

(defun fnn-extent-decoded-window-cache-attempt (worker token)
  "Extent lock held, the returned job's last borrow released.  NIL, or (:cached
ROW EVICTED): the job retired and its window moved into the cache; ROW is the
worker's row ACL2 answered, EVICTED the tokens of the entries the insertion
pushed out (the caller releases their rows)."
  (let* ((activation (fnn-cold-worker-decoded worker))
         (job (and activation (fnn-decoded-activation-job activation)))
         (movable (and job (fnn-extent-decoded-window-movable-p job))))
    ;; WW-DIAG (lane w-window, temporary): the attempt's every precondition
    ;; and the ACL2 word, so an :uncached lease and an immovable window are
    ;; both observable.
    (fnn-err "WW-DIAG attempt act=~s eq=~s movable=~s"
             (not (null activation)) (eq activation (fnn-cold-worker-decoded-storage worker))
             movable)
    (let ((w (and (vectorp job) (> (length job) 7) (svref job 7))))
      (fnn-err "WW-DIAG slot7 arr=~s svp=~s len=~s" (arrayp w) (simple-vector-p w)
               (ignore-errors (length w)))
      (fnn-err "WW-DIAG slot7b dim0=~s elem=~s" (ignore-errors (array-dimension w 0))
               (ignore-errors (array-element-type w)))
      (when (simple-vector-p w)
        (fnn-err "WW-DIAG slot7c inner=~s dim=~s"
                 (type-of (svref w 0)) (ignore-errors (array-dimension (svref w 0) 0)))))
    (when (and activation
               (eq activation (fnn-cold-worker-decoded-storage worker))
               movable)
      (destructuring-bind (word row job1 &rest ignored)
          (fnn-decoded-semantic (activation)
            (fnn-call 'fn-owner-page-decoded-job-cache
              (fnn-cold-worker-row worker) token
              (fnn-decoded-activation-job activation) (fnn-live-page-read-pool)))
        (declare (ignore ignored))
        (setf (fnn-decoded-activation-job activation) job1)
        (fnn-err "WW-DIAG attempt word=~s" word)
        (when (eq word :cached)
          (let ((window (svref job1 +fnn-decoded-job-window-slot+)))
            (setf (svref job1 +fnn-decoded-job-window-slot+) (create-fn-ew-buffer))
            (fnn-err "DECODED-WINDOW backing token=~s word=:REUSABLE scope=:persistent-partial-fixed-storage"
                     token)
            (list :cached row (fnn-extent-window-cache-insert token nil window))))))))

(defun fnn-extent-decoded-window-cache-byte (file eoff elen poff compressed trailer decoded dict-id i)
  "A cached decoded window's byte I of this exact descriptor, or NIL.  The host
only selects candidates by the token's own descriptor and requested offset;
ACL2 decides the hit (fn-owner-page-decoded-window-cache-byte-at)."
  (fnn-with-observed-mutex (*fnn-extent-lock* :extent)
    (dolist (entry *fnn-extent-window-cache* nil)
      (destructuring-bind (token plan window) entry
        (declare (ignore plan))
        ;; WW-DIAG (lane w-window, temporary): each scanned entry's whole
        ;; descriptor against the request, so a mismatching field is visible.
        (fnn-err "WW-DIAG scan kind=~s tok=(~s ~s ~s ~s ~s ~s ~s ~s ~s ~s) want=(~s ~s ~s ~s ~s ~s ~s ~s i=~s)"
                 (first token)
                 (second token) (third token) (fourth token) (fifth token)
                 (sixth token) (seventh token) (eighth token) (ninth token)
                 (tenth token) (nth 10 token)
                 file eoff elen poff compressed trailer decoded dict-id i)
        (when (and (eq (first token) :decoded-window)
                   (eql (third token) file) (eql (fourth token) eoff)
                   (eql (fifth token) elen) (eql (sixth token) poff)
                   (eql (seventh token) compressed) (eql (ninth token) trailer)
                   (eql (tenth token) decoded) (eql (nth 10 token) dict-id)
                   (integerp (eighth token)) (<= (eighth token) i))
          (destructuring-bind (word byte)
              (fnn-core-page-read-pool 'fn-owner-page-decoded-window-cache-byte-at
                                       token file eoff elen poff compressed trailer decoded
                                       dict-id i window)
            ;; WW-DIAG (lane w-window, temporary)
            (fnn-err "WW-DIAG scan answer word=~s byte=~s" word byte)
            (when (eq word :byte)
              (incf (first *fnn-extent-stats*))
              (unless (eq entry (first *fnn-extent-window-cache*))
                (setq *fnn-extent-window-cache*
                      (cons entry (delete entry *fnn-extent-window-cache* :test #'eq))))
              (return byte))))))))

(defun fnn-extent-decoded-window-run (worker token)
  "Same worker/token/pool; actual retained ACL2 controller selects each step.
The issuer draws its declared fixed-storage projection before this entry;
allocator/GC and pointed-to controller graphs remain outside that partial scope."
  (let* ((activation (fnn-cold-worker-decoded-storage worker))
         (fd nil) (incarnation nil))
    (unless (and (fnn-decoded-activation-p activation)
                 (eq (fnn-decoded-activation-stage activation) :idle))
      (fnn-fault "decoded baseline scratch unavailable or quarantined"))
    ;; Cancellation and assignment share E. A cancelled dispatch never claims
    ;; the idle scratch; after authorization, publish the alias before the
    ;; semantic assign so a torn call remains discoverable for quarantine.
    (sb-thread:with-mutex (*fnn-extent-lock*)
      (unless (first (fnn-core-cold-pool 'fn-owner-page-window-work-permittedp
                       (fnn-cold-worker-row worker) token))
        (return-from fnn-extent-decoded-window-run nil))
      (setq fd (gethash (fnn-core 'fn-pwz-nth 2 token) *fnn-extent-fds*)
            incarnation (gethash (fnn-core 'fn-pwz-nth 2 token) *fnn-extent-incarnations*))
      (unless (and fd incarnation) (fnn-fault "decoded issued file closed"))
      (setf (fnn-cold-worker-decoded worker) activation)
      (destructuring-bind (word job &rest ignored)
          (fnn-decoded-semantic (activation)
            (fnn-call 'fn-owner-page-decoded-job-assign
              (fnn-cold-worker-row worker) token token incarnation
              (fnn-decoded-activation-job activation) (fnn-live-page-read-pool)))
        (declare (ignore ignored))
        (setf (fnn-decoded-activation-job activation) job)
        (unless (eq word :decoded-assigned) (fnn-fault "decoded assignment refused"))))
    (destructuring-bind (word job)
        (fnn-decoded-semantic (activation)
          (fnn-call 'fn-dwj-begin token (fnn-decoded-activation-job activation)))
      (setf (fnn-decoded-activation-job activation) job)
      (unless (eq word :decoded-started) (fnn-fault "decoded initialization refused")))
    (loop
      (unless (sb-thread:with-mutex (*fnn-extent-lock*)
                (first (fnn-core-cold-pool 'fn-owner-page-window-work-permittedp
                         (fnn-cold-worker-row worker) token)))
        (return nil))
      (destructuring-bind (word effect job)
          (fnn-decoded-semantic (activation)
            (fnn-call 'fn-dwj-one token (fnn-decoded-activation-job activation)))
        (setf (fnn-decoded-activation-job activation) job)
        (case word
          (:read
           ;; Only this core-selected effect authorizes the physical write
           ;; into the fixed private child. That alias dies with this call.
           (let* ((read-effect (fourth effect))
                  (status (fnn-extent-decoded-window-pread
                            fd (svref job 1) token read-effect)))
             (destructuring-bind (answer next)
                 (fnn-decoded-semantic (activation)
                   (fnn-call 'fn-dwj-read-observation token (third effect) status job))
               (declare (ignore answer))
               (setf (fnn-decoded-activation-job activation) next))))
          ((:ready :refused) (return activation))
          ((:stale-decoded-worker :stale-decoded-read)
           (fnn-fault "decoded retained controller refused its current activation"))
          (otherwise nil))))))

(defun fnn-extent-decoded-window-outcome (worker token)
  (sb-thread:with-mutex (*fnn-extent-lock*)
    (unless (fnn-extent-executor-observe-returned worker)
      (return-from fnn-extent-decoded-window-outcome :pending))
    ;; A job that signalled answers its condition, cancelled or not (the
    ;; owner settles it and stops: specs/storage.md PRF-1057).
    (let ((result (fnn-cold-worker-result worker)))
      (when (typep result 'condition)
        (return-from fnn-extent-decoded-window-outcome result)))
    (when (fnn-core-cold-single 'fn-pwx-boundp
              (fnn-core-cold-single 'fn-owner-page-read-ledger (fnn-live-page-read-pool))
              (fnn-cold-worker-row worker) token :cancelled-returned)
      (return-from fnn-extent-decoded-window-outcome :cancelled))
    (let ((result (fnn-cold-worker-result worker)))
      (unless (and (fnn-decoded-activation-p result)
                   (eq (fnn-decoded-activation-stage result) :idle))
        (fnn-fault "decoded result lacks a completed private activation"))
      (first (fnn-call 'fn-owner-page-decoded-job-outcome
               (fnn-cold-worker-row worker) token
               (fnn-decoded-activation-job result) (fnn-live-page-read-pool))))))

(defun fnn-extent-decoded-window-byte-at
    (worker token file eoff elen poff compressed trailer decoded dict-id i)
  "Core checks exact returned worker, complete codec identity and coordinates."
  (sb-thread:with-mutex (*fnn-extent-lock*)
    (unless (fnn-extent-executor-observe-returned worker)
      (return-from fnn-extent-decoded-window-byte-at (values :pending nil)))
    (let ((result (fnn-cold-worker-result worker)))
      (when (typep result 'condition) (error result))
      (unless (and (fnn-decoded-activation-p result)
                   (eq (fnn-decoded-activation-stage result) :idle))
        (fnn-fault "decoded borrow lacks a completed private activation"))
      (destructuring-bind (word byte)
          (fnn-call 'fn-owner-page-decoded-job-byte-at
            (fnn-cold-worker-row worker) token file eoff elen poff compressed
            trailer decoded dict-id i (fnn-decoded-activation-job result)
            (fnn-live-page-read-pool))
        (values word byte)))))
