;;; Private catchup spool I/O executor. ACL2 selects offsets/counts and owns
;;; framing/hash/cursor decisions. One fixed request cell, one completion cell.
;;; This constructor is called only after the independent peer flight draw.
(in-package "ACL2")

(defstruct (fnn-csp-worker (:constructor %make-fnn-csp-worker))
  lease path fd created lock changed thread
  input digest replay digest-input replay-input
  (phase :idle) operation offset count status actual condition
  stopping returned joined cleanup-condition)

(defun fnn-csp-worker-perform (worker operation offset count)
  ;; The worker alone touches the spool descriptor's position. No closure
  ;; captures an article, line list, record index, owner or live Store stobj.
  (case operation
    (:open
     (let ((fd (fnn-open (fnn-csp-worker-path worker)
                         (logior sb-posix:o-rdwr sb-posix:o-creat sb-posix:o-excl
                                 +fnn-o-nofollow+) #o600)))
       (setf (fnn-csp-worker-fd worker) fd
             (fnn-csp-worker-created worker) t)
       (unless (fnn-regular-p (fnn-fstat fd))
         (fnn-fault "catchup spool is not a regular file"))
       ;; Private temporary data is not acceptance authority. Unlink while
       ;; retaining its descriptor; crashes cannot leave a growing namespace.
       (fnn-unlink (fnn-csp-worker-path worker))
       (setf (fnn-csp-worker-path worker) nil)
       (values :ok 0)))
    (:write
     (fnn-posix () (sb-posix:lseek (fnn-csp-worker-fd worker) offset sb-posix:seek-set))
     (fnn-write-range (fnn-csp-worker-fd worker) (fnn-csp-worker-input worker) 0 count)
     (values :ok count))
    ((:digest :replay)
     (let* ((input (if (eq operation :digest) (fnn-csp-worker-digest-input worker)
                     (fnn-csp-worker-replay-input worker)))
            (status (fnn-extent-window-pread (fnn-csp-worker-fd worker) input offset count)))
       (values status (svref input 1))))
    (t (fnn-fault "unknown catchup spool operation"))))

(defun fnn-csp-worker-loop (worker)
  (unwind-protect
       (loop
         (let ((operation nil) (offset nil) (count nil))
           (sb-thread:with-mutex ((fnn-csp-worker-lock worker))
             (loop until (or (fnn-csp-worker-stopping worker)
                             (eq (fnn-csp-worker-phase worker) :queued))
                   do (sb-thread:condition-wait (fnn-csp-worker-changed worker)
                                                (fnn-csp-worker-lock worker)))
             (when (fnn-csp-worker-stopping worker) (return))
             (setq operation (fnn-csp-worker-operation worker)
                   offset (fnn-csp-worker-offset worker)
                   count (fnn-csp-worker-count worker))
             (setf (fnn-csp-worker-phase worker) :running))
           (let ((status nil) (actual nil) (condition nil))
             (handler-case
                 (multiple-value-setq (status actual)
                   (fnn-csp-worker-perform worker operation offset count))
               (serious-condition (failure) (setq condition failure status :error actual 0)))
             ;; The physical syscall activation has returned/unwound. Its
             ;; borrowed buffer remains in custody until the owner takes it.
             (sb-thread:with-mutex ((fnn-csp-worker-lock worker))
               (setf (fnn-csp-worker-status worker) status
                     (fnn-csp-worker-actual worker) actual
                     (fnn-csp-worker-condition worker) condition
                     (fnn-csp-worker-phase worker) :complete)
               (sb-thread:condition-broadcast (fnn-csp-worker-changed worker))))))
    (let ((failure nil))
      (flet ((cleanup (thunk)
               (handler-case (funcall thunk)
                 (serious-condition (condition) (unless failure (setq failure condition))))))
        (when (fnn-csp-worker-fd worker)
          ;; Retire the descriptor number before close; never retry a possibly
          ;; released/reused number after a reported close error.
          (let ((fd (fnn-csp-worker-fd worker)))
            (setf (fnn-csp-worker-fd worker) nil)
            (cleanup (lambda () (fnn-close fd)))))
        (when (and (fnn-csp-worker-created worker) (fnn-csp-worker-path worker))
          (cleanup (lambda () (fnn-unlink (fnn-csp-worker-path worker))))))
      (sb-thread:with-mutex ((fnn-csp-worker-lock worker))
        (setf (fnn-csp-worker-cleanup-condition worker) failure
              (fnn-csp-worker-returned worker) t)
        (sb-thread:condition-broadcast (fnn-csp-worker-changed worker))))))

(defun fnn-csp-worker-start (path lease &optional retain)
  ;; No reusable credit is minted here. The caller retains the exact ledger
  ;; slot/generation through buffer borrowing, local acceptance and cleanup.
  (unless lease (fnn-fault "catchup worker has no independently issued lease"))
  (unless retain (fnn-fault "catchup worker has no physical custody callback"))
  (let* ((input (fnn-make-octets 512))
         (digest-input (fn-octets$c-reserve 64 (create-fn-octets$c)))
         (replay-input (fn-octets$c-reserve 512 (create-fn-octets$c)))
         (digest (svref digest-input 0)) (replay (svref replay-input 0))
         (worker (%make-fnn-csp-worker
                  :lease lease :path path :input input :digest digest :replay replay
                  :digest-input digest-input :replay-input replay-input
                  :lock (sb-thread:make-mutex :name "fn catchup spool")
                  :changed (sb-thread:make-waitqueue :name "fn catchup spool"))))
    ;; Publish physical custody before thread creation can escape.
    (funcall retain worker)
    (setf (fnn-csp-worker-thread worker)
          (sb-thread:make-thread (lambda () (fnn-csp-worker-loop worker))
                                 :name "fn catchup spool"))
    worker))

(defun fnn-csp-worker-submit (worker operation offset count)
  ;; Values came from ACL2. Representation assertions protect native memory,
  ;; not protocol/profile admission. A live borrowed window cannot be reused.
  (unless (and (integerp offset) (<= 0 offset) (integerp count) (<= 0 count)
               (< (+ offset count) (expt 2 63))
               (<= count (case operation (:digest 64) ((:write :replay) 512) (:open 0) (t -1))))
    (fnn-fault "catchup spool operation exceeds its fixed native window"))
  (sb-thread:with-mutex ((fnn-csp-worker-lock worker))
    (unless (and (not (fnn-csp-worker-stopping worker))
                 (eq (fnn-csp-worker-phase worker) :idle))
      (fnn-fault "catchup spool request cell is occupied or stopped"))
    (setf (fnn-csp-worker-operation worker) operation
          (fnn-csp-worker-offset worker) offset (fnn-csp-worker-count worker) count
          (fnn-csp-worker-phase worker) :queued)
    (sb-thread:condition-notify (fnn-csp-worker-changed worker)))
  nil)

(defun fnn-csp-worker-take (worker)
  ;; Result arrays are borrowed in place. Take before submitting another job.
  (sb-thread:with-mutex ((fnn-csp-worker-lock worker))
    (when (eq (fnn-csp-worker-phase worker) :complete)
      (setf (fnn-csp-worker-phase worker) :idle)
      (values t (fnn-csp-worker-status worker) (fnn-csp-worker-actual worker)
              (fnn-csp-worker-condition worker)))))

(defun fnn-csp-worker-stop (worker)
  ;; Cancellation revokes new jobs, never physical custody of a running one.
  (sb-thread:with-mutex ((fnn-csp-worker-lock worker))
    (setf (fnn-csp-worker-stopping worker) t)
    (sb-thread:condition-notify (fnn-csp-worker-changed worker)))
  nil)

(defun fnn-csp-worker-join-now (worker)
  ;; Fair driver never waits for blocking I/O. Only join after the actual
  ;; thread is dead; a reported cleanup failure keeps its grant unsettled.
  (unless (and (fnn-csp-worker-thread worker)
               (sb-thread:thread-alive-p (fnn-csp-worker-thread worker)))
    (unless (fnn-csp-worker-joined worker)
      (when (fnn-csp-worker-thread worker)
        (sb-thread:join-thread (fnn-csp-worker-thread worker)))
      (setf (fnn-csp-worker-joined worker) t))
    (values t (fnn-csp-worker-cleanup-condition worker))))

(defstruct (fnn-peer-flight-bank (:constructor %make-fnn-peer-flight-bank))
  policy ledger lock leases (index 0) stack runtime (phase :retained))

(defstruct (fnn-peer-flight-lease (:constructor %make-fnn-peer-flight-lease))
  bank index slot generation work-slot worker hash
  (physical nil) (semantic nil) (socket nil) (settled nil) fault)

(defun fnn-peer-flight-bank-install (dynamic protected policy stack runtime &optional retain)
  "Install only the captured independent hold, before any flight constructor."
  (unless policy (return-from fnn-peer-flight-bank-install nil))
  (let ((grant (fnn-core 'fn-pfr-startup-grant dynamic protected policy)))
    (unless (eq (first grant) :hold) (fnn-fault "peer flight startup refused ~s" grant)))
  (unless retain (fnn-fault "peer flight bank has no startup custody callback"))
  (let ((bank (%make-fnn-peer-flight-bank
               :policy policy :stack stack :runtime runtime
               :lock (sb-thread:make-mutex :name "fn peer flight bank"))))
    ;; The service now owns even a torn native allocation/install before the
    ;; first mutating call; an exception never loses the authoritative object.
    (funcall retain bank)
    (handler-case
        (progn
          ;; A raw throw can escape the constructor without a condition.
          ;; Publish calling custody first; a missing return cannot be idle.
          (setf (fnn-peer-flight-bank-phase bank) :creating)
          (setf (fnn-peer-flight-bank-ledger bank) (fnn-core 'create-fn-resource-ledger)
                (fnn-peer-flight-bank-phase bank) :installing)
          (destructuring-bind (word returned)
              (fnn-call 'fn-pfr-install-funded dynamic protected policy stack runtime
                        (fnn-peer-flight-bank-ledger bank))
            (setf (fnn-peer-flight-bank-ledger bank) returned)
            (unless (eq word :installed) (fnn-fault "peer flight bank install refused ~s" word))
            (setf (fnn-peer-flight-bank-phase bank) :installed))
          bank)
      (serious-condition (condition)
        (setf (fnn-peer-flight-bank-phase bank) :uncertain)
        (error condition)))))

(defun fnn-peer-flight-bank-drained (bank)
  (or (null bank)
      (sb-thread:with-mutex ((fnn-peer-flight-bank-lock bank))
        (and (member (fnn-peer-flight-bank-phase bank) '(:retained :installed :closed))
             (null (fnn-peer-flight-bank-leases bank))
             (or (null (fnn-peer-flight-bank-ledger bank))
                 (fnn-core 'fn-csp-bank-idle-p (fnn-peer-flight-bank-ledger bank)))))))

(defun fnn-peer-flight-bank-close (bank)
  (when bank
    (unless (fnn-peer-flight-bank-drained bank)
      (fnn-fault "peer flight bank still holds worker/socket/semantic custody"))
    (setf (fnn-peer-flight-bank-phase bank) :closed))
  nil)

(defun fnn-peer-flight-draw (bank)
  (when bank
    (sb-thread:with-mutex ((fnn-peer-flight-bank-lock bank))
      (unless (eq (fnn-peer-flight-bank-phase bank) :installed)
        (fnn-fault "peer flight bank is not installed"))
      (let* ((policy (fnn-peer-flight-bank-policy bank))
             (candidate (fnn-core 'fn-csp-candidate (fnn-peer-flight-bank-index bank) policy))
             (demand (fnn-core 'fn-pfr-flight-demand policy (fnn-peer-flight-bank-stack bank)
                               (fnn-peer-flight-bank-runtime bank))))
        (unless (and candidate demand) (fnn-fault "peer flight bank policy has no representable demand"))
        (setf (fnn-peer-flight-bank-index bank) (second candidate))
        (destructuring-bind (word generation returned)
            (fnn-call 'fn-rl-draw (third candidate) demand (fnn-peer-flight-bank-ledger bank))
          (setf (fnn-peer-flight-bank-ledger bank) returned)
          (when (eq word :drawn)
            (let ((lease (%make-fnn-peer-flight-lease
                          :bank bank :index (first candidate)
                          :slot (third candidate) :generation generation
                          :work-slot (fourth candidate))))
              ;; Retain the exact holder before any downstream constructor.
              (push lease (fnn-peer-flight-bank-leases bank))
              lease)))))))

(defun fnn-peer-flight-work (lease units)
  (let ((bank (fnn-peer-flight-lease-bank lease)))
    (sb-thread:with-mutex ((fnn-peer-flight-bank-lock bank))
      (let ((demand (fnn-core 'fn-pfr-work-demand units)))
        (unless demand (fnn-fault "peer flight work is unrepresentable"))
        (destructuring-bind (word generation returned)
            (fnn-call 'fn-rl-draw (fnn-peer-flight-lease-work-slot lease) demand
                      (fnn-peer-flight-bank-ledger bank))
          (setf (fnn-peer-flight-bank-ledger bank) returned)
          (unless (eq word :drawn) (return-from fnn-peer-flight-work nil))
          (destructuring-bind (settled returned)
              (fnn-call 'fn-rl-settle (fnn-peer-flight-lease-work-slot lease) generation
                        (fnn-peer-flight-bank-ledger bank))
            (setf (fnn-peer-flight-bank-ledger bank) returned)
            (unless (eq settled :settled) (fnn-fault "peer flight work settlement refused ~s" settled)))
          t)))))

(defun fnn-peer-flight-settle (lease)
  (unless (fnn-peer-flight-lease-settled lease)
    (unless (and (fnn-peer-flight-lease-physical lease)
                 (fnn-peer-flight-lease-semantic lease)
                 (fnn-peer-flight-lease-socket lease)
                 (not (fnn-peer-flight-lease-fault lease)))
      (fnn-fault "peer flight settlement precedes actual terminal custody"))
    (let ((bank (fnn-peer-flight-lease-bank lease)))
      (sb-thread:with-mutex ((fnn-peer-flight-bank-lock bank))
        (destructuring-bind (word returned)
            (fnn-call 'fn-rl-settle (fnn-peer-flight-lease-slot lease)
                      (fnn-peer-flight-lease-generation lease) (fnn-peer-flight-bank-ledger bank))
          (setf (fnn-peer-flight-bank-ledger bank) returned)
          (unless (eq word :settled) (fnn-fault "peer flight settlement refused ~s" word))
          (setf (fnn-peer-flight-lease-settled lease) t
                (fnn-peer-flight-lease-worker lease) nil
                (fnn-peer-flight-lease-hash lease) nil
                (fnn-peer-flight-bank-leases bank)
                (delete lease (fnn-peer-flight-bank-leases bank) :test #'eq))))))
  nil)
