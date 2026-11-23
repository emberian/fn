;;; File device primitives. One writer thread performs Writes and Fences in
;;; submission order; a small pool performs Reads. The executor owns all core
;;; calls. A loan remains outstanding until its physical completion.
(in-package "ACL2")

(sb-alien:define-alien-routine ("pread" %fn2-device-pread) sb-alien:long
  (fd sb-alien:int) (buffer sb-sys:system-area-pointer)
  (count sb-alien:unsigned-long) (offset sb-alien:long-long))
(sb-alien:define-alien-routine ("pwrite" %fn2-device-pwrite) sb-alien:long
  (fd sb-alien:int) (buffer sb-sys:system-area-pointer)
  (count sb-alien:unsigned-long) (offset sb-alien:long-long))
(sb-alien:define-alien-routine ("ftruncate" %fn2-device-truncate) sb-alien:int
  (fd sb-alien:int) (size sb-alien:long-long))
(sb-alien:define-alien-routine ("lseek" %fn2-device-seek) sb-alien:long-long
  (fd sb-alien:int) (offset sb-alien:long-long) (whence sb-alien:int))
(sb-alien:define-alien-routine ("fsync" %fn2-device-fsync) sb-alien:int
  (fd sb-alien:int))
#+linux
(sb-alien:define-alien-routine ("fdatasync" %fn2-device-fdatasync) sb-alien:int
  (fd sb-alien:int))
#+linux
(sb-alien:define-alien-routine ("posix_fallocate" %fn2-device-fallocate) sb-alien:int
  (fd sb-alien:int) (offset sb-alien:long-long) (size sb-alien:long-long))
(sb-alien:define-alien-routine ("flock" %fn2-device-flock) sb-alien:int
  (fd sb-alien:int) (operation sb-alien:int))

(defun fn2-device-open-fd (path flags)
  ;; open's mode is variadic, including on Darwin arm64.
  (sb-alien:alien-funcall
   (sb-alien:extern-alien "open"
     (function sb-alien:int sb-alien:c-string sb-alien:int &optional sb-alien:unsigned-int))
   path flags #o600))

(defun fn2-device-fence (fd)
  ;; No fallback from a failed durability primitive to a weaker one.
  #+darwin (%fn2-native-fcntl fd 51 0)
  #+linux (%fn2-device-fdatasync fd))

(defun fn2-device-preallocate (fd size)
  #+darwin
  (sb-alien:with-alien ((request (sb-alien:struct fn2-fstore
                                (flags sb-alien:unsigned-int) (position sb-alien:int)
                                (offset sb-alien:long-long) (length sb-alien:long-long)
                                (allocated sb-alien:long-long))))
    (setf (sb-alien:slot request 'flags) 4
          (sb-alien:slot request 'position) 3
          (sb-alien:slot request 'offset) 0
          (sb-alien:slot request 'length) size
          (sb-alien:slot request 'allocated) 0)
    (fn2-native-required
     (%fn2-native-fcntl fd 42 (sb-sys:sap-int (sb-alien:alien-sap (sb-alien:addr request))))
     (fn2-native-errno) :preallocate))
  #+linux
  (let ((err (%fn2-device-fallocate fd 0 size)))
    (unless (zerop err) (error "fn2 device preallocate: errno ~d" err)))
  (fn2-native-required (%fn2-device-truncate fd size) (fn2-native-errno) :truncate))

(defun fn2-device-open (path &key create-size)
  "Return fd, observed byte size and backend. CREATE-SIZE uses O_EXCL:
an existing image is never truncated, including after an interrupted init."
  (let ((fd (fn2-native-required
             (fn2-device-open-fd path
               (logior 2 #+linux #x80000 #+darwin #x1000000
                       (if create-size #+linux #xc0 #+darwin #xa00 0)))
             (fn2-native-errno) :device-open))
        (ok nil))
    (unwind-protect
         (progn
           (fn2-native-required (%fn2-device-flock fd 6) (fn2-native-errno) :device-lock)
           (when create-size
             (fn2-device-preallocate fd create-size)
             (fn2-native-required (fn2-device-fence fd) (fn2-native-errno) :device-create-fence)
             ;; Qualify the new name as well as the file's allocation. Runtime
             ;; writes never rename or mutate the directory.
             (let ((dir (fn2-native-required
                         (fn2-device-open-fd
                          (namestring (make-pathname :name nil :type nil :defaults (truename path)))
                          #+linux #x80000 #+darwin #x1000000)
                         (fn2-native-errno) :device-parent)))
               (unwind-protect
                    (fn2-native-required (%fn2-device-fsync dir) (fn2-native-errno) :device-parent-fence)
                 (fn2-native-close dir))))
           (let ((size (fn2-native-required (%fn2-device-seek fd 0 2) (fn2-native-errno) :device-size)))
             (setf ok t)
             (values fd size #+darwin :fullfsync #+linux :fdatasync)))
      (unless ok (fn2-native-close fd)))))

;;; Every submitted job takes the next sequence number. A Read begins only
;;; after every earlier Write has returned from pwrite; a Write begins only
;;; after every earlier Read has returned from pread. Reads never overlap a
;;; pwrite, so each Read/Write pair takes effect in submission order. A Fence
;;; orders Writes only: it waits for the Writes before it and holds no Read.
(defstruct fn2-device-job
  slot gen kind bytes address length offset (result 0) (errno 0)
  ;; Set at submit: this job's sequence number and, for a Read, that of the
  ;; last Write submitted before it (-1: none).
  (seq -1) (after-write -1))

;;; A bounded FIFO; one entry per operation slot. Used under the device lock.
(defstruct (fn2-device-ring (:constructor fn2-device-ring
                                (capacity &aux (items (make-array capacity :initial-element nil)))))
  items (head 0) (count 0))
(defun fn2-device-ring-peek (ring)
  (and (plusp (fn2-device-ring-count ring))
       (aref (fn2-device-ring-items ring) (fn2-device-ring-head ring))))
(defun fn2-device-ring-pop (ring)
  (let* ((items (fn2-device-ring-items ring)) (i (fn2-device-ring-head ring)) (x (aref items i)))
    (setf (aref items i) nil (fn2-device-ring-head ring) (mod (1+ i) (length items)))
    (decf (fn2-device-ring-count ring))
    x))
(defun fn2-device-ring-push (ring x)
  (let ((items (fn2-device-ring-items ring)))
    (assert (< (fn2-device-ring-count ring) (length items)))
    (setf (aref items (mod (+ (fn2-device-ring-head ring) (fn2-device-ring-count ring)) (length items))) x)
    (incf (fn2-device-ring-count ring))))

(defstruct (fn2-device (:constructor %make-fn2-device))
  fd size backend thread (read-threads nil) wake boundary
  (lock (sb-thread:make-mutex :name "fn2 device queue"))
  (available (sb-thread:make-waitqueue :name "fn2 device work"))
  (readable (sb-thread:make-waitqueue :name "fn2 device read work"))
  queue reads done                      ; Writes+Fences, Reads, completions
  (next-seq 0) (write-submitted -1) (write-completed -1)
  (active-reads 0) (active-pwrite nil) (active-fence nil)
  (stopping nil))

(defun fn2-device-perform (device job)
  ;; Exactly one syscall. Short counts and EINTR are observations; the
  ;; worker neither retries nor completes the rest of a logical write.
  (let* ((bytes (fn2-device-job-bytes job))
         (n (sb-sys:with-pinned-objects (bytes)
              (let ((sap (sb-sys:sap+ (sb-sys:vector-sap bytes) (fn2-device-job-address job))))
                (ecase (fn2-device-job-kind job)
                  (:read (%fn2-device-pread (fn2-device-fd device) sap
                           (fn2-device-job-length job) (fn2-device-job-offset job)))
                  (:write (%fn2-device-pwrite (fn2-device-fd device) sap
                            (fn2-device-job-length job) (fn2-device-job-offset job)))
                  (:fence (fn2-device-fence (fn2-device-fd device))))))))
    (setf (fn2-device-job-result job) n
          (fn2-device-job-errno job) (if (minusp n) (fn2-native-errno) 0))))

;;; Hazard rules, called under the device lock.
(defun fn2-device-read-ready-p (device job)
  ;; Read after Write: no pwrite in progress, and every Write submitted
  ;; before JOB has returned. A Fence in progress does not hold a Read.
  (and (not (fn2-device-active-pwrite device))
       (>= (fn2-device-write-completed device) (fn2-device-job-after-write job))))
(defun fn2-device-write-ready-p (device job)
  ;; Write after Read: no Read submitted before JOB is queued or in pread.
  ;; A Read submitted after JOB cannot have begun while JOB waits, so any
  ;; active Read is an earlier one.
  (let ((oldest (fn2-device-ring-peek (fn2-device-reads device))))
    (and (zerop (fn2-device-active-reads device))
         (not (and oldest (< (fn2-device-job-seq oldest) (fn2-device-job-seq job)))))))

(defun fn2-device-take-read (device)
  (let ((job (fn2-device-ring-peek (fn2-device-reads device))))
    (when (and job (fn2-device-read-ready-p device job))
      (fn2-device-ring-pop (fn2-device-reads device))
      (incf (fn2-device-active-reads device))
      ;; Readiness is monotone along the queue; hand the next Read to a peer.
      (let ((next (fn2-device-ring-peek (fn2-device-reads device))))
        (when (and next (fn2-device-read-ready-p device next))
          (sb-thread:condition-notify (fn2-device-readable device))))
      job)))
(defun fn2-device-take-write (device)
  (let ((job (fn2-device-ring-peek (fn2-device-queue device))))
    (when (and job (or (eq (fn2-device-job-kind job) :fence)
                       (fn2-device-write-ready-p device job)))
      (fn2-device-ring-pop (fn2-device-queue device))
      (if (eq (fn2-device-job-kind job) :fence)
          (setf (fn2-device-active-fence device) t)
          (setf (fn2-device-active-pwrite device) t))
      job)))

(defun fn2-device-take (device reader)
  "The next job this worker may begin, or NIL once stopping."
  (let ((lock (fn2-device-lock device)))
    (sb-thread:with-mutex (lock)
      (loop
        (when (fn2-device-stopping device) (return nil))
        (let ((job (if reader (fn2-device-take-read device) (fn2-device-take-write device))))
          (when job (return job)))
        (sb-thread:condition-wait
         (if reader (fn2-device-readable device) (fn2-device-available device)) lock)))))

(defun fn2-device-finish (device job)
  "Release JOB's hazard and post its completion; NIL once stopping."
  (sb-thread:with-mutex ((fn2-device-lock device))
    (ecase (fn2-device-job-kind job)
      (:read (when (zerop (decf (fn2-device-active-reads device)))
               (sb-thread:condition-notify (fn2-device-available device))))
      (:write (setf (fn2-device-active-pwrite device) nil
                    (fn2-device-write-completed device) (fn2-device-job-seq job))
              (sb-thread:condition-broadcast (fn2-device-readable device)))
      (:fence (setf (fn2-device-active-fence device) nil)))
    (unless (fn2-device-stopping device)
      (fn2-device-ring-push (fn2-device-done device) job)
      (funcall (fn2-device-wake device))
      t)))

(defun fn2-device-worker (device reader)
  ;; READER: one of the Read pool; otherwise the one Write/Fence thread.
  ;; Every syscall crosses the same death-cut boundary pair.
  (loop
    (let ((job (fn2-device-take device reader)))
      (unless job (return nil))
      (when (fn2-device-boundary device)
        (funcall (fn2-device-boundary device) "device-syscall" job))
      (fn2-device-perform device job)
      (when (fn2-device-boundary device)
        (funcall (fn2-device-boundary device) "device-syscall-return" job))
      (unless (fn2-device-finish device job) (return nil)))))

(defun fn2-device-start (fd size backend capacity wake &optional boundary (read-workers 4))
  "Take ownership of FD: it is closed by FN2-DEVICE-STOP, or here on failure."
  (assert (and (integerp read-workers) (plusp read-workers)))
  (let ((device (%make-fn2-device :fd fd :size size :backend backend :wake wake :boundary boundary
                                :queue (fn2-device-ring capacity) :reads (fn2-device-ring capacity)
                                :done (fn2-device-ring capacity)))
        (ok nil))
    (unwind-protect
         (progn
           (setf (fn2-device-thread device)
                 (sb-thread:make-thread (lambda () (fn2-device-worker device nil)) :name "fn2 storage"))
           (loop repeat read-workers
                 do (push (sb-thread:make-thread (lambda () (fn2-device-worker device t))
                                                 :name "fn2 storage read")
                          (fn2-device-read-threads device)))
           (setf ok t)
           device)
      (unless ok (fn2-device-stop device)))))

(defun fn2-device-submit (device job)
  (sb-thread:with-mutex ((fn2-device-lock device))
    (assert (not (fn2-device-stopping device)))
    (let ((seq (fn2-device-next-seq device)))
      (setf (fn2-device-job-seq job) seq)
      (ecase (fn2-device-job-kind job)
        (:read
         (setf (fn2-device-job-after-write job) (fn2-device-write-submitted device))
         (fn2-device-ring-push (fn2-device-reads device) job)
         (sb-thread:condition-notify (fn2-device-readable device)))
        ((:write :fence)
         (fn2-device-ring-push (fn2-device-queue device) job)
         (when (eq (fn2-device-job-kind job) :write)
           (setf (fn2-device-write-submitted device) seq))
         (sb-thread:condition-notify (fn2-device-available device))))
      (setf (fn2-device-next-seq device) (1+ seq)))))

(defun fn2-device-take-completion (device)
  (sb-thread:with-mutex ((fn2-device-lock device))
    (when (fn2-device-ring-peek (fn2-device-done device))
      (fn2-device-ring-pop (fn2-device-done device)))))

(defun fn2-device-stop (device)
  ;; Each worker finishes the syscall in hand, posts nothing more, and exits;
  ;; this waits for all of them, including a stalled one. The fd is closed
  ;; once, after the last has returned, so no pread, pwrite or Fence can act
  ;; on a closed or reused descriptor, and no wake follows the mux's teardown.
  (let ((threads (sb-thread:with-mutex ((fn2-device-lock device))
                   (unless (fn2-device-stopping device)
                     (setf (fn2-device-stopping device) t)
                     (sb-thread:condition-broadcast (fn2-device-available device))
                     (sb-thread:condition-broadcast (fn2-device-readable device))
                     (cons (fn2-device-thread device) (fn2-device-read-threads device))))))
    (when threads
      (dolist (thread threads)
        (when thread (sb-thread:join-thread thread :default nil)))
      ;; Not retried after EINTR: the descriptor may already be released.
      (%fn2-native-close (fn2-device-fd device)))))
