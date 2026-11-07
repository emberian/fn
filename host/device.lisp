;;; File device primitives. One FIFO worker owns the fd; the executor owns
;;; all core calls. A loan remains outstanding until its physical completion.
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

(defstruct fn2-device-job
  slot gen kind bytes address length offset (result 0) (errno 0))
(defstruct (fn2-device (:constructor %make-fn2-device))
  fd size backend thread wake boundary
  (lock (sb-thread:make-mutex :name "fn2 device queue"))
  (available (sb-thread:make-waitqueue :name "fn2 device work"))
  queue done (head 0) (tail 0) (pending 0) (dhead 0) (dtail 0) (completed 0)
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

(defun fn2-device-worker (device)
  (unwind-protect
       (loop
         (let ((job
                 (sb-thread:with-mutex ((fn2-device-lock device))
                   (loop while (and (zerop (fn2-device-pending device))
                                    (not (fn2-device-stopping device)))
                         do (sb-thread:condition-wait (fn2-device-available device) (fn2-device-lock device)))
                   (when (fn2-device-stopping device) (return-from fn2-device-worker nil))
                   (let* ((q (fn2-device-queue device)) (i (fn2-device-head device)) (job (aref q i)))
                     (setf (aref q i) nil (fn2-device-head device) (mod (1+ i) (length q)))
                     (decf (fn2-device-pending device))
                     job))))
           (when (fn2-device-boundary device)
             (funcall (fn2-device-boundary device) "device-syscall"))
           (fn2-device-perform device job)
           (when (fn2-device-boundary device)
             (funcall (fn2-device-boundary device) "device-syscall-return"))
           (sb-thread:with-mutex ((fn2-device-lock device))
             (when (fn2-device-stopping device) (return-from fn2-device-worker nil))
             (let ((q (fn2-device-done device)))
               (assert (< (fn2-device-completed device) (length q)))
               (setf (aref q (fn2-device-dtail device)) job
                     (fn2-device-dtail device) (mod (1+ (fn2-device-dtail device)) (length q)))
               (incf (fn2-device-completed device)))
             (funcall (fn2-device-wake device)))))
    ;; Do not retry close after EINTR: the fd may already have been closed
    ;; and reused by the executor's next accept while this thread returns.
    (%fn2-native-close (fn2-device-fd device))))

(defun fn2-device-start (fd size backend capacity wake &optional boundary)
  (let ((device (%make-fn2-device :fd fd :size size :backend backend :wake wake :boundary boundary
                                :queue (make-array capacity :initial-element nil)
                                :done (make-array capacity :initial-element nil))))
    (setf (fn2-device-thread device)
          (sb-thread:make-thread (lambda () (fn2-device-worker device)) :name "fn2 storage"))
    device))

(defun fn2-device-submit (device job)
  (sb-thread:with-mutex ((fn2-device-lock device))
    (let ((q (fn2-device-queue device)))
      (assert (not (fn2-device-stopping device)))
      (assert (< (fn2-device-pending device) (length q)))
      (setf (aref q (fn2-device-tail device)) job
            (fn2-device-tail device) (mod (1+ (fn2-device-tail device)) (length q)))
      (incf (fn2-device-pending device))
      (sb-thread:condition-notify (fn2-device-available device)))))

(defun fn2-device-take-completion (device)
  (sb-thread:with-mutex ((fn2-device-lock device))
    (when (plusp (fn2-device-completed device))
      (let* ((q (fn2-device-done device)) (i (fn2-device-dhead device)) (job (aref q i)))
        (setf (aref q i) nil (fn2-device-dhead device) (mod (1+ i) (length q)))
        (decf (fn2-device-completed device))
        job))))

(defun fn2-device-stop (device)
  ;; Never close a descriptor under a stalled syscall or release its loan.
  ;; The worker owns both until return, then closes. No join blocks the
  ;; executor, and this mutex excludes a wake after the mux is destroyed.
  (sb-thread:with-mutex ((fn2-device-lock device))
    (setf (fn2-device-stopping device) t)
    (sb-thread:condition-notify (fn2-device-available device))))
