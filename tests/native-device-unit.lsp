;;; Raw primitive control, run with sbcl --script. Uses a fresh 1 MiB image
;;; below this lane's build/; no live core or model is replaced by test code.
(defpackage "ACL2" (:use "COMMON-LISP"))
(in-package "ACL2")
(load "host/ffi.lisp")
(load "host/device.lisp")

(let* ((path (format nil "build/device-unit-~d-~d.img" (get-universal-time) (random 1000000 (make-random-state t))))
       (bytes (make-array 8192 :element-type '(unsigned-byte 8) :initial-element 0))
       (wake (sb-thread:make-semaphore))
       (release (sb-thread:make-semaphore))
       (entered (sb-thread:make-semaphore))
       (perform (symbol-function 'fn2-device-perform))
       (boundaries nil)
       (boundaries-lock (sb-thread:make-mutex :name "device unit boundaries"))
       (device nil))
  (dotimes (i 4096) (setf (aref bytes i) (mod (+ 7 (* 19 i)) 256)))
  (multiple-value-bind (fd size backend) (fn2-device-open path :create-size 1048576)
    (assert (= size 1048576))
    (assert (member backend '(:fullfsync :fdatasync)))
    (assert (handler-case (progn (fn2-device-open path :create-size 1048576) nil) (error () t)))
    (assert (handler-case (progn (fn2-device-open path) nil) (error () t)))
    (unwind-protect
         (progn
           ;; A blocked pwrite holds the Write/Fence thread and every later
           ;; Read. All submissions return before release; neither the fence
           ;; nor the read of the written range can pass that write.
           (setf (symbol-function 'fn2-device-perform)
                 (lambda (d j)
                   (when (= (fn2-device-job-slot j) 0)
                     (sb-thread:signal-semaphore entered)
                     (assert (sb-thread:wait-on-semaphore release :timeout 10)))
                   (funcall perform d j)))
           (setf device (fn2-device-start fd size backend 4 (lambda () (sb-thread:signal-semaphore wake))
                         (lambda (label job)
                           (sb-thread:with-mutex (boundaries-lock)
                             (push (cons label (fn2-device-job-slot job)) boundaries)))))
           (fn2-device-submit device (make-fn2-device-job :slot 0 :gen 1 :kind :write :bytes bytes
                                                        :address 0 :length 4096 :offset 16384))
           (assert (sb-thread:wait-on-semaphore entered :timeout 5))
           (assert (equal boundaries '(("device-syscall" . 0))))
           (fn2-device-submit device (make-fn2-device-job :slot 1 :gen 1 :kind :fence :bytes bytes :address 0))
           (fn2-device-submit device (make-fn2-device-job :slot 2 :gen 1 :kind :read :bytes bytes
                                                        :address 4096 :length 4096 :offset 16384))
           (sleep 0.05)
           (assert (null (fn2-device-take-completion device)))
           (assert (equal boundaries '(("device-syscall" . 0))))
           (sb-thread:signal-semaphore release)
           ;; The write returns first. The fence and the read both follow it,
           ;; in either order: a Read does not wait for a Fence.
           (let ((done (loop repeat 3
                             do (assert (sb-thread:wait-on-semaphore wake :timeout 10))
                             collect (let ((job (fn2-device-take-completion device)))
                                       (assert (zerop (fn2-device-job-errno job)))
                                       (cons (fn2-device-job-slot job) (fn2-device-job-result job))))))
             (assert (equal (car done) '(0 . 4096)))
             (assert (equal (sort (copy-list (cdr done)) #'< :key #'car) '((1 . 0) (2 . 4096)))))
           (assert (equalp (subseq bytes 0 4096) (subseq bytes 4096)))
           ;; The kernel's short read stays short, without a retry or padding.
           (fn2-device-submit device (make-fn2-device-job :slot 3 :gen 1 :kind :read :bytes bytes
                                                        :address 4096 :length 4096 :offset (- size 17)))
           (assert (sb-thread:wait-on-semaphore wake :timeout 10))
           (assert (= 17 (fn2-device-job-result (fn2-device-take-completion device))))
           ;; Each job crosses its syscall boundary pair exactly once, in order,
           ;; whichever worker performed it.
           (let ((seen (reverse boundaries)))
             (assert (= 8 (length seen)))
             (dotimes (slot 4)
               (assert (equal (loop for (label . s) in seen when (= s slot) collect label)
                              '("device-syscall" "device-syscall-return"))))))
      (setf (symbol-function 'fn2-device-perform) perform)
      (when device
        ;; Stop joins every worker before closing the fd.
        (fn2-device-stop device)
        (assert (notany #'sb-thread:thread-alive-p
                        (cons (fn2-device-thread device) (fn2-device-read-threads device)))))))
  (multiple-value-bind (fd size backend) (fn2-device-open path)
    (declare (ignore backend))
    (unwind-protect
         (progn
           (assert (= size 1048576))
           (fill bytes 0 :start 4096)
           (sb-sys:with-pinned-objects (bytes)
             (assert (= 4096 (%fn2-device-pread fd (sb-sys:sap+ (sb-sys:vector-sap bytes) 4096) 4096 16384))))
           (assert (equalp (subseq bytes 0 4096) (subseq bytes 4096))))
      (fn2-native-close fd)))
  (let* ((fd (fn2-device-open-fd path 0))
         (device (%make-fn2-device :fd fd))
         (job (make-fn2-device-job :kind :write :bytes bytes :address 0 :length 4096 :offset 16384)))
    (assert (not (minusp fd)))
    (unwind-protect
         (progn
           (fn2-device-perform device job)
           (assert (= -1 (fn2-device-job-result job)))
           (assert (= 9 (fn2-device-job-errno job))))
      (fn2-native-close fd)))
  (format t "DEVICE ordering stalled-worker short-read failed-write exclusive-create reopen PASS ~a~%" path))
