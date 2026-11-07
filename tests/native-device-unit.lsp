;;; Raw primitive control, run with sbcl --script. Uses a fresh 1 MiB image
;;; below this lane's build/; no live core or model is replaced by test code.
(defpackage "ACL2" (:use "COMMON-LISP"))
(in-package "ACL2")
(load "host/ffi.lisp")
(load "host/device.lisp")

(let* ((path (format nil "build/device-unit-~d-~d.img" (get-universal-time) (random 1000000)))
       (bytes (make-array 8192 :element-type '(unsigned-byte 8) :initial-element 0))
       (wake (sb-thread:make-semaphore))
       (release (sb-thread:make-semaphore))
       (entered (sb-thread:make-semaphore))
       (perform (symbol-function 'fn2-device-perform))
       (boundaries nil)
       (device nil))
  (dotimes (i 4096) (setf (aref bytes i) (mod (+ 7 (* 19 i)) 256)))
  (multiple-value-bind (fd size backend) (fn2-device-open path :create-size 1048576)
    (assert (= size 1048576))
    (assert (member backend '(:fullfsync :fdatasync)))
    (assert (handler-case (progn (fn2-device-open path :create-size 1048576) nil) (error () t)))
    (assert (handler-case (progn (fn2-device-open path) nil) (error () t)))
    (unwind-protect
         (progn
           ;; A blocked syscall holds only the storage worker. All submissions
           ;; return before release, and the fence cannot pass that write.
           (setf (symbol-function 'fn2-device-perform)
                 (lambda (d j)
                   (when (= (fn2-device-job-slot j) 0)
                     (sb-thread:signal-semaphore entered)
                     (assert (sb-thread:wait-on-semaphore release :timeout 10)))
                   (funcall perform d j)))
           (setf device (fn2-device-start fd size backend 4 (lambda () (sb-thread:signal-semaphore wake))
                         (lambda (label) (push label boundaries))))
           (fn2-device-submit device (make-fn2-device-job :slot 0 :gen 1 :kind :write :bytes bytes
                                                        :address 0 :length 4096 :offset 16384))
           (assert (sb-thread:wait-on-semaphore entered :timeout 5))
           (assert (equal boundaries '("device-syscall")))
           (fn2-device-submit device (make-fn2-device-job :slot 1 :gen 1 :kind :fence :bytes bytes :address 0))
           (fn2-device-submit device (make-fn2-device-job :slot 2 :gen 1 :kind :read :bytes bytes
                                                        :address 4096 :length 4096 :offset 16384))
           (assert (null (fn2-device-take-completion device)))
           (sb-thread:signal-semaphore release)
           (loop for slot below 3 for count in '(4096 0 4096) do
             (assert (sb-thread:wait-on-semaphore wake :timeout 10))
             (let ((job (fn2-device-take-completion device)))
               (assert (= slot (fn2-device-job-slot job)))
               (assert (= count (fn2-device-job-result job)))
               (assert (zerop (fn2-device-job-errno job)))))
           (assert (equalp (subseq bytes 0 4096) (subseq bytes 4096)))
           ;; The kernel's short read stays short, without a retry or padding.
           (fn2-device-submit device (make-fn2-device-job :slot 3 :gen 1 :kind :read :bytes bytes
                                                        :address 4096 :length 4096 :offset (- size 17)))
           (assert (sb-thread:wait-on-semaphore wake :timeout 10))
           (assert (= 17 (fn2-device-job-result (fn2-device-take-completion device))))
           (assert (equal (reverse boundaries)
                          (loop repeat 4 append '("device-syscall" "device-syscall-return")))))
      (setf (symbol-function 'fn2-device-perform) perform)
      (when device
        (fn2-device-stop device)
        (sb-thread:join-thread (fn2-device-thread device) :timeout 10))))
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
  (format t "DEVICE FIFO stalled-worker short-read failed-write exclusive-create reopen PASS ~a~%" path))
