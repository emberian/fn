; Certified policy plus the actual adapter: unsupported FUA queues a failed
; completion without submitting I/O. Ordinary writes still enter the worker.
(in-package "ACL2")
(include-book "books/host-boundary" :uncertified-okp nil)
:q
(load "host/ffi.lisp")
(load "host/adapter.lisp")
(handler-case
 (progn
  (dolist (backend '(:fdatasync :fullfsync))
   (dolist (fua '(0 1))
    (let* ((device (%make-fn2-device :backend backend
                    :queue (make-array 1 :initial-element nil)))
           (op (make-fn2-nop :state +fn2-n-waiting+ :kind *fn2-action-write*
                            :gen 1 :len 4096 :fua fua))
           (host (make-fn2-nhost :storage device :ops (vector op)
                    :completions (make-array 1 :initial-element nil))))
     (fn2-n-storage-submit host 0)
     (if (zerop fua)
      (progn
       (assert (= 1 (fn2-device-pending device)))
       (assert (= 1 (fn2-nhost-storage-pending host)))
       (assert (zerop (fn2-nhost-pending host))))
      (progn
       (assert (zerop (fn2-device-pending device)))
       (assert (zerop (fn2-nhost-storage-pending host)))
       (assert (= 1 (fn2-nhost-pending host)))
       (assert (= *fn2-outcome-failed* (fn2-nop-outcome op)))
       (assert (zerop (fn2-nop-count op))))))))
  (format t "~%NATIVE DEVICE POLICY PASS: ordinary write queued; FUA refused before I/O on both backends~%")
  (sb-ext:exit :code 0))
 (error (condition)
  (format *error-output* "NATIVE DEVICE POLICY FAIL: ~a~%" condition)
  (sb-ext:exit :code 1)))
