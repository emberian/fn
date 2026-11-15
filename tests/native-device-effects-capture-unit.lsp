;;; Narrow SBCL recorder control. This substitutes perform, so it tests the
;;; recorder interface/concurrency only, not the operating system or disk.
(defpackage "ACL2" (:use "COMMON-LISP"))
(load "host/device.lisp")
(in-package "ACL2")
(setf (symbol-function 'fn2-device-submit) (lambda (device job) (declare (ignore device job)) :queued))
(setf (symbol-function 'fn2-device-perform)
 (lambda (device job)
   (declare (ignore device))
   ;; Acquiring this lock inside the original proves the wrapper did not
   ;; serialize the physical operation under its evidence mutex.
   (let ((lock (symbol-value '*fn2-device-evidence-lock*)))
     (assert (sb-thread:grab-mutex lock :waitp nil))
     (sb-thread:release-mutex lock))
   (setf (fn2-device-job-result job) 2 (fn2-device-job-errno job) 0)
   (values :original-return :second-value)))
(load "tests/native-device-effects-capture.lsp")
(let* ((device (%make-fn2-device :fd 17))
       (bytes (make-array 4 :element-type '(unsigned-byte 8) :initial-contents '(9 1 2 3)))
       (job (make-fn2-device-job :slot 4 :gen 7 :kind :write :bytes bytes :address 1 :length 3 :offset 100)))
 (assert (eq :queued (fn2-device-submit device job)))
 (assert (equal '(:original-return :second-value) (multiple-value-list (fn2-device-perform device job)))))
;; A mutation after submission must be rejected before performing the write.
(let* ((device (%make-fn2-device :fd 17))
       (bytes (make-array 1 :element-type '(unsigned-byte 8) :initial-element 5))
       (job (make-fn2-device-job :slot 4 :gen 8 :kind :write :bytes bytes :address 0 :length 1 :offset 200)))
 (fn2-device-submit device job)
 (setf (aref bytes 0) 6)
 (assert (handler-case (progn (fn2-device-perform device job) nil) (error () t))))
;; The unmatched submit must remain in the stream, never synthesized as zero.
(close *fn2-device-evidence-stream*)
(let ((records (with-open-file (in (sb-ext:posix-getenv "FN2_TEST_DEVICE_EFFECTS"))
                 (loop for row = (read in nil :eof) until (eq row :eof) collect row))))
 (assert (equal records
  '((:submit 1 (17 4 7 :write 100 3 (1 2 3)))
    (:begin 1) (:return 1 2 0 nil)
    (:submit 2 (17 4 8 :write 200 1 (5)))))))
(format t "DEVICE EFFECT RECORDER CONTROLS PASS~%")
