;;; Deterministic fault device for the real fn2-device-perform boundary.
;;; The oracle has separate visible and persisted byte arrays. It replaces
;;; syscalls, not the device worker/normalizer's decisions. No file is opened.
;;; A fixture-sized image is not a production storage limit.
(in-package "ACL2")

(defun fn2-device-fault-controls (&optional observer)
  (let* ((visible (make-array 32 :element-type '(unsigned-byte 8) :initial-element 0))
         (persisted (copy-seq visible))
         (bytes (make-array 4 :element-type '(unsigned-byte 8) :initial-element 0))
         (device (%make-fn2-device :fd -1))
         (plan nil) (calls 0) (error-number 0) (serial 0) (delivered 0)
         (original-write (symbol-function '%fn2-device-pwrite))
         (original-fence (symbol-function 'fn2-device-fence))
         (original-errno (symbol-function 'fn2-native-errno))
         (original-perform (symbol-function 'fn2-device-perform))
         (mutant (sb-ext:posix-getenv "FN2_DEVICE_FAULT_MUTANT")))
    (labels ((expected (base offset values)
               (let ((answer (copy-seq base)))
                 (replace answer values :start1 offset) answer))
             (step-io (kind offset payload effect return-value errno outcome reason count &optional withheld)
               (replace bytes payload)
               (setf plan (list effect return-value errno))
               (let* ((before calls)
                      (job (make-fn2-device-job :slot 0 :gen (incf serial) :kind kind
                             :bytes bytes :address 0 :length (if (eq kind :write) (length payload) 0)
                             :offset offset)))
                 (when observer (funcall observer :prepare job outcome reason count))
                 (fn2-device-perform device job)
                 (assert (= calls (1+ before)) () "A logical operation retried its syscall")
                 (assert (= (fn2-device-job-result job) return-value) () "Device result was not preserved")
                 (assert (= (fn2-device-job-errno job) (if (minusp return-value) errno 0)) () "Device errno was not preserved")
                 (if withheld
                     (when observer (funcall observer :withheld job outcome reason count))
                   (progn (incf delivered)
                          (when observer (funcall observer :deliver job outcome reason count))))
                 job)))
      (unwind-protect
           (progn
             (setf (symbol-function '%fn2-device-pwrite)
                   (lambda (fd sap length offset)
                     (declare (ignore fd))
                     (incf calls)
                     (destructuring-bind (effect result errno) plan
                       (assert (<= 0 effect length))
                       (dotimes (i effect)
                         (setf (aref visible (+ offset i)) (sb-sys:sap-ref-8 sap i)))
                       (setf error-number errno)
                       result)))
             (setf (symbol-function 'fn2-device-fence)
                   (lambda (fd)
                     (declare (ignore fd))
                     (incf calls)
                     (destructuring-bind (effect result errno) plan
                       ;; Even a failed fence may have persisted some/all bytes.
                       (replace persisted visible :end1 effect :end2 effect)
                       (setf error-number errno)
                       result)))
             (setf (symbol-function 'fn2-native-errno) (lambda () error-number))
             (when mutant
               (setf (symbol-function 'fn2-device-perform)
                     (lambda (d job)
                       (let ((before (copy-seq visible)))
                         (funcall original-perform d job)
                         (when (minusp (fn2-device-job-result job))
                           (cond ((string= mutant "retry") (funcall original-perform d job))
                                 ((string= mutant "rollback") (replace visible before))
                                 ((string= mutant "errno") (setf (fn2-device-job-errno job) 0))
                                 (t (error "Unknown fault mutant ~s" mutant))))))))
             ;; This earlier range was fully written and fenced. It is the
             ;; independent preservation control, not a claimed protocol ACK.
             (step-io :write 4 #(11 12 13 14) 4 4 0 :done :none 4)
             (assert (equalp persisted (make-array 32 :initial-element 0)))
             (step-io :fence 0 #() 32 0 0 :done :none 0)
             (let ((baseline (copy-seq persisted)))
               (assert (equalp baseline (expected (make-array 32 :initial-element 0) 4 #(11 12 13 14))))
               ;; Identical reported failure/count, but both zero and nonzero
               ;; effects are possible. An error cannot certify rollback.
               (dolist (errno '(5 28))
                 (dolist (effect '(0 2 4))
                   (replace visible baseline)
                   (replace persisted baseline)
                   (step-io :write 16 #(21 22 23 24) effect -1 errno
                            :failed (if (= errno 28) :no-space :io) 0)
                   (assert (equalp visible (expected baseline 16 (subseq #(21 22 23 24) 0 effect))) () "Unreported write prefix changed")
                   (assert (equalp persisted baseline))))
               ;; A short successful pwrite is a known prefix, not a full
               ;; accepted write. The actual ACL2 normalizer owes :uncertain.
               (replace visible baseline)
               (step-io :write 16 #(21 22 23 24) 2 2 0 :failed :uncertain 2)
               (assert (equalp visible (expected baseline 16 #(21 22))))
               (assert (equalp persisted baseline))
               ;; Failed fence with partial persistence. Power loss discards
               ;; only volatile bytes; the error does not restore baseline.
               (replace visible baseline)
               (step-io :write 16 #(21 22 23 24) 4 4 0 :done :none 4)
               (step-io :fence 0 #() 18 -1 5 :failed :io 0)
               (assert (equalp persisted (expected baseline 16 #(21 22))))
               (replace visible persisted)
               (assert (not (equalp visible baseline)))
               (assert (equalp (subseq visible 4 8) #(11 12 13 14)))
               ;; Physical success without terminal delivery: durable bytes
               ;; exist, while the adapter has no completion to acknowledge.
               (replace visible baseline)
               (replace persisted baseline)
               (step-io :write 16 #(21 22 23 24) 4 4 0 :done :none 4)
               (let ((before delivered))
                 (step-io :fence 0 #() 32 0 0 :done :none 0 t)
                 (assert (= delivered before))
                 (assert (equalp persisted (expected baseline 16 #(21 22 23 24))))
                 (replace visible persisted)
                 (assert (equalp (subseq visible 4 8) #(11 12 13 14)))))
             (format t "DEVICE FAULT CONTROLS PASS: unreported effects, short write, failed fence, lost completion~%"))
        (setf (symbol-function '%fn2-device-pwrite) original-write
              (symbol-function 'fn2-device-fence) original-fence
              (symbol-function 'fn2-native-errno) original-errno
              (symbol-function 'fn2-device-perform) original-perform)))))
