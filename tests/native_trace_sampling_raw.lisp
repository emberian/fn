;;; Run inside an existing warm native/ACL2 process. TRACE was loaded only if
;;; absent; candidate is compiled from the exact edited trace-begin form.
(in-package "ACL2")

(defun fnmg-trace-sampling-loop (n begin)
  ;; Lexical hook selects the actual shared macro's begin leaf. No globally
  ;; owned function is overwritten, including on conditions/nonlocal exits.
  (flet ((fnn-trace-begin (state phase cid operation connection-generation)
           (funcall begin state phase cid operation connection-generation)))
    (dotimes (i n)
      (fnn-trace-span (:sampling-probe :cid 7 :operation 123 :connection-generation 1)
        (values i :ok)))))

(let ((*fnn-trace-state* nil) (*fnn-trace-parent* nil) (*fnn-trace-operation* nil)
      (*fnn-trace-connection-generation* nil))
  ;; Exact accepted/rejected identity classes remain identical. No payloads.
  (dolist (id (list nil 0 1 (expt 2 80) -1 1/2 1.0 :invalid "invalid"))
    (dolist (position '(0 1 2))
      (let ((ids (list 7 123 1)) (outcomes nil))
        (setf (nth position ids) id)
        (dolist (begin (list #'fnn-trace-begin #'fnmg-trace-begin-no-list))
          (fnn-trace-start :capacity 1 :sample-every 100001)
          (push (handler-case (progn (apply begin *fnn-trace-state* :sampling-probe ids) :accepted)
                  (error () :rejected)) outcomes))
        (assert (eq (first outcomes) (second outcomes))))))
  (dolist (route '(:legacy :no-identity-list))
    (let ((begin (if (eq route :legacy) #'fnn-trace-begin #'fnmg-trace-begin-no-list)))
      (fnn-trace-start :capacity 1 :sample-every 100001)
      (fnmg-trace-sampling-loop 1000 begin)
      (fnn-trace-start :capacity 1 :sample-every 100001)
      (sb-ext:gc :full t)
      (let ((before (sb-ext:get-bytes-consed)) (started (fnn-trace-now)))
        (fnmg-trace-sampling-loop 100000 begin)
        (let ((allocated (- (sb-ext:get-bytes-consed) before))
              (duration (- (fnn-trace-now) started)))
          (assert (= (fnn-trace-state-attempts *fnn-trace-state*) 100000))
          (assert (= (fnn-trace-state-next *fnn-trace-state*) 1))
          (format t "~%FN_TRACE_SAMPLING {\"route\":\"~(~a~)\",\"attempts\":100000,\"recorded\":1,\"allocated_bytes\":~d,\"duration_us\":~d,\"scope\":\"isolated-process-inclusive-probe\"}~%"
                  route allocated duration)))))
  (format t "NATIVE_TRACE_SAMPLING_PASS~%"))
