;;; Actual shared trace macro and owner section source, plain SBCL fixture.
(load "tests/native_section_envelope_raw.lisp")
(in-package "ACL2")

;;; ---- derived stubs: BEGIN (python3 tools/harness_check.py --write-stubs; do not edit) ----
(define-condition harness-stub-reached (serious-condition)
  ((name :initarg :name :reader harness-stub-reached-name)
   (source :initarg :source :reader harness-stub-reached-source))
  (:report (lambda (c s)
             (format s "harness: host function ~(~a~) (~a) was reached; this harness neither stubs nor extracts it"
                     (harness-stub-reached-name c) (harness-stub-reached-source c)))))
(defun harness-stub-reached (name source)
  (format *error-output* "harness: host function ~(~a~) (~a) was reached; this harness neither stubs nor extracts it~%"
          name source)
  (finish-output *error-output*)
  (error 'harness-stub-reached :name name :source source))
(defun fnn-owner-output-issue (service identity &optional capture)
  (declare (ignorable service identity capture))
  (harness-stub-reached 'fnn-owner-output-issue "host/native/owner.lisp"))
;;; ---- derived stubs: END ----

(load-deployed-forms "host/native/owner.lisp"
 '((defvar *fnn-owner-measure-table*) (defun fnn-owner-measure-now)
   (defun fnn-owner-measure-note) (defun fnn-owner-measure-report)))

(defun trace-disabled-loop (n)
  (dotimes (i n) (fnn-trace-span ((error "disabled phase evaluated") :cid (error "disabled CID evaluated"))
                  (values i :ok))))
(defun trace-plain-loop (n) (dotimes (i n) (values i :ok)))
(let ((*fnn-trace-state* nil))
  (assert (equal (multiple-value-list (fnn-trace-span (:disabled) (values 1 2 3))) '(1 2 3)))
  (trace-disabled-loop 10)
  (trace-plain-loop 10)
  (sb-ext:gc :full t)
  (let* ((before (sb-ext:get-bytes-consed))
         (ignored (trace-plain-loop 100000))
         (plain (- (sb-ext:get-bytes-consed) before))
         (before (sb-ext:get-bytes-consed))
         (ignored2 (trace-disabled-loop 100000))
         (disabled (- (sb-ext:get-bytes-consed) before)))
    (declare (ignore ignored ignored2))
    (format t "TRACE_DISABLED plain=~d disabled=~d scope=isolated-process granularity=allocation-region~%" plain disabled)))

(fnn-trace-start :capacity 16 :allocation :isolated-process)
(assert (equal (multiple-value-list
                (fnn-trace-span (:outer :cid 9 :operation 71 :connection-generation 4)
                  (fnn-trace-span (:inner) (values 7 8 9)))) '(7 8 9)))
(assert (eq (catch 'leave (fnn-trace-span (:throw) (throw 'leave :escaped))) :escaped))
(let ((original (make-condition 'simple-error :format-control "SECRET MUST NOT LOG")))
  (assert (eq (handler-case (fnn-trace-span (:error) (error original))
                (serious-condition (e) e)) original)))
(let ((*fnn-owner-measure* t))
  (assert (equal (multiple-value-list (fnn-owner-measured (:actual-owner 9) (values :owner :ok)))
                 '(:owner :ok))))
;; Real mux render caller over a recorded owner leaf: all six results and
;; exact ACL2 response generations remain available through the trace hook.
(load-deployed-forms "host/native/owner.lisp" '((defvar *fnn-output-grant*)))
(load-deployed-forms "host/native/mux.lisp"
 '((defstruct (fnn-mux-loop (:constructor %make-fnn-mux-loop)))
   (defstruct (fnn-mux-conn (:constructor %make-fnn-mux-conn)))
   (defun fnn-mux-service) (defun fnn-mux-render-next)))
(defun fnn-owner-render-next-quantum (service cid plan class compressed &optional borrowp)
  (assert (and (eq service :service) (= cid 9) (eq plan :plan)
               (eq class :read) (null compressed) borrowp))
  (values :octets :rest :done :yield :cold 2))
(let ((loop (%make-fnn-mux-loop :service :service))
      (conn (%make-fnn-mux-conn :cid 9 :class :read :output-grant :held
                              :response-identity '(:response 9 4 88))))
  (assert (equal (multiple-value-list (fnn-mux-render-next loop conn :plan))
                 '(:octets :rest :done :yield :cold 2))))
(fnn-trace-report *standard-output*)
(assert (eq (fnn-trace-row-outcome (aref (fnn-trace-state-rows *fnn-trace-state*) 2)) :nonlocal-exit))

;; Observer cleanup failure cannot replace a primary condition/nonlocal exit.
(let ((original (symbol-function 'fnn-trace-finish)))
  (unwind-protect
       (progn
         (setf (symbol-function 'fnn-trace-finish)
               (lambda (&rest args) (declare (ignore args)) (error "diagnostic failure")))
         (assert (eq (catch 'leave (fnn-trace-span (:cleanup-fault) (throw 'leave :primary))) :primary)))
    (setf (symbol-function 'fnn-trace-finish) original)))

;; Failure before entering a diagnostic interval also runs BODY exactly once.
(let ((original (symbol-function 'fnn-trace-now)) (calls 0))
  (unwind-protect
       (progn
         (setf (symbol-function 'fnn-trace-now) (lambda () (error "clock unavailable")))
         (assert (equal (multiple-value-list (fnn-trace-span (:clock-fault) (incf calls) (values 3 4))) '(3 4)))
         (assert (= calls 1)))
    (setf (symbol-function 'fnn-trace-now) original)))

(fnn-trace-start :capacity 2 :sample-every 2)
(dotimes (i 7) (fnn-trace-span (:bounded) i))
(assert (= (fnn-trace-state-next *fnn-trace-state*) 2))
(assert (= (fnn-trace-state-dropped *fnn-trace-state*) 2))
(fnn-trace-report *standard-output*)

;; Demonstrate actual process scope: other-thread allocations occur inside
;; this span. These are deliberately not attributed to the caller thread.
(fnn-trace-start :capacity 4 :allocation :process)
(fnn-trace-span (:concurrent-process :cid 9)
  (sb-thread:join-thread
   (sb-thread:make-thread (lambda ()
     (let ((vectors (loop repeat 256 collect (make-array 4096 :element-type '(unsigned-byte 8)))))
       (assert (= (length vectors) 256)))))))
(fnn-trace-report *standard-output*)
(format t "NATIVE_TRACE_PASS~%")
