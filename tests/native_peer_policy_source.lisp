; Actual inert codec + native file capture, with real POSIX files.
; Source execution only: no active owner/image/full peer tariff claim.
(load "tests/native_heap_default_source.lisp")
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
(defun fnn-seconds-to-deadline (deadline)
  (declare (ignorable deadline))
  (harness-stub-reached 'fnn-seconds-to-deadline "host/native/io.lisp"))
;;; ---- derived stubs: END ----
(defmacro verify-guards (&rest args) (declare (ignore args)) nil)
(defparameter *fn-rl-word-max* (1- (expt 2 64)))
(selected-source "books/heap-store-figure.lisp" '(*fn-heap-nursery-least-octets* fn-heap-nursery-trigger fn-heap-with-nursery fn-heap-grow-runtime-dynamic))
(selected-source "books/peer-flight-reservation.lisp"
 '(fn-pfr-at fn-pfr-slots fn-pfr-bookkeeping fn-pfr-fixed-backing fn-pfr-policy-p
   fn-pfr-extend-reservation))
(selected-source "books/peer-flight-startup.lisp"
 '(fn-pfr-operation-observes-p fn-pfr-extend-operation-reservation))
(selected-source "books/cbor.lisp" '(fn-cbor-octetp fn-cbor-octet-listp))
(load "books/peer-u64-codec.lisp")
(selected-source "books/peer-flight-profile.lisp"
 '(fn-pfp-file-name fn-pfp-read-bound fn-pfp-prefix fn-pfp-take fn-pfp-drop
   fn-pfp-values fn-pfp-fields fn-pfp-write fn-pfp-read fn-pfp-refusal-line))
(defun io-forms (names)
  (with-open-file (in "host/native/io.lisp")
    (loop for form = (read in nil :eof) until (eq form :eof)
          when (and (consp form) (member (car form) '(defun defmacro defvar defconstant define-condition))
                    (member (second form) names))
          do (eval form) (setf names (remove (second form) names))
             (when (null names) (return))
          finally (assert (null names)))))
(io-forms '(fnn-unwind-cleanups fnn-posix fnn-open fnn-close fnn-fstat fnn-lstat fnn-regular-p
 fnn-read-fd fnn-read-bounded-fd fnn-retry-eintr fnn-eintr-p fnn-would-block-p
 *fnn-read-syscall* +fnn-o-nofollow+ fnn-input-overbound fnn-overbound
 fnn-os-error fnn-os-fail fnn-join fnn-concat))
(source-forms "host/native/heap.lisp" '(fnn-peer-flight-profile))
(defparameter *heap-core* (symbol-function 'fnn-core))
(defun fnn-core (name &rest args)
  (case name
    ((fn-pfp-file-name fn-pfp-read-bound fn-pfp-read fn-pfp-refusal-line fn-pfr-policy-p
      fn-pfr-operation-observes-p fn-pfr-extend-operation-reservation)
     (apply (symbol-function name) args))
    (otherwise (apply *heap-core* name args))))
(defparameter *policy* '(16777216 67108864 2 1 8388608 4096))
(defun write-bytes (path bytes)
  (with-open-file (out path :direction :output :if-exists :supersede
                       :element-type '(unsigned-byte 8))
    (mapc (lambda (b) (write-byte b out)) bytes)))
(let* ((root (format nil "/tmp/fn-peer-source-~d" (sb-posix:getpid)))
       (path (concatenate 'string root "/peer-flight-profile")))
  (sb-posix:mkdir root #o700)
  (unwind-protect
       (progn
         (assert (null (fnn-peer-flight-profile root)))
         (write-bytes path (fn-pfp-write *policy*))
         (assert (equal (fnn-peer-flight-profile root) *policy*))
         ; Full launcher caller propagates the exact policy and grows threads.
         (let ((original (symbol-function 'fnn-heap-command-profile-base)))
           (unwind-protect
                (progn
                  (setf (symbol-function 'fnn-heap-command-profile-base)
                        (lambda (argv) (declare (ignore argv))
                          (values :profile 4 :run nil nil nil root)))
                  (assert (equal (eighth (multiple-value-list
                                         (fnn-heap-command-profile '("operator" "CONFIG" "run"))))
                                 *policy*)))
             (setf (symbol-function 'fnn-heap-command-profile-base) original)))
         (let ((decision (fnn-heap-reservation :profile 4 :run nil nil nil root *policy*)))
           (assert (> (second decision) 257))
           (assert (= (sixth decision) 17)))
         (dolist (bytes (list '(70 78) (append (fn-pfp-write *policy*) '(0))
                             (make-list 54 :initial-element 0)))
           (write-bytes path bytes)
           (handler-case (progn (fnn-peer-flight-profile root) (error "malformed accepted"))
             (fnn-store-error (condition) (assert (= (fnn-exit-code-for condition) 1)))))
         (delete-file path)
         (sb-posix:mkfifo path #o600)
         (handler-case (progn (fnn-peer-flight-profile root) (error "FIFO accepted"))
           (fnn-store-fault () nil))
         (delete-file path)
         (sb-posix:symlink "/etc/passwd" path)
         (handler-case (progn (fnn-peer-flight-profile root) (error "symlink accepted"))
           (fnn-os-error () nil))
         (delete-file path)
         (write-bytes path (fn-pfp-write *policy*))
         ; Failed physical read remains fault, and descriptor cleanup executes.
         (let ((closes 0) (original (symbol-function 'fnn-close))
               (*fnn-read-syscall* (lambda (&rest args) (declare (ignore args))
                                    (values nil sb-posix:eio))))
           (unwind-protect
                (progn
                  (setf (symbol-function 'fnn-close)
                        (lambda (fd) (incf closes) (funcall original fd)))
                  (handler-case (progn (fnn-peer-flight-profile root) (error "read fault accepted"))
                    (fnn-os-error () nil))
                  (assert (= closes 1)))
             (setf (symbol-function 'fnn-close) original)))
         (format t "SOURCE PEER POLICY PASSED~%"))
    (when (probe-file path) (delete-file path))
    (sb-posix:rmdir root)))
