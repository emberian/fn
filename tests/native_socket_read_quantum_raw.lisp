;;; The shipped nonblocking read primitive against the quanta ACL2 hands it.
;;; Real forms: fnn-socket-read-now and its ceiling, fnn-make-octets,
;;; fnn-eintr-p, fnn-would-block-p and the *fnn-read-syscall* seam from
;;; host/native/io.lisp; fn-tcrt-read-limit from books/tcpcl-retained-turn.lisp.
;;; Read from a real pipe.  Before 2026-10-04 the primitive's ceiling was the
;;; reader's +fnn-max-read+ (512), so TCPCL's 4096 faulted on every :read turn
;;; ("store: invalid socket read quantum", run2-d5b0b9100: the BP family).
;;; tests/native_tcpcl_retained_turn_raw-mock.lisp stubs the primitive, which
;;; is why no harness saw it.
(require :sb-posix)
(require :sb-bsd-sockets)
(defpackage "ACL2" (:use "CL"))
(in-package "ACL2")
(declaim (declaration xargs))
(define-condition fnn-store-fault (error) ((message :initarg :message :reader fnn-message))
  (:report (lambda (c s) (write-string (fnn-message c) s))))
(define-condition fnn-os-error (error) ((errno :initarg :errno)))
(defun fnn-fault (control &rest args) (error 'fnn-store-fault :message (apply #'format nil control args)))
(defun fnn-os-fail (errno &optional path) (declare (ignore path)) (error 'fnn-os-error :errno errno))
(defun selected-forms (path names)
 (with-open-file (in path)
  (let ((*package* (find-package "ACL2")))
   (loop for form = (read in nil :eof) until (eq form :eof)
    when (and (consp form) (member (car form) '(defun defconstant defvar))
              (member (second form) names)) collect form))))
(defun load-forms (path names)
 (let ((forms (selected-forms path names)))
  (assert (= (length forms) (length names)) () "~a: wanted ~a, read ~a" path names (mapcar #'second forms))
  (dolist (form forms) (eval form))))
(load-forms "host/native/io.lisp"
 '(+fnn-max-read+ fnn-make-octets *fnn-read-syscall* fnn-eintr-p fnn-would-block-p))
;;; The ceiling constant, when the source has one, then the primitive.
(let ((ceiling (selected-forms "host/native/io.lisp" '(+fnn-socket-read-attempt-max+))))
 (dolist (form ceiling) (eval form)))
(load-forms "host/native/io.lisp" '(fnn-socket-read-now))
(load-forms "books/tcpcl-retained-turn.lisp" '(fn-tcrt-read-limit))
(defun pipe-with (n)
 (multiple-value-bind (r w) (sb-posix:pipe)
  (let ((octets (make-array n :element-type '(unsigned-byte 8) :initial-element 7)))
   (sb-sys:with-pinned-objects (octets)
    (assert (= n (sb-posix:write w (sb-sys:vector-sap octets) n))))
   (sb-posix:fcntl r sb-posix:f-setfl (logior (sb-posix:fcntl r sb-posix:f-getfl) sb-posix:o-nonblock))
   (values r w))))
(defun read-once (n limit)
 (multiple-value-bind (r w) (pipe-with n)
  (unwind-protect (fnn-socket-read-now r limit)
   (sb-posix:close r) (sb-posix:close w))))
;;; TCPCL's quantum is accepted and reads at most that many octets.
(let ((got (handler-case (read-once 5000 (fn-tcrt-read-limit))
             (fnn-store-fault (c) (format t "FAIL TCPCL quantum ~d refused: ~a~%" (fn-tcrt-read-limit) c)
               (sb-ext:exit :code 1)))))
 (assert (= (length got) 4096)))
;;; The reader-sized quantum still reads.
(assert (= (length (read-once 600 +fnn-max-read+)) 512))
;;; An empty nonblocking pipe answers :wait.
(multiple-value-bind (r w) (sb-posix:pipe)
 (sb-posix:fcntl r sb-posix:f-setfl (logior (sb-posix:fcntl r sb-posix:f-getfl) sb-posix:o-nonblock))
 (unwind-protect (assert (eq (fnn-socket-read-now r 16) :wait))
  (sb-posix:close r) (sb-posix:close w)))
;;; A malformed quantum is still refused before any allocation.
(dolist (bad (list 0 -1 nil 1/2 (1+ (* 1024 1024 1024))))
 (assert (handler-case (progn (fnn-socket-read-now 0 bad) nil) (fnn-store-fault () t))))
(format t "PASS socket read quantum: TCPCL's ~d and the reader's ~d read; 0, -1, nil, 1/2 and 1 GiB are refused~%"
        (fn-tcrt-read-limit) +fnn-max-read+)
