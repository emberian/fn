;;; Raw sequencing test for host/native/feed-service.lisp.
;;;
;;; This is deliberately an external harness: the deployed source still runs
;;; only inside the saved ACL2 image.  It supplies the narrow owner boundary
;;; and verifies that one received chunk is handed to the ACL2 reply wrapper
;;; repeatedly with NIL drains, with each line's FNFD flush before its command
;;; socket write.  It does not implement NNTP framing or replies.

(require :sb-bsd-sockets)

(defpackage "ACL2" (:use "CL"))
(in-package "ACL2")

(define-condition fnn-store-error (error) ())
(define-condition fnn-store-indeterminate (fnn-store-error) ())
(define-condition fnn-store-fault (fnn-store-error) ())
(define-condition fnn-os-error (error) ())

(defconstant +fnn-max-read+ 512)

(defparameter *test-words* '(:quiet :send :need-input))
(defparameter *test-reply-inputs* nil)
(defparameter *test-flushes* 0)
(defparameter *test-sends* nil)

(defun fnn-fault (control &rest args)
  (error (apply #'format nil control args)))

(defun fnn-core (&rest args)
  (declare (ignore args))
  (error "unexpected raw core call"))
(defun fnn-octet-list-p (x)
  (and (listp x) (every (lambda (b) (and (integerp b) (<= 0 b 255))) x)))
(defun fnn-octets (x) x)
(defun fnn-octet-list (x) x)
(defun fnn-make-octets (n) (make-array n :element-type '(unsigned-byte 8)))
(defun fnn-owner-serialized (service cid thunk)
  (declare (ignore service cid))
  (funcall thunk))
(defun fnn-owner-action (name &rest args)
  (unless (eq name 'fn-owner-feed-reply-chunk)
    (error "unexpected owner action: ~s" name))
  (push (second args) *test-reply-inputs*)
  (or (pop *test-words*) (error "too many reply actions")))
(defun fnn-owner-feed-flush (service)
  (declare (ignore service))
  (incf *test-flushes*))
(defun fnn-owner-octets-global (name)
  (unless (eq name 'fn-owner-feed-command)
    (error "unexpected global: ~s" name))
  #(9 10))
(defun fnn-send-all (fd octets seconds)
  (declare (ignore seconds))
  (push (list fd (coerce octets 'list)) *test-sends*))

;;; Only read here; worker/lifecycle functions are not entered in this test.
(load "host/native/feed-service.lisp")

(let* ((runtime (%make-fnn-feed-runtime :service :test
                                         :lock (sb-thread:make-mutex)
                                         :limit 512))
       (link (%make-fnn-feed-link :peer "peer" :peer-octets #(112 101 101 114)
                                  :socket :fake :fd 7)))
  (fnn-feed-consume runtime link '(50 48 48 13 10 50 48 51 13 10) nil 1)
  (unless (equal (nreverse *test-reply-inputs*)
                 '((50 48 48 13 10 50 48 51 13 10) nil nil))
    (error "reply wrapper did not receive chunk then two NIL drains: ~s"
           *test-reply-inputs*))
  (unless (= *test-flushes* 2)
    (error "expected one durable flush per completed line, got ~s" *test-flushes*))
  (unless (equal (nreverse *test-sends*) '((7 (9 10))))
    (error "expected only the ACL2-projected command after its flush: ~s"
           *test-sends*)))

(format t "native feed raw sequencing test passed~%")
