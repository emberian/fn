;;; Exercise the deployed bound-submission helper with a refusing custom
;;; commit followed by a durable one.  This catches an in-flight submission
;;; left behind by the first result without copying the helper into the test.
(require :sb-posix)
(require :sb-bsd-sockets)
(defpackage "ACL2" (:use "CL"))
(in-package "ACL2")

(defparameter *bound-word* nil)
(defparameter *bound-inflight* nil)
(defparameter *bound-resolutions* nil)
(defparameter *bound-flushes* 0)
(defparameter *bound-logs* 0)
(defparameter *bound-msgid* #(1 2))
(defparameter *bound-payload* #(3 4))
(defparameter *bound-groups* (list #(5)))

(defun fnn-fault (control &rest args) (error (apply #'format nil control args)))
(defun fnn-indeterminate (control &rest args)
  (error (apply #'format nil control args)))
(defun fnn-octet-list (x) (coerce x 'list))
(defun fnn-owner-octets-global (name)
  (ecase name
    (fn-owner-submit-msgid *bound-msgid*)
    (fn-owner-submit-octets *bound-payload*)))
(defun fnn-owner-submit-groups () *bound-groups*)
(defun fnn-owner-feed-flush (service)
  (declare (ignore service)) (incf *bound-flushes*))
; Operator logging is a side effect after the ACL2 outcome. It does not make
; or persist the decision; count the deployed call without replacing either.
(defun fnn-owner-log () (incf *bound-logs*))
(defun fnn-owner-attempt (&rest ignored)
  (declare (ignore ignored)) (error "default commit unexpectedly called"))
(defun fnn-owner-action (name &rest args)
  (case name
    (fn-owner-take
     (if *bound-inflight* (error "previous submission remained in flight")
       (progn (setq *bound-inflight* t) :taken-control)))
    (fn-owner-submission-intent :ready)
    (fn-owner-submission-resolution
     (push (car args) *bound-resolutions*) (car args))
    (fn-owner-control-outcome
     (setq *bound-inflight* nil)
     (case (car args) (:durable :accepted) (otherwise (car args))))
    (otherwise (error "unexpected owner action ~s" name))))

(with-open-file (stream "host/native/owner.lisp")
  (loop for form = (read stream nil :eof)
        until (eq form :eof)
        when (and (consp form) (eq (car form) 'defun)
                  (eq (cadr form) 'fnn-owner-complete-bound-submission))
          do (eval form) (return)))

(flet ((submit () :submitted)
       (commit () *bound-word*))
  (setq *bound-word* :refused)
  (unless (eq (fnn-owner-complete-bound-submission
               :service #'submit *bound-msgid* *bound-payload* *bound-groups*
               #(9) 7 8 #'commit)
              :refused)
    (error "refusing custom commit did not remain refused"))
  (setq *bound-word* :durable)
  (unless (eq (fnn-owner-complete-bound-submission
               :service #'submit *bound-msgid* *bound-payload* *bound-groups*
               #(9) 7 9 #'commit)
              :accepted)
    (error "valid custom commit after refusal was not accepted")))

(unless (and (not *bound-inflight*) (= *bound-flushes* 4) (= *bound-logs* 2)
             (equal (reverse *bound-resolutions*) '(:refused :durable)))
  (error "bound submission cleanup/resolution mismatch"))

(format t "native owner custom commit refusal cleanup passed~%")
