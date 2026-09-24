;;; Exercise the shipped host boundary with ACL2-style identity lists and
;;; native metadata octet vectors. This is a host regression, not a proof.
(require :sb-posix)
(require :sb-bsd-sockets)
(defpackage "ACL2" (:use "CL"))
(in-package "ACL2")
(define-condition boundary-fault (error) ())
(defvar *calls* nil)
(defun fnn-fault (&rest args)
  (declare (ignore args)) (error 'boundary-fault))
(defun fnn-octets (x)
  (make-array (length x) :element-type '(unsigned-byte 8)
              :initial-contents x))
(defun fnn-octet-list (x) (coerce x 'list))
(defun fnn-owner-octets-global (name)
  (case name
    (fn-owner-submit-msgid #(60 120 62))
    ((fn-owner-submit-octets fn-owner-transit-payload) #(65 66))
    (otherwise (error "unexpected global ~s" name))))
(defun fnn-metadata (msgid stored)
  (assert (equalp msgid #(60 120 62)))
  (assert (equalp stored #(65 66)))
  (values (fnn-octets '(54 54 97)) (fnn-octets '(55 55 98)) nil))
(defun fnn-owner-submit-groups () (list #(103)))
(defun fnn-owner-core (name)
  (case name
    (fn-owner-transit-evidence '(69))
    (fn-owner-bp-transit-raw '(82))
    (otherwise (error "unexpected core ~s" name))))
(defun fnn-owner-action (name &rest args)
  (push name *calls*)
  (case name
    (fn-owner-take :taken-transit)
    (fn-owner-transit-decide
     (assert (equal args '((54 54 97) (55 55 98)))) :want)
    (fn-owner-submission-intent :ready)
    (fn-owner-submission-resolution
     (assert (eq (car args) :durable)) :resolved)
    (fn-owner-bp-transit-outcome
     (assert (equal args '(:durable))) :accepted)
    (otherwise (error "unexpected action ~s" name))))
(defun fnn-owner-feed-flush (service)
  (declare (ignore service)) (push :flush *calls*))
(defun fnn-owner-attempt (&rest args)
  (declare (ignore args)) (push :attempt *calls*) :durable)

(with-open-file (stream "host/native/owner.lisp")
  (let ((found nil))
    (loop for form = (read stream nil :eof) until (eq form :eof)
          when (and (consp form) (eq (car form) 'defun)
                    (eq (cadr form) 'fnn-owner-complete-bp-transit-submission))
            do (eval form) (setq found t) (return))
    (assert found)))

(defun invoke-transit (id subject)
  (fnn-owner-complete-bp-transit-submission
   :service (lambda () :submitted) #(60 120 62) #(82) #(65 66)
   (list #(103)) #(69) 1 2 id subject))
(assert (eq (invoke-transit '(54 54 97) '(55 55 98)) :accepted))
(assert (equal (reverse *calls*)
               '(fn-owner-take fn-owner-transit-decide
                 fn-owner-submission-intent :flush :attempt
                 fn-owner-submission-resolution :flush
                 fn-owner-bp-transit-outcome)))
(dolist (bad '(((54 54 98) (55 55 98)) ((54 54 97) (55 55 97))))
  (setq *calls* nil)
  (assert (handler-case (progn (apply #'invoke-transit bad) nil)
            (boundary-fault () t)))
  (assert (equal *calls* '(fn-owner-take))))
(format t "native BP transit identity regression passed~%")
