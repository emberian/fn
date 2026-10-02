;;; Sweep S028: an OS error (or any unclassified condition) inside an owner
;;; action stops the owner as a FAULT (exit 4), and the condition the caller
;;; sees is then an fnn-store-fault, so the control worker answers :fault,
;;; never REFUSED (exit 1: nothing happened).  Drives the deployed
;;; fnn-owner-shared-action-locked (host/native/owner.lisp) against recording
;;; stubs, and reads the deployed control worker's clause order
;;; (host/native/control.lisp fnn-control-handle-client): the fault clause
;;; precedes the store-error, os-error and socket-error clauses.
(require :sb-posix)
(require :sb-bsd-sockets)
(defpackage "ACL2" (:use "CL"))
(in-package "ACL2")

(defun load-deployed-forms (path wanted)
  (let ((missing (copy-list wanted)))
    (with-open-file (stream path)
      (loop for form = (read stream nil :eof)
            until (eq form :eof)
            when (and (consp form)
                      (member (car form) '(defun defmacro defvar define-condition))
                      (member (list (car form) (cadr form)) wanted :test #'equal))
              do (eval form)
                 (setf missing (remove (list (car form) (cadr form)) missing
                                       :test #'equal))))
    (when missing (error "deployed forms missing from ~a: ~s" path missing))))

(load-deployed-forms "host/native/io.lisp"
                     '((define-condition fnn-store-error)
                       (define-condition fnn-store-fault)
                       (define-condition fnn-store-indeterminate)
                       (define-condition fnn-os-error)))

;; The exit codes are ACL2's (fn-outcome-code); their values do not matter
;; here, only which one the owner stops with.
(defparameter +fnn-exit-uncertain+ :exit-uncertain)
(defparameter +fnn-exit-fault+ :exit-fault)

(defparameter *stops* nil)
(defparameter *faulted* nil)
(defun fnn-developer-selector (name) (declare (ignore name)) nil)
(defun fnn-owner-connection-selected-p (service) (declare (ignore service)) nil)
(defun fnn-owner-action (name &rest args)
  (if (eq name 'fn-owner-fault) (push (car args) *faulted*)
    (error "unexpected owner action ~s" name)))
(defun fnn-owner-stop-service-locked (service exit)
  (declare (ignore service)) (push exit *stops*))
(defun fnn-err (control &rest args) (declare (ignore control args)) nil)

(load-deployed-forms "host/native/owner.lisp"
                     '((defun fnn-owner-shared-action-locked)))

(defun raised (thunk)
  "The condition fnn-owner-shared-action-locked lets out, or :none."
  (setq *stops* nil *faulted* nil)
  (handler-case (progn (fnn-owner-shared-action-locked :service 7 thunk) :none)
    (condition (c) c)))

;; An OS error inside the action: the owner stops as a fault and the caller
;; sees an fnn-store-fault (positive witness; before S028 it saw the
;; fnn-os-error itself, which the control worker answered REFUSED).
(let ((c (raised (lambda () (error 'fnn-os-error :errno 24 :path "/x")))))
  (unless (and (typep c 'fnn-store-fault) (equal *stops* (list +fnn-exit-fault+))
               (equal *faulted* '(7)))
    (error "an OS error inside an owner action did not reach the caller as a fault: ~s ~s"
           c *stops*)))
;; A socket error and an arbitrary error: the same.
(dolist (thunk (list (lambda () (error 'sb-bsd-sockets:socket-error :errno 32))
                     (lambda () (error "arbitrary"))))
  (let ((c (raised thunk)))
    (unless (and (typep c 'fnn-store-fault) (equal *stops* (list +fnn-exit-fault+)))
      (error "an unclassified failure did not reach the caller as a fault: ~s" c))))
;; Contrasts: a known refusal stays a refusal and stops nothing; an
;; indeterminate observation stays indeterminate (exit 3); success is :none.
(let ((c (raised (lambda () (error 'fnn-store-error :message "refused")))))
  (unless (and (typep c 'fnn-store-error) (not (typep c 'fnn-store-fault))
               (null *stops*))
    (error "a known refusal was not kept a refusal: ~s ~s" c *stops*)))
(let ((c (raised (lambda () (error 'fnn-store-indeterminate :message "eio")))))
  (unless (and (typep c 'fnn-store-indeterminate)
               (equal *stops* (list +fnn-exit-uncertain+)))
    (error "an indeterminate observation lost its class: ~s" c)))
(unless (and (eq (raised (lambda () :done)) :none) (null *stops*))
  (error "a successful action stopped the owner"))

;; The control worker's clauses, in the deployed order: the fault is caught
;; as :fault before any refusal clause can see it.
(let ((clauses nil))
  (with-open-file (stream "host/native/control.lisp")
    (loop for form = (read stream nil :eof)
          until (eq form :eof)
          when (and (consp form) (eq (car form) 'defun)
                    (eq (cadr form) 'fnn-control-handle-client))
            do (labels ((walk (x)
                          (when (consp x)
                            (if (and (eq (car x) 'handler-case)
                                     (assoc 'fnn-store-fault (cddr x)))
                                (setq clauses (mapcar #'car (cddr x)))
                              (progn (walk (car x)) (walk (cdr x)))))))
                 (walk form))))
  (let ((fault (position 'fnn-store-fault clauses)))
    (unless (and fault
                 (every (lambda (later)
                          (let ((at (position later clauses)))
                            (and at (< fault at))))
                        '(fnn-store-error fnn-os-error sb-bsd-sockets:socket-error)))
      (error "the control worker can answer a stopped owner's fault as a refusal: ~s"
             clauses))))
(format t "native_owner_shared_action_raw: ok~%")
