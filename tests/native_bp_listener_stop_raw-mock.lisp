;;; A drive under way when the owner starts stopping performs no further
;;; primitive: each is admitted as a live section is (fn-fs-section-admit).
;;; Shipped: fnn-bplc-drive, fnn-bplc-step, fnn-bplc-cut.
(require :sb-posix)
(require :sb-bsd-sockets)
(defpackage "ACL2" (:use "CL"))
(in-package "ACL2")

(define-condition fnn-store-error (error) ((message :initarg :message)))
(defstruct fnn-bplc model mode (owned nil) (live nil))
(defvar *fnn-bplc-test-change* nil)
(defvar *stopping* nil)
(defvar *binds* nil)
(defvar *script*
  '((:prepare-bind 1) (:bind 1) (:prepare-bind 2) (:bind 2) (:ready)))
(defun fnn-owner-service-stopping (service) (declare (ignore service)) *stopping*)
(defun fn-fs-section-admit (admits stopping)
  (if (and stopping (equal admits :live)) :refuse :run))
(defun fnn-refuse (control &rest args)
  (error 'fnn-store-error :message (apply #'format nil control args)))
(defun fnn-indeterminate (&rest args) (error "indeterminate ~s" args))
(defun fnn-fault (&rest args) (error "fault ~s" args))
(defun fnn-out (&rest args) (declare (ignore args)) nil)
(defun fnn-developer-selector (name) (declare (ignore name)) nil)
(defun fnn-core (name &rest args)
  (declare (ignore args))
  (case name
    (fn-bplc-action (pop *script*))
    (fn-bplc-runtime-line "line")
    (t nil)))
(defun fnn-tcl-listen (port)
  (push port *binds*)
  ;; The owner starts stopping while the first bind is under way.
  (setq *stopping* t)
  (values :socket port))

(defun load-shipped (path names)
  (with-open-file (stream path)
    (dolist (wanted names)
      (file-position stream 0)
      (let ((found nil))
        (loop for form = (read stream nil :eof) until (eq form :eof)
              when (and (consp form) (eq (car form) 'defun) (eq (cadr form) wanted))
                do (eval form) (setq found t) (return))
        (unless found (error "~a: ~s not found" path wanted))))))
(load-shipped "host/native/bp-listener-control.lisp"
              '(fnn-bplc-step fnn-bplc-cut fnn-bplc-drive))

(let ((node (make-fnn-bplc :model :m)) (outcome nil))
  (handler-case (fnn-bplc-drive node :service)
    (fnn-store-error () (setq outcome :refused)))
  (unless (eq outcome :refused) (error "the drive ran on past the stop: ~s" *binds*))
  (unless (equal *binds* '(1))
    (error "a primitive ran after the stop began: ~s" *binds*)))

(format t "native BP listener stop: PASS~%")
