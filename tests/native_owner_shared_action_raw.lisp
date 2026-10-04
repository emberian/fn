;;; Sweep S028: an OS error (or any unclassified condition) inside an owner
;;; action stops the owner as a FAULT (exit 4), and the condition the caller
;;; sees is then an fnn-store-fault, so the control worker answers :fault,
;;; never REFUSED (exit 1: nothing happened); an OS error after a durable
;;; step fences the owner (exit 3) and the caller sees an
;;; fnn-store-indeterminate (:uncertain).  Drives the deployed
;;; fnn-owner-shared-action-locked and fnn-owner-classify-escape-locked
;;; (host/native/owner.lisp) over the deployed classifier (books/failure-
;;; scope.lisp fn-fs-classify and its closed tables, read from the book)
;;; against recording stubs, and reads the deployed control worker's clause order
;;; (host/native/control.lisp fnn-control-handle-client): the fault clause
;;; precedes the store-error, os-error and socket-error clauses.
(require :sb-posix)
(require :sb-bsd-sockets)
(defpackage "ACL2" (:use "CL"))
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
(defun fnn-control-answering (control socket)
  (declare (ignorable control socket))
  (harness-stub-reached 'fnn-control-answering "host/native/control.lisp"))
(defun fnn-control-live-pages-answer (service request)
  (declare (ignorable service request))
  (harness-stub-reached 'fnn-control-live-pages-answer "host/native/control.lisp"))
(defun fnn-control-live-status-answer (service request)
  (declare (ignorable service request))
  (harness-stub-reached 'fnn-control-live-status-answer "host/native/control.lisp"))
(defun fnn-control-peer-is-owner-p (socket)
  (declare (ignorable socket))
  (harness-stub-reached 'fnn-control-peer-is-owner-p "host/native/control-transport.lisp"))
(defun fnn-control-read-frame (socket maximum &optional seconds)
  (declare (ignorable socket maximum seconds))
  (harness-stub-reached 'fnn-control-read-frame "host/native/control-transport.lisp"))
(defun fnn-control-send-reply (socket status)
  (declare (ignorable socket status))
  (harness-stub-reached 'fnn-control-send-reply "host/native/control.lisp"))
(defun fnn-control-test-after-submit (status)
  (declare (ignorable status))
  (harness-stub-reached 'fnn-control-test-after-submit "host/native/control.lisp"))
(defun fnn-core (name &rest args)
  (declare (ignorable name args))
  (harness-stub-reached 'fnn-core "host/native/io.lisp"))
(defun fnn-fault (control &rest args)
  (declare (ignorable control args))
  (harness-stub-reached 'fnn-fault "host/native/io.lisp"))
(defun fnn-octet-list (octets)
  (declare (ignorable octets))
  (harness-stub-reached 'fnn-octet-list "host/native/io.lisp"))
(defun fnn-octet-list-p (x)
  (declare (ignorable x))
  (harness-stub-reached 'fnn-octet-list-p "host/native/io.lisp"))
(defun fnn-octets (sequence)
  (declare (ignorable sequence))
  (harness-stub-reached 'fnn-octets "host/native/io.lisp"))
(defun fnn-octets-ctl-fill (vector)
  (declare (ignorable vector))
  (harness-stub-reached 'fnn-octets-ctl-fill "host/native/io.lisp"))
(defun fnn-owner-consumer-local-serialized (service operation first second)
  (declare (ignorable service operation first second))
  (harness-stub-reached 'fnn-owner-consumer-local-serialized "host/native/owner.lisp"))
(defun fnn-owner-consumer-local-wait (service operation consumer argument)
  (declare (ignorable service operation consumer argument))
  (harness-stub-reached 'fnn-owner-consumer-local-wait "host/native/owner.lisp"))
(defun fnn-owner-control-submit-serialized (service msgid groups payload)
  (declare (ignorable service msgid groups payload))
  (harness-stub-reached 'fnn-owner-control-submit-serialized "host/native/owner.lisp"))
(defun fnn-owner-disk-admit (service)
  (declare (ignorable service))
  (harness-stub-reached 'fnn-owner-disk-admit "host/native/owner.lisp"))
(defun fnn-owner-fault-service (service cid condition)
  (declare (ignorable service cid condition))
  (harness-stub-reached 'fnn-owner-fault-service "host/native/owner.lisp"))
(defun fnn-owner-live-admin-serialized (service argv)
  (declare (ignorable service argv))
  (harness-stub-reached 'fnn-owner-live-admin-serialized "host/native/admin.lisp"))
(defun fnn-owner-moderation-serialized (service op login id reason)
  (declare (ignorable service op login id reason))
  (harness-stub-reached 'fnn-owner-moderation-serialized "host/native/owner.lisp"))
(defun fnn-owner-topic-local-serialized (service operation source-sequence quota observed-uid)
  (declare (ignorable service operation source-sequence quota observed-uid))
  (harness-stub-reached 'fnn-owner-topic-local-serialized "host/native/owner.lisp"))
;;; ---- derived stubs: END ----

(declaim (declaration xargs))
(defun member-equal (x l) (member x l :test #'equal))

(defun load-deployed-forms (path wanted)
  (let ((missing (copy-list wanted)))
    (with-open-file (stream path)
      (loop for form = (read stream nil :eof)
            until (eq form :eof)
            when (and (consp form)
                      (member (car form) '(defun defmacro defvar define-condition defconst))
                      (member (list (car form) (cadr form)) wanted :test #'equal))
              do (eval (if (eq (car form) 'defconst) (cons 'defparameter (cdr form)) form))
                 (setf missing (remove (list (car form) (cadr form)) missing
                                       :test #'equal))))
    (when missing (error "deployed forms missing from ~a: ~s" path missing))))

(load-deployed-forms "host/native/io.lisp"
                     '((define-condition fnn-store-error)
                       (define-condition fnn-store-fault)
                       (define-condition fnn-store-indeterminate)
                       (define-condition fnn-os-error)
                       (defvar *fnn-section-step*)
                       (defun fnn-condition-class)))

;; ACL2's classifier as the book defines it (the tables are closed: a class
;; in none of them is a fault).
(load-deployed-forms "books/failure-scope.lisp"
                     '((defconst *fn-fs-indeterminate-classes*)
                       (defconst *fn-fs-fault-classes*)
                       (defconst *fn-fs-usage-classes*)
                       (defconst *fn-fs-refusal-classes*)
                       (defconst *fn-fs-os-classes*)
                       (defun fn-fs-classify)))

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
                     '((defvar *fnn-boundary-outcome*)
                       (defun fnn-owner-classify-escape-locked)
                       (defun fnn-owner-shared-action-locked)))

(defun raised (thunk &optional step)
  "The condition fnn-owner-shared-action-locked lets out, or :none.  STEP is
the durable step the quantum completed (*fnn-section-step*)."
  (setq *stops* nil *faulted* nil *fnn-section-step* step)
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
;; An OS error AFTER a durable step (a rename landed): ACL2 decides the
;; fence, the owner stops uncertain (exit 3) and the caller sees an
;; fnn-store-indeterminate, so the control worker answers :uncertain, never
;; REFUSED.
(let ((c (raised (lambda () (error 'fnn-os-error :errno 5 :path "/x")) :replaced)))
  (unless (and (typep c 'fnn-store-indeterminate)
               (equal *stops* (list +fnn-exit-uncertain+)))
    (error "an OS error after a durable step did not reach the caller as uncertain: ~s ~s"
           c *stops*)))
;; A fault subclass keeps its own class (an extent or input-bound fault).
(let ((c (raised (lambda () (error 'fnn-store-fault :message "f")))))
  (unless (and (eq (class-name (class-of c)) 'fnn-store-fault)
               (equal *stops* (list +fnn-exit-fault+)))
    (error "a store fault was not handed on as itself: ~s" c)))
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
(format t "native_owner_shared_action_raw: PASS~%")
