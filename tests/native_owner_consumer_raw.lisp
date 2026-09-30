;;; Exercise the deployed consumer publication wrapper with recording Store
;;; stubs.  ACL2 constructs the event; this test observes only the native
;;; reservation/preparation/publication boundary and its refusal cut.
(require :sb-posix)
(require :sb-bsd-sockets)
(defpackage "ACL2" (:use "CL"))
(in-package "ACL2")

;; The deployed native wrapper calls the ACL2 actual-event verdict before
;; taking a transaction ID. This test records ordering and preserves the
;; opaque event identity; source ACL2 tests establish charge correspondence.
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

(defun read-acl2-defun (path name)
  "The form (defun NAME ...) of the ACL2 file PATH, read, never evaluated."
  (with-open-file (stream path)
    (loop for form = (read stream nil :eof)
          until (eq form :eof)
          when (and (consp form) (eq (car form) 'defun) (eq (cadr form) name))
            do (return form)
          finally (error "~a has no defun ~a" path name))))

(defun tree-mentions (tree atom)
  (or (eq tree atom)
      (and (consp tree) (or (tree-mentions (car tree) atom)
                            (tree-mentions (cdr tree) atom)))))

(defun keyword-leaves (tree)
  (cond ((keywordp tree) (list tree))
        ((consp tree) (append (keyword-leaves (car tree)) (keyword-leaves (cdr tree))))
        (t nil)))

(defparameter *at-capacity* :unaffordable)

(defvar *fnn-observe-callback* nil)
(defvar *fnn-finish-callback* nil)
(defvar *calls* nil)
(defvar *prepare-result* :prepared)
(defvar *verdict* :admissible)
(defstruct mock-service store)
(define-condition consumer-refusal (error) ())
(define-condition consumer-indeterminate (error) ())
(defun fnn-refuse (&rest args) (declare (ignore args)) (error 'consumer-refusal))
(defun fnn-indeterminate (&rest args) (declare (ignore args))
  (error 'consumer-indeterminate))
(defun fnn-owner-service-store (service) (mock-service-store service))
(defun fnn-owner-observe (&rest args) (declare (ignore args)) nil)
(defun fnn-owner-finish (&rest args) (declare (ignore args)) nil)
(defun fnn-owner-core (name &rest args)
  (push (list* :core name args) *calls*)
  (case name
    (fn-owner-consumer-publication-verdict *verdict*)
    (fn-owner-next-txid 7)
    (otherwise (error "wrong core call ~s" name))))
(defun fnn-nat (x) (unless (and (integerp x) (<= 0 x)) (error "not nat")) x)
(defun fnn-advance-frontier (store txid)
  (declare (ignore store)) (push (list :advance txid) *calls*) :advanced)
(defun fnn-owner-action (name &rest args)
  (push (cons :action (cons name args)) *calls*)
  (ecase name
    (fn-owner-prepare-consumer *prepare-result*)
    (fn-owner-refuse-reservation :refused)))
(defun fnn-owner-publish-prepared (service label)
  (declare (ignore service)) (push (list :publish label) *calls*) :durable)

(load-deployed-forms "host/native/owner.lisp"
                     '((defun fnn-owner-consumer-commit)))

(defun check (condition description)
  (unless condition (error "~a" description)))

;; Load the actual ACL2-mode wrapper body in a recording host harness.
;; Only stobj/ACL2 declaration syntax is removed. The proved ACL2 charge and
;; budget decisions are opaque stubs here: this tests argument routing and
;; cached history/debt plumbing, not their mathematics or guard translation.
(defmacro mv-let (bindings expression &body body)
  `(multiple-value-bind ,bindings ,expression ,@body))
(defun mv (&rest values) (values-list values))
(defvar *budget-input* nil)
(defun fn-owner-record-octets (hist state) (values 100 hist state))
(defun fn-owner-record-debt (hist state) (values 2 hist state))
(defun fn-owner-store (state) (declare (ignore state)) :store)
(defun fn-owner-profile-carry (state) (declare (ignore state)) :carry)
(defun fn-owner-store-profile (state) (declare (ignore state)) :profile)
(defun fn-sn-files (store) (declare (ignore store)) :files)
(defun fn-sf-records-count (files) (declare (ignore files)) 3)
(defun fn-cpb-event-verdict-carried (&rest args)
  (setf *budget-input* args) :admissible)
(let* ((form (read-acl2-defun "host/owner-host.lisp"
                              'fn-owner-consumer-publication-verdict))
       (body (remove-if (lambda (x) (and (consp x) (eq (car x) 'declare)))
                        (cdddr form))))
  (eval (list* 'defun (second form) (third form) body)))
(multiple-value-bind (error verdict hist state)
    (fn-owner-consumer-publication-verdict :event :hist :state)
  (check (and (null error) (eq verdict :admissible) (eq hist :hist)
              (eq state :state)
              (equal *budget-input* '(:carry :profile 3 100 2 :event)))
         "owner actual-event verdict misrouted current profile/count/bytes/debt/charge"))

(let* ((event '(:consumer :opaque-acl2-event))
       (service (make-mock-service :store :store)))
  (setf *calls* nil *prepare-result* :prepared)
  (check (eq (fnn-owner-consumer-commit service event) :durable)
         "prepared event did not become durable")
  (check (equal (reverse *calls*)
                (list (list :core 'fn-owner-consumer-publication-verdict event)
                      '(:core fn-owner-next-txid)
                      '(:advance 7)
                      (list :action 'fn-owner-prepare-consumer event)
                      '(:publish "consumer")))
         "consumer publication call order or event identity changed")

  (setf *calls* nil *prepare-result* :refused)
  (handler-case (progn (fnn-owner-consumer-commit service event)
                       (error "refused event published"))
    (consumer-refusal () nil))
  (check (equal (reverse *calls*)
                (list (list :core 'fn-owner-consumer-publication-verdict event)
                      '(:core fn-owner-next-txid)
                      '(:advance 7)
                      (list :action 'fn-owner-prepare-consumer event)
                      '(:action fn-owner-refuse-reservation)))
         "refused reservation was not consumed before refusal")

  ;; Every non-admissible verdict refuses before the frontier, including a
  ;; missing/malformed result. The host cannot turn an unknown word into an
  ;; admitted event or spend a reservation to discover budget refusal.
  (dolist (verdict (list *at-capacity* nil :unexpected))
    (setf *verdict* verdict *prepare-result* :prepared *calls* nil)
    (handler-case (progn (fnn-owner-consumer-commit service event)
                         (error "capacity refusal missed"))
      (consumer-refusal () nil))
    (check (equal (reverse *calls*)
                  (list (list :core 'fn-owner-consumer-publication-verdict event)))
           "capacity refusal advanced the frontier or was not the owner's verdict")))

(format t "native owner consumer boundary passed~%")
