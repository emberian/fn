;;; Exercise the deployed bound-submission helper with a refusing custom
;;; commit followed by a durable one.  This catches an in-flight submission
;;; left behind by the first result without copying the helper into the test.
(require :sb-posix)
(require :sb-bsd-sockets)
(defpackage "ACL2" (:use "CL"))
(in-package "ACL2")

;; The deployed forms this boundary runs, loaded by name so a rename fails
;; here rather than leaving a stale stub in its place: the Store condition
;; hierarchy the commit word classifies by, and the stderr writer the
;; uncertain arm reports through (fnn-err, since 000c6b6e "Log the reason
;; when a bound Store commit raises indeterminate") with what it calls.
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
                       (define-condition fnn-os-error)
                       (defvar *fnn-stderr*)
                       (defun fnn-concat)
                       (defun fnn-string-octets)
                       (defun fnn-emit)
                       (defun fnn-err)))

;; The deployed fnn-err writes to *fnn-stderr*; here that is a scratch file,
;; read back below to check the uncertain arm names its reason.
(defparameter *stderr-path*
  (format nil "/tmp/fn-bound-commit-raw-~d.err" (sb-posix:getpid)))
(setq *fnn-stderr* (open *stderr-path* :direction :output
                         :element-type '(unsigned-byte 8)
                         :if-exists :supersede :if-does-not-exist :create))

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
  (declare (ignore control args)) (error 'fnn-store-indeterminate))
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
;; operator-config (7c80e4f6) put ACL2's file-first gate in front of the
;; commit callback (PKT-069, fn-owner-bound-commit-gate, KEYSTONE
;; fn-obc-commit-only-after-filing).  The ACL2 side is a recording stub here
;; like fnn-owner-action; *bound-gate* is its answer.
(defparameter *bound-gate* :commit)
(defparameter *bound-gate-calls* nil)
(defun fnn-owner-core (name &rest args)
  (ecase name
    (fn-owner-bound-commit-gate
     (push args *bound-gate-calls*) *bound-gate*)))
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
                  (member (cadr form)
                          '(fnn-owner-bound-commit-word
                            fnn-owner-complete-bound-submission)))
          do (eval form)))

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

; A real callback preflight signals rather than returning :refused.  The
; condition must be settled before another control request reaches :take.
(flet ((submit () :submitted)
       (refuse () (error 'fnn-store-error :message "preflight"))
       (commit () :durable))
  (unless (eq (fnn-owner-complete-bound-submission
               :service #'submit *bound-msgid* *bound-payload* *bound-groups*
               #(9) 7 10 #'refuse)
              :refused)
    (error "signalled custom preflight refusal did not settle"))
  (unless (eq (fnn-owner-complete-bound-submission
               :service #'submit *bound-msgid* *bound-payload* *bound-groups*
               #(9) 7 11 #'commit)
              :accepted)
    (error "next control request remained busy after preflight refusal")))
(unless (and (not *bound-inflight*) (= *bound-flushes* 8) (= *bound-logs* 4)
             (equal (reverse *bound-resolutions*)
                    '(:refused :durable :refused :durable)))
  (error "signalled preflight refusal left a bound submission unresolved"))

; Only a known semantic refusal can be converted to a completion word.
; Ambiguity retains its class, and fault/OS conditions reach the owner fence.
(unless (eq (fnn-owner-bound-commit-word
             (lambda () (error 'fnn-store-indeterminate :message "barrier EIO")))
            :uncertain)
  (error "ambiguous Store callback lost its uncertainty"))
(close *fnn-stderr*)
(let ((logged (with-open-file (in *stderr-path*) (read-line in nil ""))))
  (delete-file *stderr-path*)
  (unless (and (search "Store outcome uncertain" logged)
               (search "barrier EIO" logged))
    (error "uncertain bound commit did not log its reason: ~s" logged)))
(dolist (condition '(fnn-store-fault fnn-os-error))
  (unless (handler-case
              (progn (fnn-owner-bound-commit-word
                      (lambda () (error condition))) nil)
            (error (caught) (typep caught condition)))
    (error "bound callback changed the ~a fault class" condition)))

; The gate's refusal is the outcome and the callback never runs: a payload
; ACL2's filing plan does not file in exactly GROUPS never reaches the Store.
(setq *bound-gate* '(:refused :groups-not-filed) *bound-resolutions* nil
      *bound-gate-calls* nil)
(flet ((submit () :submitted)
       (commit () (error "commit callback ran after the gate refused")))
  (unless (eq (fnn-owner-complete-bound-submission
               :service #'submit *bound-msgid* *bound-payload* *bound-groups*
               #(9) 7 12 #'commit)
              :refused)
    (error "gate refusal was not the outcome")))
(unless (and (not *bound-inflight*)
             (equal *bound-resolutions* '(:refused))
             (equal *bound-gate-calls*
                    (list (list (coerce *bound-payload* 'list)
                                (mapcar (lambda (g) (coerce g 'list)) *bound-groups*)))))
  (error "gate refusal left the submission unresolved or gated other octets: ~s"
         *bound-gate-calls*))
(setq *bound-gate* :malformed)
(flet ((submit () :submitted)
       (commit () (error "commit callback ran after a malformed gate")))
  (unless (handler-case
              (progn (fnn-owner-complete-bound-submission
                      :service #'submit *bound-msgid* *bound-payload* *bound-groups*
                      #(9) 7 13 #'commit)
                     nil)
            (error () t))
    (error "malformed gate answer was not a fault")))

(format t "native owner bound commit settlement passed~%")
