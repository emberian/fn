;;; Exercise the shipped BP submit dispatcher with a stale owner observation.
(require :sb-posix)
(require :sb-bsd-sockets)
(defpackage "ACL2" (:use "CL"))
(in-package "ACL2")

(defvar *actions* nil)
(defvar *events* nil)
(defvar *clock-outcome* :observed)
(defvar *stamp-status* :usable)
(defun fnn-bpapp-bind-owner-store () nil)
(defun fnn-owner-action (name &rest args)
  (declare (ignore args))
  (case name (fn-owner-app-plan :ready) (fn-owner-app-submit :accepted)
        (fn-owner-operator-submit :accepted)
        (fn-owner-stamp-status (push :stamp-status *events*) *stamp-status*)
        (otherwise (error "unexpected owner action ~s" name))))
; Operator logging is a side effect after the ACL2 outcome (the same stub as
; native_owner_bound_commit_raw.lisp); it decides nothing here.
(defun fnn-owner-log (&rest arguments) (declare (ignore arguments)) nil)
(defun fnn-octet-list (x) x)
(defun fnn-octets (x) x)
(defun fnn-nat (x) x)
(defun fnn-global (name)
  (case name
    (fn-owner-app-generation 1) (fn-owner-app-txid 2)
    (fn-owner-app-planned-result :accepted)
    (fn-owner-app-msgid '(1)) (fn-owner-app-article '(2))
    (fn-owner-app-groups '((3))) (fn-owner-app-evidence '(4))
    ;; An ordinary (non-transit) request: the bound-submission arm.
    (fn-owner-app-transitp nil)
    (otherwise (error "unexpected global ~s" name))))
(defun fnn-bpapp-action (journal request generation)
  (declare (ignore journal request generation))
  (pop *actions*))
(defun fnn-owner-advance-clock ()
  (push :observe *events*) *clock-outcome*)
(defun fnn-owner-complete-bound-submission (service thunk &rest arguments)
  (declare (ignore service arguments))
  (push :submit *events*) (funcall thunk))
(defun fnn-core-state (name &rest args)
  (declare (ignore args))
  (case name (fn-bprj-request-result :accepted)
        (otherwise (error "unexpected core query ~s" name))))
(defun fnn-receipt-adu (journal request)
  (declare (ignore journal request)) :receipt)
(defun fnn-fault (&rest arguments) (error "~{~a~^ ~}" arguments))
(defun fnn-owner-serialized (service cid thunk)
  (declare (ignore service cid)) (funcall thunk))
(defun fnn-owner-service-store (service)
  (declare (ignore service)) :store)
(defun fnn-owner-control-arm-fault (store)
  (declare (ignore store)) nil)
(defun fnn-owner-control-disarm-fault (store displaced)
  (declare (ignore store displaced)) nil)
(defun fnn-owner-core (name)
  (case name
    (fn-owner-prov-post '(1)) (fn-owner-config-generation 1)
    (fn-owner-next-txid 2) (fn-owner-app-current-generation 1)
    (otherwise (error "unexpected owner core query ~s" name))))

;; The dispatcher and the deployed txid check it calls, by name, so a rename
;; fails here rather than leaving a stub in its place.
(let ((missing (list 'fnn-bpapp-planned-txid 'fnn-bpapp-accept-locked)))
  (with-open-file (stream "host/native/bp-app.lisp")
    (loop for form = (read stream nil :eof) until (eq form :eof)
          when (and (consp form) (eq (car form) 'defun)
                    (member (cadr form) missing))
            do (eval form) (setq missing (remove (cadr form) missing))))
  (when missing (error "BP dispatcher forms not found: ~s" missing)))
(let ((found nil))
  (with-open-file (stream "host/native/owner.lisp")
    (loop for form = (read stream nil :eof) until (eq form :eof)
          when (and (consp form) (eq (car form) 'defun)
                    (eq (cadr form) 'fnn-owner-control-submit-serialized))
            do (eval form) (setq found t)))
  (unless found (error "operator submit dispatcher not found")))

(defun check (actual expected)
  (unless (equal actual expected)
    (error "expected ~s, got ~s" expected actual)))
(defun accept ()
  (multiple-value-list
   ;; The bundle identity joined the arguments with 7281e76f (BP-R17).
   (fnn-bpapp-accept-locked :service :journal :inbound '(1)
                            :node '(5) '(2) :source :destination)))

;; A refused reading cannot use the owner's previously stored observation.
(setq *clock-outcome* :refused *stamp-status* :usable
      *actions* '((:submit)) *events* nil)
(check (accept) '(:clock-unusable nil))
(check (reverse *events*) '(:observe))

;; The observation itself may be accepted without a usable wall stamp.
(setq *clock-outcome* :observed *stamp-status* :clock-unusable
      *actions* '((:submit)) *events* nil)
(check (accept) '(:clock-unusable nil))
(check (reverse *events*) '(:observe :stamp-status))

;; A fresh reading precedes the actual owner submission.
(setq *clock-outcome* :observed *stamp-status* :usable
      *actions* '((:submit) (:return-receipt)) *events* nil)
(check (accept) '(:accepted :receipt))
(check (reverse *events*) '(:observe :stamp-status :submit))

;; Replaying a committed request only returns its receipt, with no clock read.
(setq *clock-outcome* :refused *actions* '((:return-receipt)) *events* nil)
(check (accept) '(:accepted :receipt))
(check *events* nil)
(setq *clock-outcome* :refused *events* nil)
(check (fnn-owner-control-submit-serialized
        :service '(1) '((2)) '(3)) :clock-unusable)
(check (reverse *events*) '(:observe))
(setq *clock-outcome* :observed *stamp-status* :clock-unusable *events* nil)
(check (fnn-owner-control-submit-serialized
        :service '(1) '((2)) '(3)) :clock-unusable)
(check (reverse *events*) '(:observe :stamp-status))
(setq *stamp-status* :usable *events* nil)
(check (fnn-owner-control-submit-serialized
        :service '(1) '((2)) '(3)) :accepted)
(check (reverse *events*) '(:observe :stamp-status :submit))
(format t "native BP application clock dispatch passed~%")
