;;; The peer-invite handlers hand each ACL2 entry exactly its formals
;;; (SCEN-PINV-CONFIRM-ARITY, lane scenarios, 2026-10-04).
;;;
;;; From bbfc3b915 (2026-09-30) to the fix, `peer confirm' applied
;;; fn-pinv-host-confirm-record-plan to 10 arguments; it takes 8.  The image's
;;; host entry guard refused the call and stopped the owner on every confirm
;;; ("owner quantum fault; process stopped: host-entry-guard: ... takes 8
;;; arguments ... the host passed 10"; hbox run peer-d5b0b9100: peer_invite
;;; 7/7 and friends_feed red).
;;;
;;; What is real here:
;;; - the handlers, read from host/native/peer-invite.lisp;
;;; - the entry guard and its message, read from host/native/io.lisp
;;;   (fnn-entry-guard, fnn-entry-guard-describe);
;;; - each entry's formals, read from its ACL2 definition in
;;;   host/peer-invite-host.lisp.  The image reads them off its world.
;;; What is made up: fnn-core's ANSWERS (the plans that steer each handler
;;; to its next dispatch), the owner's state reads, and the signature
;;; observation.  Hence -mock.  This witnesses call shape only, not any
;;; decision.  The behaviour on an image is tests.test_native_peer_invite.
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
(defun fnn-owner-result (recognizer name &rest args)
  (declare (ignorable recognizer name args))
  (harness-stub-reached 'fnn-owner-result "host/native/owner.lisp"))
;;; ---- derived stubs: END ----
(defun source-definition (path kind name)
  (with-open-file (stream path)
    (let* ((text (make-string (file-length stream)))
           (prefix (format nil "(~a ~a " kind name)))
      (read-sequence text stream)
      (let ((start (search prefix text)))
        (unless start (error "missing definition ~a in ~a" name path))
        (read-from-string text nil nil :start start)))))
(defparameter *handlers* (or (sb-ext:posix-getenv "FN_PINV_HOST_SOURCE")
                             "host/native/peer-invite.lisp"))
(defparameter *entries* "host/peer-invite-host.lisp")
(defparameter *io* "host/native/io.lisp")

;; The guard's spec, as fnn-entry-guard-spec builds it off the world: the
;; entry's arity from its ACL2 formals, here read from its definition.  No
;; kind conjunct is checked (these entries are :program, guard t).
(define-condition fnn-store-fault (error) ((message :initarg :message :reader fault-message))
  (:report (lambda (c s) (write-string (fault-message c) s))))
(eval (source-definition *io* "define-condition" "fnn-entry-guard-fault"))
(defun fnn-entry-guard-spec (name)
  (cons (length (third (source-definition *entries* "defun" (string-downcase name)))) nil))
(eval (source-definition *io* "defun" "fnn-entry-guard-describe"))
(eval (source-definition *io* "defun" "fnn-entry-guard"))

;; The dispatcher: the real guard first, then a made-up answer per entry.
(defvar *calls* nil)
(defvar *answers* nil)
(defun fnn-core (name &rest args)
  (fnn-entry-guard name args)
  (push (cons name (length args)) *calls*)
  (let ((answer (assoc name *answers*)))
    (unless answer (error "no answer for ~(~a~)" name))
    (cdr answer)))
(defun fnn-owner-core (name &rest args)
  (declare (ignore args))
  (case name
    (fn-owner-next-store-coordinates (list 7 8 9))
    (t (list :owner-read name))))
(defun fnn-owner-serialized (service cid thunk &optional class)
  (declare (ignore service cid class))
  (funcall thunk))
(defun fnn-hsig-observe-raw (ed-key ml-key preimage signatures)
  (declare (ignore ed-key ml-key preimage signatures))
  (list :ed-observation (list :ml-verdict #(1 2 3))))
(defun fnn-err (&rest args) (declare (ignore args)))
(defun fnn-developer-selector (name) (declare (ignore name)) nil)
(defun fnn-owner-identity-commit (&rest args) (declare (ignore args)) (error "not reached"))

(dolist (name '("fnn-pinv-observe" "fnn-pinv-refused" "fnn-pinv-owner-issue"
                "fnn-pinv-owner-accept" "fnn-pinv-owner-enrol-confirmed"
                "fnn-pinv-owner-confirm"))
  (eval (source-definition *handlers* "defun" name)))

(defparameter +subject+
  '(:observe :principal ((:ed . (1)) (:ml . (2))) (3) (4)))

(defun run (label thunk answers expected-calls)
  (let ((*calls* nil) (*answers* answers))
    (handler-case (funcall thunk)
      (fnn-entry-guard-fault (fault)
        (format t "RED ~a: ~a~%" label fault)
        (sb-ext:exit :code 1)))
    (let ((calls (reverse *calls*)))
      (unless (equal calls expected-calls)
        (format t "RED ~a: dispatched ~s, expected ~s~%" label calls expected-calls)
        (sb-ext:exit :code 1))
      (format t "~a: ~{~(~a~)/~d~^ ~}~%" label
              (loop for (name . count) in calls collect name collect count)))))

;; issue: the plan refuses, so issue-plan is its only entry after the subject.
(run "issue"
     (lambda () (fnn-pinv-owner-issue :service :received))
     `((fn-pinv-host-observation-subject . ,+subject+)
       (fn-pinv-host-issue-plan :refused :harness))
     '((fn-pinv-host-observation-subject . 1) (fn-pinv-host-issue-plan . 6)))
;; accept: the record plan says enrol, then the enrolment step says current.
(run "accept"
     (lambda () (fnn-pinv-owner-accept :service :received))
     `((fn-pinv-host-observation-subject . ,+subject+)
       (fn-par-host-accept-record-plan :enrol)
       (fn-pinv-host-accept-step :current))
     '((fn-pinv-host-observation-subject . 1) (fn-par-host-accept-record-plan . 8)
       (fn-pinv-host-accept-step . 8)))
;; confirm: the same through the confirm record plan and the confirm step.
(run "confirm"
     (lambda () (fnn-pinv-owner-confirm :service :received :invitation))
     `((fn-pinv-host-observation-subject . ,+subject+)
       (fn-pinv-host-confirm-record-plan :enrol)
       (fn-pinv-host-confirm-step :current))
     '((fn-pinv-host-observation-subject . 1) (fn-pinv-host-confirm-record-plan . 8)
       (fn-pinv-host-confirm-step . 9)))
(format t "peer-invite dispatch: every entry got its formals (3 handlers) PASS~%")
