;;; Exercise the shipped common NNTP/BP transit decision wrapper at its host
;;; boundary. ACL2's plan and event values are stubbed here; the ACL2 book/test
;;; independently checks those exact source, enrollment and event bindings.
(require :sb-posix)
(require :sb-bsd-sockets)
(defpackage "ACL2" (:use "CL"))
(in-package "ACL2")
(define-condition fnn-store-indeterminate (error) ())
(define-condition fnn-store-fault (error) ())
(define-condition fnn-store-error (error) ())
(define-condition fnn-os-error (error) ())
(define-condition fnn-store-io-refusal (error) ())
(defun fnn-err (&rest args) (declare (ignore args)) nil)
(defstruct sample-store fenced)
(defvar *store* (make-sample-store))
(defvar *form* :absent)
(defvar *plan* '(:refused :local-enrollment))
(defvar *existing* nil)
(defvar *signature* :verified)
(defvar *calls* nil)
(defvar *filing* nil)
(defun fnn-fault (&rest args) (error "fault ~s" args))
(defun fnn-octet-list-p (x) (and (listp x) (every #'integerp x)))
(defun fnn-octets (x) (coerce x 'vector))
(defun fnn-owner-service-store (service)
  (declare (ignore service)) *store*)
(defun fnn-store-fenced (store) (sample-store-fenced store))
(defun (setf fnn-store-fenced) (value store)
  (setf (sample-store-fenced store) value))
(defun fnn-octet-list (x) (coerce x 'list))
(defun fnn-charge (n) n)
(defun fnn-owner-core (name &rest args)
  (case name
    (fn-owner-peer-carrier-form
     (assert (equal args '((65 66)))) *form*)
    (fn-owner-peer-carrier-plan *plan*)
    (fn-owner-group-codes '(0))
    (fn-owner-post-boundary :post-boundary)
    ;; books/peer-authored-accept.lisp fn-pa-filing-plan on an ordinary
    ;; article: the ingress's groups, unchanged.
    ;; A test sets *FILING* to answer for it.
    (fn-owner-control-filing (or *filing* (list :file (second args))))
    (fn-owner-next-store-coordinates '(3 3 3))
    (fn-owner-peer-carried-event
     (push :event *calls*) :kind4)
    ;; books/peer-authored-accept.lisp fn-pa-served-word, transcribed for
    ;; the stub: the served arm must relay ACL2's answer, not compute one.
    (fn-owner-served-carried-word
     (push :served-word *calls*)
     (destructuring-bind (word detail) args
       (if (and (eq word :refused)
                (member detail '(:article :carrier :carrier-shape
                                 :local-enrollment :signature :conflict
                                 :control-not-filed :control-malformed)))
           detail word)))
    (otherwise (error "unexpected owner core ~s" name))))
(defun fnn-core (name &rest args)
  (declare (ignore args))
  (assert (eq name 'fn-hsig-host-preimage))
  '(1 2 3))
(defun fnn-owner-action (name &rest args)
  (case name
    (fn-owner-existing-action
     (assert (equal args '((60 120 62) (65 66) (0))))
     *existing*)
    (otherwise (error "unexpected owner action ~s" name))))
(defun fnn-validate-post-boundary (&rest args)
  (declare (ignore args)) (push :boundary *calls*))
(defun fnn-owner-attempt (&rest args)
  (declare (ignore args)) (push :legacy *calls*) :durable)
(defun fnn-owner-advance-clock () (push :clock *calls*) :observed)
(defun fnn-hsig-observe-raw (&rest args)
  (declare (ignore args))
  (push :primitives *calls*)
  (list *signature* (list *signature* #(17 18))))
(defun fnn-metadata (&rest args)
  (declare (ignore args)) (values #(49) #(50) nil))
(defun fnn-owner-identity-commit (service event)
  (declare (ignore service))
  (assert (eq event :kind4))
  (push :kind4-commit *calls*) :durable)

(with-open-file (stream "host/native/owner.lisp")
  (let ((found nil))
    (loop for form = (read stream nil :eof) until (eq form :eof)
          when (and (consp form) (eq (car form) 'defun)
                    (member (cadr form) '(fnn-owner-attempt-transit
                                          fnn-owner-attempt-served)))
            do (eval form)
               (when (eq (cadr form) 'fnn-owner-attempt-served)
                 (setq found t) (return))
          when (and (consp form)
                    (or (and (eq (car form) 'defmacro)
                             (eq (cadr form) 'fnn-owner-attempt-handlers))
                        (and (eq (car form) 'defvar)
                             (eq (cadr form) '*fnn-owner-transit-detail*))
                        (and (eq (car form) 'defun)
                             (eq (cadr form) 'fnn-owner-transit-refused))))
            do (eval form))
    (assert found)))

(defun attempt ()
  (fnn-owner-attempt-transit :service #(60 120 62) #(65 66)
                             (list #(103)) #(69)))
(defun reset-case ()
  (setq *calls* nil *existing* nil *signature* :verified
        *fnn-owner-transit-detail* nil *filing* nil
        *plan* '(:refused :local-enrollment)))

; A carrier-absent article keeps the old path. A present malformed carrier
; never reaches either the old Store attempt or the signature primitive.
(reset-case)
(assert (eq (attempt) :durable))
(assert (equal *calls* '(:legacy)))
(reset-case)
(setq *form* '(:refused :carrier))
(assert (eq (attempt) :refused))
(assert (null *calls*))
; The log detail is ACL2's own refusal keyword, relayed unchanged.
(assert (eq *fnn-owner-transit-detail* :carrier))

; Exact bytes recover the old Store duplicate outcome even after a local
; tombstone.  In particular, if these bytes were already stored as a legacy
; fn-r before this receiver profile was installed, this does not upgrade that
; historical record to kind-4 or create a verified verdict.  The duplicate
; result only says that the existing Store record was left unchanged.
(reset-case)
(setq *form* '(:ok source principal keys signatures)
      *existing* :duplicate)
(assert (eq (attempt) :duplicate))
(assert (not (member :primitives *calls*)))
(assert (not (member :kind4-commit *calls*)))
(reset-case)
(assert (eq (attempt) :refused))
(assert (not (member :legacy *calls*)))
; The failure-8 refusal: no receiver-local enrollment of the principal.
(assert (eq *fnn-owner-transit-detail* :local-enrollment))

; New current-enrollment-bound bytes require both primitive observations,
; then publish the ACL2-built kind-4 event through the identity Store gate.
(reset-case)
(setq *plan* '(:ok source principal ((:ed25519 . (11))
                                    (:ml-dsa-65 . (13)))
                   ((:ed25519 . (17)) (:ml-dsa-65 . (19))) snapshot 1))
(assert (eq (attempt) :durable))
(assert (member :kind4-commit *calls*))
(assert (not (member :legacy *calls*)))
(reset-case)
(setq *plan* '(:ok source principal ((:ed25519 . (11))
                                    (:ml-dsa-65 . (13)))
                   ((:ed25519 . (17)) (:ml-dsa-65 . (19))) snapshot 1)
      *signature* :refused)
(assert (eq (attempt) :refused))
(assert (not (member :kind4-commit *calls*)))
(assert (eq *fnn-owner-transit-detail* :signature))

; The served POST arm (and the bound local submission) calls the same
; attempt; its word is the one ACL2 answers for the refusal detail.
(defun served ()
  (setq *fnn-owner-transit-detail* :stale)
  (fnn-owner-attempt-served :service #(60 120 62) #(65 66)
                            (list #(103)) #(69)))
(reset-case)
(setq *form* :absent)
(assert (eq (served) :durable))
(assert (equal *calls* '(:served-word :legacy)))
(reset-case)
(setq *form* '(:refused :carrier))
(assert (eq (served) :carrier))
(assert (not (member :legacy *calls*)))
(reset-case)
(setq *form* '(:ok source principal keys signatures))
(assert (eq (served) :local-enrollment))
(assert (not (member :legacy *calls*)))
(reset-case)
(setq *plan* '(:ok source principal ((:ed25519 . (11))
                                    (:ml-dsa-65 . (13)))
                   ((:ed25519 . (17)) (:ml-dsa-65 . (19))) snapshot 1)
      *signature* :refused)
(assert (eq (served) :signature))
(assert (not (member :kind4-commit *calls*)))
(reset-case)
(setq *plan* '(:ok source principal ((:ed25519 . (11))
                                    (:ml-dsa-65 . (13)))
                   ((:ed25519 . (17)) (:ml-dsa-65 . (19))) snapshot 1))
(assert (eq (served) :durable))
(assert (member :kind4-commit *calls*))
; C1: the filing plan's refusal stops every ingress before any Store call
; and its reason reaches the served word; a filed control article reaches
; the Store under the filing group, not the ingress's own.
(reset-case)
(setq *form* :absent *filing* '(:refused :control-not-filed))
(assert (eq (served) :control-not-filed))
(assert (equal *calls* '(:served-word)))
(reset-case)
(setq *filing* '(:refused :control-not-filed))
(assert (eq (attempt) :refused))
(assert (eq *fnn-owner-transit-detail* :control-not-filed))
(assert (null *calls*))
(reset-case)
(setq *form* :absent *filing* '(:file ((99 46 99))))
(let ((seen nil))
  (let ((old (fdefinition 'fnn-owner-attempt)))
    (setf (fdefinition 'fnn-owner-attempt)
          (lambda (service msgid payload groups evidence)
            (declare (ignore service msgid payload evidence))
            (setq seen groups) :durable))
    (assert (eq (attempt) :durable))
    (setf (fdefinition 'fnn-owner-attempt) old))
  (assert (equalp seen (list #(99 46 99)))))
(format t "native peer-authored transit boundary passed~%")
