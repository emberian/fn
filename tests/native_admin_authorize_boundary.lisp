;;; Exercise the deployed administrative wrapper and its actual fnn-core calls.
;;; The fnn-call observer checks the pure/state ABI, not authorization semantics.
(defpackage "ACL2" (:use "CL"))
(in-package "ACL2")
(defvar *the-live-state* :unexpected-state)
(defun f-get-global (name state) (declare (ignore name state)) nil)
(load "host/native/io.lisp")
(load "host/native/admin.lisp")

(defvar *authorization-result* '(:accepted :publication))
(defvar *authorization-calls* 0)
;; The lock argument is the store's own observation (`fnn-admin-lock-observation'):
;; T for a writable store with a live lock descriptor, NIL otherwise, so ACL2's
;; `:lock' refusal is reachable from the host rather than a literal T.
(defvar *expected-lock* t)
(defun fnn-call (name &rest args)
  (case name
    (fn-store-cfg-native-admin-authorize
     ;; A seventh argument would be ACL2's state, accidentally supplied by
     ;; fnn-core-state. Also pin the list conversion at the byte boundary.
     (assert (equal args (list '((1 2)) 7 '((3 4)) '(5 6) *expected-lock*
                               '((99 102 103)))))
     (incf *authorization-calls*)
     (list *authorization-result*))
    (fn-native-admin-host-publication-status
     (assert (equal args (list *authorization-result*)))
     (list (first *authorization-result*)))
    (fn-native-admin-host-publication-reason
     (assert (equal args (list *authorization-result*)))
     (list (second *authorization-result*)))
    (otherwise (error "Unexpected core call ~s" name))))

(let ((store (%make-fnn-store :frontier 7 :writable t :lock-fd 3)))
  (assert (eq (fnn-admin-authorize store (list #(1 2)) (list #(3 4))
                                 #(5 6) '("cfg"))
              *authorization-result*))
  (setf *authorization-result* '(:refused :occupied))
  (assert (handler-case
              (progn (fnn-admin-authorize store (list #(1 2)) (list #(3 4))
                                         #(5 6) '("cfg"))
                     nil)
            (fnn-store-fault (condition) (error condition))
            (fnn-store-indeterminate (condition) (error condition))
            (fnn-store-error () t)))
  (assert (= *authorization-calls* 2))
  ;; A store opened without the exclusive lock hands ACL2 NIL, and ACL2's
  ;; refusal (here `:lock') is reported as a refusal, never a publication.
  (setf *expected-lock* nil
        *authorization-result* '(:refused :lock))
  (dolist (unlocked (list (%make-fnn-store :frontier 7 :writable nil :lock-fd 3)
                          (%make-fnn-store :frontier 7 :writable t :lock-fd nil)))
    (assert (handler-case
                (progn (fnn-admin-authorize unlocked (list #(1 2)) (list #(3 4))
                                            #(5 6) '("cfg"))
                       nil)
              (fnn-store-fault (condition) (error condition))
              (fnn-store-indeterminate (condition) (error condition))
              (fnn-store-error () t))))
  (assert (= *authorization-calls* 4)))
(format t "native administration pure authorization boundary: PASS~%")
