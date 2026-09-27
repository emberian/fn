; host_check --tables must refuse every global table in this file
; (tests/test_host_check_tables.py); accepted.lisp is the same file with
; only the declarations added, so each refusal is for the named reason.
(in-package "ACL2")

(defvar *fx-lock* (sb-thread:make-mutex :name "fixture"))
(defvar *fx-shared* (make-hash-table :test 'eq))
(defparameter *fx-unsync* (make-hash-table :test 'eq :synchronized nil))
(defstruct fx-runtime
  (lock (sb-thread:make-mutex :name "fixture runtime"))
  (pending (make-hash-table)))
;; guarded-by: *fx-no-such-lock*
(defvar *fx-misnamed* (make-hash-table))
(defvar *fx-late* nil)
(defun fx-init () (setq *fx-late* (make-hash-table :test 'equal)))
(defun fx-local () (let ((seen (make-hash-table))) (setf (gethash 1 seen) t) seen))
; (defvar *fx-comment* (make-hash-table)) is a comment
(defun fx-doc () "(make-hash-table) in a string")
(defun fx-use (k) (sb-thread:with-mutex (*fx-lock*) (gethash k *fx-shared*)))
