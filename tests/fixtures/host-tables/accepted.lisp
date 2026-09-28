; refused.lisp with only the declarations (and :synchronized t) added: host_check --tables
; accepts every global table here (tests/test_host_check_tables.py).
(in-package "ACL2")

(defvar *fx-lock* (sb-thread:make-mutex :name "fixture"))
(defvar *fx-shared* (make-hash-table :test 'eq)) ; guarded-by: *fx-lock*
(defparameter *fx-unsync* (make-hash-table :test 'eq :synchronized t))
(defstruct fx-runtime
  (lock (sb-thread:make-mutex :name "fixture runtime"))
  ;; guarded-by: fx-runtime-lock
  (pending (make-hash-table)))
;; guarded-by: *fx-lock*
(defvar *fx-misnamed* (make-hash-table))
(defvar *fx-late* nil)
(defun fx-init ()
  ;; thread-confined: the fixture's loading thread
  (setq *fx-late* (make-hash-table :test 'equal)))
(defun fx-local () (let ((seen (make-hash-table))) (setf (gethash 1 seen) t) seen))
; (defvar *fx-comment* (make-hash-table)) is a comment
(defun fx-doc () "(make-hash-table) in a string")
(defun fx-use (k) (sb-thread:with-mutex (*fx-lock*) (gethash k *fx-shared*)))
(defun fx-pending (r k) (sb-thread:with-mutex ((fx-runtime-lock r)) (gethash k (fx-runtime-pending r))))
