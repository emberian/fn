; Unchanged statement result constructors/accessors, independent of identity.
(in-package "ACL2")

(defun fn-stmt-ok (value)
  (declare (xargs :guard t))
  (list :ok value))

(defun fn-stmt-ok2 (value rest)
  (declare (xargs :guard t))
  (list :ok value rest))

(defun fn-stmt-error (code)
  (declare (xargs :guard t))
  (list :error code))

(defun fn-stmt-okp (r)
  (declare (xargs :guard t))
  (and (consp r) (equal (car r) :ok)))

(defun fn-stmt-value (r)
  (declare (xargs :guard t))
  (if (and (consp r) (consp (cdr r))) (car (cdr r)) nil))

(defun fn-stmt-rest (r)
  (declare (xargs :guard t))
  (if (and (consp r) (consp (cdr r)) (consp (cdr (cdr r))))
      (car (cdr (cdr r)))
    nil))
