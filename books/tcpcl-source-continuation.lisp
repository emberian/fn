; Callback disposition only. A yielded token is opaque: this classifier does
; not issue a source, admit allocation or turn publication into acceptance.
(in-package "ACL2")
(include-book "cbor")
(set-verify-guards-eagerness 2)
(defun fn-tcl-source-result-action (result)
 (declare (xargs :guard t))
 (if (not (and (consp result) (consp (cdr result)) (null (cddr result))))
  :fault
  (cond ((and (eq (car result) :source-yield) (cadr result)) :retain)
        ((or (eq (car result) :accepted) (eq (car result) :refused)
             (eq (car result) :uncertain)) :settle)
        (t :fault))))
(defun fn-tcl-source-result-token (result)
 (declare (xargs :guard t))
 (if (eq (fn-tcl-source-result-action result) :retain)
  (cadr result) nil))
