; Exact retained-composite constructor/accessors, with no Store grammar.
; Recognizer/accepted-statement lineage remains in held-record.
(in-package "ACL2")

(defun fn-hstxa-make (stxa held)
  (declare (xargs :guard t))
  (list :hstxa stxa held))

(defun fn-hstxa-stxa (x)
  (declare (xargs :guard t))
  (if (consp x) (if (consp (cdr x)) (car (cdr x)) nil) nil))

(defun fn-hstxa-held (x)
  (declare (xargs :guard t))
  (if (consp x) (if (consp (cdr x)) (if (consp (cdr (cdr x))) (car (cdr (cdr x))) nil) nil) nil))
