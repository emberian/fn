; Captured NEWNEWS scan progress vocabulary, independent of the optional
; suffix-maxima index and its proof. Both consumers share these exact fields.
(in-package "ACL2")

(defun fn-nnw-cursor (groups threshold tail maxes horizon)
  (declare (xargs :guard t))
  (list :newnews groups threshold tail maxes horizon))
(defun fn-nnw-cursorp (cur)
  (declare (xargs :guard t))
  (and (true-listp cur) (equal (len cur) 6) (eq (car cur) :newnews)))
(defun fn-nnw-at (n x)
  (declare (xargs :guard t :measure (nfix n)))
  (if (consp x)
      (if (zp (nfix n)) (car x) (fn-nnw-at (1- (nfix n)) (cdr x)))
    nil))
(defun fn-nnw-groups (cur) (declare (xargs :guard t)) (fn-nnw-at 1 cur))
(defun fn-nnw-threshold (cur) (declare (xargs :guard t)) (fn-nnw-at 2 cur))
(defun fn-nnw-tail (cur) (declare (xargs :guard t)) (fn-nnw-at 3 cur))
(defun fn-nnw-maxes-of (cur) (declare (xargs :guard t)) (fn-nnw-at 4 cur))
(defun fn-nnw-horizon (cur) (declare (xargs :guard t)) (fn-nnw-at 5 cur))

