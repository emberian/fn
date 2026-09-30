; Exact catalog definitions factored without changing names or bodies.
(in-package "ACL2")
(include-book "held-record")

(defun fn-cat-assoc (k alist)
  (declare (xargs :guard t))
  (if (consp alist)
      (if (and (consp (car alist)) (equal k (car (car alist))))
          (car alist)
        (fn-cat-assoc k (cdr alist)))
    nil))

(defun fn-held-number-in (group h)
  (declare (xargs :guard t))
  (let ((pair (fn-cat-assoc group (fn-held-numbers h))))
    (if (consp pair) (cdr pair) nil)))

(defun fn-cat-group-high (group c)
  (declare (xargs :guard t))
  (if (consp c)
      (max (nfix (fn-held-number-in group (car c)))
           (fn-cat-group-high group (cdr c)))
    0))

(defun fn-cat-assign-numbers (groups c)
  (declare (xargs :guard t))
  (if (consp groups)
      (cons (cons (car groups) (+ 1 (fn-cat-group-high (car groups) c)))
            (fn-cat-assign-numbers (cdr groups) c))
    nil))

(defun fn-cat-assign (h c)
  (declare (xargs :guard t))
  (fn-held-with-numbers h (fn-cat-assign-numbers (fn-record-groups h) c)))
