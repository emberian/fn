; Exact original plan/effect outer-spine runtime accessors, moved verbatim.
; Narrow shape vocabulary carries no served command/index proof dependencies.
(in-package "ACL2")
(include-book "acceptance-alloc")

(defun fn-splan-of-effects (effects)
  (declare (xargs :guard t))
  (cons nil effects))

(defun fn-splan-cur (p)
  (declare (xargs :guard t))
  (if (consp p) (car p) nil))

(defun fn-splan-rest (p)
  (declare (xargs :guard t))
  (if (consp p) (cdr p) nil))

(defun fn-splan-cursor-effectp (e)
  (declare (xargs :guard t))
  (and (consp e) (or (equal (car e) :over-cursor) (equal (car e) :newnews-cursor)) (consp (cdr e))))

(defun fn-srb-effect-octets (e)
  (declare (xargs :guard t))
  (if (and (consp e) (equal (car e) :reply) (consp (cdr e)))
      (car (cdr e))
    nil))


(defthm fn-splan-cur-of-cons
  (equal (fn-splan-cur (cons a b)) a))

(defthm fn-splan-rest-of-cons
  (equal (fn-splan-rest (cons a b)) b))

