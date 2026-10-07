(in-package "ACL2")
(include-book "def-loop-fixture-dep")

(defun fn-store-group-code-in-loop (name groups i)
  (declare (xargs :guard (and (true-listp groups) (natp i))))
  (if (consp groups)
      (if (equal name (car groups))
          i
        (fn-store-group-code-in-loop name (cdr groups) (+ 1 i)))
    nil))

(defun fn-store-group-code-in (name groups)
  ; The zero-based code of a group, or nil.
  (declare (xargs :guard (true-listp groups) :verify-guards nil))
  (mbe :logic (if (consp groups)
                  (if (equal name (car groups))
                      0
                    (let ((rest (fn-store-group-code-in name (cdr groups))))
                      (if (null rest) nil (+ 1 rest))))
                nil)
       :exec (fn-store-group-code-in-loop name groups 0)))

(defthm fn-store-group-code-in-loop-is-plus
  (implies (natp i)
           (equal (fn-store-group-code-in-loop name groups i)
                  (let ((r (fn-store-group-code-in name groups)))
                    (if r (+ i r) nil)))))

(verify-guards fn-store-group-code-in)
