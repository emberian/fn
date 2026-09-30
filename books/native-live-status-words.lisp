; Literal unbounded report primitives, extracted without definition changes.
(in-package "ACL2")
(include-book "records-shape")
(local (include-book "arithmetic-5/top" :dir :system))

(defun fn-nls-text (text)
  (declare (xargs :guard t))
  (fn-record-string-octets text))

(defun fn-nls-digits (n acc)
  (declare (xargs :guard (natp n)
                  :measure (nfix n)
                  :hints (("Goal" :in-theory (disable floor mod)))))
  (if (zp n)
      acc
    (fn-nls-digits (floor n 10) (cons (+ 48 (mod n 10)) acc))))

(defun fn-nls-nat (n)
  (declare (xargs :guard t))
  (if (posp n) (fn-nls-digits n nil) '(48)))
