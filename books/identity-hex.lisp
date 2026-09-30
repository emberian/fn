; Exact identity lowercase-hex primitives, independent of digest/frame ancestry.
(in-package "ACL2")
(include-book "cbor-invariants")
(local (include-book "arithmetic/top" :dir :system))

(defun fn-id-hex-digit (n)
  (declare (xargs :guard (and (natp n) (< n 16))))
  (if (< n 10) (+ 48 n) (+ 87 n)))

(defun fn-id-hex-octets (octets)
  (declare (xargs :guard (fn-cbor-octet-listp octets)))
  (if (consp octets)
      (cons (fn-id-hex-digit (floor (car octets) 16))
            (cons (fn-id-hex-digit (mod (car octets) 16))
                  (fn-id-hex-octets (cdr octets))))
    nil))
