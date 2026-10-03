; Shared big-endian u64 octet codec, independent of served catchup.
(in-package "ACL2")

(defun fn-cu-u64-octets-aux (k n acc)
  (declare (xargs :guard (and (natp k) (natp n))))
  (if (zp k)
      acc
    (fn-cu-u64-octets-aux (1- k) (floor n 256) (cons (mod n 256) acc))))

(defun fn-cu-u64-octets (n)
  ; Eight octets, big-endian, of N below 2^64.
  (declare (xargs :guard t))
  (fn-cu-u64-octets-aux 8 (nfix n) nil))

(defun fn-cu-octets-value (xs acc)
  (declare (xargs :guard (natp acc)))
  (if (consp xs)
      (fn-cu-octets-value (cdr xs) (+ (* 256 acc) (nfix (car xs))))
    acc))

