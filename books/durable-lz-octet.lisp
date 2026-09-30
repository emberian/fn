; Scalar boundary for the existing A-DURABLE-LZ realizer.
; No new constrained function or decoder assumption is introduced. Native
; window realization must establish this exact scalar value before supply.
(in-package "ACL2")
(include-book "assumptions-durable")
(include-book "octets-stobj")

(defun fn-durable-realize-lz-octet (file eoff elen poff plen trailer n dict i)
  (declare (xargs :guard t))
  (fn-oct-nth i (fn-durable-realize-lz file eoff elen poff plen trailer n dict)))

(defthm fn-durable-realize-lz-octet-is-nth-of-existing-realizer-by-definition
  (equal (fn-durable-realize-lz-octet file eoff elen poff plen trailer n dict i)
         (nth i (fn-durable-realize-lz file eoff elen poff plen trailer n dict)))
  :hints (("Goal" :in-theory (enable fn-durable-realize-lz-octet)))
  :rule-classes nil)

(defthm fn-durable-realize-lz-octet-is-existing-durable-decoded-value
  (equal (fn-durable-realize-lz-octet file eoff elen poff plen trailer n dict i)
         (nth i (fn-lzr-lz-value dict (fn-durable-octets file poff plen) n)))
  :hints (("Goal" :in-theory (enable fn-durable-realize-lz-octet))))

(in-theory (disable fn-durable-realize-lz-octet))
