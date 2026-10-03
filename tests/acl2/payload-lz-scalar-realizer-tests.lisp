(in-package "ACL2")
(include-book "../../books/payload-lz-scalar-realizer")
; Existing assumption boundary, no new constraint. Constrained durable values
; cannot be evaluated by assert-event; these are literal logical positives.
; Physical byte/cold/refusal discrimination lives in native_lz_scalar_raw.
(local
 (defthm fn-lz-scalar-zero-positive
   (equal (fn-durable-realize-lz-octet 7 100 320 120 40 99 3 nil 0)
          (nth 0 (fn-lzr-lz-value nil (fn-durable-octets 7 120 40) 3)))
   :rule-classes nil))
(local
 (defthm fn-lz-scalar-interior-positive
   (equal (fn-durable-realize-lz-octet 7 100 320 120 40 99 3 nil 1)
          (nth 1 (fn-lzr-lz-value nil (fn-durable-octets 7 120 40) 3)))
   :rule-classes nil))
(local
 (defthm fn-lz-scalar-past-end-positive
   (equal (fn-durable-realize-lz-octet 7 100 320 120 40 99 3 nil 3)
          (nth 3 (fn-lzr-lz-value nil (fn-durable-octets 7 120 40) 3)))
   :rule-classes nil))
