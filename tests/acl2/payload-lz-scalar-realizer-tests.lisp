(in-package "ACL2")
(include-book "../../books/payload-lz-scalar-realizer")
(include-book "../../books/defkeystone")
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

; TEETH-21 BEGIN
; No hypothesis, so the teeth are the positive witness: the durable values
; are constrained (no evaluator runs them), so it is the literal ground
; theorem above, and no mutant can be evaluated.
(defteeth fn-durable-realize-lz-octet-is-decoded-nth
  :claim (() (equal (fn-durable-realize-lz-octet
                     file eoff elen poff compressed trailer decoded dict i)
                    (nth i (fn-lzr-lz-value dict
                             (fn-durable-octets file poff compressed) decoded))))
  :subject fn-durable-realize-lz-octet
  :witness ((file 7) (eoff 100) (elen 320) (poff 120) (compressed 40) (trailer 99) (decoded 3) (dict nil) (i 0))
  :witness-lemma fn-lz-scalar-zero-positive
  :mutations (:not-applicable "no hypothesis to remove; the realized octet is a constrained durable read, so no mutant evaluates"))
; TEETH-21 END
