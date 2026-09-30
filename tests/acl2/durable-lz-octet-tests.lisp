(in-package "ACL2")
(include-book "../../books/durable-lz-octet")

; Scalar interface equals the existing realizer at a nonzero payload index.
; The durable bytes remain the existing named I/O premise, not a fabricated
; host equality or an alternative decoder model.
(defthm durable-lz-octet-existing-realizer-positive
  (and (equal (fn-durable-realize-lz-octet 7 100 320 120 40 99 250 nil 200)
              (nth 200 (fn-durable-realize-lz 7 100 320 120 40 99 250 nil)))
       (equal (fn-durable-realize-lz-octet 7 100 320 120 40 99 250 nil 200)
              (nth 200 (fn-lzr-lz-value nil (fn-durable-octets 7 120 40) 250))))
  :hints (("Goal" :use (:instance
    fn-durable-realize-lz-octet-is-nth-of-existing-realizer-by-definition
    (file 7) (eoff 100) (elen 320) (poff 120) (plen 40)
    (trailer 99) (n 250) (dict nil) (i 200))))
  :rule-classes nil)

; Mutation witness: a singleton at the whole-list boundary loses nonzero I.
(assert-event (and (equal (fn-oct-nth 1 '(65 66)) 66)
                   (not (equal (fn-oct-nth 1 '(66)) 66))))
