; Packed access: exact binary bytes, invalid inputs, and index-bound teeth.
(in-package "ACL2")
(include-book "../../books/packed-octet-access")
(include-book "../../books/defkeystone")
(include-book "must-fail-checked")

(assert-event
 (let ((n (fn-bch-pack '(0 255 13 10 0))))
  (and (equal (fn-poa-length n) 5)
       (equal (fn-poa-octet 0 n) 0)
       (equal (fn-poa-octet 1 n) 255)
       (equal (fn-poa-octet 2 n) 13)
       (equal (fn-poa-octet 3 n) 10)
       (equal (fn-poa-octet 4 n) 0))))

; Total length follows UNPACK even when the high digit is not sentinel 1.
(assert-event
 (and (equal (fn-poa-length 0) 0)
      (equal (fn-poa-length 255) 0)
      (equal (fn-poa-length 65535) 1)
      (equal (fn-poa-octet 0 65535) 255)
      (equal (fn-poa-length -1) 0)
      (equal (fn-poa-length :bad) 0)))

(defteeth fn-poa-length-is-unpack-length
 :claim (() (equal (fn-poa-length n) (len (fn-bch-unpack n))))
 :subject fn-poa-length
 :witness ((n (fn-bch-pack '(0 255 13 10 0))))
 :breaks ()
 :mutations
 ((lost-byte
   (:conclusion (equal (fn-poa-length n)
                       (len (fn-bch-unpack (floor n 256)))))
   ((n (fn-bch-pack '(0 255 13 10 0))))
   :fault "Discarding a low digit loses a body byte, including zero.")))

(defteeth fn-poa-octet-is-indexed-octet
 :claim (((in-range (< (nfix index) (len (fn-bch-unpack n)))))
         (equal (fn-poa-octet index n) (nth index (fn-bch-unpack n))))
 :subject fn-poa-octet
 :witness ((index 3) (n (fn-bch-pack '(0 255 13 10 0))))
 :breaks ((in-range ((index 1) (n 257))))
 :mutations
 ((next-byte
   (:conclusion (equal (fn-poa-octet (+ 1 index) n)
                       (nth index (fn-bch-unpack n))))
   ((index 3) (n (fn-bch-pack '(0 255 13 10 0))))
   :fault "Advancing the packed index reads zero instead of LF.")))
