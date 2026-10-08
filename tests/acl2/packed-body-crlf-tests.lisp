; Packed body framing is exactly the parser's list specification.
(in-package "ACL2")
(include-book "../../books/packed-body-crlf")
(include-book "../../books/defkeystone")
(include-book "must-fail-checked")

(assert-event
 (and (fn-art-body-crlfp (fn-bch-pack '(0 255 13 10 65 13 10 0)))
      (fn-art-body-crlfp 1)
      (fn-art-body-crlfp 256)
      (not (fn-art-body-crlfp (fn-bch-pack '(13))))
      (not (fn-art-body-crlfp (fn-bch-pack '(10))))
      (not (fn-art-body-crlfp (fn-bch-pack '(13 65))))
      (not (fn-art-body-crlfp (fn-bch-pack '(13 10 10))))
      (not (fn-art-body-crlfp (fn-bch-pack '(13 13 10))))
      (not (fn-art-body-crlfp (fn-bch-pack '(65 13 10 13))))))

; No packed-validity hypothesis: even malformed naturals follow UNPACK.
(assert-event
 (and (fn-art-body-crlfp :bad)
      (fn-art-body-crlfp -1)
      (fn-art-body-crlfp 255)
      (not (fn-art-body-crlfp 525))
      (equal (fn-bch-unpack 525) '(13))))

(defteeth fn-art-body-crlfp-refines
 :claim (() (equal (fn-art-body-crlfp body)
                   (fn-article-body-crlfp (fn-bch-unpack body))))
 :subject fn-art-body-crlfp
 :witness ((body (fn-bch-pack '(0 255 13 10 65 0))))
 :breaks ()
 :mutations
 ((skip-body-check
   (:conclusion (equal t (fn-article-body-crlfp (fn-bch-unpack body))))
   ((body (fn-bch-pack '(65 10))))
   :fault "Accepting all packed bodies misses the parser's bare-LF refusal.")
  (drop-final-cr
   (:conclusion (equal (fn-art-body-crlfp (fn-bch-pack '(65)))
                       (fn-article-body-crlfp (fn-bch-unpack body))))
   ((body (fn-bch-pack '(65 13))))
   :fault "Truncating the final CR incorrectly accepts an incomplete pair.")))
