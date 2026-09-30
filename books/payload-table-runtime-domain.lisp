; PRF-1132 / SCN-1039: actual Huffman table read scalar/offset domain.
; Pointwise typed reads, not a whole-table validation or allocation tariff.
(in-package "ACL2")
(include-book "payload-window-width")

(defthm fn-paw-actual-table-read-scalar-domain
 (implies (and (natp e) (< e *fn-zin-tab-entries*)
               (fn-cbor-octetp (fn-zin-tab-get (* 2 e) fn-zin-tab))
               (fn-cbor-octetp (fn-zin-tab-get (+ 1 (* 2 e)) fn-zin-tab)))
          (and (natp (* 2 e)) (< (* 2 e) *fn-zin-tab-octets*)
               (natp (+ 1 (* 2 e)))
               (< (+ 1 (* 2 e)) *fn-zin-tab-octets*)
               (natp (* 256 (fn-zin-tab-get (+ 1 (* 2 e)) fn-zin-tab)))
               (<= (* 256 (fn-zin-tab-get (+ 1 (* 2 e)) fn-zin-tab)) 65280)
               (natp (fn-zin-tget e fn-zin-tab))
               (< (fn-zin-tget e fn-zin-tab) 65536)))
 :rule-classes nil
 :hints (("Goal" :in-theory (enable fn-zin-tget fn-cbor-octetp))))
