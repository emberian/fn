; PRF-1132: actual table read -> reviewed standalone object-family domain.
; No whole-table validation or full compiled caller/decoder/job tariff.
; The explicit entry upper bound is proved redundant from natural entry,
; current fixed table length and one pointwise typed read.
(in-package "ACL2")
(include-book "payload-table-runtime-domain")
(include-book "assumptions-selected-runtime-table")

(local
 (defthm fn-paw-table-nth-past-end
   (implies (and (natp i) (<= (len xs) i)) (equal (nth i xs) nil))
   :hints (("Goal" :induct (nth i xs) :in-theory (enable nth len)))))
(encapsulate
 ()
 (local (include-book "arithmetic-5/top" :dir :system))
 (defthm fn-paw-typed-table-read-establishes-entry-bound
   (implies (and (natp e) (fn-zin-tab-okp fn-zin-tab)
                 (fn-cbor-octetp (fn-zin-tab-get (* 2 e) fn-zin-tab)))
            (< e *fn-zin-tab-entries*))
   :rule-classes nil
   :hints (("Goal" :in-theory (enable fn-zin-tab-okp fn-zin-tab-get
                                     fn-zin-tab-len fn-cbor-octetp)))))

(defthm fn-paw-actual-table-read-establishes-selected-object-domain
 (implies (and (natp e)
               (fn-zin-tab-okp fn-zin-tab)
               (fn-cbor-octetp (fn-zin-tab-get (* 2 e) fn-zin-tab))
               (fn-cbor-octetp (fn-zin-tab-get (+ 1 (* 2 e)) fn-zin-tab)))
          (fn-srp-table-object-domain-p
            e (fn-zin-tab-get (* 2 e) fn-zin-tab)
            (fn-zin-tab-get (+ 1 (* 2 e)) fn-zin-tab)
            (fn-zin-tab-len fn-zin-tab)))
 :rule-classes nil
 :hints (("Goal" :use fn-paw-typed-table-read-establishes-entry-bound
          :in-theory (enable fn-srp-table-object-domain-p
                                    fn-zin-tab-okp fn-cbor-octetp))))

(defthm fn-paw-actual-table-read-object-workspace-by-definition
 (implies (and (fn-srp-table-coordinate-p coordinate body)
               (natp e)
               (fn-zin-tab-okp fn-zin-tab)
               (fn-cbor-octetp (fn-zin-tab-get (* 2 e) fn-zin-tab))
               (fn-cbor-octetp (fn-zin-tab-get (+ 1 (* 2 e)) fn-zin-tab)))
          (equal (fn-assume-srp-table-object-octets
                   e (fn-zin-tab-get (* 2 e) fn-zin-tab)
                   (fn-zin-tab-get (+ 1 (* 2 e)) fn-zin-tab)
                   (fn-zin-tab-len fn-zin-tab) coordinate body) 0))
 :rule-classes nil
 :hints (("Goal" :in-theory (disable fn-srp-table-object-domain-p)
          :use ((:instance fn-paw-actual-table-read-establishes-selected-object-domain)
                (:instance fn-assume-srp-table-object-path-bound
                 (entry e) (low (fn-zin-tab-get (* 2 e) fn-zin-tab))
                 (high (fn-zin-tab-get (+ 1 (* 2 e)) fn-zin-tab))
                 (table-length (fn-zin-tab-len fn-zin-tab)))))))
