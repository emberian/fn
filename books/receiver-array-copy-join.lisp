; Conditional semantic join for actual fnn-owner-receiver-fill. Raw SAME-
; provider identities and effective failure quarantine are qualification
; premises, not established by a differential or a supplied model pair.
(in-package "ACL2")
(include-book "receiver-provider-refinement")
(include-book "assumptions-rx-array-copy")
(defthm fn-rxp-list-from-cons-shift
 (implies (and (natp i) (natp n))
          (equal (fn-oct-list-from (+ 1 i) (+ 1 n) (cons a b))
                 (fn-oct-list-from i n b)))
 :hints (("Goal" :induct (fn-oct-list-from i n b)
                 :in-theory (enable fn-oct-list-from))))
(defthm fn-rxp-copy-prefix-is-full-source
 (implies (and (true-listp source) (<= (len source) (len destination)))
          (equal (fn-oct-list-from 0 (len source)
                     (fn-rxac-copy-prefix source destination (len source)))
                 source))
 :hints (("Goal" :induct (fn-rxac-copy-prefix source destination (len source))
                 :in-theory (enable fn-rxac-copy-prefix fn-oct-list-from))))
(defthm fn-rxp-array-bytes-are-registered-bytes
 (equal (fn-rxac-bytes-p bytes) (fn-cbor-octet-listp bytes))
 :hints (("Goal" :induct (fn-rxac-bytes-p bytes)
                 :in-theory (enable fn-rxac-bytes-p fn-cbor-octet-listp
                                    fn-cbor-octetp))))
(defthm fn-rxp-copy-prefix-preserves-byte-domain
 (implies (and (fn-rxac-bytes-p source) (fn-rxac-bytes-p destination))
          (fn-rxac-bytes-p (fn-rxac-copy-prefix source destination count)))
 :hints (("Goal" :induct (fn-rxac-copy-prefix source destination count)
                 :in-theory (enable fn-rxac-copy-prefix fn-rxac-bytes-p))))
(defthm fn-rxp-registered-array-domain-by-definition
 (equal (fn-octets$c-bufp bytes) (fn-cbor-octet-listp bytes))
 :hints (("Goal" :induct (fn-cbor-octet-listp bytes)
          :in-theory (enable fn-octets$c-bufp fn-cbor-octet-listp
                              fn-cbor-octetp unsigned-byte-p integer-range-p))))
(defthm fn-rxp-two-field-length-by-definition
 (equal (len (list a b)) 2))
(defthm fn-rxp-assumed-array-copy-refines-reference
 (implies
  (and (fn-rxac-domain-p source-id destination-id source destination old-fill
                         (len source) t)
       (equal (mv-nth 0 (fn-rxp-fill-range token (len source) limits fuel
                                         fn-rx-provider)) :receive-copy))
  (let ((observation
          (fn-assume-rxac-observe source-id destination-id source destination
                                  old-fill (len source) t association :copied)))
   (fn-rxp-child-corr
    (list (nth 4 observation) (nth 5 observation))
    (mv-nth 2 (fn-rxp-fill-reference token source limits fuel fn-rx-provider)))))
 :hints (("Goal"
  :use ((:instance fn-assume-rxac-observation-contract
           (end (len source)) (stable t) (outcome :copied))
        (:instance fn-rxp-copy-prefix-preserves-byte-domain
          (count (len source))))
  :in-theory (e/d (fn-rxac-domain-p fn-rxac-observation-contract-p
                   fn-rxp-child-corr fn-octets$corr fn-octets$cp)
                  (fn-rxp-fill-range
                   fn-rxp-fill-reference fn-rxac-copy-prefix fn-octets$c-bufp
                   fn-cbor-octet-listp fn-oct-list-from nth update-nth len true-listp))))
 :rule-classes nil)
