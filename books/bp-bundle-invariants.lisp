; books/bp-bundle-invariants.lisp -- the keystones of the whole-bundle codec.
;
; Three, in the shape the primary block's keystones have
; (books/bp-primary-invariants):
;
;   fn-bpb-decode-of-encode                       every bundle decodes back
;   fn-bpb-accepted-input-is-canonical-by-construction
;                                                 an accepted input IS the
;                                                 encoding of what was accepted
;   fn-bpb-decode-yields-bundle                   and what was accepted is a
;                                                 bundle, so its block numbers
;                                                 are distinct and its payload
;                                                 block is number 1
;
; plus the bound: `fn-bpb-decode-refuses-overlong-input`, which fires from the
; preflight alone and before any octet is examined.
;
; The primary block inside the bundle is `fn-bpp-decode`'s, not a second
; decoder's: `fn-bpc-dec` locates the end of its CBOR item and
; `fn-bpc-dec-reencodes-consumed-prefix` says the located prefix is exactly the
; item, so the octets handed to `fn-bpp-decode` are the primary block's own.

(in-package "ACL2")

(include-book "bp-bundle")

;; This book opens `books/bp-bundle`'s own definitions, and nothing else.
;; The records stay opaque: `fn-bpb-block-internals` and
;; `fn-bpb-bundle-internals` are NOT enabled, so no goal here is ever about
;; `car` of a record.  `fn-bpc-vocabulary` is enabled at the forms that need
;; it and never book-wide -- proof-style.md, "never enable a vocabulary
;; book-wide", measured twice on 2026-09-20.
(local (in-theory (enable fn-bpb-vocabulary)))

;; The three list facts `books/bp-bundle` keeps local, restated here for the
;; same reason: octet-ness of an append must be settled by a rule, not by
;; `fn-cbor-octet-listp` opening over a long list.
(local
 (defthm fn-bpbi-octet-listp-of-append
   (implies (and (fn-cbor-octet-listp a) (fn-cbor-octet-listp b))
            (fn-cbor-octet-listp (append a b)))
   :hints (("Goal" :in-theory (enable fn-cbor-octet-listp)))))

(local
 (defthm fn-bpbi-octet-listp-of-cons
   (implies (and (fn-cbor-octetp h) (fn-cbor-octet-listp xs))
            (fn-cbor-octet-listp (cons h xs)))
   :hints (("Goal" :in-theory (enable fn-cbor-octet-listp)))))

(local
 (defthm fn-bpbi-octet-listp-implies-true-listp
   (implies (fn-cbor-octet-listp xs) (true-listp xs))
   :rule-classes (:rewrite :forward-chaining)
   :hints (("Goal" :in-theory (enable fn-cbor-octet-listp)))))

; -----------------------------------------------------------------------------
; Octets out.

(defthm fn-bpb-encode-block-is-consp
  (consp (fn-bpb-encode-block b)))

(defthm fn-bpb-encode-block-head
  (equal (car (fn-bpb-encode-block b))
         (if (equal (fn-bpb-block-crc-type b) 0)
             *fn-bpb-block-head-5*
           *fn-bpb-block-head-6*)))

; -----------------------------------------------------------------------------
; The two field readers, each against the encoder that wrote the field.

(defthm fn-bpb-take-uint-of-argument
  (implies (and (fn-bpp-timep n) (fn-cbor-octet-listp rest))
           (equal (fn-bpb-take-uint (append (fn-bpc-argument 0 n) rest))
                  (fn-cbor-ok n rest)))
  :hints (("Goal"
           :use ((:instance fn-bpc-uint-head-decodes (n n) (rest rest))
                 (:instance fn-bpc-uint-head-range (n n))
                 (:instance fn-bpc-argument-is-consp (major 0) (n n)))
           :in-theory (e/d (fn-bpc-car-of-append fn-bpc-cdr-of-append)
                           (fn-bpc-argument fn-bpc-decode-head
                            fn-bpc-decode-argument fn-cbor-decode-argument)))))

(defthm fn-bpb-take-bytes-of-argument
  (implies (and (fn-cbor-octet-listp data) (fn-cbor-octet-listp rest)
                (natp bound) (<= (len data) bound)
                (<= bound *fn-bpc-max-uint*))
           (equal (fn-bpb-take-bytes
                   (append (fn-bpc-argument 2 (len data)) (append data rest))
                   bound)
                  (fn-cbor-ok data rest)))
  :hints (("Goal"
           :use ((:instance fn-bpc-bytes-head-decodes
                            (n (len data)) (rest (append data rest)))
                 (:instance fn-bpc-bytes-head-range (n (len data)))
                 (:instance fn-bpc-argument-is-consp (major 2) (n (len data))))
           :in-theory (e/d (fn-bpc-car-of-append fn-bpc-cdr-of-append
                            fn-bpc-len-of-append fn-bpc-take-of-append
                            fn-bpc-nthcdr-of-append fn-bpc-append-associativity)
                           (fn-bpc-argument fn-bpc-decode-head
                            fn-bpc-decode-argument fn-cbor-decode-argument)))))

; -----------------------------------------------------------------------------
; Keystone: one canonical block decodes back from its own encoding, with the
; octets after it returned untouched.

(defthm fn-bpb-decode-block-of-encode-block
  (implies (and (fn-bpb-blockp b) (fn-cbor-octet-listp rest))
           (equal (fn-bpb-decode-block (append (fn-bpb-encode-block b) rest))
                  (fn-cbor-ok b rest)))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (e/d (fn-bpb-decode-block fn-bpb-encode-block
                            fn-bpb-encode-block-with-crc
                            fn-bpc-append-associativity)
                           (fn-bpc-argument fn-bpb-block-crc
                            fn-bpc-decode-head fn-bpc-decode-argument
                            fn-cbor-decode-argument
                            fn-bpp-crc-octets fn-bpp-zero-crc)))))

; -----------------------------------------------------------------------------
; The block sequence.

(defthm fn-bpb-encode-blocks-of-append
  (implies (and (fn-bpb-block-listp xs) (fn-bpb-block-listp ys))
           (equal (fn-bpb-encode-blocks (append xs ys))
                  (append (fn-bpb-encode-blocks xs) (fn-bpb-encode-blocks ys))))
  :hints (("Goal" :in-theory (disable fn-bpb-encode-block))))

(defthm fn-bpb-front-final-reassemble
  (implies (and (true-listp xs) (consp xs))
           (equal (append (fn-bpb-front xs) (list (fn-bpb-final xs))) xs)))

(defthm fn-bpb-front-of-append-one
  (implies (true-listp xs)
           (equal (fn-bpb-front (append xs (list y))) xs)))

(defthm fn-bpb-final-of-append-one
  (equal (fn-bpb-final (append xs (list y))) y))

(defthm fn-bpb-block-listp-of-append
  (implies (and (fn-bpb-block-listp xs) (fn-bpb-block-listp ys))
           (fn-bpb-block-listp (append xs ys))))

(defthm fn-bpb-decode-blocks-of-encode-blocks
  (implies (and (fn-bpb-block-listp xs) (fn-cbor-octet-listp rest)
                (natp budget) (<= (len xs) budget))
           (equal (fn-bpb-decode-blocks
                   (append (fn-bpb-encode-blocks xs)
                           (cons *fn-bpb-array-break* rest))
                   budget)
                  (fn-cbor-ok xs rest)))
  :hints (("Goal"
           :induct (fn-bpb-decode-blocks
                    (append (fn-bpb-encode-blocks xs)
                            (cons *fn-bpb-array-break* rest))
                    budget)
           :in-theory (e/d (fn-bpc-append-associativity)
                           (fn-bpb-encode-block fn-bpb-decode-block
                            fn-bpb-block-crc)))))

; -----------------------------------------------------------------------------
; Keystone: decode of encode, over the whole bundle.

(defthm fn-bpb-payload-block-is-a-block
  (implies (fn-bpb-payload-blockp b) (fn-bpb-blockp b)))

(defthm fn-bpb-bundle-tail-are-octets
  (implies (fn-bpb-bundlep bundle)
           (fn-cbor-octet-listp
            (append (fn-bpb-encode-blocks (fn-bpb-bundle-blocks bundle))
                    (append (fn-bpb-encode-block (fn-bpb-bundle-payload bundle))
                            (list *fn-bpb-array-break*)))))
  :hints (("Goal" :in-theory (e/d (fn-cbor-octet-listp fn-cbor-octetp)
                                  (fn-bpb-encode-block fn-bpb-encode-blocks)))))

(defthm fn-bpb-decode-of-encode
  (implies (and (fn-bpb-bundlep bundle) (natp limit)
                (fn-cbor-at-mostp (fn-bpb-encode bundle) limit))
           (equal (fn-bpb-decode (fn-bpb-encode bundle) limit)
                  (fn-cbor-ok bundle nil)))
  :hints (("Goal"
           :do-not-induct t
           :use ((:instance fn-bpc-decode-of-encode
                            (flg :item)
                            (x (fn-bpp-block-value
                                (fn-bpb-bundle-primary bundle)
                                (fn-bpp-block-crc
                                 (fn-bpb-bundle-primary bundle))))
                            (rest (append
                                   (fn-bpb-encode-blocks
                                    (fn-bpb-bundle-blocks bundle))
                                   (append
                                    (fn-bpb-encode-block
                                     (fn-bpb-bundle-payload bundle))
                                    (list *fn-bpb-array-break*))))
                            (budget *fn-bpc-max-items*))
                 (:instance fn-bpp-block-value-is-shape
                            (b (fn-bpb-bundle-primary bundle))
                            (crc-octets (fn-bpp-block-crc
                                         (fn-bpb-bundle-primary bundle))))
                 (:instance fn-bpp-block-value-cost
                            (b (fn-bpb-bundle-primary bundle))
                            (crc-octets (fn-bpp-block-crc
                                         (fn-bpb-bundle-primary bundle))))
                 (:instance fn-bpp-block-crc-is-octets
                            (b (fn-bpb-bundle-primary bundle)))
                 (:instance fn-bpp-block-crc-length
                            (b (fn-bpb-bundle-primary bundle)))
                 (:instance fn-bpp-decode-of-encode
                            (b (fn-bpb-bundle-primary bundle)))
                 (:instance fn-bpb-decode-blocks-of-encode-blocks
                            (xs (append (fn-bpb-bundle-blocks bundle)
                                        (list (fn-bpb-bundle-payload bundle))))
                            (rest nil)
                            (budget *fn-bpb-max-blocks*)))
           :in-theory (e/d (fn-bpb-decode fn-bpb-encode
                            fn-bpc-len-of-append fn-bpc-take-of-append
                            fn-bpc-append-associativity)
                           (fn-bpc-dec fn-bpc-enc fn-bpp-encode fn-bpp-decode
                            fn-bpb-encode-block fn-bpb-encode-blocks
                            fn-bpb-decode-block fn-bpb-decode-blocks
                            fn-bpp-block-value fn-bpp-block-crc
                            fn-bpc-decode-of-encode
                            fn-bpp-block-value-is-shape
                            fn-bpp-block-value-cost
                            fn-bpp-decode-of-encode
                            fn-bpb-decode-blocks-of-encode-blocks)))))

; -----------------------------------------------------------------------------
; Keystone: an accepted input is the encoding of the bundle it produced.

(defthm fn-bpb-decode-block-is-canonical-by-construction
  (implies (and (fn-cbor-octet-listp octets)
                (fn-cbor-result-okp (fn-bpb-decode-block octets)))
           (equal (append (fn-bpb-encode-block
                           (fn-cbor-result-value (fn-bpb-decode-block octets)))
                          (fn-cbor-result-rest (fn-bpb-decode-block octets)))
                  octets))
  :hints (("Goal" :in-theory (disable fn-bpb-encode-block fn-bpb-block-crc))))

(defthm fn-bpb-decode-blocks-are-canonical-by-construction
  (implies (and (fn-cbor-octet-listp octets)
                (fn-cbor-result-okp (fn-bpb-decode-blocks octets budget)))
           (equal (append (fn-bpb-encode-blocks
                           (fn-cbor-result-value
                            (fn-bpb-decode-blocks octets budget)))
                          (cons *fn-bpb-array-break*
                                (fn-cbor-result-rest
                                 (fn-bpb-decode-blocks octets budget))))
                  octets))
  :hints (("Goal"
           :induct (fn-bpb-decode-blocks octets budget)
           :in-theory (disable fn-bpb-decode-block fn-bpb-encode-block
                               fn-bpb-block-crc))))

(defthm fn-bpb-decode-yields-bundle
  (implies (fn-cbor-result-okp (fn-bpb-decode octets limit))
           (fn-bpb-bundlep (fn-cbor-result-value (fn-bpb-decode octets limit))))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (e/d (fn-bpb-decode)
                           (fn-bpc-dec fn-bpp-decode fn-bpb-decode-blocks
                            fn-bpb-encode-block fn-bpb-encode-blocks
                            fn-bpb-block-crc)))))

(defthm fn-bpb-accepted-input-is-canonical-by-construction
  (implies (and (fn-cbor-octet-listp octets)
                (fn-cbor-result-okp (fn-bpb-decode octets limit)))
           (equal (fn-bpb-encode (fn-cbor-result-value
                                  (fn-bpb-decode octets limit)))
                  octets))
  :hints (("Goal"
           :do-not-induct t
           :use ((:instance fn-bpc-dec-reencodes-consumed-prefix
                            (flg :item) (count 0) (octets (cdr octets))
                            (budget *fn-bpc-max-items*)))
           :in-theory (e/d (fn-bpb-decode fn-bpb-encode
                            fn-bpc-len-of-append fn-bpc-take-of-append)
                           (fn-bpc-dec fn-bpc-enc fn-bpp-decode fn-bpp-encode
                            fn-bpb-decode-blocks fn-bpb-encode-block
                            fn-bpb-encode-blocks fn-bpb-block-crc
                            fn-bpc-dec-reencodes-consumed-prefix)))))

; -----------------------------------------------------------------------------
; Keystone: bounds before allocation.

(defthm fn-bpb-decode-refuses-overlong-input
  (implies (not (fn-cbor-at-mostp octets limit))
           (equal (fn-bpb-decode octets limit) (fn-cbor-error :limit)))
  :hints (("Goal" :in-theory (enable fn-bpb-decode))))

(defthm fn-bpb-decode-blocks-with-no-budget-accepts-only-the-break
  (implies (and (consp octets) (not (equal (car octets) *fn-bpb-array-break*)))
           (equal (fn-bpb-decode-blocks octets 0)
                  (fn-cbor-error :too-many-blocks)))
  :hints (("Goal" :in-theory (enable fn-bpb-decode-blocks))))

(defthm fn-bpb-decoded-data-is-within-bound
  (implies (and (fn-cbor-octet-listp octets)
                (fn-cbor-result-okp (fn-bpb-decode-block octets)))
           (<= (len (fn-bpb-block-data
                     (fn-cbor-result-value (fn-bpb-decode-block octets))))
               *fn-bpb-max-data*))
  :rule-classes :linear
  :hints (("Goal" :in-theory (disable fn-bpb-encode-block fn-bpb-block-crc))))

; -----------------------------------------------------------------------------
; Export theory.
;
; The keystones leave enabled; the field-reader and list lemmas are proof
; vocabulary and are withdrawn under a name.

(deftheory fn-bpb-invariants-vocabulary
  '(fn-bpb-encode-block-is-consp
    fn-bpb-encode-block-head fn-bpb-take-uint-of-argument
    fn-bpb-take-bytes-of-argument fn-bpb-encode-blocks-of-append
    fn-bpb-front-final-reassemble fn-bpb-front-of-append-one
    fn-bpb-final-of-append-one fn-bpb-block-listp-of-append
    fn-bpb-payload-block-is-a-block fn-bpb-bundle-tail-are-octets
    fn-bpb-decode-blocks-of-encode-blocks
    fn-bpb-decode-block-of-encode-block))

(in-theory (disable fn-bpb-invariants-vocabulary))
