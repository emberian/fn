; fn: the deterministic CBOR vocabulary that RFC 9171 section 4.3.1 needs.
;
; `books/cbor.lisp` carries fn's original profile: major type 0 unsigned
; integers to 2^32-1 and major type 2 definite byte strings.  The BPv7 primary
; block needs three more things and nothing else:
;
;   * definite-length arrays (major type 4) of bounded arity -- the block
;     itself, each endpoint ID, the ipn scheme-specific part, the creation
;     timestamp, and the Hop Count block's data;
;   * definite-length text strings (major type 3) -- the dtn scheme-specific
;     part;
;   * unsigned integers to 2^64-1 -- DTN time is in milliseconds since 2000
;     and, as RFC 9171 section 4.2.6 warns, "will nearly always exceed
;     (2^32 - 1)".  The existing `fn-cbor-decode-unsigned` answers
;     `:unsupported` for CBOR additional information 27, so this book carries a
;     parallel decoder rather than changing the existing one.
;
; Negative integers, maps, tags, floats, simple values and every
; indefinite-length form stay outside the profile, as does the CBOR "break"
; stop code: additional information 27 is the largest head accepted and 28
; through 31 are refused before any argument is read.
;
; Canonicality is RFC 8949 section 4.2.1 deterministic encoding: definite
; lengths everywhere and the shortest argument form for every head.  The
; decoder checks the head it was given against the head the encoder would have
; produced, so a non-minimal argument is rejected rather than normalized.
;
; Every bound is checked before the corresponding allocation: the whole input
; is length-preflighted before any octet is examined, an array's arity is
; checked before any element is decoded, and a string's claimed length is
; checked before `take` copies anything.
;
; The item budget is the decoder's termination measure and its work bound in
; one: a decode spends one unit per CBOR item and one per list step, so total
; item count and nesting depth are both bounded by the budget.

(in-package "ACL2")

(include-book "cbor-invariants")

; This is the 64-bit CBOR profile over the same primitives, so it opens the
; bounded profile locally.  Results stay opaque.
(local (in-theory (enable fn-cbor-codec-vocabulary
                          fn-cbor-invariants-vocabulary
                          fn-cbor-record-vocabulary)))

(local (include-book "arithmetic/top" :dir :system))

; `append` associativity is not available as a named rule in this image, and
; several proofs below need to re-associate an encoded prefix.
(defthm fn-bpc-append-associativity
  (equal (append (append x y) z) (append x (append y z))))

; List rules the encoder/decoder proofs need to see through an encoded prefix.
(defthm fn-bpc-car-of-append
  (implies (consp x)
           (equal (car (append x y)) (car x))))

(defthm fn-bpc-cdr-of-append
  (implies (consp x)
           (equal (cdr (append x y)) (append (cdr x) y))))

(defthm fn-bpc-consp-of-append
  (implies (consp x)
           (consp (append x y))))

(defthm fn-bpc-append-nil
  (implies (true-listp x)
           (equal (append x nil) x)))

(defthm fn-bpc-len-of-append
  (equal (len (append x y)) (+ (len x) (len y))))

(defthm fn-bpc-take-of-append
  (implies (true-listp x)
           (equal (take (len x) (append x y)) x))
  :hints (("Goal" :induct (append x y))))

(defthm fn-bpc-nthcdr-of-append
  (equal (nthcdr (len x) (append x y)) y)
  :hints (("Goal" :induct (append x y))))

; The result record, as rules rather than as definitions.  Keeping
; `fn-cbor-result-okp/value/rest` closed is what lets the octet, shape and
; length lemmas below match inside the decoder's induction; unfolding them to
; `car`/`cadr`/`caddr` silently defeats every one of those rules.
(defthm fn-bpc-fields-of-ok
  (and (fn-cbor-result-okp (fn-cbor-ok value rest))
       (equal (fn-cbor-result-value (fn-cbor-ok value rest)) value)
       (equal (fn-cbor-result-rest (fn-cbor-ok value rest)) rest)))

(defthm fn-bpc-fields-of-error
  (and (not (fn-cbor-result-okp (fn-cbor-error reason)))
       (equal (fn-cbor-result-value (fn-cbor-error reason)) reason)
       (equal (fn-cbor-result-rest (fn-cbor-error reason)) nil)))

(defthm fn-bpc-results-are-true-lists
  (and (true-listp (fn-cbor-ok value rest))
       (true-listp (fn-cbor-error reason))))

(local (in-theory (disable fn-cbor-ok fn-cbor-error fn-cbor-result-okp
                           fn-cbor-result-value fn-cbor-result-rest)))


; -----------------------------------------------------------------------------
; Bounds

(defconst *fn-bpc-max-uint* 18446744073709551615)
; The longest dtn-scheme scheme-specific part fn will parse.  RFC 9171 sets no
; length limit on a dtn URI; this is a local policy bound, not an RFC rule.
(defconst *fn-bpc-max-text* 1024)
; RFC 9171 section 4.3.1 uses arity 8 to 11; endpoint IDs, the creation
; timestamp and the Hop Count data use arity 2.
(defconst *fn-bpc-max-arity* 16)
; The only byte string RFC 9171 section 4.3.1 puts in a primary block is the
; CRC, of two or four octets.  Keeping the item bound small is what makes the
; whole-block length bound below fit inside the input preflight.
(defconst *fn-bpc-max-bytes* 64)
; One unit per decoded item and one per list step.
(defconst *fn-bpc-max-items* 128)
(defconst *fn-bpc-max-input* 65536)

; -----------------------------------------------------------------------------
; 64-bit big-endian arguments
;
; `fn-bpc-u32-octets` is total: every result octet is a `mod ... 256`, so a
; natural larger than 2^32-1 cannot produce a non-octet.  The agreement lemma
; below ties it to the existing `fn-cbor-u32-bytes` on that function's declared
; domain, so there is one deterministic encoder for the shared range.

(local
 (defthm fn-bpc-floor-256-bound
   (implies (and (integerp x) (<= 0 x) (integerp k) (< x (* 256 k)))
            (< (floor x 256) k))
   :rule-classes :linear))

; The same successive-quotient chain `fn-cbor-u32-bytes` uses, with a `mod` on
; the leading octet so that the function is total over the naturals.
(defun fn-bpc-u32-octets (n)
  (declare (xargs :guard (natp n)))
  (let* ((q0 (floor n 256))
         (q1 (floor q0 256))
         (q2 (floor q1 256)))
    (list (mod q2 256)
          (mod q1 256)
          (mod q0 256)
          (mod n 256))))

(defun fn-bpc-u64-bytes (n)
  (declare (xargs :guard (natp n)))
  (append (fn-bpc-u32-octets (floor n 4294967296))
          (fn-bpc-u32-octets (mod n 4294967296))))

(defun fn-bpc-u64-from (xs)
  (declare (xargs :guard (and (fn-cbor-octet-listp xs)
                              (consp xs) (consp (cdr xs))
                              (consp (cddr xs)) (consp (cdddr xs))
                              (consp (cddddr xs)) (consp (cdr (cddddr xs)))
                              (consp (cddr (cddddr xs)))
                              (consp (cdddr (cddddr xs))))))
  (+ (* 4294967296 (fn-cbor-u32-from xs))
     (fn-cbor-u32-from (cddddr xs))))

(defthm fn-bpc-u32-octets-are-octets
  (implies (natp n)
           (fn-cbor-octet-listp (fn-bpc-u32-octets n)))
  :hints (("Goal" :in-theory (e/d (fn-cbor-octet-listp fn-cbor-octetp)
                                  (floor mod floor-floor-integer)))))

(defthm fn-bpc-u32-octets-fields
  (and (consp (fn-bpc-u32-octets n))
       (consp (cdr (fn-bpc-u32-octets n)))
       (consp (cddr (fn-bpc-u32-octets n)))
       (consp (cdddr (fn-bpc-u32-octets n)))
       (not (cddddr (fn-bpc-u32-octets n)))
       (true-listp (fn-bpc-u32-octets n))
       (equal (len (fn-bpc-u32-octets n)) 4))
  :hints (("Goal" :in-theory (disable floor mod cancel-floor-+-basic
                                      cancel-mod-+-basic rewrite-floor-mod
                                      rewrite-mod-mod floor-floor-integer))))

; The four-octet argument sits at the front of whatever follows it.
(defthm fn-bpc-u32-octets-prefix-fields
  (and (consp (append (fn-bpc-u32-octets n) xs))
       (consp (cdr (append (fn-bpc-u32-octets n) xs)))
       (consp (cddr (append (fn-bpc-u32-octets n) xs)))
       (consp (cdddr (append (fn-bpc-u32-octets n) xs)))
       (equal (cddddr (append (fn-bpc-u32-octets n) xs)) xs)
       (equal (fn-cbor-u32-from (append (fn-bpc-u32-octets n) xs))
              (fn-cbor-u32-from (fn-bpc-u32-octets n))))
  :hints (("Goal" :in-theory (e/d (fn-cbor-u32-from)
                                  (floor mod cancel-floor-+-basic
                                   cancel-mod-+-basic rewrite-floor-mod
                                   rewrite-mod-mod floor-floor-integer)))))

; One owner for the shared range: on `fn-cbor-u32-bytes`'s declared domain the
; total form computes the same four octets.
(defthm fn-bpc-u32-octets-agree-with-fn-cbor-u32-bytes
  (implies (and (natp n) (< n 4294967296))
           (equal (fn-bpc-u32-octets n) (fn-cbor-u32-bytes n)))
  :hints (("Goal" :in-theory (enable fn-cbor-u32-bytes))))

(defthm fn-bpc-u32-octets-invert
  (implies (and (natp n) (< n 4294967296))
           (equal (fn-cbor-u32-from (fn-bpc-u32-octets n)) n))
  :hints (("Goal" :in-theory (disable fn-bpc-u32-octets fn-cbor-u32-bytes
                                      fn-cbor-u32-from))))

; The existing two-octet argument has `fn-cbor-u16-prefix-fields` in
; `cbor-invariants`; the four-octet one needs the same shape.
(defthm fn-bpc-u32-bytes-prefix-fields
  (and (consp (append (fn-cbor-u32-bytes n) xs))
       (consp (cdr (append (fn-cbor-u32-bytes n) xs)))
       (consp (cddr (append (fn-cbor-u32-bytes n) xs)))
       (consp (cdddr (append (fn-cbor-u32-bytes n) xs)))
       (equal (cddddr (append (fn-cbor-u32-bytes n) xs)) xs)
       (equal (fn-cbor-u32-from (append (fn-cbor-u32-bytes n) xs))
              (fn-cbor-u32-from (fn-cbor-u32-bytes n))))
  :hints (("Goal" :in-theory (e/d (fn-cbor-u32-from fn-cbor-u32-bytes)
                                  (floor mod cancel-floor-+-basic
                                   cancel-mod-+-basic rewrite-floor-mod
                                   rewrite-mod-mod floor-floor-integer)))))

; From here on the base-256 conversions are opaque: every later proof uses the
; inverse, length and octet lemmas above rather than reopening the arithmetic.
(in-theory (disable fn-bpc-u32-octets
                    (:executable-counterpart fn-bpc-u32-octets)
                    fn-bpc-u32-octets-agree-with-fn-cbor-u32-bytes
                    fn-cbor-u16-bytes fn-cbor-u32-bytes fn-bpc-u64-bytes
                    fn-cbor-u16-from fn-cbor-u32-from fn-bpc-u64-from))

; Length facts about the now-opaque conversions.  `fn-bpc-argument-length-bound`
; below needs them once `fn-cbor-u16-bytes` and `fn-cbor-u32-bytes` are closed.
(defthm fn-bpc-u16-bytes-have-length-two
  (equal (len (fn-cbor-u16-bytes n)) 2)
  :hints (("Goal" :in-theory (enable fn-cbor-u16-bytes))))

(defthm fn-bpc-u32-bytes-have-length-four
  (equal (len (fn-cbor-u32-bytes n)) 4)
  :hints (("Goal" :in-theory (enable fn-cbor-u32-bytes))))

; Type facts about the now-opaque conversions, in the forms ACL2's guard
; proofs ask for.
(defthm fn-bpc-u16-from-is-a-number
  (implies (and (fn-cbor-octet-listp xs) (consp xs) (consp (cdr xs)))
           (and (natp (fn-cbor-u16-from xs))
                (integerp (fn-cbor-u16-from xs))
                (rationalp (fn-cbor-u16-from xs))
                (acl2-numberp (fn-cbor-u16-from xs))
                (<= 0 (fn-cbor-u16-from xs))))
  :hints (("Goal" :use fn-cbor-u16-from-bounds
           :in-theory (disable fn-cbor-u16-from-bounds))))

(defthm fn-bpc-u32-from-is-a-number
  (implies (and (fn-cbor-octet-listp xs) (consp xs) (consp (cdr xs))
                (consp (cddr xs)) (consp (cdddr xs)))
           (and (natp (fn-cbor-u32-from xs))
                (integerp (fn-cbor-u32-from xs))
                (rationalp (fn-cbor-u32-from xs))
                (acl2-numberp (fn-cbor-u32-from xs))
                (<= 0 (fn-cbor-u32-from xs))))
  :hints (("Goal" :use fn-cbor-u32-from-bounds
           :in-theory (disable fn-cbor-u32-from-bounds))))

(defthm fn-bpc-u64-bytes-fields
  (implies (natp n)
   (and (consp (append (fn-bpc-u64-bytes n) xs))
       (consp (cdr (append (fn-bpc-u64-bytes n) xs)))
       (consp (cddr (append (fn-bpc-u64-bytes n) xs)))
       (consp (cdddr (append (fn-bpc-u64-bytes n) xs)))
       (consp (cddddr (append (fn-bpc-u64-bytes n) xs)))
       (consp (cdr (cddddr (append (fn-bpc-u64-bytes n) xs))))
       (consp (cddr (cddddr (append (fn-bpc-u64-bytes n) xs))))
       (consp (cdddr (cddddr (append (fn-bpc-u64-bytes n) xs))))
       (equal (cddddr (cddddr (append (fn-bpc-u64-bytes n) xs))) xs)))
  :hints (("Goal" :in-theory (e/d (fn-bpc-u64-bytes fn-bpc-u32-octets)
                                  (floor mod cancel-floor-+-basic
                                   cancel-mod-+-basic rewrite-floor-mod
                                   rewrite-mod-mod floor-floor-integer)))))

(defthm fn-bpc-u64-bytes-have-eight-octets
  (implies (natp n)
   (and (consp (fn-bpc-u64-bytes n))
       (consp (cdr (fn-bpc-u64-bytes n)))
       (consp (cddr (fn-bpc-u64-bytes n)))
       (consp (cdddr (fn-bpc-u64-bytes n)))
       (consp (cddddr (fn-bpc-u64-bytes n)))
       (consp (cdr (cddddr (fn-bpc-u64-bytes n))))
       (consp (cddr (cddddr (fn-bpc-u64-bytes n))))
       (consp (cdddr (cddddr (fn-bpc-u64-bytes n))))
       (true-listp (fn-bpc-u64-bytes n))
       (equal (cddddr (cddddr (fn-bpc-u64-bytes n))) nil)
       (equal (len (fn-bpc-u64-bytes n)) 8)))
  :hints (("Goal" :in-theory (e/d (fn-bpc-u64-bytes fn-bpc-u32-octets)
                                  (floor mod cancel-floor-+-basic
                                   cancel-mod-+-basic rewrite-floor-mod
                                   rewrite-mod-mod floor-floor-integer)))))

(defthm fn-bpc-u64-bytes-are-octets
  (implies (natp n)
           (fn-cbor-octet-listp (fn-bpc-u64-bytes n)))
  :hints (("Goal"
           :in-theory (e/d (fn-bpc-u64-bytes)
                           (fn-bpc-u32-octets floor mod))
           :use ((:instance fn-bpc-u32-octets-are-octets
                            (n (floor n 4294967296)))
                 (:instance fn-bpc-u32-octets-are-octets
                            (n (mod n 4294967296)))))))

(defthm fn-bpc-u64-from-of-two-arguments
  (implies (and (natp hi) (< hi 4294967296)
                (natp lo) (< lo 4294967296))
           (equal (fn-bpc-u64-from
                   (append (fn-bpc-u32-octets hi)
                           (append (fn-bpc-u32-octets lo) xs)))
                  (+ (* 4294967296 hi) lo)))
  :hints (("Goal"
           :in-theory (e/d (fn-bpc-u64-from)
                           (fn-bpc-u32-octets fn-cbor-u32-from
                            floor mod cancel-floor-+-basic
                            cancel-mod-+-basic rewrite-floor-mod
                            rewrite-mod-mod floor-floor-integer)))))

(local
 (defthm fn-bpc-u64-halves-are-bounded
   (implies (and (natp n) (<= n *fn-bpc-max-uint*))
            (and (natp (floor n 4294967296))
                 (< (floor n 4294967296) 4294967296)
                 (natp (mod n 4294967296))
                 (< (mod n 4294967296) 4294967296)))))

(defthm fn-bpc-u64-from-u64-bytes
  (implies (and (natp n) (<= n *fn-bpc-max-uint*))
           (equal (fn-bpc-u64-from (append (fn-bpc-u64-bytes n) xs)) n))
  :hints (("Goal"
           :in-theory (e/d (fn-bpc-u64-bytes fn-bpc-append-associativity)
                           (fn-bpc-u32-octets fn-bpc-u64-from fn-cbor-u32-from
                            floor mod floor-=-x/y mod-=-0
                            mod-x-y-=-x-for-rationals
                            cancel-floor-+-basic cancel-mod-+-basic
                            rewrite-floor-mod rewrite-mod-mod
                            floor-floor-integer))
           :use ((:instance fn-bpc-u64-from-of-two-arguments
                            (hi (floor n 4294967296))
                            (lo (mod n 4294967296)))
                 fn-bpc-u64-halves-are-bounded
                 (:instance floor-mod-elim (x n) (y 4294967296))))))

(defthm fn-bpc-u64-from-of-u64-bytes
  (implies (and (natp n) (<= n *fn-bpc-max-uint*))
           (equal (fn-bpc-u64-from (fn-bpc-u64-bytes n)) n))
  :hints (("Goal"
           :use ((:instance fn-bpc-u64-from-u64-bytes (xs nil)))
           :in-theory (disable fn-bpc-u64-from-u64-bytes
                               fn-bpc-u64-bytes fn-bpc-u64-from))))

(defthm fn-bpc-octet-listp-cdr
  (implies (fn-cbor-octet-listp xs)
           (fn-cbor-octet-listp (cdr xs))))

; -----------------------------------------------------------------------------
; The 27-form inverse: eight octets read as a u64 re-encode to themselves.
;
; This is the digit-extraction argument the decoder theory keeps out of its
; case tree.  It is done once, over the two 32-bit halves, on the pattern of
; `fn-cbor-u32-to-from-octets` in `cbor-invariants`: the halves are recovered
; by `floor`/`mod` at 2^32, then each half re-encodes by the existing uint32
; inverse.  Every later use goes through `fn-bpc-u64-bytes-reassemble`.

(local
 (defthm fn-bpc-split-floor
   (implies (and (natp hi) (natp lo) (< lo 4294967296))
            (equal (floor (+ (* 4294967296 hi) lo) 4294967296) hi))
   :hints (("Goal" :in-theory (disable floor mod) :nonlinearp t))))

(local
 (defthm fn-bpc-split-mod
   (implies (and (natp hi) (natp lo) (< lo 4294967296))
            (equal (mod (+ (* 4294967296 hi) lo) 4294967296) lo))
   :hints (("Goal" :in-theory (disable floor mod) :nonlinearp t))))

(defthm fn-bpc-u64-bytes-of-u64-from
  (implies (and (fn-cbor-octet-listp xs)
                (consp xs) (consp (cdr xs))
                (consp (cddr xs)) (consp (cdddr xs))
                (consp (cddddr xs)) (consp (cdr (cddddr xs)))
                (consp (cddr (cddddr xs))) (consp (cdddr (cddddr xs))))
           (equal (fn-bpc-u64-bytes (fn-bpc-u64-from xs))
                  (list (car xs) (cadr xs) (caddr xs) (cadddr xs)
                        (car (cddddr xs)) (cadr (cddddr xs))
                        (caddr (cddddr xs)) (cadddr (cddddr xs)))))
  :rule-classes nil
  :hints (("Goal"
           :in-theory (e/d (fn-bpc-u64-bytes fn-bpc-u64-from
                            fn-bpc-u32-octets-agree-with-fn-cbor-u32-bytes)
                           (fn-bpc-u32-octets fn-cbor-u32-from fn-cbor-u32-bytes
                            floor mod))
           :use ((:instance fn-bpc-split-floor
                            (hi (fn-cbor-u32-from xs))
                            (lo (fn-cbor-u32-from (cddddr xs))))
                 (:instance fn-bpc-split-mod
                            (hi (fn-cbor-u32-from xs))
                            (lo (fn-cbor-u32-from (cddddr xs))))
                 (:instance fn-cbor-u32-from-bounds (xs xs))
                 (:instance fn-cbor-u32-from-bounds (xs (cddddr xs)))
                 (:instance fn-cbor-u32-to-from-octets (xs xs))
                 (:instance fn-cbor-u32-to-from-octets (xs (cddddr xs)))))))

; `car-cdr-elim` as a rewrite rule, so that a re-encoded prefix consed back
; onto the decoder's remainder collapses to the original list without
; destructor elimination.
(defthm fn-bpc-cons-car-cdr
  (implies (consp x)
           (equal (cons (car x) (cdr x)) x)))

(defthm fn-bpc-u64-bytes-reassemble
  (implies (and (fn-cbor-octet-listp xs)
                (consp xs) (consp (cdr xs))
                (consp (cddr xs)) (consp (cdddr xs))
                (consp (cddddr xs)) (consp (cdr (cddddr xs)))
                (consp (cddr (cddddr xs))) (consp (cdddr (cddddr xs))))
           (equal (append (fn-bpc-u64-bytes (fn-bpc-u64-from xs))
                          (cddddr (cddddr xs)))
                  xs))
  :hints (("Goal" :use fn-bpc-u64-bytes-of-u64-from
           :in-theory (disable fn-bpc-u64-bytes fn-bpc-u64-from floor mod))))

(local
 (defthm fn-bpc-eight-conses-from-length
   (implies (<= 8 (len xs))
            (and (consp xs) (consp (cdr xs))
                 (consp (cddr xs)) (consp (cdddr xs))
                 (consp (cddddr xs)) (consp (cdr (cddddr xs)))
                 (consp (cddr (cddddr xs))) (consp (cdddr (cddddr xs)))))
   :hints (("Goal" :expand ((len xs) (len (cdr xs)) (len (cddr xs))
                            (len (cdddr xs)) (len (cddddr xs))
                            (len (cdr (cddddr xs))) (len (cddr (cddddr xs)))
                            (len (cdddr (cddddr xs))))))))

(local
 (defthm fn-bpc-nthcdr-eight
   (equal (nthcdr 8 xs) (cddddr (cddddr xs)))
   :hints (("Goal" :expand ((nthcdr 8 xs) (nthcdr 7 (cdr xs))
                            (nthcdr 6 (cddr xs)) (nthcdr 5 (cdddr xs))
                            (nthcdr 4 (cddddr xs)) (nthcdr 3 (cdr (cddddr xs)))
                            (nthcdr 2 (cddr (cddddr xs)))
                            (nthcdr 1 (cdddr (cddddr xs))))))))

; The same inverse in the length-hypothesis form.
(defthm fn-bpc-u64-octet-round-trip
  (implies (and (fn-cbor-octet-listp xs) (<= 8 (len xs)))
           (equal (append (fn-bpc-u64-bytes (fn-bpc-u64-from xs)) (nthcdr 8 xs))
                  xs))
  :hints (("Goal"
           :do-not-induct t
           :use (fn-bpc-eight-conses-from-length fn-bpc-u64-bytes-reassemble)
           :in-theory (e/d (fn-bpc-nthcdr-eight)
                           (fn-bpc-u64-bytes fn-bpc-u64-from floor mod len
                            nthcdr fn-bpc-u64-bytes-reassemble)))))

; Forward-chained, not only rewritten.  The decoder dispatches on the head
; octet with literal range comparisons, and linear arithmetic cannot refute a
; context that places the head strictly between two adjacent integers unless
; integrality reaches type-set.  A :rewrite rule never does; a :forward-chaining
; rule triggered on the head term does.
(defthm fn-bpc-car-of-octet-list-is-natural
  (implies (and (fn-cbor-octet-listp xs) (consp xs))
           (and (natp (car xs))
                (integerp (car xs))
                (<= 0 (car xs))))
  :rule-classes
  (:rewrite (:forward-chaining :trigger-terms ((car xs)))))

(defthm fn-bpc-car-of-octet-list-is-bounded
  (implies (and (fn-cbor-octet-listp xs) (consp xs))
           (<= (car xs) 255))
  :rule-classes :linear)

(defthm fn-bpc-octet-listp-nthcdr
  (implies (fn-cbor-octet-listp xs)
           (fn-cbor-octet-listp (nthcdr n xs)))
  :hints (("Goal" :induct (nthcdr n xs))))

(defthm fn-bpc-octet-listp-take
  (implies (and (fn-cbor-octet-listp xs) (natp n) (<= n (len xs)))
           (fn-cbor-octet-listp (take n xs)))
  :hints (("Goal" :use fn-cbor-take-preserves-octets
           :in-theory (disable fn-cbor-take-preserves-octets))))

(local
 (defthm fn-bpc-u64-bound-arith
   (implies (and (natp a) (<= a 4294967295)
                 (natp b) (<= b 4294967295))
            (<= (+ (* 4294967296 a) b) 18446744073709551615))
   :hints (("Goal" :nonlinearp t))))

(defthm fn-bpc-u64-from-is-natural
  (implies (and (fn-cbor-octet-listp xs)
                (consp xs) (consp (cdr xs))
                (consp (cddr xs)) (consp (cdddr xs))
                (consp (cddddr xs)) (consp (cdr (cddddr xs)))
                (consp (cddr (cddddr xs))) (consp (cdddr (cddddr xs))))
           (and (natp (fn-bpc-u64-from xs))
                (integerp (fn-bpc-u64-from xs))
                (rationalp (fn-bpc-u64-from xs))
                (acl2-numberp (fn-bpc-u64-from xs))
                (<= 0 (fn-bpc-u64-from xs))))
  :hints (("Goal" :in-theory (enable fn-bpc-u64-from fn-cbor-u32-from
                                     fn-cbor-octet-listp fn-cbor-octetp))))

(defthm fn-bpc-u64-from-is-bounded
  (implies (and (fn-cbor-octet-listp xs)
                (consp xs) (consp (cdr xs))
                (consp (cddr xs)) (consp (cdddr xs))
                (consp (cddddr xs)) (consp (cdr (cddddr xs)))
                (consp (cddr (cddddr xs))) (consp (cdddr (cddddr xs))))
           (<= (fn-bpc-u64-from xs) *fn-bpc-max-uint*))
  :rule-classes :linear
  :hints (("Goal"
           :in-theory (e/d (fn-bpc-u64-from) (fn-cbor-u32-from))
           :use ((:instance fn-cbor-u32-from-bounds (xs xs))
                 (:instance fn-cbor-u32-from-bounds (xs (cddddr xs)))
                 (:instance fn-bpc-u64-bound-arith
                            (a (fn-cbor-u32-from xs))
                            (b (fn-cbor-u32-from (cddddr xs))))))))

; -----------------------------------------------------------------------------
; Deterministic arguments
;
; Below 2^32 the existing deterministic encoder owns the head; at and above
; 2^32 the 27 form is the shortest RFC 8949 representation.

(defun fn-bpc-argument (major n)
  (declare (xargs :guard t))
  (if (not (and (natp major) (natp n)))
      nil
    (if (< n 4294967296)
        (fn-cbor-encode-argument major n)
      (cons (+ (* 32 major) 27) (fn-bpc-u64-bytes n)))))

(defun fn-bpc-canonical-argumentp (additional n)
  (declare (xargs :guard t))
  (and (natp additional) (natp n)
       (or (and (< n 24) (equal additional n))
           (and (equal additional 24) (<= 24 n) (< n 256))
           (and (equal additional 25) (<= 256 n) (< n 65536))
           (and (equal additional 26) (<= 65536 n) (< n 4294967296))
           (and (equal additional 27) (<= 4294967296 n)
                (<= n *fn-bpc-max-uint*)))
       t))

(verify-guards fn-bpc-argument)
(verify-guards fn-bpc-canonical-argumentp)

(defthm fn-bpc-argument-are-octets
  (implies (and (natp major) (< major 8) (natp n))
           (fn-cbor-octet-listp (fn-bpc-argument major n)))
  :hints (("Goal"
           :in-theory (e/d (fn-cbor-encode-argument fn-cbor-octet-listp
                            fn-cbor-octetp)
                           (floor mod)))))

(defthm fn-bpc-argument-is-true-list
  (true-listp (fn-bpc-argument major n))
  :hints (("Goal" :in-theory (enable fn-cbor-encode-argument))))

; -----------------------------------------------------------------------------
; The value domain
;
; A value is (:uint . n), (:text . octets), (:bytes . octets) or
; (:array . values).  The flag argument lets one recursion serve items and item
; lists, which gives every theorem below a single induction scheme.

(defun fn-bpc-shapep (flg x)
  (declare (xargs :guard t :measure (acl2-count x)))
  (if (eq flg :list)
      (if (consp x)
          (and (fn-bpc-shapep :item (car x))
               (fn-bpc-shapep :list (cdr x)))
        (null x))
    (and (consp x)
         (cond ((eq (car x) :uint)
                (and (natp (cdr x)) (<= (cdr x) *fn-bpc-max-uint*)))
               ((eq (car x) :text)
                (and (fn-cbor-octet-listp (cdr x))
                     (<= (len (cdr x)) *fn-bpc-max-text*)))
               ((eq (car x) :bytes)
                (and (fn-cbor-octet-listp (cdr x))
                     (<= (len (cdr x)) *fn-bpc-max-bytes*)))
               ((eq (car x) :array)
                (and (true-listp (cdr x))
                     (<= (len (cdr x)) *fn-bpc-max-arity*)
                     (fn-bpc-shapep :list (cdr x))))
               (t nil)))))

(defun fn-bpc-valuep (x)
  (declare (xargs :guard t))
  (fn-bpc-shapep :item x))

; The budget a decode of this value needs.  It over-counts -- it sums where the
; decoder needs only a maximum -- so this bound is sufficient, never necessary.
(defun fn-bpc-cost (flg x)
  (declare (xargs :guard t :measure (acl2-count x)))
  (if (eq flg :list)
      (if (consp x)
          (+ 1 (fn-bpc-cost :item (car x)) (fn-bpc-cost :list (cdr x)))
        1)
    (if (and (consp x) (eq (car x) :array))
        (+ 1 (fn-bpc-cost :list (cdr x)))
      1)))

(verify-guards fn-bpc-shapep)
(verify-guards fn-bpc-valuep)
(verify-guards fn-bpc-cost)

(defthm fn-bpc-cost-is-positive
  (< 0 (fn-bpc-cost flg x))
  :rule-classes :linear)

; -----------------------------------------------------------------------------
; Encoder

(defun fn-bpc-enc (flg x)
  (declare (xargs :guard t :verify-guards nil :measure (acl2-count x)))
  (if (eq flg :list)
      (if (consp x)
          (append (fn-bpc-enc :item (car x))
                  (fn-bpc-enc :list (cdr x)))
        nil)
    (if (not (consp x))
        nil
      (cond ((eq (car x) :uint)
             (if (natp (cdr x)) (fn-bpc-argument 0 (cdr x)) nil))
            ((eq (car x) :bytes)
             (if (fn-cbor-octet-listp (cdr x))
                 (append (fn-bpc-argument 2 (len (cdr x))) (cdr x))
               nil))
            ((eq (car x) :text)
             (if (fn-cbor-octet-listp (cdr x))
                 (append (fn-bpc-argument 3 (len (cdr x))) (cdr x))
               nil))
            ((eq (car x) :array)
             (if (true-listp (cdr x))
                 (append (fn-bpc-argument 4 (len (cdr x)))
                         (fn-bpc-enc :list (cdr x)))
               nil))
            (t nil)))))

(defthm fn-bpc-enc-is-true-list
  (true-listp (fn-bpc-enc flg x))
  :hints (("Goal" :induct (fn-bpc-enc flg x))))

(defthm fn-bpc-enc-are-octets
  (fn-cbor-octet-listp (fn-bpc-enc flg x))
  :hints (("Goal" :induct (fn-bpc-enc flg x))))

(verify-guards fn-bpc-enc)

(defun fn-bpc-encode (value)
  (declare (xargs :guard t))
  (fn-bpc-enc :item value))

(verify-guards fn-bpc-encode)

; -----------------------------------------------------------------------------
; Decoder

(defun fn-bpc-decode-argument (additional xs)
  (declare (xargs :guard (and (natp additional) (fn-cbor-octet-listp xs))))
  (if (< additional 27)
      (fn-cbor-decode-argument additional xs)
    (if (equal additional 27)
        (if (and (consp xs) (consp (cdr xs))
                 (consp (cddr xs)) (consp (cdddr xs))
                 (consp (cddddr xs)) (consp (cdr (cddddr xs)))
                 (consp (cddr (cddddr xs))) (consp (cdddr (cddddr xs))))
            (fn-cbor-ok (fn-bpc-u64-from xs) (cddddr (cddddr xs)))
          (fn-cbor-error :truncated))
      (fn-cbor-error :unsupported))))

(verify-guards fn-bpc-decode-argument)

(defthm fn-bpc-decode-argument-rest-are-octets
  (implies (fn-cbor-octet-listp xs)
           (fn-cbor-octet-listp
            (fn-cbor-result-rest (fn-bpc-decode-argument additional xs)))))

(defthm fn-bpc-decode-argument-value-is-natural
  (implies (and (natp additional) (fn-cbor-octet-listp xs)
                (fn-cbor-result-okp (fn-bpc-decode-argument additional xs)))
           (and (natp (fn-cbor-result-value
                       (fn-bpc-decode-argument additional xs)))
                (integerp (fn-cbor-result-value
                           (fn-bpc-decode-argument additional xs)))
                (rationalp (fn-cbor-result-value
                            (fn-bpc-decode-argument additional xs)))
                (acl2-numberp (fn-cbor-result-value
                               (fn-bpc-decode-argument additional xs)))
                (<= 0 (fn-cbor-result-value
                       (fn-bpc-decode-argument additional xs))))))

; -----------------------------------------------------------------------------
; One decoded head: the argument value and the octets after it, with the
; canonical-form check applied before anything is allocated from it.

(defun fn-bpc-decode-head (additional xs)
  (declare (xargs :guard (and (natp additional) (fn-cbor-octet-listp xs))))
  (let ((argument (fn-bpc-decode-argument additional xs)))
    (if (not (fn-cbor-result-okp argument))
        argument
      (if (not (fn-bpc-canonical-argumentp
                additional (fn-cbor-result-value argument)))
          (fn-cbor-error :noncanonical)
        argument))))

(verify-guards fn-bpc-decode-head)

(defthm fn-bpc-decode-head-rest-are-octets
  (implies (fn-cbor-octet-listp xs)
           (fn-cbor-octet-listp
            (fn-cbor-result-rest (fn-bpc-decode-head additional xs)))))

(defthm fn-bpc-decode-head-value-is-natural
  (implies (and (natp additional) (fn-cbor-octet-listp xs)
                (fn-cbor-result-okp (fn-bpc-decode-head additional xs)))
           (and (natp (fn-cbor-result-value
                       (fn-bpc-decode-head additional xs)))
                (integerp (fn-cbor-result-value
                           (fn-bpc-decode-head additional xs)))
                (rationalp (fn-cbor-result-value
                            (fn-bpc-decode-head additional xs)))
                (acl2-numberp (fn-cbor-result-value
                               (fn-bpc-decode-head additional xs)))
                (<= 0 (fn-cbor-result-value
                       (fn-bpc-decode-head additional xs)))))
  :rule-classes
  (:rewrite
   (:forward-chaining
    :trigger-terms ((fn-cbor-result-value (fn-bpc-decode-head additional xs))))))

(defthm fn-bpc-decode-head-value-is-bounded
  (implies (and (natp additional) (fn-cbor-octet-listp xs)
                (fn-cbor-result-okp (fn-bpc-decode-head additional xs)))
           (<= (fn-cbor-result-value (fn-bpc-decode-head additional xs))
               *fn-bpc-max-uint*))
  :rule-classes :linear)

; The decoder's own reasoning is about lists and bounded comparisons, never
; about base-256 arithmetic.  `arithmetic/top`'s modular rules, in particular
; the generalization rule MOD-X-Y-=-X+Y-FOR-RATIONALS, otherwise introduce
; `mod` terms into the decoder's case tree and loop the waterfall.  This is
; local, so no book that includes this one inherits it.
(local (in-theory (disable floor mod
                           mod-x-y-=-x+y-for-rationals
                           mod-x-y-=-x-for-rationals
                           mod-minus
                           mod-bounded-by-modulus
                           integerp-mod rationalp-mod mod-type
                           floor-mod-elim
                           cancel-mod-+-basic cancel-floor-+-basic
                           rewrite-mod-mod rewrite-floor-mod
                           floor-floor-integer
                           floor-=-x/y mod-=-0)))

; -----------------------------------------------------------------------------
; The streaming decoder

(defun fn-bpc-dec (flg count octets budget)
  (declare (xargs :guard (and (natp count)
                              (fn-cbor-octet-listp octets)
                              (natp budget))
                  :verify-guards nil
                  :measure (nfix budget)))
  (if (zp budget)
      (fn-cbor-error :budget)
    (if (eq flg :list)
        (if (zp count)
            (fn-cbor-ok nil octets)
          (let ((one (fn-bpc-dec :item 0 octets (- budget 1))))
            (if (not (fn-cbor-result-okp one))
                one
              (let ((more (fn-bpc-dec :list (- count 1)
                                      (fn-cbor-result-rest one)
                                      (- budget 1))))
                (if (not (fn-cbor-result-okp more))
                    more
                  (fn-cbor-ok (cons (fn-cbor-result-value one)
                                    (fn-cbor-result-value more))
                              (fn-cbor-result-rest more)))))))
      (if (not (consp octets))
          (fn-cbor-error :truncated)
        (let ((head (car octets))
              (tail (cdr octets)))
          ; Major type by range, as `books/cbor.lisp` dispatches, so that no
          ; `floor` or `mod` term ever reaches the decoder's case tree.
          (cond
           ((< head 32)
            (let ((h (fn-bpc-decode-head head tail)))
              (if (not (fn-cbor-result-okp h))
                  h
                (fn-cbor-ok (cons :uint (fn-cbor-result-value h))
                            (fn-cbor-result-rest h)))))
           ((and (< 63 head) (< head 96))
            (let ((h (fn-bpc-decode-head (- head 64) tail)))
              (if (not (fn-cbor-result-okp h))
                  h
                (let ((size (fn-cbor-result-value h))
                      (content (fn-cbor-result-rest h)))
                  (if (< *fn-bpc-max-bytes* size)
                      (fn-cbor-error :limit)
                    (if (<= size (len content))
                        (fn-cbor-ok (cons :bytes (take size content))
                                    (nthcdr size content))
                      (fn-cbor-error :truncated)))))))
           ((and (< 95 head) (< head 128))
            (let ((h (fn-bpc-decode-head (- head 96) tail)))
              (if (not (fn-cbor-result-okp h))
                  h
                (let ((size (fn-cbor-result-value h))
                      (content (fn-cbor-result-rest h)))
                  (if (< *fn-bpc-max-text* size)
                      (fn-cbor-error :limit)
                    (if (<= size (len content))
                        (fn-cbor-ok (cons :text (take size content))
                                    (nthcdr size content))
                      (fn-cbor-error :truncated)))))))
           ((and (< 127 head) (< head 160))
            (let ((h (fn-bpc-decode-head (- head 128) tail)))
              (if (not (fn-cbor-result-okp h))
                  h
                (let ((arity (fn-cbor-result-value h))
                      (content (fn-cbor-result-rest h)))
                  (if (< *fn-bpc-max-arity* arity)
                      (fn-cbor-error :limit)
                    (let ((items (fn-bpc-dec :list arity content
                                             (- budget 1))))
                      (if (not (fn-cbor-result-okp items))
                          items
                        (fn-cbor-ok (cons :array (fn-cbor-result-value items))
                                    (fn-cbor-result-rest items)))))))))
           (t (fn-cbor-error :unsupported))))))))

(defthm fn-bpc-dec-is-true-list
  (true-listp (fn-bpc-dec flg count octets budget))
  :hints (("Goal" :induct (fn-bpc-dec flg count octets budget)
           :in-theory (disable fn-cbor-octet-listp fn-bpc-decode-head
                               fn-cbor-ok fn-cbor-error fn-cbor-result-okp
                               fn-cbor-result-value fn-cbor-result-rest
                               take nthcdr floor mod))))

(defthm fn-bpc-dec-rest-are-octets
  (implies (fn-cbor-octet-listp octets)
           (fn-cbor-octet-listp
            (fn-cbor-result-rest (fn-bpc-dec flg count octets budget))))
  :hints (("Goal" :induct (fn-bpc-dec flg count octets budget)
           :in-theory (disable fn-cbor-octet-listp fn-bpc-decode-head
                               fn-cbor-ok fn-cbor-error fn-cbor-result-okp
                               fn-cbor-result-value fn-cbor-result-rest
                               take nthcdr floor mod))))

(verify-guards fn-bpc-dec)

; The public one-item decoder.  The input length preflight comes first, so a
; remote overlong list cannot make the decoder traverse or allocate in
; proportion to its claimed size.
(defun fn-bpc-decode (octets)
  (declare (xargs :guard t))
  (if (not (fn-cbor-at-mostp octets *fn-bpc-max-input*))
      (fn-cbor-error :limit)
    (if (not (fn-cbor-octet-listp octets))
        (fn-cbor-error :malformed)
      (fn-bpc-dec :item 0 octets *fn-bpc-max-items*))))

(defun fn-bpc-decode-exact (octets)
  (declare (xargs :guard t))
  (let ((result (fn-bpc-decode octets)))
    (if (not (fn-cbor-result-okp result))
        result
      (if (null (fn-cbor-result-rest result))
          result
        (fn-cbor-error :trailing)))))

(verify-guards fn-bpc-decode)
(verify-guards fn-bpc-decode-exact)

(defthm fn-bpc-decode-is-true-list
  (true-listp (fn-bpc-decode octets)))

(defthm fn-bpc-decode-exact-is-true-list
  (true-listp (fn-bpc-decode-exact octets)))

; -----------------------------------------------------------------------------
; A deterministic head is decoded back to its own argument

(defthm fn-bpc-argument-is-consp
  (implies (and (natp major) (natp n))
           (consp (fn-bpc-argument major n)))
  :hints (("Goal" :in-theory (enable fn-cbor-encode-argument))))

(defthm fn-bpc-argument-head-range
  (implies (and (natp major) (< major 8) (natp n) (<= n *fn-bpc-max-uint*))
           (and (<= (* 32 major) (car (fn-bpc-argument major n)))
                (< (car (fn-bpc-argument major n)) (+ 32 (* 32 major)))
                (fn-bpc-canonical-argumentp
                 (- (car (fn-bpc-argument major n)) (* 32 major)) n)))
  :rule-classes nil
  :hints (("Goal"
           :cases ((< n 24) (< n 256) (< n 65536) (< n 4294967296))
           :in-theory (e/d (fn-cbor-encode-argument) (floor mod)))))

(defthm fn-bpc-decode-head-of-argument
  (implies (and (natp major) (< major 8) (natp n) (<= n *fn-bpc-max-uint*)
                (fn-cbor-octet-listp rest))
           (equal (fn-bpc-decode-head
                   (- (car (fn-bpc-argument major n)) (* 32 major))
                   (append (cdr (fn-bpc-argument major n)) rest))
                  (fn-cbor-ok n rest)))
  :rule-classes nil
  :hints (("Goal"
           :cases ((< n 24) (< n 256) (< n 65536) (< n 4294967296))
           :in-theory (e/d (fn-cbor-encode-argument
                            fn-bpc-decode-argument
                            fn-cbor-decode-argument
                            fn-cbor-result-okp fn-cbor-result-value
                            fn-cbor-result-rest fn-cbor-ok)
                           (floor mod)))))

; The decoder dispatches by comparing the head octet against adjacent integer
; literals.  Without integrality, linear arithmetic cannot refute a context that
; places the head strictly between two of them -- 95 < head < 96 is consistent
; over the rationals -- so the text and bytes branches of the round trip stay
; open.  `fn-cbor-octet-listp` is closed inside those proofs, so the fact is
; stated here directly, with a forward-chaining trigger on the head term so it
; reaches the linear pot rather than waiting to be rewritten.
(defthm fn-bpc-argument-head-is-natural
  (implies (and (natp major) (< major 8) (natp n))
           (natp (car (fn-bpc-argument major n))))
  :rule-classes
  (:rewrite
   (:forward-chaining :trigger-terms ((car (fn-bpc-argument major n)))))
  :hints (("Goal"
           :cases ((< n 24) (< n 256) (< n 65536) (< n 4294967296))
           :in-theory (e/d (fn-cbor-encode-argument) (floor mod)))))

; Per-major-type corollaries.  The decoder dispatches on the head octet's
; range and subtracts a literal, so a rule whose left-hand side still mentions
; `(* 32 major)` would not match the goal; these four do.

(defthm fn-bpc-uint-head-range
  (implies (and (natp n) (<= n *fn-bpc-max-uint*))
           (< (car (fn-bpc-argument 0 n)) 32))
  :rule-classes :linear
  :hints (("Goal" :use ((:instance fn-bpc-argument-head-range (major 0))))))

(defthm fn-bpc-bytes-head-range
  (implies (and (natp n) (<= n *fn-bpc-max-uint*))
           (and (< 63 (car (fn-bpc-argument 2 n)))
                (< (car (fn-bpc-argument 2 n)) 96)))
  :rule-classes :linear
  :hints (("Goal" :use ((:instance fn-bpc-argument-head-range (major 2))))))

(defthm fn-bpc-text-head-range
  (implies (and (natp n) (<= n *fn-bpc-max-uint*))
           (and (< 95 (car (fn-bpc-argument 3 n)))
                (< (car (fn-bpc-argument 3 n)) 128)))
  :rule-classes :linear
  :hints (("Goal" :use ((:instance fn-bpc-argument-head-range (major 3))))))

(defthm fn-bpc-array-head-range
  (implies (and (natp n) (<= n *fn-bpc-max-uint*))
           (and (< 127 (car (fn-bpc-argument 4 n)))
                (< (car (fn-bpc-argument 4 n)) 160)))
  :rule-classes :linear
  :hints (("Goal" :use ((:instance fn-bpc-argument-head-range (major 4))))))

(defthm fn-bpc-uint-head-decodes
  (implies (and (natp n) (<= n *fn-bpc-max-uint*) (fn-cbor-octet-listp rest))
           (equal (fn-bpc-decode-head (car (fn-bpc-argument 0 n))
                                      (append (cdr (fn-bpc-argument 0 n)) rest))
                  (fn-cbor-ok n rest)))
  :hints (("Goal" :use ((:instance fn-bpc-decode-head-of-argument
                                   (major 0))))))

(defthm fn-bpc-bytes-head-decodes
  (implies (and (natp n) (<= n *fn-bpc-max-uint*) (fn-cbor-octet-listp rest))
           (equal (fn-bpc-decode-head (+ -64 (car (fn-bpc-argument 2 n)))
                                      (append (cdr (fn-bpc-argument 2 n)) rest))
                  (fn-cbor-ok n rest)))
  :hints (("Goal" :use ((:instance fn-bpc-decode-head-of-argument
                                   (major 2))))))

(defthm fn-bpc-text-head-decodes
  (implies (and (natp n) (<= n *fn-bpc-max-uint*) (fn-cbor-octet-listp rest))
           (equal (fn-bpc-decode-head (+ -96 (car (fn-bpc-argument 3 n)))
                                      (append (cdr (fn-bpc-argument 3 n)) rest))
                  (fn-cbor-ok n rest)))
  :hints (("Goal" :use ((:instance fn-bpc-decode-head-of-argument
                                   (major 3))))))

(defthm fn-bpc-array-head-decodes
  (implies (and (natp n) (<= n *fn-bpc-max-uint*) (fn-cbor-octet-listp rest))
           (equal (fn-bpc-decode-head (+ -128 (car (fn-bpc-argument 4 n)))
                                      (append (cdr (fn-bpc-argument 4 n)) rest))
                  (fn-cbor-ok n rest)))
  :hints (("Goal" :use ((:instance fn-bpc-decode-head-of-argument
                                   (major 4))))))

; -----------------------------------------------------------------------------
; Round trip: every typed value decodes back from its own encoding, with the
; remaining octets returned untouched.

(local
 (defun fn-bpc-round-trip-induction (flg x rest budget)
   (declare (xargs :measure (acl2-count x)))
   (if (eq flg :list)
       (if (consp x)
           (list (fn-bpc-round-trip-induction
                  :item (car x)
                  (append (fn-bpc-enc :list (cdr x)) rest)
                  (- budget 1))
                 (fn-bpc-round-trip-induction
                  :list (cdr x) rest (- budget 1)))
         (list flg x rest budget))
     (if (and (consp x) (eq (car x) :array))
         (fn-bpc-round-trip-induction :list (cdr x) rest (- budget 1))
       (list flg x rest budget)))))

(defthm fn-bpc-decode-of-encode
  (implies (and (fn-bpc-shapep flg x)
                (fn-cbor-octet-listp rest)
                (natp budget)
                (<= (fn-bpc-cost flg x) budget))
           (equal (fn-bpc-dec flg
                              (if (eq flg :list) (len x) 0)
                              (append (fn-bpc-enc flg x) rest)
                              budget)
                  (fn-cbor-ok x rest)))
  :hints (("Goal"
           :induct (fn-bpc-round-trip-induction flg x rest budget)
           :expand ((:free (a b c) (fn-bpc-dec a b c budget)))
           :in-theory (disable fn-bpc-argument fn-bpc-decode-head
                               fn-cbor-ok fn-cbor-error fn-cbor-result-okp
                               fn-cbor-result-value fn-cbor-result-rest
                               fn-cbor-octet-listp take nthcdr floor mod))))

; The public round trip.  The input-length preflight is discharged for every
; accepted value, so this is a statement about `fn-bpc-decode-exact` itself.
(defthm fn-bpc-value-round-trip
  (implies (and (fn-bpc-valuep x)
                (<= (fn-bpc-cost :item x) *fn-bpc-max-items*)
                (fn-cbor-at-mostp (fn-bpc-enc :item x) *fn-bpc-max-input*))
           (equal (fn-bpc-decode-exact (fn-bpc-encode x))
                  (fn-cbor-ok x nil)))
  :hints (("Goal"
           :use ((:instance fn-bpc-decode-of-encode
                            (flg :item) (x x) (rest nil)
                            (budget *fn-bpc-max-items*)))
           :in-theory (disable fn-bpc-dec fn-bpc-enc))))

; -----------------------------------------------------------------------------
; Decoded values are in the domain, and a decoded list has the arity its head
; declared.  Both are needed before any consumer may index into a decoded item.

(defthm fn-bpc-dec-list-has-declared-length
  (implies (and (natp count)
                (fn-cbor-result-okp (fn-bpc-dec :list count octets budget)))
           (equal (len (fn-cbor-result-value (fn-bpc-dec :list count octets budget)))
                  count))
  :hints (("Goal" :induct (fn-bpc-dec :list count octets budget)
           :in-theory (disable fn-cbor-octet-listp fn-bpc-decode-head
                               fn-cbor-ok fn-cbor-error fn-cbor-result-okp
                               fn-cbor-result-value fn-cbor-result-rest
                               take nthcdr floor mod))))

; The `okp` hypothesis is not decoration: a refusal is `(:error reason)`, whose
; value field is the reason keyword, so the unconditional form is false at
; budget zero.
(defthm fn-bpc-dec-list-is-true-list
  (implies (fn-cbor-result-okp (fn-bpc-dec :list count octets budget))
           (true-listp (fn-cbor-result-value
                        (fn-bpc-dec :list count octets budget))))
  :hints (("Goal" :induct (fn-bpc-dec :list count octets budget)
           :in-theory (disable fn-cbor-octet-listp fn-bpc-decode-head
                               fn-cbor-ok fn-cbor-error fn-cbor-result-okp
                               fn-cbor-result-value fn-cbor-result-rest
                               take nthcdr floor mod))))

(defthm fn-bpc-dec-yields-shape
  (implies (and (fn-cbor-octet-listp octets)
                (natp count)
                (fn-cbor-result-okp (fn-bpc-dec flg count octets budget)))
           (fn-bpc-shapep flg (fn-cbor-result-value
                               (fn-bpc-dec flg count octets budget))))
  :hints (("Goal" :induct (fn-bpc-dec flg count octets budget)
           :in-theory (disable fn-cbor-octet-listp fn-bpc-decode-head
                               fn-cbor-ok fn-cbor-error fn-cbor-result-okp
                               fn-cbor-result-value fn-cbor-result-rest
                               take nthcdr floor mod))))

(defthm fn-bpc-decode-exact-yields-value
  (implies (fn-cbor-result-okp (fn-bpc-decode-exact octets))
           (fn-bpc-valuep (fn-cbor-result-value (fn-bpc-decode-exact octets))))
  :hints (("Goal"
           :use ((:instance fn-bpc-dec-yields-shape
                            (flg :item) (count 0)
                            (budget *fn-bpc-max-items*)))
           :in-theory (disable fn-bpc-dec fn-bpc-dec-yields-shape))))

; -----------------------------------------------------------------------------
; Accepted-input canonicality
;
; This covers arbitrary accepted input, not only encoder output.  A non-minimal
; argument, an indefinite-length head, or any spelling other than the
; deterministic one cannot pass, because a successful decode is required to
; re-encode to exactly the octets it consumed.

; The 27 case of `fn-bpc-argument-of-decode-head` is `fn-bpc-u64-bytes-reassemble`;
; the 24 to 26 cases are the uint32 inverses from `cbor-invariants`.

(defthm fn-bpc-argument-of-decode-head
  (implies (and (fn-cbor-octet-listp tail)
                (natp additional) (< additional 32)
                (natp major) (< major 8)
                (fn-cbor-result-okp (fn-bpc-decode-head additional tail)))
           (equal (append (fn-bpc-argument
                           major
                           (fn-cbor-result-value
                            (fn-bpc-decode-head additional tail)))
                          (fn-cbor-result-rest
                           (fn-bpc-decode-head additional tail)))
                  (cons (+ (* 32 major) additional) tail)))
  :hints (("Goal"
           :in-theory (e/d (fn-bpc-decode-argument
                            fn-cbor-decode-argument
                            fn-cbor-encode-argument
                            fn-cbor-result-okp fn-cbor-result-value
                            fn-cbor-result-rest fn-cbor-ok)
                           (floor mod take nthcdr)))))

(defthm fn-bpc-dec-reencodes-consumed-prefix
  (implies (and (fn-cbor-octet-listp octets)
                (natp count)
                (fn-cbor-result-okp (fn-bpc-dec flg count octets budget)))
           (equal (append (fn-bpc-enc flg (fn-cbor-result-value
                                           (fn-bpc-dec flg count octets budget)))
                          (fn-cbor-result-rest
                           (fn-bpc-dec flg count octets budget)))
                  octets))
  :hints (("Goal"
           :induct (fn-bpc-dec flg count octets budget)
           :expand ((:free (a b c) (fn-bpc-dec a b c budget)))
           :in-theory (disable fn-bpc-argument fn-bpc-decode-head
                               fn-cbor-ok fn-cbor-error fn-cbor-result-okp
                               fn-cbor-result-value fn-cbor-result-rest
                               fn-cbor-octet-listp take nthcdr floor mod))))

(defthm fn-bpc-accepted-input-is-canonical
  (implies (fn-cbor-result-okp (fn-bpc-decode-exact octets))
           (equal (fn-bpc-encode (fn-cbor-result-value
                                  (fn-bpc-decode-exact octets)))
                  octets))
  :hints (("Goal"
           :use ((:instance fn-bpc-dec-reencodes-consumed-prefix
                            (flg :item) (count 0)
                            (budget *fn-bpc-max-items*)))
           :in-theory (disable fn-bpc-dec fn-bpc-enc
                               fn-bpc-dec-reencodes-consumed-prefix))))

; -----------------------------------------------------------------------------
; Bounds before allocation
;
; The decoder never traverses or copies more than the preflighted bound, and it
; never spends more than the declared item budget.

(defthm fn-bpc-decode-refuses-overlong-input
  (implies (not (fn-cbor-at-mostp octets *fn-bpc-max-input*))
           (equal (fn-bpc-decode octets) (fn-cbor-error :limit))))

(defthm fn-bpc-dec-with-no-budget-allocates-nothing
  (equal (fn-bpc-dec flg count octets 0) (fn-cbor-error :budget)))

(defthm fn-bpc-argument-length-bound
  (<= (len (fn-bpc-argument major n)) 9)
  :hints (("Goal" :in-theory (e/d (fn-cbor-encode-argument) (floor mod))))
  :rule-classes :linear)

; Every accepted item costs at most one head of nine octets plus one payload,
; and the largest payload in this profile is a 1024-octet text string.  The
; primary block's cost is bounded below, so this is what makes the public
; round trip's input preflight discharge.
(defthm fn-bpc-enc-length-bound
  (implies (fn-bpc-shapep flg x)
           (<= (len (fn-bpc-enc flg x)) (* 1033 (fn-bpc-cost flg x))))
  :hints (("Goal" :induct (fn-bpc-enc flg x)))
  :rule-classes :linear)

(defthm fn-bpc-decoded-text-is-within-bound
  (implies (and (fn-cbor-octet-listp octets)
                (fn-cbor-result-okp (fn-bpc-decode-exact octets))
                (equal (car (fn-cbor-result-value (fn-bpc-decode-exact octets)))
                       :text))
           (<= (len (cdr (fn-cbor-result-value (fn-bpc-decode-exact octets))))
               *fn-bpc-max-text*))
  :hints (("Goal"
           :use fn-bpc-decode-exact-yields-value
           :in-theory (e/d (fn-bpc-valuep)
                           (fn-bpc-decode-exact
                            fn-bpc-decode-exact-yields-value)))))

(defthm fn-bpc-decoded-array-is-within-arity
  (implies (and (fn-cbor-octet-listp octets)
                (fn-cbor-result-okp (fn-bpc-decode-exact octets))
                (equal (car (fn-cbor-result-value (fn-bpc-decode-exact octets)))
                       :array))
           (<= (len (cdr (fn-cbor-result-value (fn-bpc-decode-exact octets))))
               *fn-bpc-max-arity*))
  :hints (("Goal"
           :use fn-bpc-decode-exact-yields-value
           :in-theory (e/d (fn-bpc-valuep)
                           (fn-bpc-decode-exact
                            fn-bpc-decode-exact-yields-value)))))

; -----------------------------------------------------------------------------
; Export theory.
;
; The keystones leave this book enabled: `fn-bpc-decode-of-encode',
; `fn-bpc-value-round-trip', `fn-bpc-accepted-input-is-canonical', the two
; decoded-bound theorems, the no-budget theorem and the overlong refusal,
; together with the result record lemmas `fn-bpc-fields-of-ok',
; `fn-bpc-fields-of-error' and `fn-bpc-results-are-true-lists'.  Everything
; else is list, arithmetic and head vocabulary, including every rule that
; backchains into `len', `consp' or `true-listp'.

(deftheory fn-bpc-vocabulary
  '(    fn-bpc-append-associativity fn-bpc-car-of-append fn-bpc-cdr-of-append
    fn-bpc-consp-of-append fn-bpc-append-nil fn-bpc-len-of-append
    fn-bpc-take-of-append fn-bpc-nthcdr-of-append
    fn-bpc-u32-octets-are-octets fn-bpc-u32-octets-fields
    fn-bpc-u32-octets-prefix-fields
    fn-bpc-u32-octets-agree-with-fn-cbor-u32-bytes
    fn-bpc-u32-octets-invert fn-bpc-u32-bytes-prefix-fields
    fn-bpc-u16-bytes-have-length-two fn-bpc-u32-bytes-have-length-four
    fn-bpc-u16-from-is-a-number fn-bpc-u32-from-is-a-number
    fn-bpc-u64-bytes-fields fn-bpc-u64-bytes-have-eight-octets
    fn-bpc-u64-bytes-are-octets fn-bpc-u64-from-of-two-arguments
    fn-bpc-u64-from-u64-bytes fn-bpc-u64-from-of-u64-bytes
    fn-bpc-octet-listp-cdr fn-bpc-cons-car-cdr fn-bpc-u64-bytes-reassemble
    fn-bpc-u64-octet-round-trip fn-bpc-car-of-octet-list-is-natural
    fn-bpc-car-of-octet-list-is-bounded fn-bpc-octet-listp-nthcdr
    fn-bpc-octet-listp-take fn-bpc-u64-from-is-natural
    fn-bpc-u64-from-is-bounded fn-bpc-argument-are-octets
    fn-bpc-argument-is-true-list fn-bpc-cost-is-positive
    fn-bpc-enc-is-true-list fn-bpc-enc-are-octets
    fn-bpc-decode-argument-rest-are-octets
    fn-bpc-decode-argument-value-is-natural
    fn-bpc-decode-head-rest-are-octets fn-bpc-decode-head-value-is-natural
    fn-bpc-decode-head-value-is-bounded fn-bpc-dec-is-true-list
    fn-bpc-dec-rest-are-octets fn-bpc-decode-is-true-list
    fn-bpc-decode-exact-is-true-list fn-bpc-argument-is-consp
    fn-bpc-argument-head-is-natural fn-bpc-uint-head-range
    fn-bpc-bytes-head-range fn-bpc-text-head-range fn-bpc-array-head-range
    fn-bpc-uint-head-decodes fn-bpc-bytes-head-decodes
    fn-bpc-text-head-decodes fn-bpc-array-head-decodes
    fn-bpc-dec-list-has-declared-length fn-bpc-dec-list-is-true-list
    fn-bpc-dec-yields-shape fn-bpc-argument-of-decode-head
    fn-bpc-dec-reencodes-consumed-prefix fn-bpc-argument-length-bound
    fn-bpc-enc-length-bound))

(in-theory (disable fn-bpc-append-associativity fn-bpc-car-of-append
             fn-bpc-cdr-of-append fn-bpc-consp-of-append fn-bpc-append-nil
             fn-bpc-len-of-append fn-bpc-take-of-append
             fn-bpc-nthcdr-of-append fn-bpc-u32-octets-are-octets
             fn-bpc-u32-octets-fields fn-bpc-u32-octets-prefix-fields
             fn-bpc-u32-octets-agree-with-fn-cbor-u32-bytes
             fn-bpc-u32-octets-invert fn-bpc-u32-bytes-prefix-fields
             fn-bpc-u16-bytes-have-length-two
             fn-bpc-u32-bytes-have-length-four fn-bpc-u16-from-is-a-number
             fn-bpc-u32-from-is-a-number fn-bpc-u64-bytes-fields
             fn-bpc-u64-bytes-have-eight-octets
             fn-bpc-u64-bytes-are-octets fn-bpc-u64-from-of-two-arguments
             fn-bpc-u64-from-u64-bytes fn-bpc-u64-from-of-u64-bytes
             fn-bpc-octet-listp-cdr fn-bpc-cons-car-cdr
             fn-bpc-u64-bytes-reassemble fn-bpc-u64-octet-round-trip
             fn-bpc-car-of-octet-list-is-natural
             fn-bpc-car-of-octet-list-is-bounded fn-bpc-octet-listp-nthcdr
             fn-bpc-octet-listp-take fn-bpc-u64-from-is-natural
             fn-bpc-u64-from-is-bounded fn-bpc-argument-are-octets
             fn-bpc-argument-is-true-list fn-bpc-cost-is-positive
             fn-bpc-enc-is-true-list fn-bpc-enc-are-octets
             fn-bpc-decode-argument-rest-are-octets
             fn-bpc-decode-argument-value-is-natural
             fn-bpc-decode-head-rest-are-octets
             fn-bpc-decode-head-value-is-natural
             fn-bpc-decode-head-value-is-bounded fn-bpc-dec-is-true-list
             fn-bpc-dec-rest-are-octets fn-bpc-decode-is-true-list
             fn-bpc-decode-exact-is-true-list fn-bpc-argument-is-consp
             fn-bpc-argument-head-is-natural fn-bpc-uint-head-range
             fn-bpc-bytes-head-range fn-bpc-text-head-range
             fn-bpc-array-head-range fn-bpc-uint-head-decodes
             fn-bpc-bytes-head-decodes fn-bpc-text-head-decodes
             fn-bpc-array-head-decodes fn-bpc-dec-list-has-declared-length
             fn-bpc-dec-list-is-true-list fn-bpc-dec-yields-shape
             fn-bpc-argument-of-decode-head
             fn-bpc-dec-reencodes-consumed-prefix
             fn-bpc-argument-length-bound fn-bpc-enc-length-bound))
