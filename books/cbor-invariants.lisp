; Arithmetic and round-trip invariants for the bounded fn CBOR primitive
; profile.  This book introduces no new codec values or API; it proves facts
; about books/cbor.lisp using ACL2's standard quotient/remainder lemmas.

(in-package "ACL2")

(include-book "ihs/quotient-remainder-lemmas" :dir :system)
(include-book "cbor")

; This book is the codec's proof book: every theorem below is about the
; definitions in `cbor', so it opens them locally.  Results stay opaque; the
; record lemmas exported by `cbor' are what close the goals about them.
(local (in-theory (enable fn-cbor-codec-vocabulary)))

(defthm fn-cbor-u16-from-u16-bytes
  (implies (and (natp n) (< n 65536))
           (equal (fn-cbor-u16-from (fn-cbor-u16-bytes n)) n))
  :hints (("Goal" :in-theory (enable fn-cbor-u16-from
                                      fn-cbor-u16-bytes))))

(defthm fn-cbor-u16-bytes-are-octets
  (implies (and (natp n) (< n 65536))
           (fn-cbor-octet-listp (fn-cbor-u16-bytes n)))
  :hints (("Goal" :in-theory (e/d (fn-cbor-u16-bytes
                                        fn-cbor-octet-listp
                                        fn-cbor-octetp)
                                   (floor mod)))))

(defthm fn-cbor-u32-from-u32-bytes
  (implies (and (natp n) (<= n *fn-cbor-max-uint*))
           (equal (fn-cbor-u32-from (fn-cbor-u32-bytes n)) n))
  :hints (("Goal"
           :in-theory (e/d (fn-cbor-u32-from fn-cbor-u32-bytes)
                           (floor mod floor-floor-integer))
           :nonlinearp t
           :use ((:instance floor-mod-elim (x n) (y 256))
                 (:instance floor-mod-elim (x (floor n 256)) (y 256))
                 (:instance floor-mod-elim
                            (x (floor (floor n 256) 256)) (y 256))))))

(defthm fn-cbor-u32-bytes-are-octets
  (implies (and (natp n) (<= n *fn-cbor-max-uint*))
           (fn-cbor-octet-listp (fn-cbor-u32-bytes n)))
  :hints (("Goal" :in-theory (e/d (fn-cbor-u32-bytes
                                         fn-cbor-octet-listp
                                         fn-cbor-octetp)
                                    (floor mod floor-floor-integer)))))

(defthm fn-cbor-u16-bytes-fit-decoder-tail
  (fn-cbor-at-mostp (fn-cbor-u16-bytes n) 65537)
  :hints (("Goal" :in-theory (enable fn-cbor-u16-bytes
                                      fn-cbor-at-mostp))))

(defthm fn-cbor-u16-bytes-have-two-octets
  (and (consp (fn-cbor-u16-bytes n))
       (consp (cdr (fn-cbor-u16-bytes n)))
       (not (cdr (cdr (fn-cbor-u16-bytes n)))))
  :hints (("Goal" :in-theory (enable fn-cbor-u16-bytes))))

(defthm fn-cbor-u32-bytes-fit-decoder-tail
  (fn-cbor-at-mostp (fn-cbor-u32-bytes n) 65537)
  :hints (("Goal" :in-theory (enable fn-cbor-u32-bytes
                                      fn-cbor-at-mostp))))

(defthm fn-cbor-u32-bytes-have-four-octets
  (and (consp (fn-cbor-u32-bytes n))
       (consp (cdr (fn-cbor-u32-bytes n)))
       (consp (cdr (cdr (fn-cbor-u32-bytes n))))
       (consp (cdr (cdr (cdr (fn-cbor-u32-bytes n)))))
       (not (cdr (cdr (cdr (cdr (fn-cbor-u32-bytes n)))))))
  :hints (("Goal" :in-theory (enable fn-cbor-u32-bytes))))

(defthm fn-cbor-at-mostp-from-length
  (implies (and (true-listp xs)
                (natp bound)
                (<= (len xs) bound))
           (fn-cbor-at-mostp xs bound))
  :hints (("Goal" :induct (fn-cbor-at-mostp xs bound))))

(defthm fn-cbor-at-mostp-append
  (implies (and (true-listp xs)
                (true-listp ys)
                (natp x-bound)
                (natp y-bound)
                (fn-cbor-at-mostp xs x-bound)
                (fn-cbor-at-mostp ys y-bound))
           (fn-cbor-at-mostp (append xs ys) (+ x-bound y-bound)))
  :hints (("Goal" :induct (fn-cbor-at-mostp xs x-bound))))

(defthm fn-cbor-byte-header-fits
  (implies (and (natp n) (<= n *fn-cbor-max-bytes*))
           (fn-cbor-at-mostp (fn-cbor-encode-argument 2 n) 3))
  :hints (("Goal"
           :cases ((< n 24) (< n 256))
           :in-theory (enable fn-cbor-encode-argument
                               fn-cbor-at-mostp))))

(defthm fn-cbor-byte-encoding-fits-input-bound
  (implies (and (fn-cbor-octet-listp xs)
                (<= (len xs) *fn-cbor-max-bytes*))
           (fn-cbor-at-mostp
            (append (fn-cbor-encode-argument 2 (len xs)) xs)
            *fn-cbor-max-input*))
  :hints (("Goal"
           :use ((:instance fn-cbor-at-mostp-append
                            (xs (fn-cbor-encode-argument 2 (len xs)))
                            (ys xs)
                            (x-bound 3)
                            (y-bound 65535))))))

(defthm fn-cbor-octet-listp-append
  (implies (true-listp xs)
           (equal (fn-cbor-octet-listp (append xs ys))
                  (and (fn-cbor-octet-listp xs)
                       (fn-cbor-octet-listp ys))))
  :hints (("Goal" :induct (fn-cbor-octet-listp xs))))

(defthm fn-cbor-byte-header-are-octets
  (implies (and (natp n) (<= n *fn-cbor-max-bytes*))
           (fn-cbor-octet-listp (fn-cbor-encode-argument 2 n)))
  :hints (("Goal"
           :cases ((< n 24) (< n 256))
           :in-theory (e/d (fn-cbor-encode-argument
                              fn-cbor-octet-listp
                              fn-cbor-octetp)
                             (fn-cbor-u16-bytes)))))

(defthm fn-cbor-byte-encoding-are-octets
  (implies (and (fn-cbor-octet-listp xs)
                (<= (len xs) *fn-cbor-max-bytes*))
           (fn-cbor-octet-listp
            (append (fn-cbor-encode-argument 2 (len xs)) xs)))
  :hints (("Goal"
           :in-theory (disable fn-cbor-encode-argument
                               fn-cbor-u16-bytes)
           :use ((:instance fn-cbor-byte-header-are-octets
                            (n (len xs)))
                 (:instance fn-cbor-octet-listp-append
                            (xs (fn-cbor-encode-argument 2 (len xs)))
                            (ys xs))))))

; This covers every unsigned integer accepted by the profile, including all
; four RFC 8949 deterministic argument widths (immediate, uint8, uint16,
; uint32).  The byte-conversion lemmas above discharge the non-immediate
; cases; no host codec participates in this statement.
(defthm fn-cbor-uint32-round-trip
  (implies (and (natp n) (<= n *fn-cbor-max-uint*))
           (equal (fn-cbor-decode-exact
                   (fn-cbor-encode (cons :uint n)))
                  (fn-cbor-ok (cons :uint n) nil)))
  :hints (("Goal"
           :cases ((< n 24) (< n 256) (< n 65536))
           :in-theory (e/d (fn-cbor-decode-exact
                              fn-cbor-decode
                              fn-cbor-at-mostp
                              fn-cbor-octet-listp
                              fn-cbor-encode
                              fn-cbor-valuep
                              fn-cbor-encode-argument
                              fn-cbor-decode-unsigned
                              fn-cbor-decode-argument
                              fn-cbor-canonical-argumentp)
                             (fn-cbor-u16-bytes
                              fn-cbor-u16-from
                              fn-cbor-u32-bytes
                              fn-cbor-u32-from)))))

(defthm fn-cbor-take-whole-list
  (implies (true-listp xs)
           (equal (take (len xs) xs) xs))
  :hints (("Goal" :induct (len xs))))

(defthm fn-cbor-nthcdr-whole-list
  (implies (true-listp xs)
           (equal (nthcdr (len xs) xs) nil))
  :hints (("Goal" :induct (len xs))))

(defthm fn-cbor-u16-prefix-fields
  (and (consp (append (fn-cbor-u16-bytes n) xs))
       (consp (cdr (append (fn-cbor-u16-bytes n) xs)))
       (equal (cddr (append (fn-cbor-u16-bytes n) xs)) xs)
       (equal (fn-cbor-u16-from (append (fn-cbor-u16-bytes n) xs))
              (fn-cbor-u16-from (fn-cbor-u16-bytes n))))
  :hints (("Goal" :in-theory (disable floor mod))))

(defthm fn-cbor-byte-string-round-trip
  (implies (and (fn-cbor-octet-listp xs)
                (<= (len xs) *fn-cbor-max-bytes*))
           (equal (fn-cbor-decode-exact
                   (fn-cbor-encode (cons :bytes xs)))
                  (fn-cbor-ok (cons :bytes xs) nil)))
  :hints (("Goal"
           :cases ((< (len xs) 24) (< (len xs) 256))
           :use ((:instance fn-cbor-byte-encoding-fits-input-bound)
                 (:instance fn-cbor-byte-encoding-are-octets))
           :in-theory (disable fn-cbor-u16-bytes fn-cbor-u16-from
                               fn-cbor-at-mostp fn-cbor-octet-listp
                               take nthcdr))))

(defthm fn-cbor-value-round-trip
  (implies (fn-cbor-valuep value)
           (equal (fn-cbor-decode-exact (fn-cbor-encode value))
                  (fn-cbor-ok value nil)))
  :hints (("Goal"
           :use ((:instance fn-cbor-uint32-round-trip (n (cdr value)))
                 (:instance fn-cbor-byte-string-round-trip (xs (cdr value))))
           :in-theory (disable fn-cbor-encode fn-cbor-decode-exact))))

; Local arithmetic normalization supports the inverse base-256 direction.
(local (include-book "arithmetic/top" :dir :system))

(defthm fn-cbor-u16-to-from-octets
  (implies (and (fn-cbor-octet-listp xs)
                (consp xs) (consp (cdr xs)))
           (equal (fn-cbor-u16-bytes (fn-cbor-u16-from xs))
                  (list (car xs) (cadr xs))))
  :hints (("Goal"
           :expand ((fn-cbor-octet-listp xs) (fn-cbor-octet-listp (cdr xs)))
           :in-theory (e/d (associativity-of-* distributivity) (floor mod))
           :nonlinearp t)))

(defthm fn-cbor-u32-to-from-octets
  (implies (and (fn-cbor-octet-listp xs)
                (consp xs) (consp (cdr xs))
                (consp (cddr xs)) (consp (cdddr xs)))
           (equal (fn-cbor-u32-bytes (fn-cbor-u32-from xs))
                  (list (car xs) (cadr xs) (caddr xs) (cadddr xs))))
  :hints (("Goal"
           :expand ((fn-cbor-octet-listp xs) (fn-cbor-octet-listp (cdr xs))
                    (fn-cbor-octet-listp (cddr xs)) (fn-cbor-octet-listp (cdddr xs)))
           :in-theory (e/d (associativity-of-* distributivity)
                           (floor mod floor-floor-integer))
           :nonlinearp t)))

(defthm fn-cbor-take-and-rest-reconstruct
  (implies (and (natp n) (<= n (len xs)))
           (equal (append (take n xs) (nthcdr n xs)) xs))
  :hints (("Goal" :induct (take n xs))))

(defthm fn-cbor-take-has-length
  (implies (natp n)
           (equal (len (take n xs)) n))
  :hints (("Goal" :induct (take n xs))))

(defthm fn-cbor-take-preserves-octets
  (implies (and (fn-cbor-octet-listp xs) (natp n) (<= n (len xs)))
           (fn-cbor-octet-listp (take n xs)))
  :hints (("Goal" :induct (take n xs))))

(defthm fn-cbor-u16-from-bounds
  (implies (and (fn-cbor-octet-listp xs)
                (consp xs) (consp (cdr xs)))
           (and (natp (fn-cbor-u16-from xs))
                (< (fn-cbor-u16-from xs) 65536)))
  :hints (("Goal"
           :expand ((fn-cbor-octet-listp xs) (fn-cbor-octet-listp (cdr xs))))))

(defthm fn-cbor-u32-from-bounds
  (implies (and (fn-cbor-octet-listp xs)
                (consp xs) (consp (cdr xs))
                (consp (cddr xs)) (consp (cdddr xs)))
           (and (natp (fn-cbor-u32-from xs))
                (<= (fn-cbor-u32-from xs) *fn-cbor-max-uint*)))
  :hints (("Goal"
           :expand ((fn-cbor-octet-listp xs) (fn-cbor-octet-listp (cdr xs))
                    (fn-cbor-octet-listp (cddr xs)) (fn-cbor-octet-listp (cdddr xs))))))

(defthm fn-cbor-u16-from-upper-bound
  (implies (and (fn-cbor-octet-listp xs)
                (consp xs) (consp (cdr xs)))
           (< (fn-cbor-u16-from xs) 65536))
  :rule-classes :linear
  :hints (("Goal" :use fn-cbor-u16-from-bounds)))

(defthm fn-cbor-u32-from-upper-bound
  (implies (and (fn-cbor-octet-listp xs)
                (consp xs) (consp (cdr xs))
                (consp (cddr xs)) (consp (cdddr xs)))
           (<= (fn-cbor-u32-from xs) *fn-cbor-max-uint*))
  :rule-classes :linear
  :hints (("Goal" :use fn-cbor-u32-from-bounds)))

(defthm fn-cbor-unsigned-reencode-prefix
  (implies (and (fn-cbor-octet-listp tail)
                (natp additional) (< additional 32)
                (fn-cbor-result-okp (fn-cbor-decode-unsigned additional tail)))
           (equal (append (fn-cbor-encode
                           (fn-cbor-result-value
                            (fn-cbor-decode-unsigned additional tail)))
                          (fn-cbor-result-rest
                           (fn-cbor-decode-unsigned additional tail)))
                  (cons additional tail)))
  :hints (("Goal" :in-theory (disable fn-cbor-u16-bytes fn-cbor-u16-from
                                      fn-cbor-u32-bytes fn-cbor-u32-from))))

(defthm fn-cbor-bytes-reencode-prefix
  (implies (and (fn-cbor-octet-listp tail)
                (natp additional) (< additional 32)
                (fn-cbor-result-okp (fn-cbor-decode-bytes additional tail)))
           (equal (append (fn-cbor-encode
                           (fn-cbor-result-value
                            (fn-cbor-decode-bytes additional tail)))
                          (fn-cbor-result-rest
                           (fn-cbor-decode-bytes additional tail)))
                  (cons (+ 64 additional) tail)))
  :hints (("Goal" :in-theory (disable fn-cbor-u16-bytes fn-cbor-u16-from
                                      fn-cbor-u32-bytes fn-cbor-u32-from
                                      take nthcdr))))

; Successful streaming parses reconstruct exactly the consumed prefix and its
; untouched remainder.  This covers arbitrary accepted input, not only encoder
; output, so non-minimal representations cannot pass unnoticed.
(defthm fn-cbor-decode-reencode-prefix
  (implies (fn-cbor-result-okp (fn-cbor-decode octets))
           (equal (append (fn-cbor-encode
                           (fn-cbor-result-value (fn-cbor-decode octets)))
                          (fn-cbor-result-rest (fn-cbor-decode octets)))
                  octets))
  :hints (("Goal"
           :use ((:instance fn-cbor-unsigned-reencode-prefix
                  (additional (car octets)) (tail (cdr octets)))
                 (:instance fn-cbor-bytes-reencode-prefix
                  (additional (- (car octets) 64)) (tail (cdr octets))))
           :in-theory (disable fn-cbor-decode-unsigned
                               fn-cbor-decode-bytes-bounded
                               fn-cbor-encode fn-cbor-at-mostp))))

; The bounded encoder's octets are a true list whatever the bound; the
; unbounded twin below is its instance at *fn-cbor-max-bytes*.  This one is
; a type-prescription rule and stays ENABLED on export, unlike the rewrite
; vocabulary withdrawn at the end of this book: a caller's guard obligation
; `(true-listp (fn-cbor-encode-bounded v budget))' with a FREE budget is not
; decided by evaluation the way the constant-bound twin's is, and every book
; that appends the bounded encoding meets exactly that obligation
; (stx-evidence-records, checkpoint-compaction; measured on the hbox
; freeze of dev db2e182a, 2026-09-22, where books/stx-evidence-records
; failed this guard and 55 books above it went uncertified).  A
; type-prescription rule does not backchain into `len'/`consp' goals, which
; is the cost the withdrawal below protects against.
(defthm fn-cbor-bounded-encoding-is-true-list
  (true-listp (fn-cbor-encode-bounded value max-bytes))
  :rule-classes :type-prescription)

(defthm fn-cbor-encoding-is-true-list
  (true-listp (fn-cbor-encode value)))

(defthm fn-cbor-accepted-input-is-canonical
  (implies (fn-cbor-result-okp (fn-cbor-decode-exact octets))
           (equal (fn-cbor-encode
                   (fn-cbor-result-value (fn-cbor-decode-exact octets)))
                  octets))
  :hints (("Goal" :use fn-cbor-decode-reencode-prefix
           :in-theory (disable fn-cbor-decode fn-cbor-encode))))

; ---------------------------------------------------------------------------
; The wide uint (packet P6): round trip, agreement with the narrow profile,
; and reverse canonicality.

(local (defthm fn-cbor-u32-from-of-u32-bytes-append
         (equal (fn-cbor-u32-from (append (fn-cbor-u32-bytes x) y))
                (fn-cbor-u32-from (fn-cbor-u32-bytes x)))
         :hints (("Goal" :in-theory (e/d (fn-cbor-u32-from fn-cbor-u32-bytes)
                                         (floor mod))))))

(local (defthm fn-cbor-cddddr-of-u32-bytes-append
         (equal (cddddr (append (fn-cbor-u32-bytes x) y)) y)
         :hints (("Goal" :in-theory (e/d (fn-cbor-u32-bytes) (floor mod))))))

(local (defthm fn-cbor-u64-halves
         (implies (natp n)
                  (equal (+ (* 4294967296 (floor n 4294967296))
                            (mod n 4294967296))
                         n))))

(local (defthm fn-cbor-wide-append-assoc
         (equal (append (append a b) c) (append a (append b c)))))

(local (defthm fn-cbor-u64-half-bounds
         (implies (and (natp n) (<= n *fn-cbor-max-uint64*))
                  (and (<= (floor n 4294967296) *fn-cbor-max-uint*)
                       (<= (mod n 4294967296) *fn-cbor-max-uint*)
                       (natp (floor n 4294967296))
                       (natp (mod n 4294967296))))
         :hints (("Goal" :use ((:instance floor-bounded-by-/
                                          (x n) (y 4294967296))
                               (:instance mod-bounded-by-modulus
                                          (x n) (y 4294967296)))
                  :in-theory (disable floor-bounded-by-/ mod-bounded-by-modulus
                                      floor mod)))))

(defthm fn-cbor-u64-from-u64-bytes
  (implies (and (natp n) (<= n *fn-cbor-max-uint64*))
           (equal (fn-cbor-u64-from (append (fn-cbor-u64-bytes n) rest)) n))
  :hints (("Goal" :in-theory (e/d (fn-cbor-u64-from fn-cbor-u64-bytes
                                   fn-cbor-u32-from-u32-bytes)
                                  (floor mod fn-cbor-u32-from fn-cbor-u32-bytes)))))

(defthm fn-cbor-u64-bytes-are-octets
  (implies (and (natp n) (<= n *fn-cbor-max-uint64*))
           (fn-cbor-octet-listp (fn-cbor-u64-bytes n)))
  :hints (("Goal" :in-theory (e/d (fn-cbor-u64-bytes fn-cbor-octet-listp-append)
                                  (floor mod fn-cbor-u32-bytes))
           :use ((:instance fn-cbor-u32-bytes-are-octets (n (floor n 4294967296)))
                 (:instance fn-cbor-u32-bytes-are-octets (n (mod n 4294967296)))))))

(local (defthm fn-cbor-wide-len-of-append
         (equal (len (append x y)) (+ (len x) (len y)))))

(local (defthm fn-cbor-wide-len-of-u32-bytes
         (equal (len (fn-cbor-u32-bytes n)) 4)
         :hints (("Goal" :in-theory (e/d (fn-cbor-u32-bytes) (floor mod))))))

(defthm fn-cbor-u64-bytes-length
  (equal (len (fn-cbor-u64-bytes n)) 8)
  :hints (("Goal" :in-theory (e/d (fn-cbor-u64-bytes)
                                  (floor mod fn-cbor-u32-bytes)))))

(local (defthm fn-cbor-wide-nthcdr-of-append
         (implies (equal (len x) k)
                  (equal (nthcdr k (append x y)) y))))

(local (defthm fn-cbor-wide-at-leastp-of-append
         (implies (and (natp k) (<= k (len x)))
                  (fn-cbor-at-leastp (append x y) k))
         :hints (("Goal" :in-theory (enable fn-cbor-at-leastp-is-length-lower-bound)))))

; The wide encoder writes the narrow encoder's bytes for every narrow value.
(defthm fn-cbor-encode-uint-wide-is-narrow
  (implies (and (natp n) (<= n *fn-cbor-max-uint*))
           (equal (fn-cbor-encode-uint-wide n)
                  (fn-cbor-encode (cons :uint n)))))

; Whenever the narrow one-item decoder accepts, the wide one returns the
; same result: no accepted encoding changes meaning.
(defthm fn-cbor-decode-prechecked-wide-extends-narrow
  (implies (fn-cbor-result-okp (fn-cbor-decode-prechecked octets budget))
           (equal (fn-cbor-decode-prechecked-wide octets budget)
                  (fn-cbor-decode-prechecked octets budget))))

(local (defthm fn-cbor-wide-u32-prefix-fields
  (and (consp (append (fn-cbor-u32-bytes n) xs))
       (consp (cdr (append (fn-cbor-u32-bytes n) xs)))
       (consp (cddr (append (fn-cbor-u32-bytes n) xs)))
       (consp (cdddr (append (fn-cbor-u32-bytes n) xs)))
       (equal (cddddr (append (fn-cbor-u32-bytes n) xs)) xs)
       (equal (fn-cbor-u32-from (append (fn-cbor-u32-bytes n) xs))
              (fn-cbor-u32-from (fn-cbor-u32-bytes n))))
  :hints (("Goal" :in-theory (e/d (fn-cbor-u32-bytes fn-cbor-u32-from)
                                  (floor mod))))))

(local (defthm fn-cbor-narrow-prechecked-uint-round-trip
  (implies (and (natp n) (<= n *fn-cbor-max-uint*)
                (fn-cbor-octet-listp rest))
           (equal (fn-cbor-decode-prechecked
                   (append (fn-cbor-encode (cons :uint n)) rest) budget)
                  (fn-cbor-ok (cons :uint n) rest)))
  :hints (("Goal" :cases ((< n 24) (< n 256) (< n 65536))
           :in-theory (disable fn-cbor-u16-bytes fn-cbor-u32-bytes
                               fn-cbor-u16-from fn-cbor-u32-from
                               fn-cbor-at-mostp)))))

(local (defthm fn-cbor-wide-u64-uint-round-trip
  (implies (and (natp n) (< *fn-cbor-max-uint* n) (<= n *fn-cbor-max-uint64*)
                (fn-cbor-octet-listp rest))
           (equal (fn-cbor-decode-unsigned-wide 27 (append (fn-cbor-u64-bytes n) rest))
                  (fn-cbor-ok (cons :uint n) rest)))
  :hints (("Goal" :in-theory (e/d (fn-cbor-decode-unsigned-wide)
                                  (fn-cbor-u64-bytes fn-cbor-u64-from))))))

(local (defthm fn-cbor-decode-prechecked-wide-of-narrow-uint
  (implies (and (natp n) (<= n *fn-cbor-max-uint*)
                (fn-cbor-octet-listp rest))
           (equal (fn-cbor-decode-prechecked-wide
                   (append (fn-cbor-encode-uint-wide n) rest) budget)
                  (fn-cbor-ok (cons :uint n) rest)))
  :hints (("Goal" :use ((:instance fn-cbor-decode-prechecked-wide-extends-narrow
                         (octets (append (fn-cbor-encode (cons :uint n)) rest))))
           :in-theory (e/d (fn-cbor-encode-uint-wide-is-narrow)
                           (fn-cbor-decode-prechecked-wide-extends-narrow
                            fn-cbor-encode-uint-wide fn-cbor-encode
                            fn-cbor-decode-prechecked fn-cbor-decode-prechecked-wide))))))

(local (defthm fn-cbor-decode-prechecked-wide-of-u64-uint
  (implies (and (natp n) (< *fn-cbor-max-uint* n) (<= n *fn-cbor-max-uint64*)
                (fn-cbor-octet-listp rest))
           (equal (fn-cbor-decode-prechecked-wide
                   (append (fn-cbor-encode-uint-wide n) rest) budget)
                  (fn-cbor-ok (cons :uint n) rest)))
  :hints (("Goal" :in-theory (e/d (fn-cbor-encode-uint-wide
                                   fn-cbor-decode-prechecked-wide)
                                  (fn-cbor-decode-unsigned-wide
                                   fn-cbor-u64-bytes fn-cbor-u64-from))))))

(defthm fn-cbor-decode-prechecked-wide-of-uint
  (implies (and (natp n) (<= n *fn-cbor-max-uint64*)
                (fn-cbor-octet-listp rest))
           (equal (fn-cbor-decode-prechecked-wide
                   (append (fn-cbor-encode-uint-wide n) rest) budget)
                  (fn-cbor-ok (cons :uint n) rest)))
  :hints (("Goal" :cases ((<= n *fn-cbor-max-uint*))
           :in-theory (disable fn-cbor-encode-uint-wide
                               fn-cbor-decode-prechecked-wide))))

(local (defthm fn-cbor-narrow-unsigned-value-bound
  (implies (and (fn-cbor-octet-listp tail) (natp additional)
                (fn-cbor-result-okp (fn-cbor-decode-unsigned additional tail)))
           (and (natp (cdr (fn-cbor-result-value (fn-cbor-decode-unsigned additional tail))))
                (<= (cdr (fn-cbor-result-value (fn-cbor-decode-unsigned additional tail)))
                    *fn-cbor-max-uint*)))
  :hints (("Goal" :in-theory (disable fn-cbor-u16-from fn-cbor-u32-from)))))

(local (defthm fn-cbor-decode-prechecked-wide-when-not-27
  (implies (not (and (consp octets) (equal (car octets) 27)))
           (equal (fn-cbor-decode-prechecked-wide octets budget)
                  (fn-cbor-decode-prechecked octets budget)))
  :hints (("Goal" :in-theory (e/d (fn-cbor-decode-prechecked-wide
                                   fn-cbor-decode-unsigned-wide
                                   fn-cbor-decode-prechecked)
                                  (fn-cbor-decode-unsigned
                                   fn-cbor-decode-bytes-bounded))))))

(local (defthm fn-cbor-bytes-bounded-value-is-bytes
  (implies (fn-cbor-result-okp (fn-cbor-decode-bytes-bounded additional tail budget))
           (equal (car (fn-cbor-result-value
                        (fn-cbor-decode-bytes-bounded additional tail budget)))
                  :bytes))
  :hints (("Goal" :in-theory (e/d (fn-cbor-decode-bytes-bounded)
                                  (fn-cbor-decode-argument take nthcdr))))))

(local (defthm fn-cbor-narrow-prechecked-uint-domain
  (implies (and (fn-cbor-octet-listp octets)
                (fn-cbor-result-okp (fn-cbor-decode-prechecked octets budget))
                (equal (car (fn-cbor-result-value
                             (fn-cbor-decode-prechecked octets budget)))
                       :uint))
           (and (natp (cdr (fn-cbor-result-value
                            (fn-cbor-decode-prechecked octets budget))))
                (<= (cdr (fn-cbor-result-value
                          (fn-cbor-decode-prechecked octets budget)))
                    *fn-cbor-max-uint*)))
  :hints (("Goal" :use ((:instance fn-cbor-narrow-unsigned-value-bound
                         (additional (car octets)) (tail (cdr octets))))
           :in-theory (e/d (fn-cbor-decode-prechecked)
                           (fn-cbor-narrow-unsigned-value-bound
                            fn-cbor-decode-unsigned fn-cbor-decode-bytes-bounded))))))

(defthm fn-cbor-u64-from-bounds
  (implies (and (fn-cbor-octet-listp xs) (fn-cbor-at-leastp xs 8))
           (and (natp (fn-cbor-u64-from xs))
                (<= (fn-cbor-u64-from xs) *fn-cbor-max-uint64*)))
  :hints (("Goal"
           :expand ((fn-cbor-at-leastp xs 8) (fn-cbor-at-leastp (cdr xs) 7)
                    (fn-cbor-at-leastp (cddr xs) 6) (fn-cbor-at-leastp (cdddr xs) 5)
                    (fn-cbor-at-leastp (cddddr xs) 4)
                    (fn-cbor-at-leastp (cdr (cddddr xs)) 3)
                    (fn-cbor-at-leastp (cddr (cddddr xs)) 2)
                    (fn-cbor-at-leastp (cdddr (cddddr xs)) 1)
                    (fn-cbor-octet-listp xs) (fn-cbor-octet-listp (cdr xs))
                    (fn-cbor-octet-listp (cddr xs)) (fn-cbor-octet-listp (cdddr xs)))
           :use ((:instance fn-cbor-u32-from-bounds (xs (cddddr xs)))
                 (:instance fn-cbor-u32-from-bounds (xs xs)))
           :in-theory (e/d (fn-cbor-u64-from)
                           (fn-cbor-u32-from-bounds fn-cbor-u32-from
                            fn-cbor-at-leastp-is-length-lower-bound)))))

(defthm fn-cbor-decode-prechecked-wide-uint-domain
  (implies (and (fn-cbor-result-okp (fn-cbor-decode-prechecked-wide octets budget))
                (equal (car (fn-cbor-result-value
                             (fn-cbor-decode-prechecked-wide octets budget)))
                       :uint)
                (fn-cbor-octet-listp octets))
           (and (natp (cdr (fn-cbor-result-value
                            (fn-cbor-decode-prechecked-wide octets budget))))
                (<= (cdr (fn-cbor-result-value
                          (fn-cbor-decode-prechecked-wide octets budget)))
                    *fn-cbor-max-uint64*)))
  :hints (("Goal" :cases ((and (consp octets) (equal (car octets) 27))))
          ("Subgoal 2" :use fn-cbor-narrow-prechecked-uint-domain
           :in-theory (disable fn-cbor-narrow-prechecked-uint-domain
                               fn-cbor-decode-prechecked-wide
                               fn-cbor-decode-prechecked))
          ("Subgoal 1" :use ((:instance fn-cbor-u64-from-bounds (xs (cdr octets))))
           :in-theory (e/d (fn-cbor-decode-prechecked-wide fn-cbor-decode-unsigned-wide)
                           (fn-cbor-u64-from-bounds fn-cbor-u64-from
                            fn-cbor-decode-prechecked)))))

(local (defthm fn-cbor-u64-floor-of-halves
  (implies (and (natp hi) (natp lo) (< lo 4294967296))
           (equal (floor (+ lo (* 4294967296 hi)) 4294967296) hi))
  :hints (("Goal" :in-theory (disable floor mod)
           :use ((:instance floor-mod-elim (x (+ lo (* 4294967296 hi))) (y 4294967296))
                 (:instance mod-bounded-by-modulus (x (+ lo (* 4294967296 hi))) (y 4294967296))
)))))

(local (defthm fn-cbor-u64-split-of-halves
  (implies (and (natp hi) (natp lo) (< lo 4294967296))
           (and (equal (floor (+ lo (* 4294967296 hi)) 4294967296) hi)
                (equal (mod (+ lo (* 4294967296 hi)) 4294967296) lo)))
  :hints (("Goal" :in-theory (e/d (mod) (floor))))))

(defthm fn-cbor-u64-to-from-octets
  (implies (and (fn-cbor-octet-listp xs) (fn-cbor-at-leastp xs 8))
           (equal (fn-cbor-u64-bytes (fn-cbor-u64-from xs))
                  (take 8 xs)))
  :hints (("Goal"
           :expand ((fn-cbor-at-leastp xs 8) (fn-cbor-at-leastp (cdr xs) 7)
                    (fn-cbor-at-leastp (cddr xs) 6) (fn-cbor-at-leastp (cdddr xs) 5)
                    (fn-cbor-at-leastp (cddddr xs) 4)
                    (fn-cbor-at-leastp (cdr (cddddr xs)) 3)
                    (fn-cbor-at-leastp (cddr (cddddr xs)) 2)
                    (fn-cbor-at-leastp (cdddr (cddddr xs)) 1)
                    (fn-cbor-octet-listp xs) (fn-cbor-octet-listp (cdr xs))
                    (fn-cbor-octet-listp (cddr xs)) (fn-cbor-octet-listp (cdddr xs)))
           :use ((:instance fn-cbor-u32-to-from-octets (xs (cddddr xs)))
                 (:instance fn-cbor-u32-to-from-octets (xs xs))
                 (:instance fn-cbor-u32-from-bounds (xs (cddddr xs)))
                 (:instance fn-cbor-u32-from-bounds (xs xs))
                 (:instance fn-cbor-u64-split-of-halves
                  (hi (fn-cbor-u32-from xs)) (lo (fn-cbor-u32-from (cddddr xs)))))
           :in-theory (e/d (fn-cbor-u64-bytes fn-cbor-u64-from)
                           (fn-cbor-u64-split-of-halves fn-cbor-u32-from-bounds
                            fn-cbor-u32-to-from-octets
                            fn-cbor-u32-from fn-cbor-u32-bytes floor mod
                            fn-cbor-at-leastp-is-length-lower-bound)))))

(local (defthm fn-cbor-wide-cons-uint-of-cdr
  (implies (equal (car v) :uint)
           (equal (cons :uint (cdr v)) v))))

(local (defthm fn-cbor-narrow-prechecked-uint-reencode
  (implies (and (fn-cbor-octet-listp octets)
                (fn-cbor-result-okp (fn-cbor-decode-prechecked octets budget))
                (equal (car (fn-cbor-result-value
                             (fn-cbor-decode-prechecked octets budget)))
                       :uint))
           (equal (append (fn-cbor-encode
                           (cons :uint (cdr (fn-cbor-result-value
                                             (fn-cbor-decode-prechecked octets budget)))))
                          (fn-cbor-result-rest
                           (fn-cbor-decode-prechecked octets budget)))
                  octets))
  :hints (("Goal" :use ((:instance fn-cbor-unsigned-reencode-prefix
                         (additional (car octets)) (tail (cdr octets))))
           :in-theory (e/d (fn-cbor-decode-prechecked)
                           (fn-cbor-unsigned-reencode-prefix fn-cbor-encode
                            fn-cbor-decode-unsigned fn-cbor-decode-bytes-bounded))))))

(local (defthm fn-cbor-wide-27-reencode
  (implies (and (fn-cbor-octet-listp octets)
                (consp octets) (equal (car octets) 27)
                (fn-cbor-result-okp (fn-cbor-decode-prechecked-wide octets budget)))
           (equal (append (fn-cbor-encode-uint-wide
                           (cdr (fn-cbor-result-value
                                 (fn-cbor-decode-prechecked-wide octets budget))))
                          (fn-cbor-result-rest
                           (fn-cbor-decode-prechecked-wide octets budget)))
                  octets))
  :hints (("Goal" :use ((:instance fn-cbor-u64-to-from-octets (xs (cdr octets)))
                        (:instance fn-cbor-u64-from-bounds (xs (cdr octets)))
                        (:instance fn-cbor-take-and-rest-reconstruct (n 8) (xs (cdr octets))))
           :in-theory (e/d (fn-cbor-decode-prechecked-wide fn-cbor-decode-unsigned-wide
                            fn-cbor-encode-uint-wide)
                           (fn-cbor-u64-to-from-octets fn-cbor-u64-from-bounds
                            fn-cbor-take-and-rest-reconstruct
                            fn-cbor-u64-bytes fn-cbor-u64-from take nthcdr))))))

; Reverse canonicality: an accepted uint is exactly the wide encoding of its
; value followed by the returned rest.
(defthm fn-cbor-decode-prechecked-wide-uint-reencode-prefix
  (implies (and (fn-cbor-octet-listp octets)
                (fn-cbor-result-okp (fn-cbor-decode-prechecked-wide octets budget))
                (equal (car (fn-cbor-result-value
                             (fn-cbor-decode-prechecked-wide octets budget)))
                       :uint))
           (equal (append (fn-cbor-encode-uint-wide
                           (cdr (fn-cbor-result-value
                                 (fn-cbor-decode-prechecked-wide octets budget))))
                          (fn-cbor-result-rest
                           (fn-cbor-decode-prechecked-wide octets budget)))
                  octets))
  :hints (("Goal" :cases ((and (consp octets) (equal (car octets) 27))))
          ("Subgoal 2" :use (fn-cbor-narrow-prechecked-uint-reencode
                             fn-cbor-narrow-prechecked-uint-domain)
           :in-theory (e/d (fn-cbor-encode-uint-wide-is-narrow)
                           (fn-cbor-narrow-prechecked-uint-reencode
                            fn-cbor-narrow-prechecked-uint-domain
                            fn-cbor-encode-uint-wide fn-cbor-encode
                            fn-cbor-decode-prechecked-wide
                            fn-cbor-decode-prechecked)))
          ("Subgoal 1" :use fn-cbor-wide-27-reencode
           :in-theory (disable fn-cbor-wide-27-reencode fn-cbor-encode-uint-wide
                               fn-cbor-decode-prechecked-wide
                               fn-cbor-decode-prechecked))))

(local (defthm fn-cbor-wide-octet-listp-of-nthcdr
  (implies (fn-cbor-octet-listp xs)
           (fn-cbor-octet-listp (nthcdr n xs)))))

(local (defthm fn-cbor-narrow-prechecked-rest-octets
  (implies (and (fn-cbor-octet-listp octets)
                (fn-cbor-result-okp (fn-cbor-decode-prechecked octets budget)))
           (fn-cbor-octet-listp
            (fn-cbor-result-rest (fn-cbor-decode-prechecked octets budget))))
  :hints (("Goal" :in-theory (disable fn-cbor-u16-from fn-cbor-u32-from take)))))

(defthm fn-cbor-decode-prechecked-wide-rest-octets
  (implies (and (fn-cbor-octet-listp octets)
                (fn-cbor-result-okp (fn-cbor-decode-prechecked-wide octets budget)))
           (fn-cbor-octet-listp
            (fn-cbor-result-rest (fn-cbor-decode-prechecked-wide octets budget))))
  :hints (("Goal" :cases ((and (consp octets) (equal (car octets) 27))))
          ("Subgoal 2" :in-theory (disable fn-cbor-decode-prechecked-wide
                                           fn-cbor-decode-prechecked))
          ("Subgoal 1" :in-theory (e/d (fn-cbor-decode-prechecked-wide
                                        fn-cbor-decode-unsigned-wide)
                                       (fn-cbor-u64-from fn-cbor-decode-prechecked)))))

(defthm fn-cbor-encode-uint-wide-octets
  (implies (and (natp n) (<= n *fn-cbor-max-uint64*))
           (and (fn-cbor-octet-listp (fn-cbor-encode-uint-wide n))
                (true-listp (fn-cbor-encode-uint-wide n))
                (consp (fn-cbor-encode-uint-wide n))))
  :hints (("Goal" :in-theory (e/d (fn-cbor-encode-uint-wide)
                                  (fn-cbor-u64-bytes fn-cbor-u16-bytes
                                   fn-cbor-u32-bytes))
           :use (fn-cbor-u64-bytes-are-octets
                 (:instance fn-cbor-u32-bytes-are-octets)
                 (:instance fn-cbor-u16-bytes-are-octets)))))

; -----------------------------------------------------------------------------
; Export theory.
;
; The keystones leave this book enabled: `fn-cbor-uint32-round-trip',
; `fn-cbor-byte-string-round-trip', `fn-cbor-value-round-trip',
; `fn-cbor-decode-reencode-prefix' and `fn-cbor-accepted-input-is-canonical'.
; Everything else here is arithmetic and list vocabulary, including every rule
; that backchains into `len', `consp' or `true-listp'; those were the rules
; that made a plain `append' associativity goal take 108 s in
; `frame-invariants' (planning/lanes/LANEDUMP-twins-into-acl2.md, 3.1b).  A
; book that needs them enables this one name and says why.

(deftheory fn-cbor-invariants-vocabulary
  '(fn-cbor-u16-from-u16-bytes fn-cbor-u16-bytes-are-octets
    fn-cbor-u32-from-u32-bytes fn-cbor-u32-bytes-are-octets
    fn-cbor-u16-bytes-fit-decoder-tail fn-cbor-u16-bytes-have-two-octets
    fn-cbor-u32-bytes-fit-decoder-tail fn-cbor-u32-bytes-have-four-octets
    fn-cbor-octet-listp-implies-true-listp fn-cbor-at-mostp-from-length
    fn-cbor-at-mostp-append fn-cbor-byte-header-fits
    fn-cbor-byte-encoding-fits-input-bound fn-cbor-octet-listp-append
    fn-cbor-byte-header-are-octets fn-cbor-byte-encoding-are-octets
    fn-cbor-take-whole-list fn-cbor-nthcdr-whole-list
    fn-cbor-u16-prefix-fields fn-cbor-take-and-rest-reconstruct
    fn-cbor-take-has-length fn-cbor-take-preserves-octets
    fn-cbor-u16-from-bounds fn-cbor-u32-from-bounds
    fn-cbor-u16-from-upper-bound fn-cbor-u32-from-upper-bound
    fn-cbor-u16-to-from-octets fn-cbor-u32-to-from-octets
    fn-cbor-unsigned-reencode-prefix fn-cbor-bytes-reencode-prefix
    fn-cbor-encoding-is-true-list))

(in-theory (disable fn-cbor-u16-from-u16-bytes fn-cbor-u16-bytes-are-octets
             fn-cbor-u32-from-u32-bytes fn-cbor-u32-bytes-are-octets
             fn-cbor-u16-bytes-fit-decoder-tail
             fn-cbor-u16-bytes-have-two-octets
             fn-cbor-u32-bytes-fit-decoder-tail
             fn-cbor-u32-bytes-have-four-octets
             fn-cbor-octet-listp-implies-true-listp
             fn-cbor-at-mostp-from-length fn-cbor-at-mostp-append
             fn-cbor-byte-header-fits
             fn-cbor-byte-encoding-fits-input-bound
             fn-cbor-octet-listp-append fn-cbor-byte-header-are-octets
             fn-cbor-byte-encoding-are-octets fn-cbor-take-whole-list
             fn-cbor-nthcdr-whole-list fn-cbor-u16-prefix-fields
             fn-cbor-take-and-rest-reconstruct fn-cbor-take-has-length
             fn-cbor-take-preserves-octets fn-cbor-u16-from-bounds
             fn-cbor-u32-from-bounds fn-cbor-u16-from-upper-bound
             fn-cbor-u32-from-upper-bound fn-cbor-u16-to-from-octets
             fn-cbor-u32-to-from-octets fn-cbor-unsigned-reencode-prefix
             fn-cbor-bytes-reencode-prefix fn-cbor-encoding-is-true-list))
