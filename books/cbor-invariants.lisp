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

(defthm fn-cbor-octet-listp-implies-true-listp
  (implies (fn-cbor-octet-listp xs)
           (true-listp xs))
  :hints (("Goal" :induct (fn-cbor-octet-listp xs))))

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

(defthm fn-cbor-encoding-is-true-list
  (true-listp (fn-cbor-encode value)))

(defthm fn-cbor-accepted-input-is-canonical
  (implies (fn-cbor-result-okp (fn-cbor-decode-exact octets))
           (equal (fn-cbor-encode
                   (fn-cbor-result-value (fn-cbor-decode-exact octets)))
                  octets))
  :hints (("Goal" :use fn-cbor-decode-reencode-prefix
           :in-theory (disable fn-cbor-decode fn-cbor-encode))))

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
