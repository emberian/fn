; Arithmetic and round-trip invariants for the bounded fn CBOR primitive
; profile.  This book introduces no new codec values or API; it proves facts
; about books/cbor.lisp using ACL2's standard quotient/remainder lemmas.

(in-package "ACL2")

(include-book "ihs/quotient-remainder-lemmas" :dir :system)
(include-book "cbor")

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
                              fn-cbor-result-okp
                              fn-cbor-result-value
                              fn-cbor-result-rest
                              fn-cbor-canonical-argumentp)
                             (fn-cbor-u16-bytes
                              fn-cbor-u16-from
                              fn-cbor-u32-bytes
                              fn-cbor-u32-from)))))
