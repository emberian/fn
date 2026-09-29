; fn: octets packed in a natural, one octet a byte (lane chunked-body, row B6
; of COMPLETE-BEFORE-6.6.0, 2026-09-28; D27).
;
;     (fn-bch-pack xs) = 256^|xs| + sum_i xs_i 256^i
;
; The top "sentinel" digit keeps trailing zero octets.  This book is the
; codec books/body-chunks.lisp builds the held article body from: the
; logical packing and unpacking (specifications), the digit reader the host
; path runs (`fn-bch-digits-onto', divide and conquer: depth log2 of the
; length, each level two shifts), the one-octet append's digit
; (`fn-bch-digit') and the constant-work length test
; (fn-bch-packed-len-is-top-digit).
;
; KEYSTONES fn-bch-unpack-of-pack (the round trip, for octet lists),
; fn-bch-pack-of-append (the packing of a concatenation),
; fn-bch-digits-onto-is-digits (the reader is the digits),
; fn-bch-unpack-is-digits (the digits of a packed natural are its octets).

(in-package "ACL2")
(local (include-book "arithmetic-5/top" :dir :system))

(local (defthm fn-bch-append-assoc
         (equal (append (append x y) z) (append x (append y z)))))

(local (defthm fn-bch-len-of-append
         (equal (len (append x y)) (+ (len x) (len y)))))

; -----------------------------------------------------------------------------
; Octets and the packed natural.

(defun fn-bch-octetp (x)
  (declare (xargs :guard t))
  (and (natp x) (< x 256)))

(defun fn-bch-octetsp (xs)
  (declare (xargs :guard t))
  (if (consp xs)
      (and (fn-bch-octetp (car xs))
           (fn-bch-octetsp (cdr xs)))
    (null xs)))

(defun fn-bch-byte (x)
  (declare (xargs :guard t))
  (if (fn-bch-octetp x) x 0))

(defthm fn-bch-byte-natp
  (natp (fn-bch-byte x))
  :rule-classes :type-prescription)

(defthm fn-bch-byte-bound
  (< (fn-bch-byte x) 256)
  :rule-classes :linear)

; The logical packing (a specification: no host path executes it; the
; executables below pack from a buffer span or by one octet).
(defun fn-bch-pack (xs)
  (declare (xargs :guard t))
  (if (consp xs)
      (+ (fn-bch-byte (car xs)) (* 256 (fn-bch-pack (cdr xs))))
    1))

(defun fn-bch-rev-onto (xs acc)
  (declare (xargs :guard t))
  (if (consp xs) (fn-bch-rev-onto (cdr xs) (cons (car xs) acc)) acc))

; The low digit first, the top (sentinel) digit dropped.  Executes by a loop
; (the digits reversed, then reversed back): no frame per octet.
(defun fn-bch-unpack-rev-onto (n acc)
  (declare (xargs :guard t :measure (nfix n)))
  (if (and (natp n) (<= 256 n))
      (fn-bch-unpack-rev-onto (floor n 256) (cons (mod n 256) acc))
    acc))

(defun fn-bch-unpack (n)
  (declare (xargs :guard t :measure (nfix n) :verify-guards nil))
  (mbe :logic (if (and (natp n) (<= 256 n))
                  (cons (mod n 256) (fn-bch-unpack (floor n 256)))
                nil)
       :exec (fn-bch-rev-onto (fn-bch-unpack-rev-onto n nil) nil)))

(defthm fn-bch-rev-onto-of-list-is-revappend
  (equal (fn-bch-rev-onto xs acc) (revappend xs acc)))

(defthm fn-bch-unpack-rev-onto-is
  (equal (fn-bch-unpack-rev-onto n acc)
         (revappend (fn-bch-unpack n) acc)))

(local (defthm fn-bch-revappend-append-acc
         (equal (revappend x (append a b))
                (append (revappend x a) b))))

(local (defthm fn-bch-revappend-to-append
         (implies (syntaxp (not (equal acc ''nil)))
                  (equal (revappend x acc)
                         (append (revappend x nil) acc)))
         :hints (("Goal" :use ((:instance fn-bch-revappend-append-acc (a nil) (b acc)))
                  :in-theory (disable fn-bch-revappend-append-acc)))))

(local (defthm fn-bch-revappend-gen
         (implies (true-listp x)
                  (equal (revappend (revappend x acc) nil)
                         (append (revappend acc nil) x)))
         :hints (("Goal" :induct (revappend x acc)))))

(local (defthm fn-bch-unpack-true-listp
         (true-listp (fn-bch-unpack n))))

(local (defthm fn-bch-revappend-revappend-nil
         (implies (true-listp x)
                  (equal (revappend (revappend x nil) nil) x))
         :hints (("Goal" :use ((:instance fn-bch-revappend-gen (acc nil)))))))

(verify-guards fn-bch-unpack)

(defun fn-bch-packedp (n)
  (declare (xargs :guard t :measure (nfix n)))
  (and (natp n)
       (if (< n 256)
           (equal n 1)
         (fn-bch-packedp (floor n 256)))))

(defthm fn-bch-pack-posp
  (posp (fn-bch-pack xs))
  :rule-classes :type-prescription)

(defthm fn-bch-pack-of-consp-at-least-256
  (implies (consp xs) (<= 256 (fn-bch-pack xs)))
  :rule-classes :linear)

(defthm fn-bch-unpack-of-pack
  (implies (fn-bch-octetsp xs)
           (equal (fn-bch-unpack (fn-bch-pack xs)) xs)))

; Packing reads each element as an octet (fn-bch-byte), so it round-trips
; any list to its octets.
(defun fn-bch-bytes (xs)
  (declare (xargs :guard t))
  (if (consp xs)
      (cons (fn-bch-byte (car xs)) (fn-bch-bytes (cdr xs)))
    nil))

(defthm fn-bch-unpack-of-pack-is-bytes
  (equal (fn-bch-unpack (fn-bch-pack xs)) (fn-bch-bytes xs)))

(defthm fn-bch-bytes-when-octetsp
  (implies (fn-bch-octetsp xs) (equal (fn-bch-bytes xs) xs)))

(defthm fn-bch-pack-of-bytes
  (equal (fn-bch-pack (fn-bch-bytes xs)) (fn-bch-pack xs)))

(defthm fn-bch-bytes-of-append
  (equal (fn-bch-bytes (append xs ys))
         (append (fn-bch-bytes xs) (fn-bch-bytes ys))))

(defthm fn-bch-pack-of-cons-byte
  (equal (fn-bch-pack (cons (fn-bch-byte x) ys))
         (fn-bch-pack (cons x ys))))

(defthm fn-bch-pack-of-append-cons-byte
  (equal (fn-bch-pack (append a (cons (fn-bch-byte x) ys)))
         (fn-bch-pack (append a (cons x ys)))))

(defthm fn-bch-packedp-of-pack
  (fn-bch-packedp (fn-bch-pack xs)))

(defthm fn-bch-octetsp-of-unpack
  (fn-bch-octetsp (fn-bch-unpack n)))

(defthm fn-bch-pack-of-unpack
  (implies (fn-bch-packedp n)
           (equal (fn-bch-pack (fn-bch-unpack n)) n)))

; 256^K, by its own recursion so the arithmetic library's normalization of
; `expt' never meets it.
(defun fn-bch-pow (k)
  (declare (xargs :guard t))
  (if (and (natp k) (< 0 k)) (* 256 (fn-bch-pow (- k 1))) 1))

(defthm fn-bch-pow-posp
  (posp (fn-bch-pow k))
  :rule-classes :type-prescription)

(defthm fn-bch-pow-of-1+
  (implies (natp k) (equal (fn-bch-pow (+ 1 k)) (* 256 (fn-bch-pow k)))))

(defthm fn-bch-pow-of-plus
  (implies (and (natp j) (natp k))
           (equal (fn-bch-pow (+ j k)) (* (fn-bch-pow j) (fn-bch-pow k)))))

(in-theory (disable fn-bch-pow))

; The packing of a concatenation: the second part's digits shifted past the
; first's (the first's sentinel is replaced by the second's value).
(defthm fn-bch-pack-of-append
  (equal (fn-bch-pack (append xs ys))
         (+ (fn-bch-pack xs)
            (* (fn-bch-pow (len xs)) (- (fn-bch-pack ys) 1)))))

(defthm fn-bch-pack-of-singleton
  (equal (fn-bch-pack (list b)) (+ 256 (fn-bch-byte b))))

; -----------------------------------------------------------------------------
; Appending one octet: the tail gains a digit under its sentinel; a full tail
; becomes the newest block.  Executes by a shift (one copy of the tail).

(local (defthm fn-bch-pow-is-expt
         (implies (natp k) (equal (fn-bch-pow k) (expt 256 k)))
         :hints (("Goal" :in-theory (enable fn-bch-pow)))))
(local (in-theory (disable fn-bch-pow-is-expt)))

(local (defthm fn-bch-ash-is-times-pow
         (implies (and (natp x) (natp k))
                  (equal (ash x (* 8 k)) (* x (fn-bch-pow k))))
         :hints (("Goal" :in-theory (enable fn-bch-pow-is-expt)))))

(defun fn-bch-digit (b k)
  (declare (xargs :guard (natp k)))
  (mbe :logic (* (+ 255 (fn-bch-byte b)) (fn-bch-pow k))
       :exec (ash (+ 255 (fn-bch-byte b)) (* 8 k))))

; -----------------------------------------------------------------------------
; Reading the octets back: the low LEN base-256 digits of N.  Total, so the
; readers below need only the wire's scalar guard; under a well-formed store
; they are the unpacking (fn-bch-unpack-is-digits).  Executes divide and
; conquer: two shifts a level, depth log2 of LEN.

(defun fn-bch-digits (n len)
  (declare (xargs :guard (and (natp n) (natp len))))
  (if (zp len)
      nil
    (cons (mod n 256) (fn-bch-digits (floor n 256) (- len 1)))))

(defthm fn-bch-unpack-is-digits
  (implies (fn-bch-packedp n)
           (equal (fn-bch-digits n (len (fn-bch-unpack n)))
                  (fn-bch-unpack n))))

(local
 (defthm fn-bch-floor-floor-256
   (implies (and (natp n) (natp h))
            (equal (floor (floor n 256) (fn-bch-pow h))
                   (floor n (fn-bch-pow (+ 1 h)))))))

(defthm fn-bch-digits-of-plus
  (implies (and (natp n) (natp a) (natp b))
           (equal (fn-bch-digits n (+ a b))
                  (append (fn-bch-digits n a)
                          (fn-bch-digits (floor n (fn-bch-pow a)) b))))
  :hints (("Goal" :induct (fn-bch-digits n a))))

(local
 (defthm fn-bch-floor-of-mod-256
   (implies (and (natp n) (posp q))
            (equal (floor (mod n (* 256 q)) 256)
                   (mod (floor n 256) q)))))

(local
 (defthm fn-bch-mod-of-mod-256
   (implies (and (natp n) (posp q))
            (equal (mod (mod n (* 256 q)) 256)
                   (mod n 256)))))

(defthm fn-bch-digits-of-zero-len
  (equal (fn-bch-digits n 0) nil))

(defthm fn-bch-digits-of-mod
  (implies (and (natp n) (natp h))
           (equal (fn-bch-digits (mod n (fn-bch-pow h)) h)
                  (fn-bch-digits n h)))
  :hints (("Goal" :induct (fn-bch-digits n h)
                  :in-theory (disable (:definition fn-bch-digits))
                  :expand ((fn-bch-pow h) (fn-bch-digits n h)
                           (fn-bch-digits (mod n (* 256 (fn-bch-pow (+ -1 h)))) h)))))

; The executable reader: the digits consed before ACC, divide and conquer.
; Depth log2 of LEN (a block: 7 levels); each level two shifts of its part.
(defun fn-bch-low (n h)
  (declare (xargs :guard (and (natp n) (natp h))
                  :guard-hints (("Goal" :in-theory (enable fn-bch-pow-is-expt mod)))))
  (mbe :logic (mod n (fn-bch-pow h))
       :exec (- n (ash (ash n (- (* 8 h))) (* 8 h)))))

(defun fn-bch-high (n h)
  (declare (xargs :guard (and (natp n) (natp h))
                  :guard-hints (("Goal" :in-theory (enable fn-bch-pow-is-expt)))))
  (mbe :logic (floor n (fn-bch-pow h))
       :exec (ash n (- (* 8 h)))))

; Half of LEN, opaque to the arithmetic library (its bounds below).
(defun fn-bch-half (len)
  (declare (xargs :guard (natp len)))
  (nfix (floor len 2)))

(defthm fn-bch-half-bounds
  (implies (and (natp len) (< 8 len))
           (and (< 0 (fn-bch-half len))
                (< (fn-bch-half len) len)))
  :rule-classes :linear)

(defthm fn-bch-half-natp
  (natp (fn-bch-half len))
  :rule-classes :type-prescription)

(in-theory (disable fn-bch-half))

(defthm fn-bch-low-natp
  (implies (and (natp n) (natp h)) (natp (fn-bch-low n h)))
  :rule-classes :type-prescription)

(defthm fn-bch-high-natp
  (implies (and (natp n) (natp h)) (natp (fn-bch-high n h)))
  :rule-classes :type-prescription)

(defthm fn-bch-digits-of-low
  (implies (and (natp n) (natp h))
           (equal (fn-bch-digits (fn-bch-low n h) h)
                  (fn-bch-digits n h))))

(defthm fn-bch-digits-split
  (implies (and (natp n) (natp a) (natp b))
           (equal (fn-bch-digits n (+ a b))
                  (append (fn-bch-digits n a)
                          (fn-bch-digits (fn-bch-high n a) b)))))

(in-theory (disable fn-bch-low fn-bch-high))

(defun fn-bch-digits-onto (n len acc)
  (declare (xargs :guard (and (natp n) (natp len))
                  :measure (nfix len)
                  :verify-guards nil))
  (if (or (zp len) (<= len 8))
      (append (fn-bch-digits n len) acc)
    (let ((h (fn-bch-half len)))
      (fn-bch-digits-onto (fn-bch-low n h) h
                          (fn-bch-digits-onto (fn-bch-high n h) (- len h) acc)))))

(defthm fn-bch-digits-onto-is-digits
  (implies (and (natp n) (natp len))
           (equal (fn-bch-digits-onto n len acc)
                  (append (fn-bch-digits n len) acc)))
  :hints (("Goal" :induct (fn-bch-digits-onto n len acc)
                  :in-theory (disable fn-bch-digits fn-bch-digits-of-plus fn-bch-digits-split
                                      fn-bch-digits-of-mod))
          ("Subgoal *1/2" :use ((:instance fn-bch-digits-split
                                           (a (fn-bch-half len)) (b (- len (fn-bch-half len))))))))

(defthm fn-bch-digits-true-listp
  (true-listp (fn-bch-digits n len))
  :rule-classes :type-prescription)

(verify-guards fn-bch-digits-onto)

; -----------------------------------------------------------------------------
; A packed natural's length in constant work: N packs exactly K octets
; exactly when its digits above them are the sentinel 1 (the store's fast
; path test, books/body-chunks.lisp fn-bch-tail-okp).

(defthm fn-bch-ash-right-is-floor-pow
  (implies (and (natp n) (natp k))
           (equal (ash n (- (* 8 k))) (floor n (fn-bch-pow k))))
  :hints (("Goal" :in-theory (enable fn-bch-pow-is-expt))))

(defthm fn-bch-packed-len-is-top-digit
   (implies (and (posp n) (natp k))
            (equal (and (fn-bch-packedp n) (equal (len (fn-bch-unpack n)) k))
                   (equal (floor n (fn-bch-pow k)) 1)))
  :rule-classes nil
  :hints (("Goal" :induct (fn-bch-digits n k)
                  :in-theory (disable fn-bch-unpack fn-bch-packedp)
                  :expand ((fn-bch-pow k) (fn-bch-unpack n) (fn-bch-packedp n)))))

; The test as the store runs it (a shift and a comparison).
(defthm fn-bch-top-digit-test
  (implies (and (posp n) (natp k))
           (equal (equal (ash n (- (* 8 k))) 1)
                  (and (fn-bch-packedp n) (equal (len (fn-bch-unpack n)) k))))
  :rule-classes nil
  :hints (("Goal" :use ((:instance fn-bch-packed-len-is-top-digit)
                        (:instance fn-bch-ash-right-is-floor-pow))
                  :in-theory (disable ash fn-bch-packedp fn-bch-unpack
                                      fn-bch-ash-right-is-floor-pow))))

; X shifted past K octets.
(defun fn-bch-shift (x k)
  (declare (xargs :guard (and (natp x) (natp k))))
  (mbe :logic (* x (fn-bch-pow k))
       :exec (ash x (* 8 k))))

