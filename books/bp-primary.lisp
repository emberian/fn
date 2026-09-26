; fn: the BPv7 primary bundle block (RFC 9171 section 4.3.1).
;
; This book models the block fn must be able to read and write in order to be a
; relay rather than an endpoint of one pinned agent: version, bundle processing
; control flags, CRC type and CRC, three endpoint IDs in both registered
; schemes, the creation timestamp, lifetime, and the fragment fields.  It also
; models the three extension blocks RFC 9171 section 4.4 requires every
; conforming implementation to recognize and parse.
;
; What this book is NOT: it is not a bundle codec (the canonical block format
; of section 4.3.2 and the payload block are not here), not a forwarder, not a
; BPSec implementation (RFC 9172 and RFC 9173 remain out of scope, and the
; primary block's CRC-MAY-be-zero allowance depends on a Block Integrity Block
; fn does not yet model), and not an administrative record or status report
; generator.  It performs no I/O and makes no acceptance decision.
;
; Section numbers cited in this book are RFC 9171's own.  In particular
; lifetime and the fragment fields are specified in section 4.3.1 as fields of
; the primary block, not in a section of their own.

(in-package "ACL2")

(include-book "bp-primary-cbor")

(local (include-book "arithmetic/top" :dir :system))
; codecs withdrew the record and cbor proof vocabularies at export (2026-09-19);
; this book reasons under them, so open them here, locally.
(local (in-theory (enable fn-cbor-record-vocabulary fn-cbor-codec-vocabulary fn-cbor-invariants-vocabulary)))

; `arithmetic/top`'s generalization rule for `mod` introduces fresh `mod`
; terms into case trees that never had one, and loops the waterfall on the
; bit-level recursions below.  Local, so nothing downstream inherits it.
(local (in-theory (disable mod-x-y-=-x+y-for-rationals)))

; -----------------------------------------------------------------------------
; Bounded exclusive-or
;
; The CRCs below need a 32-bit exclusive-or.  Defining it by recursion on bits
; keeps every guard obligation inside natural-number arithmetic and makes the
; bound on the result immediate; no logical-operation library participates.

(defun fn-bpp-xor (a b k)
  (declare (xargs :guard (and (natp a) (natp b) (natp k))
                  :measure (nfix k)
                  :verify-guards nil))
  (mbe :logic (if (zp k)
                  0
                (+ (if (equal (mod a 2) (mod b 2)) 0 1)
                   (* 2 (fn-bpp-xor (floor a 2) (floor b 2) (- k 1)))))
       :exec (logand (logxor a b) (+ -1 (expt 2 k)))))

; The executed body is the machine exclusive-or masked to k bits; the logical
; body above is the definition every theorem in this book and its includers
; reasons about.  The keystone equating them, which the guard proof below
; uses (PRF-190).  The lemmas are local: the arithmetic of `logxor' and
; `logand' never reaches an includer.
(encapsulate
  ()
  (local (include-book "ihs/quotient-remainder-lemmas" :dir :system))
  (local (encapsulate
           ()
           (local (include-book "arithmetic-5/top" :dir :system))
           (defthm fn-bpp-logxor-mod-2
             (implies (and (natp a) (natp b))
                      (equal (mod (logxor a b) 2)
                             (if (equal (mod a 2) (mod b 2)) 0 1))))
           (defthm fn-bpp-logxor-floor-2
             (implies (and (natp a) (natp b))
                      (equal (floor (logxor a b) 2)
                             (logxor (floor a 2) (floor b 2)))))
           (defthm fn-bpp-logand-mod-2
             (implies (and (integerp x) (natp y))
                      (equal (mod (logand x y) 2)
                             (if (and (equal (mod x 2) 1) (equal (mod y 2) 1))
                                 1
                               0))))
           (defthm fn-bpp-logand-floor-2
             (implies (and (integerp x) (natp y))
                      (equal (floor (logand x y) 2)
                             (logand (floor x 2) (floor y 2)))))
           (defthm fn-bpp-expt-2-negative
             (implies (and (integerp k) (< k 0))
                      (and (< 0 (expt 2 k)) (< (expt 2 k) 1)))
             :rule-classes :linear)))
  (local (defthm fn-bpp-mod-expt-2-step
           (implies (and (integerp x) (not (zp k)))
                    (equal (mod x (expt 2 k))
                           (+ (mod x 2) (* 2 (mod (floor x 2) (expt 2 (- k 1)))))))))
  (local (defthm fn-bpp-integer-halves
           (implies (integerp x)
                    (equal (+ (mod x 2) (* 2 (floor x 2))) x))
           :rule-classes nil))
  (local (defun fn-bpp-halving-induction (x k)
           (declare (xargs :measure (nfix k)))
           (if (zp k)
               x
             (fn-bpp-halving-induction (floor x 2) (- k 1)))))
  (local (defthm fn-bpp-bit-plus-twice
           (implies (and (natp r) (or (equal bit 0) (equal bit 1)))
                    (and (equal (mod (+ bit (* 2 r)) 2) bit)
                         (equal (floor (+ bit (* 2 r)) 2) r)))))
  (local (defthm fn-bpp-mask-floor-2
           (implies (not (zp k))
                    (and (equal (floor (+ -1 (expt 2 k)) 2) (+ -1 (expt 2 (- k 1))))
                         (equal (mod (+ -1 (expt 2 k)) 2) 1)))
           :hints (("Goal" :use ((:instance fn-bpp-bit-plus-twice
                                            (bit 1) (r (+ -1 (expt 2 (- k 1))))))
                           :expand ((expt 2 k))
                           :in-theory (disable fn-bpp-bit-plus-twice)))))
  (local (defthm fn-bpp-logand-mask-is-mod
           (implies (and (integerp x) (natp k))
                    (equal (logand x (+ -1 (expt 2 k))) (mod x (expt 2 k))))
           :hints (("Goal" :induct (fn-bpp-halving-induction x k))
                   ("Subgoal *1/2" :use ((:instance fn-bpp-integer-halves
                                                    (x (logand x (+ -1 (expt 2 k))))))))))
  (local (defthm fn-bpp-xor-is-mod-logxor
           (implies (and (natp a) (natp b) (natp k))
                    (equal (fn-bpp-xor a b k) (mod (logxor a b) (expt 2 k))))
           :hints (("Goal" :induct (fn-bpp-xor a b k)
                           :in-theory (disable floor mod binary-logxor))
                   ("Subgoal *1/2" :use ((:instance fn-bpp-mod-expt-2-step
                                                    (x (logxor a b))))))))
  (local (defthm fn-bpp-xor-is-masked-logxor-at-a-width
           (implies (and (natp a) (natp b) (natp k))
                    (equal (fn-bpp-xor a b k)
                           (logand (logxor a b) (+ -1 (expt 2 k)))))))
  ;; A width that is not a natural is no width: both sides are 0 (a negative
  ;; width's mask is a fraction, a non-integer one's is 0), so the keystone
  ;; carries no hypothesis on k.
  (local (defthm fn-bpp-mask-of-negative-width
           (implies (and (integerp k) (< k 0))
                    (equal (logand x (+ -1 (expt 2 k))) 0))
           :hints (("Goal" :expand ((binary-logand x (+ -1 (expt 2 k))))))))
  (local (defthm fn-bpp-xor-is-masked-logxor-at-no-width
           (implies (and (natp a) (natp b) (not (natp k)))
                    (equal (fn-bpp-xor a b k)
                           (logand (logxor a b) (+ -1 (expt 2 k)))))
           :hints (("Goal" :cases ((integerp k))
                           :in-theory (disable binary-logxor)))))
  (defthmd fn-bpp-xor-is-masked-logxor
    (implies (and (natp a) (natp b))
             (equal (fn-bpp-xor a b k)
                    (logand (logxor a b) (+ -1 (expt 2 k)))))
    :hints (("Goal" :use (fn-bpp-xor-is-masked-logxor-at-a-width
                          fn-bpp-xor-is-masked-logxor-at-no-width)
                    :in-theory (disable binary-logxor fn-bpp-xor
                                        fn-bpp-xor-is-masked-logxor-at-a-width
                                        fn-bpp-xor-is-masked-logxor-at-no-width))))

  (verify-guards fn-bpp-xor
    :hints (("Goal" :use (fn-bpp-xor-is-masked-logxor (:definition fn-bpp-xor))
                    :in-theory (disable fn-bpp-xor floor mod binary-logxor
                                        binary-logand)))))

(defthm fn-bpp-xor-is-natural
  (natp (fn-bpp-xor a b k))
  :rule-classes (:rewrite :type-prescription))

(defthm fn-bpp-xor-is-bounded
  (implies (natp k)
           (< (fn-bpp-xor a b k) (expt 2 k)))
  :rule-classes :linear
  :hints (("Goal" :induct (fn-bpp-xor a b k))))

; -----------------------------------------------------------------------------
; CRC type (section 4.2.1) and CRC (section 4.2.2)
;
;   0  no CRC
;   1  standard X-25 CRC-16   (CRC-16/IBM-SDLC: reflected 0x8408, init 0xFFFF,
;                              final xor 0xFFFF)
;   2  standard CRC32C        (CRC-32/ISCSI: reflected 0x82F63B78,
;                              init 0xFFFFFFFF, final xor 0xFFFFFFFF)
;
; Both are transmitted as a CBOR byte string holding the unsigned value in
; network byte order (section 4.2.2), two octets for type 1 and four for
; type 2.

(defconst *fn-bpp-crc16-poly* 33800)
(defconst *fn-bpp-crc32c-poly* 2197175160)

(defun fn-bpp-crc16-bit (crc)
  (declare (xargs :guard (natp crc)))
  (if (equal (mod crc 2) 1)
      (fn-bpp-xor (floor crc 2) *fn-bpp-crc16-poly* 16)
    (floor crc 2)))

(defun fn-bpp-crc16-octet (crc k)
  (declare (xargs :guard (and (natp crc) (natp k)) :measure (nfix k)))
  (if (zp k)
      (nfix crc)
    (fn-bpp-crc16-octet (fn-bpp-crc16-bit crc) (- k 1))))

(defun fn-bpp-crc16-scan (crc xs)
  (declare (xargs :guard (and (natp crc) (fn-cbor-octet-listp xs))))
  (if (consp xs)
      (fn-bpp-crc16-scan
       (fn-bpp-crc16-octet (fn-bpp-xor crc (car xs) 16) 8)
       (cdr xs))
    (nfix crc)))

(defun fn-bpp-crc16 (xs)
  (declare (xargs :guard (fn-cbor-octet-listp xs)))
  (fn-bpp-xor (fn-bpp-crc16-scan 65535 xs) 65535 16))

(defun fn-bpp-crc32c-bit (crc)
  (declare (xargs :guard (natp crc)))
  (if (equal (mod crc 2) 1)
      (fn-bpp-xor (floor crc 2) *fn-bpp-crc32c-poly* 32)
    (floor crc 2)))

(defun fn-bpp-crc32c-octet (crc k)
  (declare (xargs :guard (and (natp crc) (natp k)) :measure (nfix k)))
  (if (zp k)
      (nfix crc)
    (fn-bpp-crc32c-octet (fn-bpp-crc32c-bit crc) (- k 1))))

; The executed CRC-32C (PRF-190).  One octet of the bitwise register above is
; eight steps of `fn-bpp-crc32c-bit'; the executed scan does those eight steps
; as one lookup in a 256-entry table, the classic table-driven CRC.  The table
; is not written out: the defconst below evaluates `fn-bpp-crc32c-octet' at
; every octet value, so it cannot drift from the bitwise definition, and
; `fn-bpp-crc32c-table-agrees' checks every one of the 256 entries by
; evaluation inside the proof.  It is kept as 16 rows of 16 so a lookup walks
; at most 30 conses.

(defun fn-bpp-crc32c-table-row (r j)
  (declare (xargs :guard (and (natp r) (natp j))
                  :measure (nfix (- 16 (nfix j)))))
  (if (and (natp j) (< j 16))
      (cons (fn-bpp-crc32c-octet (+ (* 16 (nfix r)) j) 8)
            (fn-bpp-crc32c-table-row r (+ 1 j)))
    nil))

(defun fn-bpp-crc32c-table-rows (r)
  (declare (xargs :guard (natp r)
                  :measure (nfix (- 16 (nfix r)))))
  (if (and (natp r) (< r 16))
      (cons (fn-bpp-crc32c-table-row r 0)
            (fn-bpp-crc32c-table-rows (+ 1 r)))
    nil))

(defconst *fn-bpp-crc32c-table* (fn-bpp-crc32c-table-rows 0))

(defun fn-bpp-crc32c-table-ref (i)
  (declare (xargs :guard (and (natp i) (< i 256))
                  :verify-guards nil))
  (nth (logand i 15) (nth (ash i -4) *fn-bpp-crc32c-table*)))

(defun fn-bpp-crc32c-scan-table (crc xs)
  (declare (xargs :guard (and (natp crc) (fn-cbor-octet-listp xs))
                  :verify-guards nil))
  (if (consp xs)
      (let ((c (logand (logxor crc (car xs)) 4294967295)))
        (fn-bpp-crc32c-scan-table
         (logand (logxor (ash c -8) (fn-bpp-crc32c-table-ref (logand c 255)))
                 4294967295)
         (cdr xs)))
    crc))

(defun fn-bpp-crc32c-scan (crc xs)
  (declare (xargs :guard (and (natp crc) (fn-cbor-octet-listp xs))
                  :verify-guards nil))
  (mbe :logic (if (consp xs)
                  (fn-bpp-crc32c-scan
                   (fn-bpp-crc32c-octet (fn-bpp-xor crc (car xs) 32) 8)
                   (cdr xs))
                (nfix crc))
       :exec (fn-bpp-crc32c-scan-table crc xs)))

(defun fn-bpp-crc32c (xs)
  (declare (xargs :guard (fn-cbor-octet-listp xs)
                  :verify-guards nil))
  (fn-bpp-xor (fn-bpp-crc32c-scan 4294967295 xs) 4294967295 32))

;; The table-driven scan equals the bitwise one (PRF-190).  The argument is the
;; textbook one, over the bitwise definitions: one register step is linear in
;; the register under exclusive-or, so eight steps of a register c are eight
;; steps of its low octet exclusive-or eight steps of its high part, and eight
;; steps of a register whose low octet is zero only shift it down by eight.
(encapsulate
  ()
  (local (include-book "ihs/quotient-remainder-lemmas" :dir :system))
  (local (encapsulate
           ()
           (local (include-book "arithmetic-5/top" :dir :system))
           (defthm fn-bpp-crc-shift-and-mask
             (implies (natp c)
                      (and (equal (ash c -8) (floor c 256))
                           (equal (ash c -4) (floor c 16))
                           (equal (logand c 255) (mod c 256))
                           (equal (logand c 15) (mod c 16)))))
           (defthm fn-bpp-crc-masked-bounds
             (implies (integerp x)
                      (and (natp (logand x 4294967295))
                           (natp (logand x 255))
                           (< (logand x 255) 256))))))
  (local (in-theory (disable fn-bpp-crc-masked-bounds)))
  (local (defthm fn-bpp-crc-bit-plus-twice
           (implies (and (natp r) (or (equal bit 0) (equal bit 1)))
                    (and (equal (mod (+ bit (* 2 r)) 2) bit)
                         (equal (floor (+ bit (* 2 r)) 2) r)))))
  (local (defthm fn-bpp-crc-mod-2-cases
           (implies (natp a) (or (equal (mod a 2) 0) (equal (mod a 2) 1)))
           :rule-classes nil))
  (local (defthm fn-bpp-crc-mod-expt-step
           (implies (and (integerp x) (not (zp k)))
                    (equal (mod x (expt 2 k))
                           (+ (mod x 2) (* 2 (mod (floor x 2) (expt 2 (- k 1)))))))))
  (local (defthm fn-bpp-crc-mod-mod-2
           (implies (and (natp c) (not (zp j)))
                    (equal (mod (mod c (expt 2 j)) 2) (mod c 2)))))
  (local (defthm fn-bpp-crc-floor-mod-2
           (implies (and (natp c) (not (zp j)))
                    (equal (floor (mod c (expt 2 j)) 2)
                           (mod (floor c 2) (expt 2 (- j 1)))))
           :hints (("Goal" :use ((:instance fn-bpp-crc-mod-expt-step (x c) (k j))
                                 (:instance fn-bpp-crc-mod-2-cases (a c)))
                           :in-theory (disable fn-bpp-crc-mod-expt-step
                                               fn-bpp-crc-mod-mod-2)))))
  (local (defthm fn-bpp-crc-floor-expt-step
           (implies (and (natp c) (not (zp j)))
                    (equal (floor c (expt 2 j))
                           (floor (floor c 2) (expt 2 (- j 1)))))
           :hints (("Goal" :use ((:instance floor-floor-integer
                                            (x c) (i 2) (j (expt 2 (- j 1)))))
                           :in-theory (disable floor-floor-integer)))))
  (local (defthm fn-bpp-crc-shifted-halves
           (implies (and (natp f) (not (zp j)))
                    (and (equal (mod (* (expt 2 j) f) 2) 0)
                         (equal (floor (* (expt 2 j) f) 2)
                                (* (expt 2 (- j 1)) f))))))
  (local (in-theory (disable floor mod)))

  ;; Exclusive-or over k bits: parity, halving, and the group laws.
  (local (defthm fn-bpp-xor-mod-2
           (implies (not (zp k))
                    (equal (mod (fn-bpp-xor a b k) 2)
                           (if (equal (mod a 2) (mod b 2)) 0 1)))
           :hints (("Goal" :expand ((fn-bpp-xor a b k))))))
  (local (defthm fn-bpp-xor-floor-2
           (implies (not (zp k))
                    (equal (floor (fn-bpp-xor a b k) 2)
                           (fn-bpp-xor (floor a 2) (floor b 2) (- k 1))))
           :hints (("Goal" :expand ((fn-bpp-xor a b k))))))
  (local (defthm fn-bpp-xor-commutes
           (equal (fn-bpp-xor b a k) (fn-bpp-xor a b k))
           :rule-classes ((:rewrite :loop-stopper ((a b))))))
  (local (defun fn-bpp-crc-induct-3 (a b c k)
           (declare (xargs :measure (nfix k)))
           (if (zp k)
               (list a b c)
             (fn-bpp-crc-induct-3 (floor a 2) (floor b 2) (floor c 2) (- k 1)))))
  (local (defthm fn-bpp-xor-associates
           (implies (and (natp a) (natp b) (natp c))
                    (equal (fn-bpp-xor (fn-bpp-xor a b k) c k)
                           (fn-bpp-xor a (fn-bpp-xor b c k) k)))
           :hints (("Goal" :induct (fn-bpp-crc-induct-3 a b c k)
                           :expand ((fn-bpp-xor (fn-bpp-xor a b k) c k)
                                    (fn-bpp-xor a (fn-bpp-xor b c k) k))))))
  (local (defthm fn-bpp-xor-commutes-2
           (implies (and (natp a) (natp b) (natp c))
                    (equal (fn-bpp-xor a (fn-bpp-xor b c k) k)
                           (fn-bpp-xor b (fn-bpp-xor a c k) k)))
           :rule-classes ((:rewrite :loop-stopper ((a b))))
           :hints (("Goal" :use ((:instance fn-bpp-xor-associates)
                                 (:instance fn-bpp-xor-associates (a b) (b a)))
                           :in-theory (disable fn-bpp-xor-associates)))))
  (local (defthm fn-bpp-xor-self
           (equal (fn-bpp-xor a a k) 0)))
  (local (defthm fn-bpp-xor-self-2
           (implies (and (natp a) (natp c) (natp k) (< c (expt 2 k)))
                    (equal (fn-bpp-xor a (fn-bpp-xor a c k) k) c))
           :hints (("Goal" :use ((:instance fn-bpp-xor-associates (b a)))
                           :in-theory (disable fn-bpp-xor-associates)))))
  (local (defthm fn-bpp-xor-zero
           (implies (and (natp b) (natp k) (< b (expt 2 k)))
                    (equal (fn-bpp-xor 0 b k) b))))
  (local (defthm fn-bpp-xor-widen
           (implies (and (natp a) (natp b) (natp k)
                         (< a (expt 2 k)) (< b (expt 2 k)))
                    (equal (fn-bpp-xor a b (+ 1 k)) (fn-bpp-xor a b k)))
           :hints (("Goal" :induct (fn-bpp-crc-induct-3 a b c k)))))
  (local (defthm fn-bpp-xor-32-floor-2
           (implies (and (natp x) (natp y) (< x 4294967296) (< y 4294967296))
                    (equal (floor (fn-bpp-xor x y 32) 2)
                           (fn-bpp-xor (floor x 2) (floor y 2) 32)))
           :hints (("Goal" :use ((:instance fn-bpp-xor-widen
                                            (a (floor x 2)) (b (floor y 2)) (k 31)))
                           :in-theory (disable fn-bpp-xor-widen)))))
  (local (in-theory (disable fn-bpp-xor-floor-2)))

  ;; A low part and a high part (S): c = (c mod 2^j) xor 2^j * floor(c / 2^j).
  (local (defun fn-bpp-crc-induct-split (c j k)
           (declare (xargs :measure (nfix j)))
           (if (or (zp j) (zp k))
               (list c k)
             (fn-bpp-crc-induct-split (floor c 2) (- j 1) (- k 1)))))
  (local (defthm fn-bpp-xor-splits
           (implies (and (natp c) (natp j) (natp k) (< c (expt 2 k)))
                    (equal (fn-bpp-xor (mod c (expt 2 j))
                                       (* (expt 2 j) (floor c (expt 2 j)))
                                       k)
                           c))
           :hints (("Goal" :induct (fn-bpp-crc-induct-split c j k))
                   ("Subgoal *1/2" :expand ((fn-bpp-xor (mod c (expt 2 j))
                                                        (* (expt 2 j) (floor c (expt 2 j)))
                                                        k))))))

  ;; The register step (C1, C2, C3, C4).
  (local (defthm fn-bpp-crc32c-bit-bounded
           (implies (and (natp c) (< c 4294967296))
                    (and (natp (fn-bpp-crc32c-bit c))
                         (< (fn-bpp-crc32c-bit c) 4294967296)))))
  (local (defthm fn-bpp-xor-pair-cancels
           (implies (and (natp a) (natp b) (natp p) (< b 4294967296))
                    (equal (fn-bpp-xor (fn-bpp-xor a p 32) (fn-bpp-xor b p 32) 32)
                           (fn-bpp-xor a b 32)))
           :hints (("Goal" :use ((:instance fn-bpp-xor-associates
                                            (b p) (c (fn-bpp-xor b p 32)) (k 32))
                                 (:instance fn-bpp-xor-commutes-2
                                            (a p) (c p) (k 32))
                                 (:instance fn-bpp-xor-self (a p) (k 32))
                                 (:instance fn-bpp-xor-commutes (a 0) (k 32))
                                 (:instance fn-bpp-xor-zero (k 32)))
                           :in-theory (disable fn-bpp-xor fn-bpp-xor-associates
                                               fn-bpp-xor-commutes-2 fn-bpp-xor-self
                                               fn-bpp-xor-self-2 fn-bpp-xor-commutes
                                               fn-bpp-xor-zero)))))
  (local (defthm fn-bpp-xor-rotates
           (implies (and (natp a) (natp b) (natp p))
                    (equal (fn-bpp-xor (fn-bpp-xor a b 32) p 32)
                           (fn-bpp-xor (fn-bpp-xor a p 32) b 32)))
           :rule-classes nil
           :hints (("Goal" :use ((:instance fn-bpp-xor-associates (c p) (k 32))
                                 (:instance fn-bpp-xor-associates (b p) (c b) (k 32))
                                 (:instance fn-bpp-xor-commutes (a b) (b p) (k 32)))
                           :in-theory (disable fn-bpp-xor fn-bpp-xor-associates
                                               fn-bpp-xor-commutes-2 fn-bpp-xor-self
                                               fn-bpp-xor-self-2 fn-bpp-xor-commutes
                                               fn-bpp-xor-zero)))))
  (local (defthm fn-bpp-crc32c-bit-linear
           (implies (and (natp x) (natp y) (< x 4294967296) (< y 4294967296))
                    (equal (fn-bpp-crc32c-bit (fn-bpp-xor x y 32))
                           (fn-bpp-xor (fn-bpp-crc32c-bit x) (fn-bpp-crc32c-bit y) 32)))
           :hints (("Goal" :use ((:instance fn-bpp-crc-mod-2-cases (a x))
                                 (:instance fn-bpp-crc-mod-2-cases (a y))
                                 (:instance fn-bpp-xor-rotates
                                            (a (floor x 2)) (b (floor y 2))
                                            (p *fn-bpp-crc32c-poly*))
                                 (:instance fn-bpp-xor-rotates
                                            (a (floor y 2)) (b (floor x 2))
                                            (p *fn-bpp-crc32c-poly*)))
                           :in-theory (disable fn-bpp-xor-associates
                                               fn-bpp-xor-commutes-2
                                               fn-bpp-xor-self-2)))))
  (local (in-theory (disable fn-bpp-crc32c-bit)))
  (local (defun fn-bpp-crc-induct-2 (x y k)
           (declare (xargs :measure (nfix k)))
           (if (zp k)
               (list x y)
             (fn-bpp-crc-induct-2 (fn-bpp-crc32c-bit x) (fn-bpp-crc32c-bit y) (- k 1)))))
  (local (defthm fn-bpp-crc32c-octet-linear
           (implies (and (natp x) (natp y) (< x 4294967296) (< y 4294967296))
                    (equal (fn-bpp-crc32c-octet (fn-bpp-xor x y 32) k)
                           (fn-bpp-xor (fn-bpp-crc32c-octet x k)
                                       (fn-bpp-crc32c-octet y k)
                                       32)))
           :hints (("Goal" :induct (fn-bpp-crc-induct-2 x y k)))))
  (local (defthm fn-bpp-crc32c-octet-shifts
           (implies (and (natp h) (natp k))
                    (equal (fn-bpp-crc32c-octet (* (expt 2 k) h) k) h))
           :hints (("Goal" :in-theory (enable fn-bpp-crc32c-bit)))))

  ;; K: eight register steps are one table entry and a shift.
  (local (defthmd fn-bpp-crc32c-octet-is-table-step
    (implies (and (natp c) (< c 4294967296))
             (equal (fn-bpp-crc32c-octet c 8)
                    (fn-bpp-xor (fn-bpp-crc32c-octet (mod c 256) 8)
                                (floor c 256)
                                32)))
    :hints (("Goal" :use ((:instance fn-bpp-xor-splits (j 8) (k 32))
                          (:instance fn-bpp-crc32c-octet-linear
                                     (x (mod c 256)) (y (* 256 (floor c 256))) (k 8))
                          (:instance fn-bpp-crc32c-octet-shifts (h (floor c 256)) (k 8)))
                    :in-theory (disable fn-bpp-xor-splits fn-bpp-crc32c-octet-linear
                                        fn-bpp-crc32c-octet-shifts)))))

  ;; The table: every entry checked by evaluation.
  (local (defthm fn-bpp-crc-nth-of-true-list-list
           (implies (true-list-listp l)
                    (true-listp (nth r l)))))
  (local (defthm fn-bpp-crc32c-table-rows-are-true-lists
           (true-listp (nth r *fn-bpp-crc32c-table*))
           :hints (("Goal" :use ((:instance fn-bpp-crc-nth-of-true-list-list
                                            (l *fn-bpp-crc32c-table*)))
                           :in-theory (disable fn-bpp-crc-nth-of-true-list-list nth)))))
  (verify-guards fn-bpp-crc32c-table-ref)
  (defun fn-bpp-crc32c-table-agrees (n)
    (declare (xargs :guard (and (natp n) (<= n 256))))
    (if (zp n)
        t
      (and (equal (fn-bpp-crc32c-table-ref (- n 1))
                  (fn-bpp-crc32c-octet (- n 1) 8))
           (fn-bpp-crc32c-table-agrees (- n 1)))))
  (local (defthm fn-bpp-crc32c-table-agrees-means
           (implies (and (fn-bpp-crc32c-table-agrees n) (natp n) (natp i) (< i n))
                    (equal (fn-bpp-crc32c-table-ref i)
                           (fn-bpp-crc32c-octet i 8)))
           :hints (("Goal" :in-theory (disable fn-bpp-crc32c-table-ref
                                               fn-bpp-crc32c-octet)))))
  (local (defthmd fn-bpp-crc32c-table-ref-is-octet
    (implies (and (natp i) (< i 256))
             (equal (fn-bpp-crc32c-table-ref i) (fn-bpp-crc32c-octet i 8)))
    :hints (("Goal" :use ((:instance fn-bpp-crc32c-table-agrees-means (n 256)))
                    :in-theory (disable fn-bpp-crc32c-table-agrees-means
                                        fn-bpp-crc32c-table-ref
                                        fn-bpp-crc32c-octet)))))

  ;; The keystone: the executed scan is the bitwise scan.
  (local (defthm fn-bpp-crc32c-scan-table-step
           (implies (and (natp crc) (natp x))
                    (equal (logand (logxor (ash (logand (logxor crc x) 4294967295) -8)
                                           (fn-bpp-crc32c-table-ref
                                            (logand (logand (logxor crc x) 4294967295) 255)))
                                   4294967295)
                           (fn-bpp-crc32c-octet (fn-bpp-xor crc x 32) 8)))
           :hints (("Goal" :use ((:instance fn-bpp-xor-is-masked-logxor
                                            (a crc) (b x) (k 32))
                                 (:instance fn-bpp-xor-is-masked-logxor
                                            (a (floor (fn-bpp-xor crc x 32) 256))
                                            (b (fn-bpp-crc32c-octet
                                                (mod (fn-bpp-xor crc x 32) 256) 8))
                                            (k 32))
                                 (:instance fn-bpp-crc32c-octet-is-table-step
                                            (c (fn-bpp-xor crc x 32)))
                                 (:instance fn-bpp-crc32c-table-ref-is-octet
                                            (i (mod (fn-bpp-xor crc x 32) 256))))
                           :in-theory (disable fn-bpp-crc32c-table-ref
                                               fn-bpp-crc32c-octet binary-logxor
                                               binary-logand ash)))))
  (defthmd fn-bpp-crc32c-scan-table-is-scan
    (implies (and (natp crc) (fn-cbor-octet-listp xs))
             (equal (fn-bpp-crc32c-scan-table crc xs)
                    (fn-bpp-crc32c-scan crc xs)))
    :hints (("Goal" :induct (fn-bpp-crc32c-scan-table crc xs)
                    :in-theory (disable fn-bpp-crc32c-table-ref
                                        fn-bpp-crc32c-octet binary-logxor
                                        binary-logand ash))))
  (local (defthm fn-bpp-crc32c-table-ref-is-natural
           (implies (and (natp i) (< i 256))
                    (natp (fn-bpp-crc32c-table-ref i)))
           :hints (("Goal" :use ((:instance fn-bpp-crc32c-table-ref-is-octet))
                           :in-theory (disable fn-bpp-crc32c-table-ref)))))
  (verify-guards fn-bpp-crc32c-scan-table
    :hints (("Goal" :use ((:instance fn-bpp-crc32c-table-ref-is-natural
                                     (i (logand (logand (logxor crc (car xs)) 4294967295)
                                                255)))
                          (:instance fn-bpp-crc-masked-bounds
                                     (x (logand (logxor crc (car xs)) 4294967295)))
                          (:instance fn-bpp-crc-masked-bounds
                                     (x (logxor crc (car xs)))))
                    :in-theory (disable fn-bpp-crc32c-table-ref binary-logxor
                                        binary-logand ash fn-bpp-crc-shift-and-mask
                                        fn-bpp-crc32c-table-ref-is-natural)))))

(verify-guards fn-bpp-crc16-bit)
(verify-guards fn-bpp-crc16-octet)
(verify-guards fn-bpp-crc16-scan)
(verify-guards fn-bpp-crc16)
(verify-guards fn-bpp-crc32c-bit)
(verify-guards fn-bpp-crc32c-octet)
(verify-guards fn-bpp-crc32c-scan
  :hints (("Goal" :use ((:instance fn-bpp-crc32c-scan-table-is-scan)))))
(verify-guards fn-bpp-crc32c)

(defthm fn-bpp-crc16-is-natural
  (natp (fn-bpp-crc16 xs))
  :rule-classes (:rewrite :type-prescription))

(defthm fn-bpp-crc16-is-bounded
  (< (fn-bpp-crc16 xs) 65536)
  :rule-classes :linear
  :hints (("Goal" :use ((:instance fn-bpp-xor-is-bounded
                                   (a (fn-bpp-crc16-scan 65535 xs))
                                   (b 65535) (k 16)))
           :in-theory (disable fn-bpp-xor-is-bounded))))

(defthm fn-bpp-crc32c-is-natural
  (natp (fn-bpp-crc32c xs))
  :rule-classes (:rewrite :type-prescription))

(defthm fn-bpp-crc32c-is-bounded
  (< (fn-bpp-crc32c xs) 4294967296)
  :rule-classes :linear
  :hints (("Goal" :use ((:instance fn-bpp-xor-is-bounded
                                   (a (fn-bpp-crc32c-scan 4294967295 xs))
                                   (b 4294967295) (k 32)))
           :in-theory (disable fn-bpp-xor-is-bounded))))

(defun fn-bpp-crc-typep (x)
  (declare (xargs :guard t))
  (or (equal x 0) (equal x 1) (equal x 2)))

(defun fn-bpp-crc-width (type)
  (declare (xargs :guard (fn-bpp-crc-typep type)))
  (cond ((equal type 1) 2)
        ((equal type 2) 4)
        (t 0)))

(defun fn-bpp-zero-crc (type)
  (declare (xargs :guard (fn-bpp-crc-typep type)))
  (cond ((equal type 1) (list 0 0))
        ((equal type 2) (list 0 0 0 0))
        (t nil)))

(defun fn-bpp-crc-octets (type octets)
  (declare (xargs :guard (and (fn-bpp-crc-typep type)
                              (fn-cbor-octet-listp octets))))
  (cond ((equal type 1) (fn-cbor-u16-bytes (fn-bpp-crc16 octets)))
        ((equal type 2) (fn-cbor-u32-bytes (fn-bpp-crc32c octets)))
        (t nil)))

(verify-guards fn-bpp-crc-typep)
(verify-guards fn-bpp-crc-width)
(verify-guards fn-bpp-zero-crc)
(verify-guards fn-bpp-crc-octets)

; -----------------------------------------------------------------------------
; Bundle processing control flags (section 4.2.3)
;
; A CBOR unsigned integer processed as a bit field, numbered from the low-order
; bit.  Bits 3, 4, 7 to 13, 15, 19 and 20 are reserved and bits 21 to 63 are
; unassigned; RFC 9171 requires unrecognized flags to be IGNORED, so this model
; keeps the whole 64-bit value rather than rejecting unknown bits.

(defconst *fn-bpp-flag-fragment* 1)
(defconst *fn-bpp-flag-administrative* 2)
(defconst *fn-bpp-flag-no-fragment* 4)
(defconst *fn-bpp-flag-app-ack* 32)
(defconst *fn-bpp-flag-status-time* 64)
(defconst *fn-bpp-flag-report-reception* 16384)
(defconst *fn-bpp-flag-report-forwarding* 65536)
(defconst *fn-bpp-flag-report-delivery* 131072)
(defconst *fn-bpp-flag-report-deletion* 262144)

(defun fn-bpp-flag-setp (x)
  (declare (xargs :guard t))
  (and (natp x) (<= x *fn-bpc-max-uint*)))

(defun fn-bpp-flag-onp (flags mask)
  (declare (xargs :guard (and (natp flags) (posp mask))))
  (equal (mod (floor flags mask) 2) 1))

(defun fn-bpp-fragmentp (flags)
  (declare (xargs :guard (natp flags)))
  (fn-bpp-flag-onp flags *fn-bpp-flag-fragment*))

(defun fn-bpp-administrativep (flags)
  (declare (xargs :guard (natp flags)))
  (fn-bpp-flag-onp flags *fn-bpp-flag-administrative*))

(defun fn-bpp-no-fragmentp (flags)
  (declare (xargs :guard (natp flags)))
  (fn-bpp-flag-onp flags *fn-bpp-flag-no-fragment*))

(defun fn-bpp-any-status-requestp (flags)
  (declare (xargs :guard (natp flags)))
  (or (fn-bpp-flag-onp flags *fn-bpp-flag-report-reception*)
      (fn-bpp-flag-onp flags *fn-bpp-flag-report-forwarding*)
      (fn-bpp-flag-onp flags *fn-bpp-flag-report-delivery*)
      (fn-bpp-flag-onp flags *fn-bpp-flag-report-deletion*)))

(verify-guards fn-bpp-flag-setp)
(verify-guards fn-bpp-flag-onp)
(verify-guards fn-bpp-fragmentp)
(verify-guards fn-bpp-administrativep)
(verify-guards fn-bpp-no-fragmentp)
(verify-guards fn-bpp-any-status-requestp)

; -----------------------------------------------------------------------------
; Endpoint IDs (section 4.2.5.1)
;
;   (:dtn-none)        the null endpoint "dtn:none", CBOR [1, 0]
;   (:dtn . ssp)       CBOR [1, "<ssp>"] where ssp is the complete
;                      scheme-specific part including its leading "//"
;   (:ipn node svc)    CBOR [2, [node, svc]]
;
; The dtn SSP carried on the wire is the whole SSP.  RFC 9171 section 4.2.5.1.1
; gives dtn-hier-part = "//" node-name "/" demux, so a conforming text SSP
; begins "//", has a non-empty node-name, and has the name delimiter present
; even when the demux is empty.

(defun fn-bpp-vcharp (x)
  (declare (xargs :guard t))
  (and (natp x) (<= 33 x) (<= x 126)))

(defun fn-bpp-vchar-listp (xs)
  (declare (xargs :guard t))
  (if (consp xs)
      (and (fn-bpp-vcharp (car xs)) (fn-bpp-vchar-listp (cdr xs)))
    (null xs)))

(defthm fn-bpp-vchar-listp-implies-true-listp
  (implies (fn-bpp-vchar-listp xs) (true-listp xs))
  :rule-classes (:rewrite :forward-chaining))

(defun fn-bpp-name-delim-at (xs)
  (declare (xargs :guard t))
  (cond ((not (consp xs)) nil)
        ((equal (car xs) 47) 0)
        (t (let ((k (fn-bpp-name-delim-at (cdr xs))))
             (if k (+ 1 k) nil)))))

; The SSP is "//" then a non-empty node-name then "/" then the demux.
(defun fn-bpp-dtn-sspp (xs)
  (declare (xargs :guard t))
  (and (fn-bpp-vchar-listp xs)
       (<= (len xs) *fn-bpc-max-text*)
       (consp xs) (equal (car xs) 47)
       (consp (cdr xs)) (equal (cadr xs) 47)
       (let ((k (fn-bpp-name-delim-at (cddr xs))))
         (and (natp k) (< 0 k)))))

(defun fn-bpp-eidp (x)
  (declare (xargs :guard t))
  (or (equal x (list :dtn-none))
      (and (consp x) (eq (car x) :dtn) (fn-bpp-dtn-sspp (cdr x)))
      (and (true-listp x) (equal (len x) 3) (eq (car x) :ipn)
           (natp (nth 1 x)) (<= (nth 1 x) *fn-bpc-max-uint*)
           (natp (nth 2 x)) (<= (nth 2 x) *fn-bpc-max-uint*))))

(verify-guards fn-bpp-vcharp)
(verify-guards fn-bpp-vchar-listp)
(verify-guards fn-bpp-name-delim-at)
(verify-guards fn-bpp-dtn-sspp)
(verify-guards fn-bpp-eidp)

(defthm fn-bpp-dtn-sspp-has-a-name-delimiter
  (implies (fn-bpp-dtn-sspp ssp)
           (and (true-listp ssp)
                (natp (fn-bpp-name-delim-at (cddr ssp)))
                (< 0 (fn-bpp-name-delim-at (cddr ssp))))))

; Singleton-ness (section 4.2.5.1.1 and 4.2.5.1.2): every ipn endpoint is a
; singleton; a dtn endpoint is a singleton unless its demux begins with '~'.
(defun fn-bpp-dtn-demux-first (ssp)
  (declare (xargs :guard (fn-bpp-dtn-sspp ssp)))
  (nth (+ 3 (fn-bpp-name-delim-at (cddr ssp))) ssp))

(defun fn-bpp-dtn-demux-emptyp (ssp)
  (declare (xargs :guard (fn-bpp-dtn-sspp ssp)))
  (equal (len ssp) (+ 3 (fn-bpp-name-delim-at (cddr ssp)))))

(verify-guards fn-bpp-dtn-demux-first)
(verify-guards fn-bpp-dtn-demux-emptyp)

(defun fn-bpp-eid-singletonp (x)
  (declare (xargs :guard (fn-bpp-eidp x)))
  (cond ((eq (car x) :ipn) t)
        ((and (consp x) (eq (car x) :dtn) (fn-bpp-dtn-sspp (cdr x)))
         (not (equal (fn-bpp-dtn-demux-first (cdr x)) 126)))
        (t nil)))

; Node IDs (section 4.2.5.2): a dtn EID whose demux is empty, or an ipn EID
; whose service number is zero, may serve as a node ID.
(defun fn-bpp-eid-node-idp (x)
  (declare (xargs :guard (fn-bpp-eidp x)))
  (cond ((and (true-listp x) (equal (len x) 3) (eq (car x) :ipn))
         (equal (nth 2 x) 0))
        ((and (consp x) (eq (car x) :dtn) (fn-bpp-dtn-sspp (cdr x)))
         (fn-bpp-dtn-demux-emptyp (cdr x)))
        (t nil)))

(verify-guards fn-bpp-eid-singletonp)
(verify-guards fn-bpp-eid-node-idp)

(defun fn-bpp-eid-value (e)
  (declare (xargs :guard (fn-bpp-eidp e)))
  (cond ((equal e (list :dtn-none))
         (cons :array (list (cons :uint 1) (cons :uint 0))))
        ((eq (car e) :ipn)
         (cons :array (list (cons :uint 2)
                            (cons :array (list (cons :uint (nth 1 e))
                                               (cons :uint (nth 2 e)))))))
        (t (cons :array (list (cons :uint 1) (cons :text (cdr e)))))))

(verify-guards fn-bpp-eid-value)

(defun fn-bpp-value-eid (v)
  (declare (xargs :guard t))
  (if (not (and (consp v) (eq (car v) :array)
                (true-listp (cdr v)) (equal (len (cdr v)) 2)))
      nil
    (let ((scheme (nth 0 (cdr v)))
          (ssp (nth 1 (cdr v))))
      (cond ((equal scheme (cons :uint 1))
             (cond ((equal ssp (cons :uint 0)) (list :dtn-none))
                   ((and (consp ssp) (eq (car ssp) :text)
                         (fn-bpp-dtn-sspp (cdr ssp)))
                    (cons :dtn (cdr ssp)))
                   (t nil)))
            ((equal scheme (cons :uint 2))
             (if (and (consp ssp) (eq (car ssp) :array)
                      (true-listp (cdr ssp)) (equal (len (cdr ssp)) 2)
                      (consp (nth 0 (cdr ssp)))
                      (eq (car (nth 0 (cdr ssp))) :uint)
                      (natp (cdr (nth 0 (cdr ssp))))
                      (<= (cdr (nth 0 (cdr ssp))) *fn-bpc-max-uint*)
                      (consp (nth 1 (cdr ssp)))
                      (eq (car (nth 1 (cdr ssp))) :uint)
                      (natp (cdr (nth 1 (cdr ssp))))
                      (<= (cdr (nth 1 (cdr ssp))) *fn-bpc-max-uint*))
                 (list :ipn (cdr (nth 0 (cdr ssp))) (cdr (nth 1 (cdr ssp))))
               nil))
            (t nil)))))

(verify-guards fn-bpp-value-eid)

; -----------------------------------------------------------------------------
; The primary block record
;
; Version is not a field of the record: RFC 9171 defines version 7 and this
; model constructs and accepts nothing else, so a stored version field could
; only ever disagree with the codec.

(defconst *fn-bpp-version* 7)

(defun fn-bpp-make-block (flags crc-type destination source report-to
                          creation-time sequence lifetime
                          fragment-offset total-adu-length)
  (declare (xargs :guard t))
  (list :fn-bp-primary flags crc-type destination source report-to
        creation-time sequence lifetime fragment-offset total-adu-length))

(defun fn-bpp-flags (b) (declare (xargs :guard (true-listp b))) (nth 1 b))
(defun fn-bpp-crc-type (b) (declare (xargs :guard (true-listp b))) (nth 2 b))
(defun fn-bpp-destination (b) (declare (xargs :guard (true-listp b))) (nth 3 b))
(defun fn-bpp-source (b) (declare (xargs :guard (true-listp b))) (nth 4 b))
(defun fn-bpp-report-to (b) (declare (xargs :guard (true-listp b))) (nth 5 b))
(defun fn-bpp-creation-time (b) (declare (xargs :guard (true-listp b))) (nth 6 b))
(defun fn-bpp-sequence (b) (declare (xargs :guard (true-listp b))) (nth 7 b))
(defun fn-bpp-lifetime (b) (declare (xargs :guard (true-listp b))) (nth 8 b))
(defun fn-bpp-fragment-offset (b) (declare (xargs :guard (true-listp b))) (nth 9 b))
(defun fn-bpp-total-adu-length (b) (declare (xargs :guard (true-listp b))) (nth 10 b))

(verify-guards fn-bpp-make-block)
(verify-guards fn-bpp-flags)
(verify-guards fn-bpp-crc-type)
(verify-guards fn-bpp-destination)
(verify-guards fn-bpp-source)
(verify-guards fn-bpp-report-to)
(verify-guards fn-bpp-creation-time)
(verify-guards fn-bpp-sequence)
(verify-guards fn-bpp-lifetime)
(verify-guards fn-bpp-fragment-offset)
(verify-guards fn-bpp-total-adu-length)

; Accessor-of-constructor, for the five block projections this book withdraws
; at its end (`fn-bpp-projection-vocabulary`).
;
; Why the law is stated over a cons nest and not over `fn-bpp-make-block`.
; The constructor stays ENABLED: withdrawing it as well would oblige this
; book to export the tag, the length, the `true-listp` and the five
; projections it still leaves enabled as five more rules apiece, which is the
; opaque-record refactor (item 4 of `planning/deputies/bp.md`) and not this
; lane's.  With the constructor enabled, ACL2 rewrites inside out and a
; caller's goal never contains `(fn-bpp-flags (fn-bpp-make-block ...))`: by
; the time the accessor is reached its argument is already the cons nest.
; Measured 2026-09-21 on `fn-bpn-send-bundle-is-a-bundle`, whose checkpoint
; is `(INTEGERP (FN-BPP-FLAGS (LIST* :FN-BP-PRIMARY 0 0 PEER ...)))`.
;
; Each rule needs an EXPLICIT cons, so none of them can fire on an opaque
; block -- which is exactly what withdrawing the definition is for.
(defthm fn-bpp-flags-of-a-built-block
  (equal (fn-bpp-flags (cons tag (cons flags rest))) flags))

(defthm fn-bpp-crc-type-of-a-built-block
  (equal (fn-bpp-crc-type (cons tag (cons flags (cons crc-type rest))))
         crc-type))

(defthm fn-bpp-source-of-a-built-block
  (equal (fn-bpp-source
          (cons tag (cons flags (cons crc-type (cons destination
                                                     (cons source rest))))))
         source))

(defthm fn-bpp-creation-time-of-a-built-block
  (equal (fn-bpp-creation-time
          (cons tag
                (cons flags
                      (cons crc-type
                            (cons destination
                                  (cons source
                                        (cons report-to
                                              (cons creation-time rest))))))))
         creation-time))

(defthm fn-bpp-sequence-of-a-built-block
  (equal (fn-bpp-sequence
          (cons tag
                (cons flags
                      (cons crc-type
                            (cons destination
                                  (cons source
                                        (cons report-to
                                              (cons creation-time
                                                    (cons sequence rest)))))))))
         sequence))

(defun fn-bpp-timep (x)
  (declare (xargs :guard t))
  (and (natp x) (<= x *fn-bpc-max-uint*)))

(defun fn-bpp-blockp (b)
  (declare (xargs :guard t))
  (and (true-listp b)
       (equal (len b) 11)
       (eq (nth 0 b) :fn-bp-primary)
       (fn-bpp-flag-setp (fn-bpp-flags b))
       (fn-bpp-crc-typep (fn-bpp-crc-type b))
       (fn-bpp-eidp (fn-bpp-destination b))
       (fn-bpp-eidp (fn-bpp-source b))
       (fn-bpp-eidp (fn-bpp-report-to b))
       (fn-bpp-timep (fn-bpp-creation-time b))
       (fn-bpp-timep (fn-bpp-sequence b))
       (fn-bpp-timep (fn-bpp-lifetime b))
       (if (fn-bpp-fragmentp (fn-bpp-flags b))
           (and (fn-bpp-timep (fn-bpp-fragment-offset b))
                (fn-bpp-timep (fn-bpp-total-adu-length b)))
         (and (null (fn-bpp-fragment-offset b))
              (null (fn-bpp-total-adu-length b))))))

(verify-guards fn-bpp-timep)
(verify-guards fn-bpp-blockp)

; The two flag constraints RFC 9171 section 4.2.3 states as MUST.  They are
; kept apart from `fn-bpp-blockp` so that the codec accepts exactly what the
; wire format allows and a policy layer decides what to do about a peer that
; violates them.
(defun fn-bpp-flags-conformantp (b)
  (declare (xargs :guard (fn-bpp-blockp b)))
  (let ((flags (fn-bpp-flags b)))
    (and (implies (fn-bpp-administrativep flags)
                  (not (fn-bpp-any-status-requestp flags)))
         (implies (equal (fn-bpp-source b) (list :dtn-none))
                  (and (fn-bpp-no-fragmentp flags)
                       (not (fn-bpp-any-status-requestp flags)))))))

(verify-guards fn-bpp-flags-conformantp)

; -----------------------------------------------------------------------------
; Block to CBOR value and back (section 4.3.1 field order)

(defun fn-bpp-block-value (b crc-octets)
  (declare (xargs :guard (fn-bpp-blockp b)))
  (cons :array
        (append
         (list (cons :uint *fn-bpp-version*)
               (cons :uint (fn-bpp-flags b))
               (cons :uint (fn-bpp-crc-type b))
               (fn-bpp-eid-value (fn-bpp-destination b))
               (fn-bpp-eid-value (fn-bpp-source b))
               (fn-bpp-eid-value (fn-bpp-report-to b))
               (cons :array (list (cons :uint (fn-bpp-creation-time b))
                                  (cons :uint (fn-bpp-sequence b))))
               (cons :uint (fn-bpp-lifetime b)))
         (if (fn-bpp-fragmentp (fn-bpp-flags b))
             (list (cons :uint (fn-bpp-fragment-offset b))
                   (cons :uint (fn-bpp-total-adu-length b)))
           nil)
         (if (equal (fn-bpp-crc-type b) 0)
             nil
           (list (cons :bytes crc-octets))))))

(verify-guards fn-bpp-block-value)

(defun fn-bpp-uint-of (v)
  (declare (xargs :guard t))
  (if (and (consp v) (eq (car v) :uint) (natp (cdr v))
           (<= (cdr v) *fn-bpc-max-uint*))
      (cdr v)
    nil))

(verify-guards fn-bpp-uint-of)

(defthm fn-bpp-uint-of-is-bounded-natural
  (implies (fn-bpp-uint-of v)
           (and (natp (fn-bpp-uint-of v))
                (integerp (fn-bpp-uint-of v))
                (<= 0 (fn-bpp-uint-of v))
                (<= (fn-bpp-uint-of v) *fn-bpc-max-uint*))))

(defun fn-bpp-value-block (v)
  (declare (xargs :guard t))
  (if (not (and (consp v) (eq (car v) :array) (true-listp (cdr v))))
      nil
    (let* ((items (cdr v))
           (arity (len items)))
      (if (or (< arity 8) (< 11 arity))
          nil
        (let ((version (fn-bpp-uint-of (nth 0 items)))
              (flags (fn-bpp-uint-of (nth 1 items)))
              (crc-type (fn-bpp-uint-of (nth 2 items)))
              (destination (fn-bpp-value-eid (nth 3 items)))
              (source (fn-bpp-value-eid (nth 4 items)))
              (report-to (fn-bpp-value-eid (nth 5 items)))
              (stamp (nth 6 items))
              (lifetime (fn-bpp-uint-of (nth 7 items))))
          (if (not (and (equal version *fn-bpp-version*)
                        flags crc-type destination source report-to lifetime
                        (fn-bpp-crc-typep crc-type)
                        (consp stamp) (eq (car stamp) :array)
                        (true-listp (cdr stamp))
                        (equal (len (cdr stamp)) 2)
                        (fn-bpp-uint-of (nth 0 (cdr stamp)))
                        (natp (fn-bpp-uint-of (nth 1 (cdr stamp))))))
              nil
            (let* ((fragment (fn-bpp-fragmentp flags))
                   (expected (+ 8 (if fragment 2 0)
                                (if (equal crc-type 0) 0 1))))
              (if (not (equal arity expected))
                  nil
                (let ((offset (if fragment (fn-bpp-uint-of (nth 8 items)) nil))
                      (total (if fragment (fn-bpp-uint-of (nth 9 items)) nil)))
                  (if (and fragment (not (and offset (natp total))))
                      nil
                    (fn-bpp-make-block
                     flags crc-type destination source report-to
                     (fn-bpp-uint-of (nth 0 (cdr stamp)))
                     (fn-bpp-uint-of (nth 1 (cdr stamp)))
                     lifetime offset total)))))))))))

(verify-guards fn-bpp-value-block)

(defun fn-bpp-value-crc-field (v)
  (declare (xargs :guard t))
  (if (not (and (consp v) (eq (car v) :array) (true-listp (cdr v))))
      nil
    (let ((items (cdr v)))
      (if (not (consp items))
          nil
        (let ((last-item (nth (- (len items) 1) items)))
          (if (and (consp last-item) (eq (car last-item) :bytes))
              (cdr last-item)
            nil))))))

(verify-guards fn-bpp-value-crc-field)

; -----------------------------------------------------------------------------
; Encoding
;
; Section 4.3.1: "The CRC SHALL be computed over the concatenation of all bytes
; ... of the primary block including the CRC field itself, which, for this
; purpose, SHALL be temporarily populated with all bytes set to zero."  The
; zero-filled encoding therefore has exactly the length of the final encoding,
; and only the CRC field's content differs between them.

(defun fn-bpp-zeroed-encoding (b)
  (declare (xargs :guard (fn-bpp-blockp b)))
  (fn-bpc-enc :item (fn-bpp-block-value b (fn-bpp-zero-crc (fn-bpp-crc-type b)))))

; From here on the guard proofs need only that an encoding is an octet list
; (`fn-bpc-enc-are-octets`); opening `fn-bpc-enc` over the whole block array
; instead does not terminate in practice.
(local (in-theory (disable fn-bpc-enc)))

; The CRC guard needs only the CRC type out of `fn-bpp-blockp'; with its
; field recognizers open, the guard proof splits on every field (4 s).
; Closed from here to the last guard that opens the block.
(local (in-theory (disable fn-bpp-eidp fn-bpp-timep fn-bpp-flag-setp
                           fn-bpp-fragmentp)))

(defun fn-bpp-block-crc (b)
  (declare (xargs :guard (fn-bpp-blockp b)))
  (fn-bpp-crc-octets (fn-bpp-crc-type b) (fn-bpp-zeroed-encoding b)))

(defun fn-bpp-encode (b)
  (declare (xargs :guard (fn-bpp-blockp b)))
  (fn-bpc-enc :item (fn-bpp-block-value b (fn-bpp-block-crc b))))

(verify-guards fn-bpp-zeroed-encoding)
(verify-guards fn-bpp-block-crc)
(verify-guards fn-bpp-encode)

(local (in-theory (enable fn-bpp-eidp fn-bpp-timep fn-bpp-flag-setp
                          fn-bpp-fragmentp)))

; -----------------------------------------------------------------------------
; Decoding
;
; Four outcomes stay distinct: a CBOR-level refusal keeps the CBOR reason, a
; structurally wrong block is `:malformed`, a block whose attached CRC does not
; match what section 4.2.2 requires is `:crc-mismatch`, and a block whose CBOR
; spelling is not the deterministic one is `:noncanonical`.

(defun fn-bpp-ok (b) (declare (xargs :guard t)) (list :ok b))
(defun fn-bpp-error (reason) (declare (xargs :guard t)) (list :error reason))
(defun fn-bpp-result-okp (r)
  (declare (xargs :guard t))
  (and (consp r) (equal (car r) :ok)))
(defun fn-bpp-result-block (r)
  (declare (xargs :guard (true-listp r)))
  (nth 1 r))

(verify-guards fn-bpp-ok)
(verify-guards fn-bpp-error)
(verify-guards fn-bpp-result-okp)
(verify-guards fn-bpp-result-block)

; The same law for the decode result, and for the same reason: `fn-bpp-ok`
; stays enabled, so a caller's goal contains the cons nest rather than the
; constructor.
(defthm fn-bpp-result-block-of-a-built-result
  (equal (fn-bpp-result-block (cons tag (cons b rest))) b))

(defun fn-bpp-decode (octets)
  (declare (xargs :guard t))
  (let ((decoded (fn-bpc-decode-exact octets)))
    (if (not (fn-cbor-result-okp decoded))
        (fn-bpp-error (nth 1 decoded))
      (let* ((value (fn-cbor-result-value decoded))
             (b (fn-bpp-value-block value)))
        (if (not (and b (fn-bpp-blockp b)))
            (fn-bpp-error :malformed)
          (if (and (not (equal (fn-bpp-crc-type b) 0))
                   (not (equal (fn-bpp-value-crc-field value)
                               (fn-bpp-block-crc b))))
              (fn-bpp-error :crc-mismatch)
            (if (not (equal (fn-bpp-encode b) octets))
                (fn-bpp-error :noncanonical)
              (fn-bpp-ok b))))))))

(verify-guards fn-bpp-decode)

; -----------------------------------------------------------------------------
; Bundle identity (sections 4.2.7 and 5.9)
;
; Two distinct notions, and RFC 9171 keeps them apart:
;
;   * the ADU key -- source node ID plus creation timestamp -- is what
;     section 5.9 uses to group fragments for reassembly, and it is entirely
;     determined by the primary block;
;   * the bundle identity of a fragment adds the fragment offset and THIS
;     bundle's payload length (section 4.3.1, under Creation Timestamp).  The
;     payload length lives in the payload block, not the primary block, so the
;     primary block alone does not determine a fragment's bundle identity.
;     `fn-bpp-bundle-id` therefore takes the payload length as an argument.
;
; A source node ID of dtn:none makes the bundle not uniquely identifiable at
; all (section 4.2.3); `fn-bpp-identifiablep` says so explicitly.

(defun fn-bpp-adu-key (b)
  (declare (xargs :guard (fn-bpp-blockp b)))
  (list :fn-bp-adu-key
        (fn-bpp-source b)
        (fn-bpp-creation-time b)
        (fn-bpp-sequence b)))

(defun fn-bpp-bundle-id (b payload-length)
  (declare (xargs :guard (fn-bpp-blockp b)))
  (list :fn-bp-bundle-id
        (fn-bpp-source b)
        (fn-bpp-creation-time b)
        (fn-bpp-sequence b)
        (if (fn-bpp-fragmentp (fn-bpp-flags b)) (fn-bpp-fragment-offset b) nil)
        (if (fn-bpp-fragmentp (fn-bpp-flags b)) payload-length nil)))

(defun fn-bpp-identifiablep (b)
  (declare (xargs :guard (fn-bpp-blockp b)))
  (not (equal (fn-bpp-source b) (list :dtn-none))))

(verify-guards fn-bpp-adu-key)
(verify-guards fn-bpp-bundle-id)
(verify-guards fn-bpp-identifiablep)

; The primary-block identity, as canonical octets.
;
; This is the whole of the bundle identity that the primary block determines:
; the source node ID, the creation timestamp's time and sequence number and,
; when the fragment flag is set, the fragment offset and the total ADU length.
; It is deliberately NOT `fn-bpp-bundle-id`.  RFC 9171 section 4.3.1 identifies
; a fragment by THIS bundle's payload length, which lives in the payload block;
; two fragments of one ADU at the same offset with different payload lengths
; share this projection and are nevertheless different bundles.  So this is the
; coarsest key a receiver can compute from the primary block alone, and a
; reassembling receiver must still compare payload lengths.  A whole bundle and
; a fragment never collide here, because the encoded array has three elements
; in the first case and five in the second.
;
; The octets are this profile's CBOR encoding of that array, so canonicality
; comes from `fn-bpc-accepted-input-is-canonical` and invertibility from
; `fn-bpc-decode-of-encode`; there is no second spelling to keep in step.

(defun fn-bpp-primary-identity-value (b)
  (declare (xargs :guard (fn-bpp-blockp b)))
  (cons :array
        (if (fn-bpp-fragmentp (fn-bpp-flags b))
            (list (fn-bpp-eid-value (fn-bpp-source b))
                  (cons :uint (fn-bpp-creation-time b))
                  (cons :uint (fn-bpp-sequence b))
                  (cons :uint (fn-bpp-fragment-offset b))
                  (cons :uint (fn-bpp-total-adu-length b)))
          (list (fn-bpp-eid-value (fn-bpp-source b))
                (cons :uint (fn-bpp-creation-time b))
                (cons :uint (fn-bpp-sequence b))))))

(defun fn-bpp-primary-identity (b)
  (declare (xargs :guard (fn-bpp-blockp b)))
  (fn-bpc-encode (fn-bpp-primary-identity-value b)))

(verify-guards fn-bpp-primary-identity-value)
(verify-guards fn-bpp-primary-identity)

; Routing and reporting fields that identity must ignore.  These constructors
; exist so that the "identity ignores X" theorems have a subject.
(defun fn-bpp-with-destination (b d)
  (declare (xargs :guard (fn-bpp-blockp b)))
  (fn-bpp-make-block (fn-bpp-flags b) (fn-bpp-crc-type b)
                     d (fn-bpp-source b) (fn-bpp-report-to b)
                     (fn-bpp-creation-time b) (fn-bpp-sequence b)
                     (fn-bpp-lifetime b) (fn-bpp-fragment-offset b)
                     (fn-bpp-total-adu-length b)))

(defun fn-bpp-with-lifetime (b l)
  (declare (xargs :guard (fn-bpp-blockp b)))
  (fn-bpp-make-block (fn-bpp-flags b) (fn-bpp-crc-type b)
                     (fn-bpp-destination b) (fn-bpp-source b)
                     (fn-bpp-report-to b)
                     (fn-bpp-creation-time b) (fn-bpp-sequence b)
                     l (fn-bpp-fragment-offset b)
                     (fn-bpp-total-adu-length b)))

(defun fn-bpp-with-crc-type (b type)
  (declare (xargs :guard (fn-bpp-blockp b)))
  (fn-bpp-make-block (fn-bpp-flags b) type
                     (fn-bpp-destination b) (fn-bpp-source b)
                     (fn-bpp-report-to b)
                     (fn-bpp-creation-time b) (fn-bpp-sequence b)
                     (fn-bpp-lifetime b) (fn-bpp-fragment-offset b)
                     (fn-bpp-total-adu-length b)))

(verify-guards fn-bpp-with-destination)
(verify-guards fn-bpp-with-lifetime)
(verify-guards fn-bpp-with-crc-type)

; -----------------------------------------------------------------------------
; Extension blocks (section 4.4)
;
; Only the block-type-specific data is modeled here; the canonical block frame
; of section 4.3.2 is not part of this packet.  Each of the three is a bounded
; value with a deterministic CBOR encoding and an explicit decoder.

(defconst *fn-bpp-block-type-previous-node* 6)
(defconst *fn-bpp-block-type-bundle-age* 7)
(defconst *fn-bpp-block-type-hop-count* 10)

; Section 4.4.1: the data is the node ID of the forwarder, which SHALL conform
; to section 4.2.5.2 -- that is, it must be usable as a node ID.
(defun fn-bpp-previous-nodep (e)
  (declare (xargs :guard t))
  (and (fn-bpp-eidp e) (fn-bpp-eid-node-idp e)))

(defun fn-bpp-previous-node-data (e)
  (declare (xargs :guard (fn-bpp-previous-nodep e)))
  (fn-bpc-enc :item (fn-bpp-eid-value e)))

(defun fn-bpp-data-previous-node (octets)
  (declare (xargs :guard t))
  (let ((decoded (fn-bpc-decode-exact octets)))
    (if (not (fn-cbor-result-okp decoded))
        nil
      (let ((e (fn-bpp-value-eid (fn-cbor-result-value decoded))))
        (if (and e (fn-bpp-previous-nodep e)) e nil)))))

(verify-guards fn-bpp-previous-nodep)
(verify-guards fn-bpp-previous-node-data)
(verify-guards fn-bpp-data-previous-node)

; Section 4.4.2: milliseconds between creation and most recent forwarding.
(defun fn-bpp-bundle-agep (ms)
  (declare (xargs :guard t))
  (fn-bpp-timep ms))

(defun fn-bpp-bundle-age-data (ms)
  (declare (xargs :guard (fn-bpp-bundle-agep ms)))
  (fn-bpc-enc :item (cons :uint ms)))

(defun fn-bpp-data-bundle-age (octets)
  (declare (xargs :guard t))
  (let ((decoded (fn-bpc-decode-exact octets)))
    (if (not (fn-cbor-result-okp decoded))
        nil
      (fn-bpp-uint-of (fn-cbor-result-value decoded)))))

(verify-guards fn-bpp-bundle-agep)
(verify-guards fn-bpp-bundle-age-data)
(verify-guards fn-bpp-data-bundle-age)

; Section 4.4.3: hop limit MUST be in 1..255; hop count starts at zero and
; increases by one per hop.  A bundle whose count exceeds its limit SHOULD be
; deleted, so the count is allowed to reach the limit but the excess case is
; representable and recognized.
(defun fn-bpp-hop-countp (x)
  (declare (xargs :guard t))
  (and (true-listp x) (equal (len x) 3) (eq (car x) :hop-count)
       (natp (nth 1 x)) (<= 1 (nth 1 x)) (<= (nth 1 x) 255)
       (natp (nth 2 x)) (<= (nth 2 x) *fn-bpc-max-uint*)))

(defun fn-bpp-make-hop-count (limit count)
  (declare (xargs :guard t))
  (list :hop-count limit count))

(defun fn-bpp-hop-limit-exceededp (x)
  (declare (xargs :guard (fn-bpp-hop-countp x)))
  (< (nth 1 x) (nth 2 x)))

(defun fn-bpp-hop-count-data (x)
  (declare (xargs :guard (fn-bpp-hop-countp x)))
  (fn-bpc-enc :item (cons :array (list (cons :uint (nth 1 x))
                                       (cons :uint (nth 2 x))))))

(defun fn-bpp-data-hop-count (octets)
  (declare (xargs :guard t))
  (let ((decoded (fn-bpc-decode-exact octets)))
    (if (not (fn-cbor-result-okp decoded))
        nil
      (let ((v (fn-cbor-result-value decoded)))
        (if (not (and (consp v) (eq (car v) :array) (true-listp (cdr v))
                      (equal (len (cdr v)) 2)))
            nil
          (let ((x (fn-bpp-make-hop-count
                    (fn-bpp-uint-of (nth 0 (cdr v)))
                    (fn-bpp-uint-of (nth 1 (cdr v))))))
            (if (fn-bpp-hop-countp x) x nil)))))))

(verify-guards fn-bpp-hop-countp)
(verify-guards fn-bpp-make-hop-count)
(verify-guards fn-bpp-hop-limit-exceededp)
(verify-guards fn-bpp-hop-count-data)
(verify-guards fn-bpp-data-hop-count)

; -----------------------------------------------------------------------------
; Export theory: the primary-block identity.
;
; The identity projection and its encoding are proof vocabulary, not keystones:
; a book above reasons about them through the theorems in
; `books/bp-primary-invariants.lisp` (shape, octets, the routing/lifetime/CRC
; projection fact and `fn-bpp-primary-identity-determines-adu-key`), and the
; host evaluates them.  Nothing above needs their definitions opened, so they
; are withdrawn here under a name a book that does can enable in one line.
;
; The rest of this book -- the block record, the endpoint and time codecs, the
; extension-block data -- still exports its definitions enabled.  Making those
; opaque is item 4 of the bp deputy's proposal
; (planning/deputies/bp.md, "opaque records for bp-workflow, relay, bp-primary,
; bp-fragment") and is not this lane's to take.

(deftheory fn-bpp-identity-vocabulary
  '((:d fn-bpp-primary-identity-value) (:d fn-bpp-primary-identity)))

(in-theory (disable fn-bpp-identity-vocabulary))

; -----------------------------------------------------------------------------
; Export theory: the projections.
;
; These six are the `enabled_projection` lint's six entries for this book.
; A projection whose `:definition` ships enabled is unfolded out of a
; downstream goal before any rule stated over it can match, so a book above
; that states a theorem about `(fn-bpp-flags p)` is reasoning about a term
; that has already become `(nth 1 p)`.  Measured 2026-09-20, that is the
; whole reason `books/bp-node` could not verify `fn-bpn-receive`'s guard:
; the obligation is `fn-bpp-fragmentp`'s `(natp flags)` on the primary of a
; decoded bundle, and every fact available was about `fn-bpp-blockp` or
; `(fn-bpp-flags p)` while the goal said `(integerp (nth 1 p))`.
;
; What replaces the unfolding, above: the accessor-of-constructor laws
; beside the accessors (an explicit cons is the only thing they match, so a
; block that arrived from a decoder stays opaque), and the shape conjuncts
; `fn-bpp-blockp` already carries in projection vocabulary.
;
; The other five block projections (`fn-bpp-destination`,
; `fn-bpp-report-to`, `fn-bpp-lifetime`, `fn-bpp-fragment-offset`,
; `fn-bpp-total-adu-length`) stay enabled: the lint does not name them
; because no book above states a theorem over them, and withdrawing them
; without their own accessor-of-constructor laws would only move the
; problem.  Withdrawing the constructor too -- the opaque-record refactor,
; item 4 of `planning/deputies/bp.md` -- is what makes that worth doing in
; one step.

(deftheory fn-bpp-projection-vocabulary
  '((:d fn-bpp-flags) (:d fn-bpp-crc-type) (:d fn-bpp-source)
    (:d fn-bpp-creation-time) (:d fn-bpp-sequence)
    (:d fn-bpp-result-block)))

(in-theory (disable fn-bpp-projection-vocabulary))
