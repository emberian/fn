; books/bp-bundle.lisp -- RFC 9171 section 4.3: the bundle around the primary
; block.
;
; `books/bp-primary` models the primary block and the block-type-specific data
; of the three extension blocks of section 4.4.  It does not model the frame
; those data sit in (section 4.3.2, the canonical block) nor the array that
; holds the whole bundle (section 4.3, "a bundle is a concatenation of blocks
; ... represented as an indefinite-length CBOR array").  Until this book, a
; transfer's octets were a blob to fn: the convergence layer carried them and
; nothing above it could say what they were.
;
; What is here:
;
;   * `fn-bpb-block`, the canonical block of section 4.3.2 -- type code, block
;     number, processing control flags, CRC type, block-type-specific data --
;     as an `fn-defrecord`.  The payload block (type 1, number 1, section 4.3.3)
;     is a canonical block like any other; `fn-bpb-payload-blockp` says which.
;   * `fn-bpb-encode-block` / `fn-bpb-decode-block`, with the CRC of
;     section 4.2.2 computed over the block's own zero-filled encoding, reusing
;     `fn-bpp-crc16` and `fn-bpp-crc32c`.  A CRC is a checksum, not a digest:
;     it is computed in the logic and there is no seam here.
;   * `fn-bpb-encode` / `fn-bpb-decode` over the whole bundle.
;   * the three extension blocks of section 4.4 as canonical blocks whose data
;     are `fn-bpp-previous-node-data`, `fn-bpp-bundle-age-data` and
;     `fn-bpp-hop-count-data`.
;
; The primary block inside a bundle is decoded by `fn-bpp-decode` itself, not
; by a second implementation of it: `fn-bpc-dec` is used only to find where the
; primary block's CBOR item ends, and the octets between there and the bundle's
; first octet are handed to `fn-bpp-decode` unchanged.  So every primary-block
; keystone -- `fn-bpp-decode-of-encode`,
; `fn-bpp-accepted-input-is-canonical-by-construction`,
; `fn-bpp-accepted-block-has-valid-crc` -- is about the function this book
; calls.
;
; Bounds before allocation, in the order the decoder applies them: the input
; length against `limit` (`fn-cbor-at-mostp`, which walks at most limit+1
; conses and allocates nothing); then, per block, the declared byte-string
; length against `*fn-bpb-max-data*` before any `take`; then the block count
; against `*fn-bpb-max-blocks*`.

(in-package "ACL2")

(include-book "bp-primary-invariants")
(include-book "defrecord")

; -----------------------------------------------------------------------------
; Bounds.

; A canonical block's block-type-specific data.  One mebibyte is well above the
; largest ADU fn produces and well below what a peer could use to make a single
; `take` expensive.
(defconst *fn-bpb-max-data* 1048576)

; Section 4.1: a bundle is a primary block, zero or more canonical blocks and a
; payload block.  fn accepts at most this many canonical blocks in one bundle.
(defconst *fn-bpb-max-blocks* 32)

; The default whole-bundle limit, when a caller has no tighter one.  The
; convergence layer's transfer MRU is the tighter one in practice and
; `fn-bpn-receive` passes it.
(defconst *fn-bpb-max-input* 1048576)

; Section 4.3.3 and 4.1: the payload block is type 1 and MUST be block number 1.
(defconst *fn-bpb-block-type-payload* 1)
(defconst *fn-bpb-payload-block-number* 1)

; Section 4.3.2 head octets: a definite-length CBOR array of five elements
; without a CRC field, of six with one.  Both are the deterministic spelling
; (RFC 8949 section 4.2.1: a count below 24 is the additional information).
(defconst *fn-bpb-block-head-5* 133)
(defconst *fn-bpb-block-head-6* 134)

; Section 4.3: the bundle is an indefinite-length array, so 0x9f opens it and
; 0xff closes it.
(defconst *fn-bpb-array-open* 159)
(defconst *fn-bpb-array-break* 255)

; -----------------------------------------------------------------------------
; The canonical block (section 4.3.2)

(defun fn-bpb-datap (x)
  (declare (xargs :guard t))
  (and (fn-cbor-octet-listp x)
       (<= (len x) *fn-bpb-max-data*)))

(fn-defrecord fn-bpb-block
  :tag :fn-bpb-block
  :constructor (fn-bpb-make-block type number flags crc-type data)
  :fields ((fn-bpb-block-type fn-bpp-timep)
           (fn-bpb-block-number fn-bpp-timep)
           (fn-bpb-block-flags fn-bpp-flag-setp)
           (fn-bpb-block-crc-type fn-bpp-crc-typep)
           (fn-bpb-block-data fn-bpb-datap))
  :car-fn fn-cbor-ag-car
  :cdr-fn fn-cbor-ag-cdr)

; Section 4.2.4, the block processing control flags, numbered from the
; low-order bit.  As with the bundle flags, unrecognized bits are kept rather
; than rejected (section 4.2.4: "SHALL be ignored").
(defconst *fn-bpb-flag-replicate* 1)
(defconst *fn-bpb-flag-report-if-unprocessable* 2)
(defconst *fn-bpb-flag-delete-if-unprocessable* 4)
(defconst *fn-bpb-flag-discard-if-unprocessable* 16)

(defun fn-bpb-flag-replicate-in-fragments (b)
  (declare (xargs :guard (fn-bpb-blockp b)))
  (fn-bpp-flag-onp (fn-bpb-block-flags b) *fn-bpb-flag-replicate*))

(defun fn-bpb-flag-report-if-unprocessable (b)
  (declare (xargs :guard (fn-bpb-blockp b)))
  (fn-bpp-flag-onp (fn-bpb-block-flags b) *fn-bpb-flag-report-if-unprocessable*))

(defun fn-bpb-flag-delete-if-unprocessable (b)
  (declare (xargs :guard (fn-bpb-blockp b)))
  (fn-bpp-flag-onp (fn-bpb-block-flags b) *fn-bpb-flag-delete-if-unprocessable*))

(defun fn-bpb-flag-discard-if-unprocessable (b)
  (declare (xargs :guard (fn-bpb-blockp b)))
  (fn-bpp-flag-onp (fn-bpb-block-flags b) *fn-bpb-flag-discard-if-unprocessable*))

(defun fn-bpb-payload-blockp (b)
  (declare (xargs :guard t))
  (and (fn-bpb-blockp b)
       (equal (fn-bpb-block-type b) *fn-bpb-block-type-payload*)
       (equal (fn-bpb-block-number b) *fn-bpb-payload-block-number*)))

(defun fn-bpb-block-listp (xs)
  (declare (xargs :guard t))
  (if (consp xs)
      (and (fn-bpb-blockp (car xs))
           (fn-bpb-block-listp (cdr xs)))
    (null xs)))

(defun fn-bpb-block-numbers (xs)
  (declare (xargs :guard (fn-bpb-block-listp xs)))
  (if (consp xs)
      (cons (fn-bpb-block-number (car xs)) (fn-bpb-block-numbers (cdr xs)))
    nil))

; Section 4.1: "the block number of the payload block is always 1" and block
; number 0 is the primary block's, so a non-payload canonical block carries
; neither, and no two carry the same.
(defun fn-bpb-numbers-distinctp (xs)
  (declare (xargs :guard (fn-bpb-block-listp xs)))
  (let ((numbers (fn-bpb-block-numbers xs)))
    (and (no-duplicatesp-equal numbers)
         (not (member-equal 0 numbers))
         (not (member-equal *fn-bpb-payload-block-number* numbers)))))

(verify-guards fn-bpb-datap)
(verify-guards fn-bpb-payload-blockp)
(verify-guards fn-bpb-block-listp)
(verify-guards fn-bpb-block-numbers)
(verify-guards fn-bpb-numbers-distinctp)

(defthm fn-bpb-block-listp-implies-true-listp
  (implies (fn-bpb-block-listp xs) (true-listp xs))
  :rule-classes (:rewrite :forward-chaining))

; -----------------------------------------------------------------------------
; Encoding one canonical block
;
; Section 4.3.2, in field order: block type code, block number, block
; processing control flags, CRC type, block-type-specific data, and the CRC
; field iff the CRC type is not zero.  Section 4.2.2 fixes the CRC: it is
; computed over the whole block with the CRC field present and zero filled, so
; the zero-filled encoding has exactly the final encoding's length.

(defun fn-bpb-encode-block-with-crc (b crc)
  (declare (xargs :guard (and (fn-bpb-blockp b) (fn-cbor-octet-listp crc))))
  (cons (if (equal (fn-bpb-block-crc-type b) 0)
            *fn-bpb-block-head-5*
          *fn-bpb-block-head-6*)
        (append (fn-bpc-argument 0 (fn-bpb-block-type b))
        (append (fn-bpc-argument 0 (fn-bpb-block-number b))
        (append (fn-bpc-argument 0 (fn-bpb-block-flags b))
        (append (fn-bpc-argument 0 (fn-bpb-block-crc-type b))
        (append (fn-bpc-argument 2 (len (fn-bpb-block-data b)))
        (append (fn-bpb-block-data b)
                (if (equal (fn-bpb-block-crc-type b) 0)
                    nil
                  (append (fn-bpc-argument 2 (len crc)) crc))))))))))

(verify-guards fn-bpb-encode-block-with-crc)

; Three list facts, stated once so that the encoding's octet-ness is settled
; by them and `fn-cbor-octet-listp` never opens over a long append.  They are
; `local`: `books/cbor.lisp` owns this vocabulary and no book above should
; inherit a `consp`-backchaining rule from here.
(local
 (defthm fn-bpb-octet-listp-of-append
   (implies (and (fn-cbor-octet-listp a) (fn-cbor-octet-listp b))
            (fn-cbor-octet-listp (append a b)))
   :hints (("Goal" :in-theory (enable fn-cbor-octet-listp)))))

(local
 (defthm fn-bpb-octet-listp-of-cons
   (implies (and (fn-cbor-octetp h) (fn-cbor-octet-listp xs))
            (fn-cbor-octet-listp (cons h xs)))
   :hints (("Goal" :in-theory (enable fn-cbor-octet-listp)))))

(local
 (defthm fn-bpb-octet-listp-implies-true-listp
   (implies (fn-cbor-octet-listp xs) (true-listp xs))
   :rule-classes (:rewrite :forward-chaining)
   :hints (("Goal" :in-theory (enable fn-cbor-octet-listp)))))

(local
 (defthm fn-bpb-octet-listp-of-nil
   (fn-cbor-octet-listp nil)
   :hints (("Goal" :in-theory (enable fn-cbor-octet-listp)))))

; The encoding of a block is octets.  Stated here rather than in
; `books/bp-bundle-invariants` because the CRC is computed over it, so the
; guard of `fn-bpb-block-crc` needs it.
(defthm fn-bpb-encode-block-with-crc-are-octets
  (implies (and (fn-bpb-blockp b) (fn-cbor-octet-listp crc))
           (fn-cbor-octet-listp (fn-bpb-encode-block-with-crc b crc)))
  :hints (("Goal"
           :in-theory (e/d (fn-bpb-datap fn-bpc-argument-are-octets)
                           (fn-cbor-octet-listp fn-bpc-argument)))))

(defun fn-bpb-block-crc (b)
  (declare (xargs :guard (fn-bpb-blockp b) :verify-guards nil))
  (fn-bpp-crc-octets (fn-bpb-block-crc-type b)
                     (fn-bpb-encode-block-with-crc
                      b (fn-bpp-zero-crc (fn-bpb-block-crc-type b)))))

(verify-guards fn-bpb-block-crc
  :hints (("Goal" :in-theory (disable fn-bpb-encode-block-with-crc))))

; The CRC field is octets and has the width its type prescribes.  Both are
; `books/bp-primary`'s facts about `fn-bpp-crc-octets`; the hint keeps that
; function closed so that the rules about it match rather than the CRC scan
; opening into base-256 arithmetic.
(defthm fn-bpb-block-crc-are-octets
  (implies (fn-bpb-blockp b) (fn-cbor-octet-listp (fn-bpb-block-crc b)))
  :hints (("Goal" :in-theory (disable fn-bpb-encode-block-with-crc
                                      fn-bpp-crc-octets fn-cbor-u16-bytes
                                      fn-cbor-u32-bytes fn-bpp-zero-crc))))

(defthm fn-bpb-block-crc-length
  (implies (fn-bpb-blockp b) (<= (len (fn-bpb-block-crc b)) 4))
  :rule-classes :linear
  :hints (("Goal" :in-theory (disable fn-bpb-encode-block-with-crc
                                      fn-bpp-crc-octets fn-cbor-u16-bytes
                                      fn-cbor-u32-bytes fn-bpp-zero-crc))))

(defun fn-bpb-encode-block (b)
  (declare (xargs :guard (fn-bpb-blockp b) :verify-guards nil))
  (fn-bpb-encode-block-with-crc b (fn-bpb-block-crc b)))

(verify-guards fn-bpb-encode-block
  :hints (("Goal" :in-theory (disable fn-bpb-encode-block-with-crc
                                      fn-bpb-block-crc))))

(defthm fn-bpb-encode-block-are-octets
  (implies (fn-bpb-blockp b) (fn-cbor-octet-listp (fn-bpb-encode-block b)))
  :hints (("Goal" :in-theory (disable fn-bpb-encode-block-with-crc
                                      fn-bpb-block-crc))))

; `append`'s guard on the canonicality check of `fn-bpb-decode-block`, and
; nothing else; a `true-listp` rule backchaining through the encoder is not
; something a book above should inherit, so it is stated for the encoder term
; alone.
(defthm fn-bpb-encode-block-is-true-list
  (implies (fn-bpb-blockp b) (true-listp (fn-bpb-encode-block b)))
  :hints (("Goal" :in-theory (disable fn-bpb-encode-block
                                      fn-bpb-encode-block-with-crc
                                      fn-bpb-block-crc))))

; -----------------------------------------------------------------------------
; Decoding one canonical block
;
; Two field readers, each of which refuses before it allocates: a head whose
; major type is not the one this position requires is a refusal, and a declared
; byte-string length above the bound is a refusal taken from the length alone.

(defun fn-bpb-take-uint (octets)
  (declare (xargs :guard (fn-cbor-octet-listp octets)
                  :guard-hints
                  (("Goal" :in-theory
                    (e/d (fn-bpc-octet-listp-cdr
                          fn-bpc-car-of-octet-list-is-natural)
                         (fn-bpc-decode-head fn-bpc-decode-argument
                          fn-cbor-decode-argument))))))
  (if (not (consp octets))
      (fn-cbor-error :truncated)
    (if (not (< (car octets) 32))
        (fn-cbor-error :not-an-unsigned-integer)
      (fn-bpc-decode-head (car octets) (cdr octets)))))

(defun fn-bpb-take-bytes (octets bound)
  (declare (xargs :guard (and (fn-cbor-octet-listp octets) (natp bound))
                  :guard-hints
                  (("Goal" :in-theory
                    (e/d (fn-bpc-octet-listp-cdr
                          fn-bpc-car-of-octet-list-is-natural
                          fn-bpc-octet-listp-nthcdr
                          fn-bpc-octet-listp-take
                          fn-bpc-decode-head-rest-are-octets
                          fn-bpc-decode-head-value-is-natural)
                         (fn-bpc-decode-head fn-bpc-decode-argument
                          fn-cbor-decode-argument))))))
  (if (not (consp octets))
      (fn-cbor-error :truncated)
    (if (not (and (< 63 (car octets)) (< (car octets) 96)))
        (fn-cbor-error :not-a-byte-string)
      (let ((h (fn-bpc-decode-head (- (car octets) 64) (cdr octets))))
        (if (not (fn-cbor-result-okp h))
            h
          (let ((n (fn-cbor-result-value h))
                (rest (fn-cbor-result-rest h)))
            (if (< bound n)
                (fn-cbor-error :limit)
              (if (not (<= n (len rest)))
                  (fn-cbor-error :truncated)
                (fn-cbor-ok (take n rest) (nthcdr n rest))))))))))


(defthm fn-bpb-take-uint-rest-are-octets
  (implies (fn-cbor-octet-listp octets)
           (fn-cbor-octet-listp (fn-cbor-result-rest (fn-bpb-take-uint octets))))
  :hints (("Goal" :in-theory (e/d (fn-bpc-decode-head-rest-are-octets
                                   fn-bpc-octet-listp-cdr)
                                  (fn-bpc-decode-head fn-bpc-decode-argument fn-cbor-decode-argument)))))

(defthm fn-bpb-take-bytes-rest-are-octets
  (implies (fn-cbor-octet-listp octets)
           (fn-cbor-octet-listp
            (fn-cbor-result-rest (fn-bpb-take-bytes octets bound))))
  :hints (("Goal" :in-theory (e/d (fn-bpc-decode-head-rest-are-octets
                                   fn-bpc-octet-listp-cdr
                                   fn-bpc-octet-listp-nthcdr)
                                  (fn-bpc-decode-head fn-bpc-decode-argument fn-cbor-decode-argument)))))

(defthm fn-bpb-take-bytes-value-are-octets
  (implies (and (fn-cbor-octet-listp octets)
                (fn-cbor-result-okp (fn-bpb-take-bytes octets bound)))
           (fn-cbor-octet-listp
            (fn-cbor-result-value (fn-bpb-take-bytes octets bound))))
  :hints (("Goal" :in-theory (e/d (fn-bpc-decode-head-rest-are-octets
                                   fn-bpc-decode-head-value-is-natural
                                   fn-bpc-octet-listp-cdr
                                   fn-bpc-octet-listp-take)
                                  (fn-bpc-decode-head fn-bpc-decode-argument fn-cbor-decode-argument)))))

; What `fn-bpb-take-bytes` returns is bounded by its `bound` argument, and
; what `fn-bpb-take-uint` returns is a 64-bit time; neither is stated here.
; `fn-bpb-decode-block` reconstructs the record and re-applies
; `fn-bpb-blockp`, so the field types are established by the recognizer at the
; one place they are used, not by five lemmas about the readers.

(defun fn-bpb-decode-block (octets)
  (declare (xargs :guard (fn-cbor-octet-listp octets)
                  :guard-hints
                  (("Goal" :in-theory
                    (e/d (fn-bpc-octet-listp-cdr)
                         (fn-bpc-decode-head fn-bpc-decode-argument
                          fn-cbor-decode-argument fn-bpb-take-uint
                          fn-bpb-take-bytes fn-bpb-encode-block
                          fn-bpb-block-crc))))))
  (if (not (and (consp octets)
                (or (equal (car octets) *fn-bpb-block-head-5*)
                    (equal (car octets) *fn-bpb-block-head-6*))))
      (fn-cbor-error :malformed)
    (let* ((crcp (equal (car octets) *fn-bpb-block-head-6*))
           (r1 (fn-bpb-take-uint (cdr octets)))
           (r2 (fn-bpb-take-uint (fn-cbor-result-rest r1)))
           (r3 (fn-bpb-take-uint (fn-cbor-result-rest r2)))
           (r4 (fn-bpb-take-uint (fn-cbor-result-rest r3)))
           (r5 (fn-bpb-take-bytes (fn-cbor-result-rest r4) *fn-bpb-max-data*))
           (r6 (if crcp
                   (fn-bpb-take-bytes (fn-cbor-result-rest r5) 4)
                 (fn-cbor-ok nil (fn-cbor-result-rest r5)))))
      ; The first field that refused is returned as it refused: a
      ; non-deterministic spelling is `:noncanonical`, a declared length above
      ; the bound is `:limit`, and a short input is `:truncated`.  Collapsing
      ; them to one reason would lose the distinction the caller reports.
      (if (not (fn-cbor-result-okp r1)) r1
      (if (not (fn-cbor-result-okp r2)) r2
      (if (not (fn-cbor-result-okp r3)) r3
      (if (not (fn-cbor-result-okp r4)) r4
      (if (not (fn-cbor-result-okp r5)) r5
      (if (not (fn-cbor-result-okp r6)) r6
        (let ((b (fn-bpb-make-block (fn-cbor-result-value r1)
                                    (fn-cbor-result-value r2)
                                    (fn-cbor-result-value r3)
                                    (fn-cbor-result-value r4)
                                    (fn-cbor-result-value r5))))
          (if (not (fn-bpb-blockp b))
              (fn-cbor-error :malformed)
            (if (not (equal crcp (not (equal (fn-bpb-block-crc-type b) 0))))
                (fn-cbor-error :crc-type-mismatch)
              (if (and crcp
                       (not (equal (fn-cbor-result-value r6)
                                   (fn-bpb-block-crc b))))
                  (fn-cbor-error :crc-mismatch)
                (if (not (equal octets
                                (append (fn-bpb-encode-block b)
                                        (fn-cbor-result-rest r6))))
                    (fn-cbor-error :noncanonical)
                  (fn-cbor-ok b (fn-cbor-result-rest r6))))))))))))))))


; -----------------------------------------------------------------------------
; The block sequence, up to the break octet.

; The guard is `append''s: each block's encoding is a true list, which
; `fn-bpb-encode-block-is-true-list' states.  With the encoder and the block
; recognizer open, the CRC scans split the conjecture 128 ways twice, 1.8 s
; (planning/evidence/misc-books-cost-2026-09-23.md).
(defun fn-bpb-encode-blocks (xs)
  (declare (xargs :guard (fn-bpb-block-listp xs)
                  :guard-hints (("Goal" :in-theory
                                 (disable fn-bpb-encode-block
                                          fn-bpb-blockp)))))
  (if (consp xs)
      (append (fn-bpb-encode-block (car xs)) (fn-bpb-encode-blocks (cdr xs)))
    nil))

(defun fn-bpb-decode-blocks (octets budget)
  (declare (xargs :guard (and (fn-cbor-octet-listp octets) (natp budget))
                  :verify-guards nil
                  :measure (nfix budget)))
  (if (not (consp octets))
      (fn-cbor-error :truncated)
    (if (equal (car octets) *fn-bpb-array-break*)
        (fn-cbor-ok nil (cdr octets))
      (if (zp budget)
          (fn-cbor-error :too-many-blocks)
        (let ((one (fn-bpb-decode-block octets)))
          (if (not (fn-cbor-result-okp one))
              one
            (let ((more (fn-bpb-decode-blocks (fn-cbor-result-rest one)
                                              (- budget 1))))
              (if (not (fn-cbor-result-okp more))
                  more
                (fn-cbor-ok (cons (fn-cbor-result-value one)
                                  (fn-cbor-result-value more))
                            (fn-cbor-result-rest more))))))))))

(verify-guards fn-bpb-encode-blocks)

(defthm fn-bpb-decode-block-rest-are-octets
  (implies (fn-cbor-octet-listp octets)
           (fn-cbor-octet-listp (fn-cbor-result-rest (fn-bpb-decode-block octets))))
  :hints (("Goal" :in-theory (e/d (fn-bpc-octet-listp-cdr)
                                  (fn-bpb-take-uint fn-bpb-take-bytes
                                   fn-bpb-encode-block fn-bpb-block-crc)))))

(verify-guards fn-bpb-decode-blocks
  :hints (("Goal" :in-theory (e/d (fn-bpc-octet-listp-cdr)
                                  (fn-bpb-decode-block)))))

; -----------------------------------------------------------------------------
; The bundle (section 4.3)
;
; The payload block is held apart from the other canonical blocks because
; section 4.1 requires it to be last and unique; keeping it in the list would
; make "last" a property to re-derive on every use.

(defun fn-bpb-splitp (blocks payload)
  (declare (xargs :guard t))
  (and (fn-bpb-block-listp blocks)
       (<= (len blocks) *fn-bpb-max-blocks*)
       (fn-bpb-numbers-distinctp blocks)
       (fn-bpb-payload-blockp payload)))

(verify-guards fn-bpb-splitp)

(fn-defrecord fn-bpb-bundle
  :tag :fn-bpb-bundle
  :constructor (fn-bpb-make-bundle primary blocks payload)
  :fields ((fn-bpb-bundle-primary fn-bpp-blockp)
           (fn-bpb-bundle-blocks fn-bpb-block-listp)
           (fn-bpb-bundle-payload fn-bpb-payload-blockp))
  :extra ((fn-bpb-splitp (fn-bpb-bundle-blocks x) (fn-bpb-bundle-payload x)))
  :car-fn fn-cbor-ag-car
  :cdr-fn fn-cbor-ag-cdr)

(defun fn-bpb-payload (bundle)
  (declare (xargs :guard (fn-bpb-bundlep bundle)))
  (fn-bpb-block-data (fn-bpb-bundle-payload bundle)))

(defun fn-bpb-bundle-id (bundle)
  (declare (xargs :guard (fn-bpb-bundlep bundle)
                  :guard-hints
                  (("Goal" :in-theory (disable fn-bpp-blockp fn-bpb-splitp
                                               fn-bpb-block-listp
                                               fn-bpb-payload-blockp)))))
  (fn-bpp-bundle-id (fn-bpb-bundle-primary bundle)
                    (len (fn-bpb-payload bundle))))

(verify-guards fn-bpb-payload)
(verify-guards fn-bpb-bundle-id)

(defthm fn-bpb-encode-blocks-are-octets
  (implies (fn-bpb-block-listp xs)
           (fn-cbor-octet-listp (fn-bpb-encode-blocks xs)))
  :hints (("Goal" :in-theory (disable fn-bpb-encode-block fn-bpb-block-crc))))

(local
 (defthm fn-bpb-bpp-encode-is-true-list
   (true-listp (fn-bpp-encode b))
   :hints (("Goal" :in-theory (enable fn-bpc-enc-is-true-list)))))

(defun fn-bpb-encode (bundle)
  (declare (xargs :guard (fn-bpb-bundlep bundle)
                  :guard-hints
                  (("Goal" :in-theory (disable fn-bpb-encode-block
                                               fn-bpb-encode-blocks
                                               fn-bpb-block-crc fn-bpp-encode
                                               fn-bpp-blockp fn-bpb-splitp)))))
  (cons *fn-bpb-array-open*
        (append (fn-bpp-encode (fn-bpb-bundle-primary bundle))
        (append (fn-bpb-encode-blocks (fn-bpb-bundle-blocks bundle))
        (append (fn-bpb-encode-block (fn-bpb-bundle-payload bundle))
                (list *fn-bpb-array-break*))))))


; All but the last, and the last.  Written out rather than taken from
; `butlast`/`last` so that the two lemmas the round trip needs are about
; functions this book owns and no `nfix`/`nthcdr` normal form arrives with
; them.
(defun fn-bpb-front (xs)
  (declare (xargs :guard t))
  (if (consp xs)
      (if (consp (cdr xs)) (cons (car xs) (fn-bpb-front (cdr xs))) nil)
    nil))

(defun fn-bpb-final (xs)
  (declare (xargs :guard t))
  (if (consp xs)
      (if (consp (cdr xs)) (fn-bpb-final (cdr xs)) (car xs))
    nil))

(verify-guards fn-bpb-front)
(verify-guards fn-bpb-final)

; The decoder, in three functions rather than one.  Written out as a single
; nested `let*` its guard conjecture is one term with every branch inlined,
; and ACL2 8.7 exhausts the control stack normalizing it under `certify-book`
; (measured 2026-09-20: `IF-COMPILE` backtrace, no error message).  Each
; piece below has a guard conjecture the prover can hold.

; The primary block prefix.  `fn-bpc-dec` is used ONLY to find where the
; primary block's CBOR item ends; the octets up to there go to `fn-bpp-decode`
; unchanged, so the decoder of a bundle's primary block is the certified one
; and not a second implementation of it.
; `take` wants a non-negative count, so the scan's remainder must be no
; longer than what it scanned.  That is a corollary of the CBOR decoder's own
; `-reencodes-consumed-prefix`: the consumed prefix appended to the remainder
; IS the input, so the remainder's length is at most the input's.  Proving it
; by induction over `fn-bpc-dec` instead is what exhausted the prover here on
; 2026-09-20.
(local
 (defthm fn-bpb-dec-rest-is-no-longer
   (implies (and (fn-cbor-octet-listp octets)
                 (fn-cbor-result-okp (fn-bpc-dec :item 0 octets budget)))
            (<= (len (fn-cbor-result-rest (fn-bpc-dec :item 0 octets budget)))
                (len octets)))
   :rule-classes :linear
   :hints (("Goal"
            :use ((:instance fn-bpc-dec-reencodes-consumed-prefix
                             (flg :item) (count 0)))
            :in-theory (e/d (fn-bpc-len-of-append)
                            (fn-bpc-dec fn-bpc-enc
                             fn-bpc-dec-reencodes-consumed-prefix))))))

(defun fn-bpb-scan-primary (octets)
  (declare (xargs :guard (fn-cbor-octet-listp octets)
                  :guard-hints
                  (("Goal" :in-theory
                    (e/d (fn-bpc-dec-rest-are-octets fn-bpc-octet-listp-take)
                         (fn-bpc-dec fn-bpp-decode))))))
  (let ((scan (fn-bpc-dec :item 0 octets *fn-bpc-max-items*)))
    (if (not (fn-cbor-result-okp scan))
        (fn-cbor-error :malformed)
      (let* ((after (fn-cbor-result-rest scan))
             (chunk (take (- (len octets) (len after)) octets))
             (p (fn-bpp-decode chunk)))
        (if (not (fn-bpp-result-okp p))
            (fn-cbor-error :primary-block-refused)
          (fn-cbor-ok (fn-bpp-result-block p) after))))))

(defthm fn-bpb-scan-primary-yields-a-block
  (implies (fn-cbor-result-okp (fn-bpb-scan-primary octets))
           (fn-bpp-blockp (fn-cbor-result-value (fn-bpb-scan-primary octets))))
  :hints (("Goal" :in-theory (disable fn-bpc-dec fn-bpp-decode
                                      fn-bpp-blockp fn-bpp-result-block))))

(defthm fn-bpb-scan-primary-rest-are-octets
  (implies (fn-cbor-octet-listp octets)
           (fn-cbor-octet-listp
            (fn-cbor-result-rest (fn-bpb-scan-primary octets))))
  :hints (("Goal" :in-theory (e/d (fn-bpc-dec-rest-are-octets)
                                  (fn-bpc-dec fn-bpp-decode)))))

; The list version below inducts over `fn-bpb-decode-blocks` with
; `fn-bpb-decode-block` CLOSED, so the one-block fact has to be a rule before
; it.  Without it the induction has nothing to apply and the prover runs
; away: measured 2026-09-20, the run was killed at the 2400 s cap with this
; theorem still open (`build/acl2/certify-20260920T195958Z-1136779`).
(defthm fn-bpb-decode-block-yields-a-block
  (implies (fn-cbor-result-okp (fn-bpb-decode-block octets))
           (fn-bpb-blockp (fn-cbor-result-value (fn-bpb-decode-block octets))))
  :hints (("Goal" :in-theory (disable fn-bpb-encode-block fn-bpb-block-crc
                                      fn-bpb-take-uint fn-bpb-take-bytes))))

(defthm fn-bpb-decode-blocks-yield-blocks
  (implies (and (fn-cbor-octet-listp octets)
                (fn-cbor-result-okp (fn-bpb-decode-blocks octets budget)))
           (fn-bpb-block-listp
            (fn-cbor-result-value (fn-bpb-decode-blocks octets budget))))
  :hints (("Goal"
           :induct (fn-bpb-decode-blocks octets budget)
           :in-theory (e/d (fn-bpc-octet-listp-cdr)
                           (fn-bpb-decode-block fn-bpb-encode-block
                            fn-bpb-block-crc)))))

; Section 4.1: the payload block is the last one, and there is one.  The
; recognizer decides the rest -- pairwise distinct block numbers, no
; canonical block numbered 0 or 1, the payload block numbered 1 -- so a
; separate uniqueness check here would restate a conjunct of `fn-bpb-bundlep`.
(defun fn-bpb-assemble (primary blocks)
  (declare (xargs :guard (and (fn-bpp-blockp primary)
                              (fn-bpb-block-listp blocks))))
  (if (not (consp blocks))
      (fn-cbor-error :no-payload-block)
    (let ((bundle (fn-bpb-make-bundle primary (fn-bpb-front blocks)
                                      (fn-bpb-final blocks))))
      (if (not (fn-bpb-bundlep bundle))
          (fn-cbor-error :malformed)
        (fn-cbor-ok bundle nil)))))

; `limit` is the caller's whole-input bound -- the convergence layer's
; transfer MRU when the caller is `fn-bpn-receive` -- and it is applied
; before the first octet is examined.
(defun fn-bpb-decode (octets limit)
  (declare (xargs :guard (and (fn-cbor-octet-listp octets) (natp limit))
                  :guard-hints
                  (("Goal" :in-theory
                    (e/d (fn-bpc-octet-listp-cdr)
                         (fn-bpb-scan-primary fn-bpb-decode-blocks
                          fn-bpb-assemble))))))
  (if (not (fn-cbor-at-mostp octets limit))
      (fn-cbor-error :limit)
    (if (not (and (consp octets) (equal (car octets) *fn-bpb-array-open*)))
        (fn-cbor-error :malformed)
      (let ((p (fn-bpb-scan-primary (cdr octets))))
        (if (not (fn-cbor-result-okp p))
            p
          ;; The budget counts EVERY block in the array after the primary,
          ;; and the payload block is one of them (section 4.1 requires it
          ;; last), so a bundle carrying the full `*fn-bpb-max-blocks*`
          ;; canonical blocks is an array of that many plus one.  Found by
          ;; `fn-bpb-decode-of-encode` on 2026-09-20 (w10/dtn-3): with the
          ;; budget at `*fn-bpb-max-blocks*` the round trip is FALSE at
          ;; `(len (fn-bpb-bundle-blocks bundle)) = 32` --- the encoder
          ;; admits the bundle and the decoder refuses its own output with
          ;; `:too-many-blocks`.  The bound on canonical blocks is not
          ;; loosened: an array carrying one canonical block more than
          ;; `*fn-bpb-max-blocks*` is `*fn-bpb-max-blocks*` + 2 blocks long
          ;; and the budget still refuses it, and `fn-bpb-assemble` re-applies
          ;; `fn-bpb-splitp` to whatever the budget let through.
          (let ((bs (fn-bpb-decode-blocks (fn-cbor-result-rest p)
                                          (+ 1 *fn-bpb-max-blocks*))))
            (if (not (fn-cbor-result-okp bs))
                bs
              (if (not (null (fn-cbor-result-rest bs)))
                  (fn-cbor-error :trailing-octets)
                (fn-bpb-assemble (fn-cbor-result-value p)
                                 (fn-cbor-result-value bs))))))))))

; -----------------------------------------------------------------------------
; Extension blocks (section 4.4) as canonical blocks.
;
; The data are `books/bp-primary`'s; the frame is this book's.  A constructor
; per block so that `books/bp-node` never spells a type code.

(defun fn-bpb-previous-node-block (number flags crc-type node)
  (declare (xargs :guard (and (fn-bpp-timep number) (fn-bpp-flag-setp flags)
                              (fn-bpp-crc-typep crc-type)
                              (fn-bpp-previous-nodep node))))
  (fn-bpb-make-block *fn-bpp-block-type-previous-node* number flags crc-type
                     (fn-bpp-previous-node-data node)))

(defun fn-bpb-bundle-age-block (number flags crc-type ms)
  (declare (xargs :guard (and (fn-bpp-timep number) (fn-bpp-flag-setp flags)
                              (fn-bpp-crc-typep crc-type)
                              (fn-bpp-bundle-agep ms))))
  (fn-bpb-make-block *fn-bpp-block-type-bundle-age* number flags crc-type
                     (fn-bpp-bundle-age-data ms)))

(defun fn-bpb-hop-count-block (number flags crc-type hop)
  (declare (xargs :guard (and (fn-bpp-timep number) (fn-bpp-flag-setp flags)
                              (fn-bpp-crc-typep crc-type)
                              (fn-bpp-hop-countp hop))))
  (fn-bpb-make-block *fn-bpp-block-type-hop-count* number flags crc-type
                     (fn-bpp-hop-count-data hop)))

(defun fn-bpb-payload-block (crc-type payload)
  (declare (xargs :guard (and (fn-bpp-crc-typep crc-type)
                              (fn-bpb-datap payload))))
  (fn-bpb-make-block *fn-bpb-block-type-payload* *fn-bpb-payload-block-number*
                     0 crc-type payload))

; The first block of the given type, or nil.  Section 4.1 allows at most one of
; each of the three, so "the first" is "the one".
(defun fn-bpb-find-block (type xs)
  (declare (xargs :guard (and (fn-bpp-timep type) (fn-bpb-block-listp xs))))
  (if (consp xs)
      (if (equal (fn-bpb-block-type (car xs)) type)
          (car xs)
        (fn-bpb-find-block type (cdr xs)))
    nil))

(defun fn-bpb-bundle-hop-count (bundle)
  (declare (xargs :guard (fn-bpb-bundlep bundle)))
  (let ((b (fn-bpb-find-block *fn-bpp-block-type-hop-count*
                              (fn-bpb-bundle-blocks bundle))))
    (if (not (fn-bpb-blockp b))
        nil
      (fn-bpp-data-hop-count (fn-bpb-block-data b)))))

(defun fn-bpb-bundle-age (bundle)
  (declare (xargs :guard (fn-bpb-bundlep bundle)))
  (let ((b (fn-bpb-find-block *fn-bpp-block-type-bundle-age*
                              (fn-bpb-bundle-blocks bundle))))
    (if (not (fn-bpb-blockp b))
        nil
      (fn-bpp-data-bundle-age (fn-bpb-block-data b)))))

(defun fn-bpb-bundle-previous-node (bundle)
  (declare (xargs :guard (fn-bpb-bundlep bundle)))
  (let ((b (fn-bpb-find-block *fn-bpp-block-type-previous-node*
                              (fn-bpb-bundle-blocks bundle))))
    (if (not (fn-bpb-blockp b))
        nil
      (fn-bpp-data-previous-node (fn-bpb-block-data b)))))

(verify-guards fn-bpb-previous-node-block)
(verify-guards fn-bpb-bundle-age-block)
(verify-guards fn-bpb-hop-count-block)
(verify-guards fn-bpb-payload-block)
(verify-guards fn-bpb-find-block)
(verify-guards fn-bpb-bundle-hop-count)
(verify-guards fn-bpb-bundle-age)
(verify-guards fn-bpb-bundle-previous-node)

; -----------------------------------------------------------------------------
; Export theory.
;
; The records are opaque (`fn-defrecord` withdrew their internals).  The
; recognizers, the codec functions and the extension-block constructors are
; withdrawn here; `books/bp-bundle-invariants` proves the keystones with them
; open, and `books/bp-node` reasons in accessor vocabulary and by the
; keystones.  The list-recursive vocabulary -- `fn-bpb-block-listp`,
; `fn-bpb-block-numbers`, `fn-bpb-encode-blocks`, `fn-bpb-front`,
; `fn-bpb-final`, `fn-bpb-find-block` -- is the induction vocabulary and stays
; enabled (proof-style section 8).

(fn-defrecord-export fn-bpb-vocabulary
  :records (fn-bpb-block fn-bpb-bundle)
  :also (fn-bpb-datap fn-bpb-payload-blockp fn-bpb-numbers-distinctp
         fn-bpb-splitp
         fn-bpb-encode-block-with-crc fn-bpb-block-crc fn-bpb-encode-block
         fn-bpb-take-uint fn-bpb-take-bytes fn-bpb-decode-block
         fn-bpb-decode-blocks fn-bpb-encode fn-bpb-decode
         fn-bpb-scan-primary fn-bpb-assemble
         fn-bpb-payload fn-bpb-bundle-id
         fn-bpb-previous-node-block fn-bpb-bundle-age-block
         fn-bpb-hop-count-block fn-bpb-payload-block
         fn-bpb-bundle-hop-count fn-bpb-bundle-age
         fn-bpb-bundle-previous-node
         fn-bpb-flag-replicate-in-fragments
         fn-bpb-flag-report-if-unprocessable
         fn-bpb-flag-delete-if-unprocessable
         fn-bpb-flag-discard-if-unprocessable))
