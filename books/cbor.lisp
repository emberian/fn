; fn: a deliberately small deterministic CBOR primitive profile.
;
; This is an experimental codec building block, not a persistent-object
; schema.  It implements only RFC 8949 major type 0 unsigned integers and
; major type 2 definite-length byte strings.  Values are represented as
; (:uint . n) and (:bytes . octets), where n is at most 2^32-1 and a byte
; string contains at most 2^16-1 octets.  Every accepted argument uses its
; shortest RFC 8949 deterministic form.  Arrays, maps, text, tags, floats,
; negative integers, and every indefinite-length form are outside this profile.
;
; The parser consumes one item and returns (:ok value rest) or (:error reason).
; `fn-cbor-decode-exact` additionally rejects trailing octets.  Its input cap
; bounds parsing work and every decoded byte-string allocation.  These pure ACL2
; functions consume octet lists only; they never invoke a host Lisp reader.
;
; RFC 8949: sections 3, 3.1, 4.1, and 4.2.1.  The full RFC has a wider value
; domain; this profile's narrower bounds are a local experimental policy.

(in-package "ACL2")

; -----------------------------------------------------------------------------
; Domains and result records

(defconst *fn-cbor-max-uint* 4294967295)
(defconst *fn-cbor-max-bytes* 65535)
; A maximum byte string has a three-octet head.  This is also the maximum
; accepted input to the one-item decoder; stream framing belongs to a caller.
(defconst *fn-cbor-max-input* 65538)

(defun fn-cbor-octetp (x)
  (and (integerp x) (<= 0 x) (<= x 255)))

(defun fn-cbor-octet-listp (xs)
  (if (consp xs)
      (and (fn-cbor-octetp (car xs))
           (fn-cbor-octet-listp (cdr xs)))
    (null xs)))

(verify-guards fn-cbor-octetp)
(verify-guards fn-cbor-octet-listp)

(defthm fn-cbor-octet-listp-implies-true-listp
  (implies (fn-cbor-octet-listp xs)
           (true-listp xs))
  :hints (("Goal" :induct (fn-cbor-octet-listp xs))))

; This preflight examines no more than `bound + 1` cons cells.  It comes
; before octet validation, so a remote overlong list cannot make the decoder
; traverse or allocate in proportion to its unbounded claimed size.
(defun fn-cbor-at-mostp (xs bound)
  (declare (xargs :guard (natp bound)))
  (if (consp xs)
      (if (zp bound)
          nil
        (fn-cbor-at-mostp (cdr xs) (1- bound)))
    t))

(verify-guards fn-cbor-at-mostp)

; Whether XS contains at least N cons cells.  Unlike (<= N (len XS)), this
; stops after the declared item length and never scans the untouched suffix.
(defun fn-cbor-at-leastp (xs n)
  (declare (xargs :guard (natp n) :measure (nfix n)))
  (if (zp n) t
    (and (consp xs) (fn-cbor-at-leastp (cdr xs) (1- n)))))

(verify-guards fn-cbor-at-leastp)

(defthm fn-cbor-at-leastp-is-length-lower-bound
  (implies (natp n)
           (equal (fn-cbor-at-leastp xs n)
                  (<= n (len xs))))
  :hints (("Goal" :induct (fn-cbor-at-leastp xs n))))

(defun fn-cbor-valuep-bounded (x max-bytes)
  (declare (xargs :guard (natp max-bytes)))
  (or (and (consp x)
           (equal (car x) :uint)
           (natp (cdr x))
           (<= (cdr x) *fn-cbor-max-uint*))
      (and (consp x)
           (equal (car x) :bytes)
           (fn-cbor-octet-listp (cdr x))
           (<= (len (cdr x)) max-bytes)
           (<= (len (cdr x)) *fn-cbor-max-uint*))))

(defun fn-cbor-valuep (x)
  (fn-cbor-valuep-bounded x *fn-cbor-max-bytes*))

(verify-guards fn-cbor-valuep-bounded)
(verify-guards fn-cbor-valuep)

; The decoder's result is an opaque record.  Its shape, constructors and
; accessors are proved once here and then withdrawn: every book above reasons
; about a result through `fn-cbor-result-okp', `fn-cbor-result-value' and
; `fn-cbor-result-rest' and the record lemmas below, never by opening a list.

(defun fn-cbor-ag-car (x)
  (declare (xargs :guard t))
  (mbe :logic (car x) :exec (if (consp x) (car x) nil)))

(defun fn-cbor-ag-cdr (x)
  (declare (xargs :guard t))
  (mbe :logic (cdr x) :exec (if (consp x) (cdr x) nil)))

(verify-guards fn-cbor-ag-car)
(verify-guards fn-cbor-ag-cdr)

(defun fn-cbor-result-shapep (x)
  (declare (xargs :guard t))
  (and (true-listp x)
       (consp x)
       (or (equal (len x) 2) (equal (len x) 3))))

(defun fn-cbor-ok (value rest)
  (declare (xargs :guard t))
  (list :ok value rest))

(defun fn-cbor-error (reason)
  (declare (xargs :guard t))
  (list :error reason))

(defun fn-cbor-result-okp (x)
  (declare (xargs :guard t))
  (and (consp x) (equal (fn-cbor-ag-car x) :ok)))

(defun fn-cbor-result-value (x)
  (declare (xargs :guard t :verify-guards nil))
  (mbe :logic (car (cdr x))
       :exec (fn-cbor-ag-car (fn-cbor-ag-cdr x))))

(defun fn-cbor-result-rest (x)
  (declare (xargs :guard t :verify-guards nil))
  (mbe :logic (car (cdr (cdr x)))
       :exec (fn-cbor-ag-car (fn-cbor-ag-cdr (fn-cbor-ag-cdr x)))))

(verify-guards fn-cbor-result-shapep)
(verify-guards fn-cbor-ok)
(verify-guards fn-cbor-error)
(verify-guards fn-cbor-result-okp)
(verify-guards fn-cbor-result-value)
(verify-guards fn-cbor-result-rest)

; Record lemmas: shape, accessor of constructor, injectivity and the two
; constructors' distinctness.  These are the only rules about a result that
; leave this book, and every rule above reasons in this vocabulary.

(defthm fn-cbor-result-shapep-of-fn-cbor-ok
  (fn-cbor-result-shapep (fn-cbor-ok value rest)))

(defthm fn-cbor-result-shapep-of-fn-cbor-error
  (fn-cbor-result-shapep (fn-cbor-error reason)))

(defthm fn-cbor-result-okp-of-fn-cbor-ok
  (fn-cbor-result-okp (fn-cbor-ok value rest)))

(defthm fn-cbor-result-okp-of-fn-cbor-error
  (not (fn-cbor-result-okp (fn-cbor-error reason))))

(defthm fn-cbor-result-value-of-fn-cbor-ok
  (equal (fn-cbor-result-value (fn-cbor-ok value rest)) value))

(defthm fn-cbor-result-rest-of-fn-cbor-ok
  (equal (fn-cbor-result-rest (fn-cbor-ok value rest)) rest))

(defthm fn-cbor-ok-is-injective
  (equal (equal (fn-cbor-ok value rest) (fn-cbor-ok value2 rest2))
         (and (equal value value2) (equal rest rest2))))

(defthm fn-cbor-error-is-injective
  (equal (equal (fn-cbor-error reason) (fn-cbor-error reason2))
         (equal reason reason2)))

(defthm fn-cbor-ok-is-not-fn-cbor-error
  (not (equal (fn-cbor-ok value rest) (fn-cbor-error reason))))

(in-theory (disable (:d fn-cbor-result-shapep) (:d fn-cbor-ok)
                    (:d fn-cbor-error) (:d fn-cbor-result-okp)
                    (:d fn-cbor-result-value) (:d fn-cbor-result-rest)))

; -----------------------------------------------------------------------------
; Big-endian arguments and deterministic heads

(defun fn-cbor-u16-bytes (n)
  (declare (xargs :guard (and (natp n) (<= n *fn-cbor-max-uint*))))
  (list (floor n 256)
        (mod n 256)))

(defun fn-cbor-u32-bytes (n)
  (declare (xargs :guard (and (natp n) (<= n *fn-cbor-max-uint*))))
  ; Successive quotient/remainder steps are extensionally the usual big-endian
  ; base-256 decomposition.  Keeping the quotient chain explicit also gives
  ; the executable definition a direct reconstruction proof.
  (let* ((q0 (floor n 256))
         (q1 (floor q0 256))
         (q2 (floor q1 256)))
    (list q2
          (mod q1 256)
          (mod q0 256)
          (mod n 256))))

(defun fn-cbor-u16-from (xs)
  (declare (xargs :guard (and (fn-cbor-octet-listp xs)
                              (consp xs) (consp (cdr xs)))))
  (+ (* 256 (car xs))
     (car (cdr xs))))

(defun fn-cbor-u32-from (xs)
  (declare (xargs :guard (and (fn-cbor-octet-listp xs)
                              (consp xs) (consp (cdr xs))
                              (consp (cdr (cdr xs)))
                              (consp (cdr (cdr (cdr xs)))))))
  (+ (* 16777216 (car xs))
     (* 65536 (car (cdr xs)))
     (* 256 (car (cdr (cdr xs))))
     (car (cdr (cdr (cdr xs))))))

(verify-guards fn-cbor-u16-bytes)
(verify-guards fn-cbor-u32-bytes)
(verify-guards fn-cbor-u16-from)
(verify-guards fn-cbor-u32-from)

; `major` is intentionally an internal numeric argument (0 or 2 here).
(defun fn-cbor-encode-argument (major n)
  (if (not (and (natp major)
                (natp n)
                (<= n *fn-cbor-max-uint*)))
      nil
    (if (< n 24)
        (list (+ (* 32 major) n))
      (if (< n 256)
          (list (+ (* 32 major) 24) n)
        (if (< n 65536)
            (cons (+ (* 32 major) 25)
                  (fn-cbor-u16-bytes n))
          (cons (+ (* 32 major) 26)
                (fn-cbor-u32-bytes n)))))))

; The argument length selected by the deterministic encoder.  It is used by
; the decoder as a direct, executable canonicality check.
(defun fn-cbor-canonical-argumentp (additional n)
  (declare (xargs :guard (and (natp additional) (natp n))))
  (or (and (< n 24) (equal additional n))
      (and (equal additional 24) (<= 24 n) (< n 256))
      (and (equal additional 25) (<= 256 n) (< n 65536))
      (and (equal additional 26) (<= 65536 n)
           (<= n *fn-cbor-max-uint*))))

(verify-guards fn-cbor-encode-argument)
(verify-guards fn-cbor-canonical-argumentp)

; -----------------------------------------------------------------------------
; Encoder

(defun fn-cbor-encode-bounded (value max-bytes)
  (declare (xargs :guard (natp max-bytes)))
  (if (not (fn-cbor-valuep-bounded value max-bytes))
      nil
    (if (equal (car value) :uint)
        (fn-cbor-encode-argument 0 (cdr value))
      (append (fn-cbor-encode-argument 2 (len (cdr value)))
              (cdr value)))))

(defun fn-cbor-encode (value)
  (fn-cbor-encode-bounded value *fn-cbor-max-bytes*))

(verify-guards fn-cbor-encode-bounded)
(verify-guards fn-cbor-encode)

; -----------------------------------------------------------------------------
; Decoder

; Decode the CBOR argument carried by additional information.  The result is
; (:ok argument remaining-octets) or an error.  Reserved and 64-bit argument
; forms are outside the bounded profile; callers distinguish truncation before
; declaring a syntactically present form unsupported.
(defun fn-cbor-decode-argument (additional xs)
  (declare (xargs :guard (and (natp additional)
                              (fn-cbor-octet-listp xs))))
  (if (< additional 24)
      (fn-cbor-ok additional xs)
    (if (equal additional 24)
        (if (consp xs)
            (fn-cbor-ok (car xs) (cdr xs))
          (fn-cbor-error :truncated))
      (if (equal additional 25)
          (if (and (consp xs) (consp (cdr xs)))
              (fn-cbor-ok (fn-cbor-u16-from xs) (cdr (cdr xs)))
            (fn-cbor-error :truncated))
        (if (equal additional 26)
            (if (and (consp xs) (consp (cdr xs))
                     (consp (cdr (cdr xs)))
                     (consp (cdr (cdr (cdr xs)))))
                (fn-cbor-ok (fn-cbor-u32-from xs)
                            (cdr (cdr (cdr (cdr xs)))))
              (fn-cbor-error :truncated))
          (fn-cbor-error :unsupported))))))

(verify-guards fn-cbor-decode-argument)

(defun fn-cbor-decode-unsigned (additional tail)
  (declare (xargs :guard (and (natp additional)
                              (fn-cbor-octet-listp tail))))
  (let ((argument (fn-cbor-decode-argument additional tail)))
    (if (not (fn-cbor-result-okp argument))
        argument
      (if (not (fn-cbor-canonical-argumentp
                additional (fn-cbor-result-value argument)))
          (fn-cbor-error :noncanonical)
        (fn-cbor-ok (cons :uint (fn-cbor-result-value argument))
                    (fn-cbor-result-rest argument))))))

(verify-guards fn-cbor-decode-unsigned)

(defun fn-cbor-decode-bytes-bounded (additional tail max-bytes)
  (declare (xargs :guard (and (natp additional)
                              (fn-cbor-octet-listp tail)
                              (natp max-bytes))))
  (let ((argument (fn-cbor-decode-argument additional tail)))
    (if (not (fn-cbor-result-okp argument))
        argument
      (let ((length (fn-cbor-result-value argument))
            (content (fn-cbor-result-rest argument)))
        (if (not (fn-cbor-canonical-argumentp additional length))
            (fn-cbor-error :noncanonical)
          ; This check precedes TAKE, so a declared length outside the caller's
          ; profile cannot drive allocation.  The legacy entry point below
          ; supplies *fn-cbor-max-bytes* and therefore keeps its exact domain.
          (if (< max-bytes length)
              (fn-cbor-error :limit)
            (if (fn-cbor-at-leastp content length)
                (fn-cbor-ok (cons :bytes (take length content))
                            (nthcdr length content))
              (fn-cbor-error :truncated))))))))

(verify-guards fn-cbor-decode-bytes-bounded)

(defun fn-cbor-decode-bytes (additional tail)
  (declare (xargs :guard (and (natp additional)
                              (fn-cbor-octet-listp tail))))
  (fn-cbor-decode-bytes-bounded additional tail *fn-cbor-max-bytes*))

(verify-guards fn-cbor-decode-bytes)

; A one-item streaming decoder.  Its explicit input maximum gives a fixed
; bound on list traversal, decoded byte allocation, and returned remainder.
(defun fn-cbor-decode-prechecked (octets item-budget)
  (declare (xargs :guard (and (fn-cbor-octet-listp octets)
                              (natp item-budget))))
  (if (not (consp octets))
      (fn-cbor-error :truncated)
    (let ((head (car octets)))
      (if (< head 32)
          (fn-cbor-decode-unsigned head (cdr octets))
        (if (and (< 63 head) (< head 96))
            (fn-cbor-decode-bytes-bounded (- head 64) (cdr octets)
                                          item-budget)
          (fn-cbor-error :unsupported))))))

(verify-guards fn-cbor-decode-prechecked)

(defun fn-cbor-decode-bounded (octets input-budget item-budget)
  (declare (xargs :guard (and (natp input-budget) (natp item-budget))))
  (if (not (fn-cbor-at-mostp octets input-budget))
      (fn-cbor-error :limit)
    (if (not (fn-cbor-octet-listp octets))
        (fn-cbor-error :malformed)
      (fn-cbor-decode-prechecked octets item-budget))))

(verify-guards fn-cbor-decode-bounded)

; Compatibility entry point.  Every pre-existing caller retains both the
; 65,538-octet whole-input cap and the 65,535-octet byte-string cap.
(defun fn-cbor-decode (octets)
  (fn-cbor-decode-bounded octets *fn-cbor-max-input* *fn-cbor-max-bytes*))

(verify-guards fn-cbor-decode)

; Object/frame fields normally require exactly one item, so do not let a caller
; accidentally disregard a concatenated second CBOR item.
(defun fn-cbor-decode-exact (octets)
  (let ((result (fn-cbor-decode octets)))
    (if (not (fn-cbor-result-okp result))
        result
      (if (null (fn-cbor-result-rest result))
          result
        (fn-cbor-error :trailing)))))
(verify-guards fn-cbor-decode-exact)

; -----------------------------------------------------------------------------
; Certified primitive properties.  The initial theorems cover the one-octet
; deterministic range and streaming remainder exactly; larger numeric heads
; and payload round trips are executable golden-vector coverage in this slice.

(defthm fn-cbor-zero-stream-decodes-exactly
  (implies (and (fn-cbor-octet-listp rest)
                (fn-cbor-at-mostp rest 65537))
           (equal (fn-cbor-decode (cons 0 rest))
                  (fn-cbor-ok (cons :uint 0) rest))))

(defthm fn-cbor-empty-bytes-stream-decodes-exactly
  (implies (and (fn-cbor-octet-listp rest)
                (fn-cbor-at-mostp rest 65537))
           (equal (fn-cbor-decode (cons 64 rest))
                  (fn-cbor-ok (cons :bytes nil) rest))))

(defthm fn-cbor-small-unsigned-round-trip
  (implies (and (natp n) (< n 24))
           (equal (fn-cbor-decode-exact
                   (fn-cbor-encode (cons :uint n)))
                  (fn-cbor-ok (cons :uint n) nil))))


; -----------------------------------------------------------------------------
; The wide uint (D27, design 2026-09-25-bounds §2.3, packet P6).
;
; RFC 8949 §3 gives a uint an eight-octet argument (additional information
; 27).  The profile above stops at the four-octet argument, and every existing
; caller keeps that domain: nothing above changes.  A codec whose integer
; fields are 64-bit (the transaction record's sequence, transaction ID,
; generation, charge and stamp) reads them through the wide entry below.  For
; every value at most 2^32 - 1 the wide encoder writes the narrow encoder's
; bytes, and the wide decoder returns the narrow decoder's result whenever the
; narrow one accepts (cbor-invariants: `fn-cbor-encode-uint-wide-is-narrow',
; `fn-cbor-decode-prechecked-wide-extends-narrow'), so no existing encoding
; moves.  An eight-octet argument is canonical only above 2^32 - 1 (RFC 8949
; §4.2.1, shortest form).

(defconst *fn-cbor-max-uint64* 18446744073709551615)

(local (include-book "ihs/quotient-remainder-lemmas" :dir :system))

(local (defthm fn-cbor-u64-floor-bound
         (implies (and (natp n) (<= n *fn-cbor-max-uint64*))
                  (<= (floor n 4294967296) *fn-cbor-max-uint*))
         :rule-classes :linear
         :hints (("Goal" :use ((:instance floor-bounded-by-/
                                          (x n) (y 4294967296)))
                  :in-theory (disable floor-bounded-by-/)))))

(local (defthm fn-cbor-u64-mod-bound
         (implies (natp n)
                  (< (mod n 4294967296) 4294967296))
         :rule-classes :linear
         :hints (("Goal" :use ((:instance mod-bounded-by-modulus
                                          (x n) (y 4294967296)))
                  :in-theory (disable mod-bounded-by-modulus)))))

(local (defthm fn-cbor-u64-halves-natural
         (implies (natp n)
                  (and (natp (floor n 4294967296))
                       (natp (mod n 4294967296))))
         ))

(defun fn-cbor-u64-bytes (n)
  (declare (xargs :guard (and (natp n) (<= n *fn-cbor-max-uint64*))
                  :verify-guards nil))
  (append (fn-cbor-u32-bytes (floor n 4294967296))
          (fn-cbor-u32-bytes (mod n 4294967296))))

(defun fn-cbor-u64-from (xs)
  (declare (xargs :guard (and (fn-cbor-octet-listp xs)
                              (fn-cbor-at-leastp xs 8))
                  :verify-guards nil))
  (+ (* 4294967296 (fn-cbor-u32-from xs))
     (fn-cbor-u32-from (cdr (cdr (cdr (cdr xs)))))))

(local (defthm fn-cbor-at-leastp-8-shape
         (implies (fn-cbor-at-leastp xs 8)
                  (and (consp xs) (consp (cdr xs)) (consp (cddr xs))
                       (consp (cdddr xs)) (consp (cddddr xs))
                       (consp (cdr (cddddr xs)))
                       (consp (cddr (cddddr xs)))
                       (consp (cdddr (cddddr xs)))))
         :hints (("Goal" :expand ((fn-cbor-at-leastp xs 8)
                                  (fn-cbor-at-leastp (cdr xs) 7)
                                  (fn-cbor-at-leastp (cddr xs) 6)
                                  (fn-cbor-at-leastp (cdddr xs) 5)
                                  (fn-cbor-at-leastp (cddddr xs) 4)
                                  (fn-cbor-at-leastp (cdr (cddddr xs)) 3)
                                  (fn-cbor-at-leastp (cddr (cddddr xs)) 2)
                                  (fn-cbor-at-leastp (cdddr (cddddr xs)) 1))))))

(verify-guards fn-cbor-u64-bytes :hints (("Goal" :in-theory (disable floor mod))))
(verify-guards fn-cbor-u64-from)

(defun fn-cbor-encode-uint-wide (n)
  (declare (xargs :guard t))
  (if (and (natp n) (<= n *fn-cbor-max-uint*))
      (fn-cbor-encode-argument 0 n)
    (if (and (natp n) (<= n *fn-cbor-max-uint64*))
        (cons 27 (fn-cbor-u64-bytes n))
      nil)))

(verify-guards fn-cbor-encode-uint-wide)

(defun fn-cbor-decode-unsigned-wide (additional tail)
  (declare (xargs :guard (and (natp additional)
                              (fn-cbor-octet-listp tail))))
  (if (equal additional 27)
      (if (fn-cbor-at-leastp tail 8)
          (let ((n (fn-cbor-u64-from tail)))
            (if (<= n *fn-cbor-max-uint*)
                (fn-cbor-error :noncanonical)
              (fn-cbor-ok (cons :uint n) (nthcdr 8 tail))))
        (fn-cbor-error :truncated))
    (fn-cbor-decode-unsigned additional tail)))

(verify-guards fn-cbor-decode-unsigned-wide)

; The one-item decoder with the wide uint.  Byte strings are the narrow
; decoder's, bounded by the caller's item budget.
(defun fn-cbor-decode-prechecked-wide (octets item-budget)
  (declare (xargs :guard (and (fn-cbor-octet-listp octets)
                              (natp item-budget))))
  (if (and (consp octets) (< (car octets) 32))
      (fn-cbor-decode-unsigned-wide (car octets) (cdr octets))
    (fn-cbor-decode-prechecked octets item-budget)))

(verify-guards fn-cbor-decode-prechecked-wide)

; -----------------------------------------------------------------------------
; Export theory.
;
; What leaves this book enabled: the record lemmas above, the three theorems
; below, and the list-recursive vocabulary the proofs above induct on
; (`fn-cbor-octetp', `fn-cbor-octet-listp', `fn-cbor-at-mostp') together with
; the total `fn-cbor-ag-' helpers.  The codec itself is proof vocabulary: a
; book that must open it enables `fn-cbor-codec-vocabulary' locally and says
; why.  `fn-cbor-record-vocabulary' exists so that a book which genuinely has
; to open a result names exactly that.

(deftheory fn-cbor-record-vocabulary
  '((:d fn-cbor-result-shapep) (:d fn-cbor-ok) (:d fn-cbor-error)
    (:d fn-cbor-result-okp) (:d fn-cbor-result-value)
    (:d fn-cbor-result-rest)))

(deftheory fn-cbor-codec-vocabulary
  '((:d fn-cbor-valuep-bounded) (:d fn-cbor-valuep)
    (:d fn-cbor-canonical-argumentp)
    (:d fn-cbor-encode-argument) (:d fn-cbor-encode-bounded) (:d fn-cbor-encode)
    (:d fn-cbor-decode-argument) (:d fn-cbor-decode-unsigned)
    (:d fn-cbor-decode-bytes-bounded) (:d fn-cbor-decode-bytes)
    (:d fn-cbor-decode-prechecked) (:d fn-cbor-decode-bounded)
    (:d fn-cbor-decode) (:d fn-cbor-decode-exact)
    (:d fn-cbor-u16-bytes) (:d fn-cbor-u32-bytes)
    (:d fn-cbor-u16-from) (:d fn-cbor-u32-from)
    (:d fn-cbor-u64-bytes) (:d fn-cbor-u64-from)
    (:d fn-cbor-encode-uint-wide) (:d fn-cbor-decode-unsigned-wide)
    (:d fn-cbor-decode-prechecked-wide)))

(in-theory (disable (:d fn-cbor-valuep-bounded) (:d fn-cbor-valuep)
             (:d fn-cbor-canonical-argumentp) (:d
             fn-cbor-encode-argument) (:d fn-cbor-encode-bounded)
             (:d fn-cbor-encode) (:d
             fn-cbor-decode-argument) (:d fn-cbor-decode-unsigned) (:d
             fn-cbor-decode-bytes-bounded) (:d fn-cbor-decode-bytes) (:d
             fn-cbor-decode-prechecked) (:d fn-cbor-decode-bounded)
             (:d fn-cbor-decode) (:d
             fn-cbor-decode-exact) (:d fn-cbor-u16-bytes) (:d
             fn-cbor-u32-bytes) (:d fn-cbor-u16-from) (:d
             fn-cbor-u32-from) (:d fn-cbor-u64-bytes) (:d fn-cbor-u64-from)
             (:d fn-cbor-encode-uint-wide) (:d fn-cbor-decode-unsigned-wide)
             (:d fn-cbor-decode-prechecked-wide)))
