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

; This preflight examines no more than `bound + 1` cons cells.  It comes
; before octet validation, so a remote overlong list cannot make the decoder
; traverse or allocate in proportion to its unbounded claimed size.
(defun fn-cbor-at-mostp (xs bound)
  (if (consp xs)
      (if (zp bound)
          nil
        (fn-cbor-at-mostp (cdr xs) (1- bound)))
    t))

(defun fn-cbor-valuep (x)
  (or (and (consp x)
           (equal (car x) :uint)
           (natp (cdr x))
           (<= (cdr x) *fn-cbor-max-uint*))
      (and (consp x)
           (equal (car x) :bytes)
           (fn-cbor-octet-listp (cdr x))
           (<= (len (cdr x)) *fn-cbor-max-bytes*))))

(defun fn-cbor-ok (value rest)
  (list :ok value rest))

(defun fn-cbor-error (reason)
  (list :error reason))

(defun fn-cbor-result-okp (x)
  (and (consp x) (equal (car x) :ok)))

(defun fn-cbor-result-value (x)
  (car (cdr x)))

(defun fn-cbor-result-rest (x)
  (car (cdr (cdr x))))

; -----------------------------------------------------------------------------
; Big-endian arguments and deterministic heads

(defun fn-cbor-u16-bytes (n)
  (list (floor n 256)
        (mod n 256)))

(defun fn-cbor-u32-bytes (n)
  (list (floor n 16777216)
        (mod (floor n 65536) 256)
        (mod (floor n 256) 256)
        (mod n 256)))

(defun fn-cbor-u16-from (xs)
  (+ (* 256 (car xs))
     (car (cdr xs))))

(defun fn-cbor-u32-from (xs)
  (+ (* 16777216 (car xs))
     (* 65536 (car (cdr xs)))
     (* 256 (car (cdr (cdr xs))))
     (car (cdr (cdr (cdr xs))))))

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
  (or (and (< n 24) (equal additional n))
      (and (equal additional 24) (<= 24 n) (< n 256))
      (and (equal additional 25) (<= 256 n) (< n 65536))
      (and (equal additional 26) (<= 65536 n)
           (<= n *fn-cbor-max-uint*))))

; -----------------------------------------------------------------------------
; Encoder

(defun fn-cbor-encode (value)
  (if (not (fn-cbor-valuep value))
      nil
    (if (equal (car value) :uint)
        (fn-cbor-encode-argument 0 (cdr value))
      (append (fn-cbor-encode-argument 2 (len (cdr value)))
              (cdr value)))))

; -----------------------------------------------------------------------------
; Decoder

; Decode the CBOR argument carried by additional information.  The result is
; (:ok argument remaining-octets) or an error.  Reserved and 64-bit argument
; forms are outside the bounded profile; callers distinguish truncation before
; declaring a syntactically present form unsupported.
(defun fn-cbor-decode-argument (additional xs)
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

(defun fn-cbor-decode-unsigned (additional tail)
  (let ((argument (fn-cbor-decode-argument additional tail)))
    (if (not (fn-cbor-result-okp argument))
        argument
      (if (not (fn-cbor-canonical-argumentp
                additional (fn-cbor-result-value argument)))
          (fn-cbor-error :noncanonical)
        (fn-cbor-ok (cons :uint (fn-cbor-result-value argument))
                    (fn-cbor-result-rest argument))))))

(defun fn-cbor-decode-bytes (additional tail)
  (let ((argument (fn-cbor-decode-argument additional tail)))
    (if (not (fn-cbor-result-okp argument))
        argument
      (let ((length (fn-cbor-result-value argument))
            (content (fn-cbor-result-rest argument)))
        (if (not (fn-cbor-canonical-argumentp additional length))
            (fn-cbor-error :noncanonical)
          (if (< *fn-cbor-max-bytes* length)
              (fn-cbor-error :limit)
            (if (<= length (len content))
                (fn-cbor-ok (cons :bytes (take length content))
                            (nthcdr length content))
              (fn-cbor-error :truncated))))))))

; A one-item streaming decoder.  Its explicit input maximum gives a fixed
; bound on list traversal, decoded byte allocation, and returned remainder.
(defun fn-cbor-decode (octets)
  (if (not (fn-cbor-at-mostp octets *fn-cbor-max-input*))
      (fn-cbor-error :limit)
    (if (not (fn-cbor-octet-listp octets))
        (fn-cbor-error :malformed)
      (if (not (consp octets))
          (fn-cbor-error :truncated)
        (let ((head (car octets)))
          (if (< head 32)
              (fn-cbor-decode-unsigned head (cdr octets))
            (if (and (< 63 head) (< head 96))
                (fn-cbor-decode-bytes (- head 64) (cdr octets))
              (fn-cbor-error :unsupported))))))))

; Object/frame fields normally require exactly one item, so do not let a caller
; accidentally disregard a concatenated second CBOR item.
(defun fn-cbor-decode-exact (octets)
  (let ((result (fn-cbor-decode octets)))
    (if (not (fn-cbor-result-okp result))
        result
      (if (null (fn-cbor-result-rest result))
          result
        (fn-cbor-error :trailing)))))

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
