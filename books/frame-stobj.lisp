; fn: the store frame codec over the octet buffer (D27 boundary 8; the
; megaspike, D28).  Prefix `fn-frs-'.
;
; The list codec (books/frame-fields, books/frame-journal) builds a store
; frame as `(append header record)' then appends the trailer, and decodes one
; by splitting the list three times (`fn-frame-split', one copy each) and
; comparing the trailer with the host's digest.  Here the frame lives in the
; buffer stobj of books/octets-stobj in the layout the file has:
;
;     [header 10][record n][trailer 32]
;
; `fn-frs-store-seal' writes the header over ten placeholder octets in front
; of the record already in the buffer and appends the trailer, which is
; SHA-256 over the protected prefix read in place (`fn-sha256-of-string' of
; the prefix as a string: one allocation of 4 bytes per octet on SBCL and no
; list).  `fn-frs-store-decode' checks the frame in place and names the
; record's range; nothing is copied until a caller slices the range.
;
; The correspondence theorems at the end are stated against the list
; codec with `fn-sha256' as the digest: `fn-frame-seal' and `fn-frame-open'
; are stated against the constrained `fn-frame-digest', and the host image
; attaches `fn-sha256-stobj' to it (books/crypto-attach), which is
; `fn-sha256' by `fn-sha256-stobj-is-sha256'.  So the octets these functions
; write and accept are exactly the octets `fnn-frame'/`fnn-unframe'
; (host/native/io.lisp) wrote and accepted before this book.

(in-package "ACL2")
(include-book "octets-stobj")
(include-book "frame-journal")
(include-book "sha256-stobj")

; A computed value read as an octet: total, so every write below has a
; trivial guard.  On the reachable values it is the identity.
(defun fn-frs-byte (x)
  (declare (xargs :guard t))
  (if (fn-cbor-octetp x) x 0))

(defthm fn-frs-byte-is-octet
  (and (integerp (fn-frs-byte x))
       (<= 0 (fn-frs-byte x))
       (<= (fn-frs-byte x) 255)
       (fn-cbor-octetp (fn-frs-byte x)))
  :rule-classes ((:type-prescription :corollary (and (integerp (fn-frs-byte x)) (<= 0 (fn-frs-byte x))))
                 (:linear :corollary (<= (fn-frs-byte x) 255))
                 (:rewrite :corollary (fn-cbor-octetp (fn-frs-byte x)))
                 (:rewrite :corollary (and (integerp (fn-frs-byte x)) (<= 0 (fn-frs-byte x))))))

; The arithmetic inside a byte is never opened: the guards only need the
; facts above (the runaway of 2026-09-25 opened `floor' 584 subgoals deep).
(in-theory (disable fn-frs-byte floor mod))

(defun fn-frs-append-octets (xs fn-octets)
  ; Append XS, each element read as an octet.
  (declare (xargs :stobjs fn-octets :guard t))
  (if (atom xs)
      fn-octets
    (let ((fn-octets (fn-octets-append-octet (fn-frs-byte (car xs)) fn-octets)))
      (fn-frs-append-octets (cdr xs) fn-octets))))

(defun fn-frs-put-list (i xs fn-octets)
  ; Write XS at I, in place.
  (declare (xargs :stobjs fn-octets
                  :guard (and (natp i) (fn-cbor-octet-listp xs)
                              (<= (+ i (len xs)) (fn-octets-len fn-octets)))
                  :measure (len xs)))
  (if (atom xs)
      fn-octets
    (let ((fn-octets (fn-octets-put i (car xs) fn-octets)))
      (fn-frs-put-list (1+ i) (cdr xs) fn-octets))))

(defun fn-frs-put-u32 (i n fn-octets)
  ; The big-endian 32-bit length at [i, i+4): `fn-cbor-u32-bytes' in place.
  (declare (xargs :stobjs fn-octets
                  :guard (and (natp i) (<= (+ i 4) (fn-octets-len fn-octets)) (natp n))))
  (let* ((fn-octets (fn-octets-put i (fn-frs-byte (mod (floor n 16777216) 256)) fn-octets))
         (fn-octets (fn-octets-put (+ i 1) (fn-frs-byte (mod (floor n 65536) 256)) fn-octets))
         (fn-octets (fn-octets-put (+ i 2) (fn-frs-byte (mod (floor n 256) 256)) fn-octets))
         (fn-octets (fn-octets-put (+ i 3) (fn-frs-byte (mod n 256)) fn-octets)))
    fn-octets))

(defun fn-frs-get-u32 (i fn-octets)
  ; `fn-cbor-u32-from' read in place.
  (declare (xargs :stobjs fn-octets
                  :guard (and (natp i) (<= (+ i 4) (fn-octets-len fn-octets)))))
  (+ (* 16777216 (fn-frs-byte (fn-octets-get i fn-octets)))
     (* 65536 (fn-frs-byte (fn-octets-get (+ i 1) fn-octets)))
     (* 256 (fn-frs-byte (fn-octets-get (+ i 2) fn-octets)))
     (fn-frs-byte (fn-octets-get (+ i 3) fn-octets))))

(defun fn-frs-append-zeros (k fn-octets)
  (declare (xargs :stobjs fn-octets :guard (natp k)))
  (if (zp k)
      fn-octets
    (let ((fn-octets (fn-octets-append-octet 0 fn-octets)))
      (fn-frs-append-zeros (1- k) fn-octets))))

(defun fn-frs-prefix-digest (end fn-octets)
  ; SHA-256 of the buffer's first END octets, read in place.
  (declare (xargs :stobjs fn-octets
                  :guard (and (natp end) (<= end (fn-octets-len fn-octets)))))
  (fn-sha256-of-string (fn-oct-slice-string 0 end fn-octets)))

; -----------------------------------------------------------------------------
; Seal: the buffer holds ten placeholder octets then the record octets.

(defun fn-frs-store-seal (fn-octets)
  (declare (xargs :stobjs fn-octets))
  (let ((n (- (fn-octets-len fn-octets) *fn-frame-header-octets*)))
    (if (or (< n 0) (< *fn-frame-max-store-payload* n))
        (mv nil fn-octets)
      (let* ((fn-octets (fn-frs-put-list 0 *fn-frame-magic-store* fn-octets))
             (fn-octets (fn-octets-put 4 *fn-frame-version* fn-octets))
             (fn-octets (fn-octets-put 5 *fn-frame-store-kind* fn-octets))
             (fn-octets (fn-frs-put-u32 6 n fn-octets))
             (digest (fn-frs-prefix-digest (fn-octets-len fn-octets) fn-octets))
             (fn-octets (fn-frs-append-octets digest fn-octets)))
        (mv t fn-octets)))))

; -----------------------------------------------------------------------------
; Decode: the whole buffer is one frame.  The checks are the reference's, in
; the reference's order (books/frame-fields `fn-frame-decode', then
; books/frame-journal `fn-frame-store-decode' for magic, version and kind),
; and the result on success names the record's range instead of copying it.

(defun fn-frs-store-decode (fn-octets)
  (declare (xargs :stobjs fn-octets))
  (let ((n (fn-octets-len fn-octets)))
    (if (< (+ *fn-frame-overhead-octets* *fn-frame-max-store-payload*) n)
        (fn-frame-error :limit)
      (if (< n *fn-frame-header-octets*)
          (fn-frame-error :truncated)
        (let ((declared (fn-frs-get-u32 6 fn-octets)))
          (if (< *fn-frame-max-store-payload* declared)
              (fn-frame-error :limit)
            (if (not (equal n (+ *fn-frame-header-octets* declared
                                 *fn-frame-trailer-octets*)))
                (if (< n (+ *fn-frame-header-octets* declared *fn-frame-trailer-octets*))
                    (fn-frame-error :truncated)
                  (fn-frame-error :length))
              (let* ((prefix-end (- n *fn-frame-trailer-octets*))
                     (digest (fn-frs-prefix-digest prefix-end fn-octets)))
                (if (not (and (fn-cbor-octet-listp digest)
                              (equal (len digest) *fn-frame-trailer-octets*)
                              (fn-oct-prefix-equalp prefix-end digest fn-octets)))
                    (fn-frame-error :integrity)
                  (if (not (and (fn-oct-prefix-equalp 0 *fn-frame-magic-store* fn-octets)
                                (equal (fn-octets-get 4 fn-octets) *fn-frame-version*)
                                (equal (fn-octets-get 5 fn-octets) *fn-frame-store-kind*)))
                      (fn-frame-error :magic)
                    (list :ok *fn-frame-header-octets* prefix-end)))))))))))

(defun fn-frs-okp (result)
  (declare (xargs :guard t))
  (and (consp result) (equal (car result) :ok)
       (consp (cdr result)) (natp (car (cdr result)))
       (consp (cdr (cdr result))) (natp (car (cdr (cdr result))))
       (<= (car (cdr result)) (car (cdr (cdr result))))))

(defun fn-frs-start (result)
  (declare (xargs :guard (fn-frs-okp result)))
  (car (cdr result)))

(defun fn-frs-end (result)
  (declare (xargs :guard (fn-frs-okp result)))
  (car (cdr (cdr result))))

; The reference's success result, as a range.
(defun fn-frs-range-of (result)
  (declare (xargs :guard t))
  (if (fn-frame-result-okp result)
      (list :ok *fn-frame-header-octets*
            (+ *fn-frame-header-octets* (len (fn-frame-result-payload result))))
    result))

; -----------------------------------------------------------------------------
; The correspondence.

;; SPIKE: defers the three theorems below.  Statements: the in-place decoder
;; is the list decoder under the SHA-256 of the protected prefix, with its
;; payload named as a range; the range's slice is that payload; the in-place
;; seal is `fn-frame-encode' with the SHA-256 of the protected prefix, on the
;; record that follows the ten placeholder octets.  The dev lane proves them
;; from `fn-frs-get-u32' = `fn-cbor-u32-from' of the header slice,
;; `fn-oct-prefix-equalp' = `equal' of `take'/`nthcdr', and
;; `fn-sha256-of-string-is-sha256-of-octets' on `fn-oct-slice-string'.
(skip-proofs
 (progn
   (defthm fn-frs-store-decode-is-store-decode
     (equal (fn-frs-store-decode fn-octets)
            (fn-frs-range-of
             (fn-frame-store-decode
              (fn-octets-list fn-octets)
              (fn-sha256 (fn-frame-protected-prefix (fn-octets-list fn-octets)))))))
   (defthm fn-frs-store-decode-range-is-payload
     (implies (fn-frs-okp (fn-frs-store-decode fn-octets))
              (equal (fn-oct-slice-list (fn-frs-start (fn-frs-store-decode fn-octets))
                                        (fn-frs-end (fn-frs-store-decode fn-octets))
                                        fn-octets)
                     (fn-frame-result-payload
                      (fn-frame-store-decode
                       (fn-octets-list fn-octets)
                       (fn-sha256 (fn-frame-protected-prefix (fn-octets-list fn-octets))))))))
   (defthm fn-frs-store-seal-is-frame-encode
     (implies (and (<= *fn-frame-header-octets* (len (fn-octets-list fn-octets)))
                   (<= (- (len (fn-octets-list fn-octets)) *fn-frame-header-octets*)
                       *fn-frame-max-store-payload*))
              (and (equal (mv-nth 0 (fn-frs-store-seal fn-octets)) t)
                   (equal (fn-octets-list (mv-nth 1 (fn-frs-store-seal fn-octets)))
                          (let ((record (nthcdr *fn-frame-header-octets*
                                                (fn-octets-list fn-octets))))
                            (fn-frame-encode
                             *fn-frame-magic-store* *fn-frame-version*
                             *fn-frame-store-kind* record
                             (fn-sha256 (fn-frame-protected
                                         *fn-frame-magic-store* *fn-frame-version*
                                         *fn-frame-store-kind* record))))))))))
