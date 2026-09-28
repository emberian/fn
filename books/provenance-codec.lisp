; fn: the provenance codec --- canonical octets for a typed provenance value,
; and the string that rides in the durable record's existing evidence field.
;
; Beside the record codec, and out of its parts.  `books/records.lisp' reads a
; CBOR stream with `fn-record-read-uint' and `fn-record-read-bytes' and
; `books/records-invariants.lisp' proves those two are the inverses of
; `fn-cbor-encode' on a stream (`fn-record-read-uint-encoded',
; `fn-record-read-bytes-encoded'); this book spends those lemmas rather than
; a second CBOR parser.
;
; The layout is FIXED, eight items, one shape for all four structured kinds,
; so there is one encoder, one decoder and one round trip rather than four:
;
;   (:uint 0)        the sentinel.  `fn-cbor-encode' of it is the single
;                    octet 0, and a legacy evidence string whose first octet
;                    is not 0 therefore cannot collide with a structured
;                    encoding.  That is the whole disambiguation, and
;                    `fn-prov-plain-stringp' below is its exact statement.
;   (:uint kind)     1 :post, 2 :peer-transit, 3 :bp-receive, 4 :local
;   (:bytes a)       principal | peer      | node-id | reason
;   (:bytes b)       ()        | Path identity of a :mismatch diagnostic
;                                          | bundle  | ()
;   (:bytes c)       ()        | ()        | label   | ()
;   (:uint m)        generation| generation| 0       | 0
;   (:uint n)        0         | 1 IHAVE, 2 TAKETHIS | 0 | 0
;   (:uint o)        0         | 1 :match, 2 :mismatch | 0 | 0
;
; The LEGACY kind is not encoded at all: its octets are the string's own
; octets, so an evidence value that was a string before this lane occupies
; exactly the bytes it occupied before, and `fn-prov-wire' of it is that
; string.  Nothing in an existing store or journal changes.
;
; The WIRE form is those octets in lowercase hexadecimal behind the eight
; octets "fnprov1:", and it is printable ASCII on purpose: the host boundary
; guard `fn-store-text-octetsp' (host/store-host.lisp) admits an evidence
; octet only in 33 to 126, and the record grammar bounds the field at
; `*fn-record-max-metadata*' = 256 octets.  So the octet codec above is the
; canonical form and the hexadecimal is the transport, exactly as
; `books/identity.lisp' does for a content identity --- and it is that
; book's `fn-id-hex-octets'/`fn-id-unhex' and their two round trips, not a
; second hexadecimal.  `*fn-prov-max-field*' is 32 because 8 + 2*(the
; longest encoding those fields allow) must stay under 256.
;
; What the tree calls this codec for: `fn-prov-wire' is the projection a
; durable writer takes of a typed provenance to put it in the record's
; `release-evidence' field (a bounded string, `fn-record-metadata-bytes-p'),
; and `fn-prov-of-wire' is what replay, `fn inspect' and the feed's loop
; check read it back with.

(in-package "ACL2")
(include-book "provenance")
(include-book "records-canonicality")
(include-book "identity-invariants")

(local (in-theory (enable fn-cbor-invariants-vocabulary)))

; -----------------------------------------------------------------------------
; Field domains

(defconst *fn-prov-max-field* 32)

; "fnprov1:", the wire prefix.  A legacy evidence string that begins with
; these eight octets is the one value this codec cannot carry and read back;
; `fn-prov-plain-stringp' says so and the test book exhibits one.
(defconst *fn-prov-wire-prefix* '(102 110 112 114 111 118 49 58))

(defun fn-prov-textp (text)
  (declare (xargs :guard t))
  (and (fn-record-octet-stringp text)
       (<= (len (fn-record-string-octets text)) *fn-prov-max-field*)))

; Total prefix test and total drop: no `take'/`nthcdr' guard obligation on a
; value that may be anything (the decoder's input is untrusted).
(defun fn-prov-prefixp (prefix octets)
  (declare (xargs :guard t))
  (if (consp prefix)
      (and (consp octets)
           (equal (car prefix) (car octets))
           (fn-prov-prefixp (cdr prefix) (cdr octets)))
    t))

(defun fn-prov-drop (n xs)
  (declare (xargs :guard (natp n) :measure (nfix n)))
  (if (zp n) xs (fn-prov-drop (- (nfix n) 1) (fn-ag-cdr xs))))

(defun fn-prov-wire-prefixedp (octets)
  (declare (xargs :guard t))
  (fn-prov-prefixp *fn-prov-wire-prefix* octets))

; The one disambiguation.  A string that begins "fnprov1:" is still a
; `fn-provp' --- the recognizer accepts every string, which is what makes the
; widening free --- but it is not a string this codec can write and read
; back, because a wire form begins with those octets.  No writer in the tree
; produces one; `tests/acl2/provenance-tests.lisp' exhibits the excluded
; value rather than asserting that none exists.
(defun fn-prov-plain-stringp (text)
  (declare (xargs :guard t))
  (and (stringp text)
       (not (fn-prov-wire-prefixedp (fn-record-string-octets text)))))

(defun fn-prov-diagnostic-identity (d)
  (declare (xargs :guard t))
  (if (and (consp d) (equal (fn-ag-car d) :mismatch)
           (fn-cbor-octet-listp (fn-ag-car (fn-ag-cdr d))))
      (fn-ag-car (fn-ag-cdr d))
    nil))

(defun fn-prov-diagnostic-code (d)
  (declare (xargs :guard t))
  (if (equal d (list :match)) 1 2))

(defun fn-prov-transit-kind-code (kind)
  (declare (xargs :guard t))
  (if (equal kind :ihave) 1 2))

(defun fn-prov-kind-code (p)
  (declare (xargs :guard t))
  (let ((k (fn-prov-kind p)))
    (cond ((equal k :post) 1)
          ((equal k :peer-transit) 2)
          ((equal k :bp-receive) 3)
          ((equal k :local) 4)
          (t 0))))

; -----------------------------------------------------------------------------
; The eight fields of a structured provenance

(defun fn-prov-field-a (p)
  (declare (xargs :guard t))
  (cond ((fn-prov-postp p) (fn-record-string-octets (fn-prov-post-principal p)))
        ((fn-prov-transitp p) (fn-record-string-octets (fn-prov-transit-peer p)))
        ((fn-prov-bpp p) (fn-record-string-octets (fn-prov-bp-node-id p)))
        ((fn-prov-localp p) (fn-record-string-octets (fn-prov-local-reason p)))
        (t nil)))

(defun fn-prov-field-b (p)
  (declare (xargs :guard t))
  (cond ((fn-prov-transitp p)
         (fn-prov-diagnostic-identity (fn-prov-transit-diagnostic p)))
        ((fn-prov-bpp p) (fn-record-string-octets (fn-prov-bp-bundle p)))
        (t nil)))

(defun fn-prov-field-c (p)
  (declare (xargs :guard t))
  (if (fn-prov-bpp p) (fn-record-string-octets (fn-prov-bp-label p)) nil))

(defun fn-prov-field-m (p)
  (declare (xargs :guard t))
  (cond ((fn-prov-postp p) (nfix (fn-prov-post-generation p)))
        ((fn-prov-transitp p) (nfix (fn-prov-transit-generation p)))
        (t 0)))

(defun fn-prov-field-n (p)
  (declare (xargs :guard t))
  (if (fn-prov-transitp p)
      (fn-prov-transit-kind-code (fn-prov-transit-kind p))
    0))

(defun fn-prov-field-o (p)
  (declare (xargs :guard t))
  (if (fn-prov-transitp p)
      (fn-prov-diagnostic-code (fn-prov-transit-diagnostic p))
    0))

; What the codec can write and read back.  Every field is a bounded octet
; string and every natural is in the 32-bit CBOR profile the record codec
; uses; the legacy kind is every string that is not a structured encoding.
(defun fn-prov-encodablep (p)
  (declare (xargs :guard t))
  (and (fn-provp p)
       (cond
        ((stringp p) (fn-prov-plain-stringp p))
        ((fn-prov-postp p)
         (and (fn-prov-textp (fn-prov-post-principal p))
              (fn-record-uint32p (fn-prov-post-generation p))))
        ((fn-prov-transitp p)
         (and (fn-prov-textp (fn-prov-transit-peer p))
              (<= (len (fn-prov-diagnostic-identity
                        (fn-prov-transit-diagnostic p)))
                  *fn-prov-max-field*)
              (fn-record-uint32p (fn-prov-transit-generation p))))
        ((fn-prov-bpp p)
         (and (fn-prov-textp (fn-prov-bp-node-id p))
              (fn-prov-textp (fn-prov-bp-bundle p))
              (fn-prov-textp (fn-prov-bp-label p))))
        ((fn-prov-localp p) (fn-prov-textp (fn-prov-local-reason p)))
        (t nil))))

; -----------------------------------------------------------------------------
; Encoder

(defun fn-prov-structured-octets (p)
  (declare (xargs :guard t))
  (append
   (fn-cbor-encode (cons :uint 0))
   (append
    (fn-cbor-encode (cons :uint (fn-prov-kind-code p)))
    (append
     (fn-cbor-encode (cons :bytes (fn-prov-field-a p)))
     (append
      (fn-cbor-encode (cons :bytes (fn-prov-field-b p)))
      (append
       (fn-cbor-encode (cons :bytes (fn-prov-field-c p)))
       (append
        (fn-cbor-encode (cons :uint (fn-prov-field-m p)))
        (append
         (fn-cbor-encode (cons :uint (fn-prov-field-n p)))
         (fn-cbor-encode (cons :uint (fn-prov-field-o p)))))))))))

(defun fn-prov-octets (p)
  (declare (xargs :guard t))
  (if (stringp p)
      (fn-record-string-octets p)
    (fn-prov-structured-octets p)))

(defun fn-prov-wire-octets (p)
  (declare (xargs :guard t))
  (append *fn-prov-wire-prefix*
          (fn-id-hex-octets (fn-prov-structured-octets p))))

(defun fn-prov-wire (p)
  (declare (xargs :guard t))
  (if (stringp p) p (fn-record-octets-string (fn-prov-wire-octets p))))

; -----------------------------------------------------------------------------
; Decoder
;
; The rebuild is total: an out-of-domain code, an out-of-domain transit kind
; or an out-of-domain diagnostic code yields NIL, which is not a `fn-provp',
; so a caller that checks `fn-provp' of the answer has checked the parse.

(defun fn-prov-rebuild (code a b c m n o)
  (declare (xargs :guard t))
  (cond ((equal code 1)
         (fn-prov-make-post (fn-record-octets-string a) (nfix m)))
        ((equal code 2)
         (fn-prov-make-transit
          (fn-record-octets-string a)
          (if (equal n 1) :ihave (if (equal n 2) :takethis nil))
          (if (equal o 1)
              (fn-prov-diagnostic-match)
            (if (equal o 2) (fn-prov-diagnostic-mismatch b) nil))
          (nfix m)))
        ((equal code 3)
         (fn-prov-make-bp (fn-record-octets-string a)
                          (fn-record-octets-string b)
                          (fn-record-octets-string c)))
        ((equal code 4)
         (fn-prov-make-local (fn-record-octets-string a)))
        (t nil)))

(defun fn-prov-parse-octets (octets)
  (declare (xargs :guard (fn-cbor-octet-listp octets) :verify-guards nil))
  (let ((r0 (fn-record-read-uint octets)))
    (if (or (not (fn-record-parse-okp r0))
            (not (equal (fn-record-parse-value r0) 0)))
        nil
      (let ((r1 (fn-record-read-uint (fn-record-parse-rest r0))))
        (if (not (fn-record-parse-okp r1))
            nil
          (let ((ra (fn-record-read-bytes (fn-record-parse-rest r1))))
            (if (not (fn-record-parse-okp ra))
                nil
              (let ((rb (fn-record-read-bytes (fn-record-parse-rest ra))))
                (if (not (fn-record-parse-okp rb))
                    nil
                  (let ((rc (fn-record-read-bytes (fn-record-parse-rest rb))))
                    (if (not (fn-record-parse-okp rc))
                        nil
                      (let ((rm (fn-record-read-uint (fn-record-parse-rest rc))))
                        (if (not (fn-record-parse-okp rm))
                            nil
                          (let ((rn (fn-record-read-uint
                                     (fn-record-parse-rest rm))))
                            (if (not (fn-record-parse-okp rn))
                                nil
                              (let ((ro (fn-record-read-uint
                                         (fn-record-parse-rest rn))))
                                (if (or (not (fn-record-parse-okp ro))
                                        (not (null (fn-record-parse-rest ro))))
                                    nil
                                  (fn-prov-rebuild
                                   (fn-record-parse-value r1)
                                   (fn-record-parse-value ra)
                                   (fn-record-parse-value rb)
                                   (fn-record-parse-value rc)
                                   (fn-record-parse-value rm)
                                   (fn-record-parse-value rn)
                                   (fn-record-parse-value ro)))))))))))))))))))

; The same hint shape `books/records.lisp' uses for `fn-record-decode-tail':
; the two success-domain lemmas carry the octet-ness of each remainder and
; every parser accessor stays closed.
(verify-guards fn-prov-parse-octets
  :hints (("Goal"
           :in-theory (e/d (fn-record-read-uint-success-domain
                            fn-record-read-bytes-success-domain)
                           (fn-record-read-uint fn-record-read-bytes
                            fn-record-octets-string fn-record-parse-okp
                            fn-record-parse-value fn-record-parse-rest
                            fn-record-uint32p fn-cbor-octet-listp
                            true-listp)))))

; The decoder.  Anything the structured parse does not accept is the LEGACY
; kind: the octets read as a string, verbatim.  That is total, and it is why
; no store written before this lane changes meaning.
(defun fn-prov-of-octets (octets)
  (declare (xargs :guard (fn-cbor-octet-listp octets)))
  (let ((parsed (fn-prov-parse-octets octets)))
    (if (fn-provp parsed) parsed (fn-record-octets-string octets))))

; Every ACL2 character code is an octet, so the octets of any string are an
; octet list; `fn-record-octet-stringp' (books/records.lisp) is the same
; conjunct stated for a string, and this is it stated for every value.
(local
 (defthm fn-prov-string-octets-aux-are-octets
   (fn-cbor-octet-listp (fn-record-string-octets-aux chars))
   :hints (("Goal" :in-theory (enable fn-record-string-octets-aux
                                      fn-cbor-octet-listp fn-cbor-octetp)))))

(defthm fn-prov-string-octets-are-octets
  (fn-cbor-octet-listp (fn-record-string-octets text))
  :hints (("Goal" :in-theory (enable fn-record-string-octets))))

(defthm fn-prov-a-string-is-an-octet-string
  (implies (stringp text) (fn-record-octet-stringp text))
  :hints (("Goal" :in-theory (enable fn-record-octet-stringp))))

(defun fn-prov-of-wire (text)
  (declare (xargs :guard t))
  (let ((octets (fn-record-string-octets text)))
    (if (not (fn-prov-wire-prefixedp octets))
        (if (stringp text) text "")
      (let* ((body (fn-prov-drop 8 octets))
             (raw (if (fn-id-hex-listp body) (fn-id-unhex body) nil))
             (decoded (if (fn-cbor-octet-listp raw)
                          (fn-prov-parse-octets raw)
                        nil)))
        (if (fn-provp decoded)
            decoded
          (if (stringp text) text ""))))))

; The sentinel does its job: a CBOR uint whose value is 0 is the single
; octet 0 (the canonical argument form), so a stream whose first octet is
; not 0 cannot start with the sentinel and the structured parse refuses it
; at its first step.  That is the whole legacy/structured disambiguation.

(local
 (defthm fn-prov-encode-zero-uint
   (equal (fn-cbor-encode (cons :uint 0)) (list 0))))

(local
 (defthm fn-prov-zero-value-means-zero-head
   (implies (and (fn-record-parse-okp (fn-record-read-uint octets))
                 (equal (fn-record-parse-value (fn-record-read-uint octets))
                        0))
            (equal (car octets) 0))
   :rule-classes nil
   :hints (("Goal"
            :use ((:instance fn-record-read-uint-reencode-prefix))
            :in-theory (disable fn-record-read-uint fn-record-parse-okp
                                fn-record-parse-value fn-record-parse-rest
                                fn-cbor-encode)))))

(local
 (defthm fn-prov-parse-of-a-nonzero-head
   (implies (not (equal (car octets) 0))
            (equal (fn-prov-parse-octets octets) nil))
   :hints (("Goal"
            :use ((:instance fn-prov-zero-value-means-zero-head))
            :in-theory (e/d (fn-prov-parse-octets)
                            (fn-record-read-uint fn-record-read-bytes
                             fn-record-parse-okp fn-record-parse-value
                             fn-record-parse-rest fn-cbor-encode))))))

; -----------------------------------------------------------------------------
; The round trip, in three steps: the encoding is inside the CBOR profile's
; bounds (so the two stream lemmas of books/records-invariants apply), the
; parse of an encoding is the rebuild of the fields, and the rebuild of a
; record's own fields is that record.

; Unconditional shapes of one encoded item.  A uint is at most five octets
; and a byte string at most three more than its content; out of profile the
; encoder answers NIL, which is length 0, so neither needs a hypothesis.
(local
 (defthm fn-prov-uint-item-length
   (<= (len (fn-cbor-encode (cons :uint n))) 5)
   :rule-classes :linear
   :hints (("Goal" :in-theory (enable fn-cbor-encode fn-cbor-encode-bounded
                                      fn-cbor-encode-argument
                                      fn-cbor-valuep fn-cbor-valuep-bounded
                                      fn-cbor-u16-bytes fn-cbor-u32-bytes)))))

(local
 (defthm fn-prov-bytes-item-length
   (<= (len (fn-cbor-encode (cons :bytes xs))) (+ 3 (len xs)))
   :rule-classes :linear
   :hints (("Goal" :in-theory (enable fn-cbor-encode fn-cbor-encode-bounded
                                      fn-cbor-encode-argument
                                      fn-cbor-valuep fn-cbor-valuep-bounded
                                      fn-cbor-u16-bytes fn-cbor-u32-bytes)))))

(local
 (defthm fn-prov-len-of-append
   (equal (len (append a b)) (+ (len a) (len b)))))

; The field domains under `fn-prov-encodablep'.
(local
 (defthm fn-prov-fields-are-octets
   (and (fn-cbor-octet-listp (fn-prov-field-a p))
        (fn-cbor-octet-listp (fn-prov-field-b p))
        (fn-cbor-octet-listp (fn-prov-field-c p)))
   :hints (("Goal" :in-theory (enable fn-prov-field-a fn-prov-field-b
                                      fn-prov-field-c
                                      fn-prov-diagnostic-identity)))))

(local
 (defthm fn-prov-fields-are-bounded
   (implies (fn-prov-encodablep p)
            (and (<= (len (fn-prov-field-a p)) *fn-prov-max-field*)
                 (<= (len (fn-prov-field-b p)) *fn-prov-max-field*)
                 (<= (len (fn-prov-field-c p)) *fn-prov-max-field*)))
   :rule-classes :linear
   :hints (("Goal" :in-theory (enable fn-prov-encodablep fn-prov-textp
                                      fn-prov-field-a fn-prov-field-b
                                      fn-prov-field-c)))))

(local
 (defthm fn-prov-uints-are-uint32
   (implies (fn-prov-encodablep p)
            (and (fn-record-uint32p (fn-prov-field-m p))
                 (fn-record-uint32p (fn-prov-field-n p))
                 (fn-record-uint32p (fn-prov-field-o p))
                 (fn-record-uint32p (fn-prov-kind-code p))))
   :hints (("Goal" :in-theory (enable fn-prov-encodablep fn-record-uint32p
                                      fn-prov-field-m fn-prov-field-n
                                      fn-prov-field-o fn-prov-kind-code
                                      fn-prov-transit-kind-code
                                      fn-prov-diagnostic-code)))))

(local
 (defthm fn-prov-structured-octets-are-octets
   (fn-cbor-octet-listp (fn-prov-structured-octets p))
   :hints (("Goal" :in-theory (enable fn-prov-structured-octets)))))

; Step 2: the parse of an encoding is the rebuild of the fields it encoded.
; Seven applications of `fn-record-read-uint-encoded' and
; `fn-record-read-bytes-encoded' (books/records-invariants.lisp), whose
; bound hypotheses the six lemmas above discharge by linear arithmetic.
(local
 (defthm fn-prov-parse-of-structured-octets
   (implies (and (fn-prov-encodablep p) (not (stringp p)))
            (equal (fn-prov-parse-octets (fn-prov-structured-octets p))
                   (fn-prov-rebuild (fn-prov-kind-code p)
                                    (fn-prov-field-a p)
                                    (fn-prov-field-b p)
                                    (fn-prov-field-c p)
                                    (fn-prov-field-m p)
                                    (fn-prov-field-n p)
                                    (fn-prov-field-o p))))
   :hints (("Goal"
            :in-theory (e/d (fn-prov-parse-octets fn-prov-structured-octets
                             fn-codecs-includer-vocabulary
                             fn-record-read-uint-encoded
                             fn-record-read-bytes-encoded
                             fn-record-parse-ok-is-success
                             fn-record-parse-ok-has-value
                             fn-record-parse-ok-has-rest)
                            (fn-record-read-uint fn-record-read-bytes
                             fn-cbor-encode fn-prov-rebuild
                             fn-prov-field-a fn-prov-field-b fn-prov-field-c
                             fn-prov-field-m fn-prov-field-n fn-prov-field-o
                             fn-prov-kind-code))))))

; Step 3: the rebuild of a record's own fields is that record.  This is where
; the four generated `<ctor>-of-accessors' facts (`fn-defrecord',
; books/defrecord.lisp) and the octet/string round trip of
; `books/records-invariants.lisp' are spent.
;
; Two things about the citation, both measured on 2026-09-20 (w10/dtn-3),
; when the generated family replaced `books/provenance.lisp's four
; hand-written `-of-its-accessors' lemmas.  The generated rule is stated
; under the SHAPE predicate, so the instance's hypothesis is
; `(fn-prov-post-shapep p)`, which the generated
; `fn-prov-postp-forward-shape' puts in the context of the branch where
; `(fn-prov-postp p)' holds.  And the generated rule is an ENABLED rewrite,
; so all four are DISABLED in the `e/d' below: without that the rewriter
; collapses each `:use' hypothesis to `(equal p p)' and the citation is gone
; before the goal can spend it.
(local
 (defthm fn-prov-rebuild-of-its-own-fields
   (implies (and (fn-prov-encodablep p) (not (stringp p)))
            (equal (fn-prov-rebuild (fn-prov-kind-code p)
                                    (fn-prov-field-a p)
                                    (fn-prov-field-b p)
                                    (fn-prov-field-c p)
                                    (fn-prov-field-m p)
                                    (fn-prov-field-n p)
                                    (fn-prov-field-o p))
                   p))
   :hints (("Goal"
            :use ((:instance fn-prov-make-post-of-accessors (x p))
                  (:instance fn-prov-make-transit-of-accessors (x p))
                  (:instance fn-prov-make-bp-of-accessors (x p))
                  (:instance fn-prov-make-local-of-accessors (x p)))
            :in-theory (e/d (fn-prov-rebuild fn-prov-kind-code
                             fn-prov-field-a fn-prov-field-b fn-prov-field-c
                             fn-prov-field-m fn-prov-field-n fn-prov-field-o
                             fn-prov-encodablep fn-prov-textp
                             fn-prov-transit-kind-code fn-prov-diagnostic-code
                             fn-prov-diagnostic-identity
                             fn-prov-transit-kindp fn-prov-diagnosticp
                             fn-prov-diagnostic-match
                             fn-prov-diagnostic-mismatch
                             fn-record-uint32p fn-record-string-round-trip)
                            (fn-record-string-octets
                             fn-record-octets-string
                             ;; Cited above by `:use'; enabled, each would
                             ;; rewrite its own citation away.
                             fn-prov-make-post-of-accessors
                             fn-prov-make-transit-of-accessors
                             fn-prov-make-bp-of-accessors
                             fn-prov-make-local-of-accessors))))))

; -----------------------------------------------------------------------------
; Keystones

(defthm fn-prov-wire-is-a-string
  (stringp (fn-prov-wire p)))

(defthm fn-prov-of-octets-is-a-prov
  (fn-provp (fn-prov-of-octets octets)))

(defthm fn-prov-of-wire-is-a-prov
  (fn-provp (fn-prov-of-wire text))
  :hints (("Goal" :in-theory (disable fn-prov-parse-octets))))

; The transport layer: the prefix is exactly the first eight octets and the
; hexadecimal is exactly the rest.
(local
 (defthm fn-prov-prefixp-of-prefixed
   (fn-prov-wire-prefixedp (append *fn-prov-wire-prefix* xs))
   :hints (("Goal" :in-theory (enable fn-prov-wire-prefixedp
                                      fn-prov-prefixp)))))

(local
 (defthm fn-prov-drop-8-of-prefixed
   (equal (fn-prov-drop 8 (append *fn-prov-wire-prefix* xs)) xs)
   :hints (("Goal" :in-theory (enable fn-prov-drop)))))

(local
 (defthm fn-prov-wire-octets-are-octets
   (fn-cbor-octet-listp (fn-prov-wire-octets p))
   :hints (("Goal" :in-theory (enable fn-prov-wire-octets)))))

; A legacy evidence value occupies exactly the bytes it occupied before this
; lane: the wire form of a string IS the string.  -by-definition: the
; hypothesis is the branch test of `fn-prov-wire' and the conclusion is that
; branch's value, so this is `:rule-classes nil' and is NOT a registry event
; (docs/proof-style.md section 7; `tools/ledger.py's SUSPECT lint says the
; same thing).  The claim with content is K-PROV-3 below, which says the
; string comes BACK; the witnesses are in the test book.
(defthm fn-prov-wire-of-a-string-is-itself-by-definition
  (implies (stringp text)
           (equal (fn-prov-wire text) text))
  :rule-classes nil)

; K-PROV-2.  A legacy evidence value read back is itself, as the `:legacy'
; kind.  This is the theorem that says no store or journal written before
; this lane changes meaning.  -by-definition: `fn-prov-of-wire' branches on
; the prefix and `fn-prov-plain-stringp' is the negation of that test; the
; content is that the branch is the only one a plain string can take.
(defthm fn-prov-of-wire-of-a-plain-string
  (implies (fn-prov-plain-stringp text)
           (equal (fn-prov-of-wire text) text))
  :hints (("Goal" :in-theory (e/d (fn-prov-of-wire fn-prov-plain-stringp)
                                  (fn-prov-parse-octets
                                   fn-prov-wire-prefixedp)))))

(defthm fn-prov-kind-of-a-decoded-plain-string
  (implies (fn-prov-plain-stringp text)
           (equal (fn-prov-kind (fn-prov-of-wire text)) :legacy))
  :hints (("Goal" :in-theory (e/d (fn-prov-plain-stringp)
                                  (fn-prov-of-wire fn-prov-kind)))))

; K-PROV-3.  The canonical round trip: a provenance this codec can write is
; the provenance it reads back.
(defthm fn-prov-of-wire-of-wire
  (implies (fn-prov-encodablep p)
           (equal (fn-prov-of-wire (fn-prov-wire p)) p))
  :hints (("Goal"
           :cases ((stringp p))
           :use ((:instance fn-record-string-octets-of-octets-string
                            (octets (fn-prov-wire-octets p)))
                 (:instance fn-record-string-round-trip (text p))
                 (:instance fn-id-unhex-of-hex-octets
                            (octets (fn-prov-structured-octets p)))
                 (:instance fn-id-hex-octets-are-hex
                            (octets (fn-prov-structured-octets p))))
           :in-theory (e/d (fn-prov-of-wire fn-prov-wire fn-prov-wire-octets
                            fn-prov-encodablep fn-prov-plain-stringp)
                           (fn-prov-parse-octets fn-prov-structured-octets
                            fn-record-string-octets fn-record-octets-string
                            fn-id-hex-octets fn-id-unhex fn-id-hex-listp
                            fn-prov-rebuild fn-prov-kind-code
                            fn-prov-field-a fn-prov-field-b fn-prov-field-c
                            fn-prov-field-m fn-prov-field-n
                            fn-prov-field-o)))))

; -----------------------------------------------------------------------------
; What a durable writer may put in the record's evidence field
;
; `fn-record-p' bounds that field by `fn-record-metadata-bytes-p' (nonempty,
; at most 256 octets).  `fn-prov-durablep' is `fn-prov-encodablep' plus that
; bound, checked on the wire form itself rather than re-derived from the
; field lengths, so it is exact and executable.

(defun fn-prov-durablep (p)
  (declare (xargs :guard t))
  (and (fn-prov-encodablep p)
       (fn-record-metadata-bytes-p (fn-prov-wire p))))

; -by-definition: the second conjunct of `fn-prov-durablep', restated for the
; store boundary that needs it as a rewrite.
(defthm fn-prov-durable-wire-is-metadata
  (implies (fn-prov-durablep p)
           (fn-record-metadata-bytes-p (fn-prov-wire p))))

(defthm fn-prov-of-wire-of-a-durable-wire
  (implies (fn-prov-durablep p)
           (equal (fn-prov-of-wire (fn-prov-wire p)) p))
  :hints (("Goal" :in-theory (disable fn-prov-wire fn-prov-of-wire))))

(in-theory (disable fn-prov-durablep fn-prov-textp fn-prov-plain-stringp
                    fn-prov-wire-prefixedp fn-prov-wire-octets
                    fn-prov-prefixp fn-prov-drop
                    fn-prov-encodablep
                    fn-prov-octets fn-prov-structured-octets fn-prov-wire
                    fn-prov-parse-octets fn-prov-of-octets fn-prov-of-wire
                    fn-prov-rebuild fn-prov-kind-code fn-prov-field-a
                    fn-prov-field-b fn-prov-field-c fn-prov-field-m
                    fn-prov-field-n fn-prov-field-o
                    fn-prov-diagnostic-identity fn-prov-diagnostic-code
                    fn-prov-transit-kind-code))
