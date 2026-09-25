; fn: experimental local transaction-record bytes, schema 0.
;
; This is a deliberately narrow local prototype envelope.  It is not a native
; article, signature, batch, journal, or storage ABI, and it makes no
; compatibility promise.  Its only wire primitives are the deterministic CBOR
; uint32 and definite byte-string profile in books/cbor.lisp.  No definition in
; this book reads, prints, or evaluates external Lisp data.
;
; The logical record is the ten-element tuple
;   (sequence txid generation msgid payload groups obligation-id
;    content-subject release-evidence charge)
; where all text-like fields are ACL2 strings.  `msgid` and every group name
; are ASCII.  The three metadata fields are nonempty octet-domain strings:
; every character has a code in 0..255.  Conversion to a byte string is exactly
; the list of `char-code`s; parsing uses the inverse `code-char` conversion.
; `payload` alone is an arbitrary list of octets.
;
; Schema-0 exact grammar, a concatenation of self-delimiting primitive items:
;   bstr h'666e2d72'                 ; magic "fn-r"
;   uint 0                           ; local schema version
;   uint sequence, uint txid, uint generation
;   bstr msgid, bstr payload
;   uint group-count, bstr group[0] ... bstr group[group-count - 1]
;   bstr obligation-id, bstr content-subject, bstr release-evidence
;   uint charge
; The decoder requires the stated order, exact group count, canonical CBOR
; heads, and no trailing octets.  It checks the input bound before octet
; traversal; magic/version/group count are checked before the remaining record
; is parsed or constructed.

; THE SEAM (plan 2026-09-22 §4.1, step T1).  This book is the codec's
; implementation: `fn-record-encode-impl' and `fn-record-decode-exact-impl'.
; No book above the codec calls them.  `books/records-seam.lisp' constrains
; `fn-record-encode' and `fn-record-decode-exact' by exactly the properties
; `records-invariants' and `records-canonicality' prove of these two, and
; `books/records-attach.lisp' attaches these two to them for evaluation.
; The record itself (bounds, domains, accessors, recognizer, result shapes)
; is `books/records-shape.lisp', which is not a codec.

(in-package "ACL2")
(include-book "records-shape")


; This book is the schema-0 codec over the CBOR primitives, so it opens their
; definitions locally.  CBOR results stay opaque: the record lemmas exported
; by `cbor' are what close the goals about them.
(local (in-theory (enable fn-cbor-codec-vocabulary)))

; The record's domains and the four list facts the guard proofs below lean on
; are withdrawn by `records-shape' on export; the codec proofs are about them.
(local (in-theory (enable fn-record-shape-vocabulary
                          fn-record-cbor-octet-list-true-listp
                          fn-record-cbor-octet-listp-of-nthcdr
                          fn-record-cbor-octet-listp-of-take
                          fn-record-len-of-take-within-list)))

; -----------------------------------------------------------------------------
; The record's byte-string item codec (D27, design 2026-09-25-bounds §2.3).
;
; Every byte-string field is encoded and read through the CBOR bounded API at
; the record's own width, `*fn-record-max-octets*' (the FNST LENGTH field's
; u32), not through the generic entry, whose 65 535-octet item and
; 65 538-octet input caps would cap the record's data.  The decoder is the
; prechecked one-item parser: `fn-record-decode-exact-impl' checks the whole
; input's bound and octet domain once, so no field re-walks the remaining
; record (per-field work is the field's own length; the logical octet check
; below is `mbe' :logic only).  For an item of at most
; 65 535 octets the bytes are exactly the generic encoder's
; (`fn-record-item-encode-is-cbor-encode' in records-invariants), so every
; record written before this change keeps its bytes.  Uints are unaffected:
; their head does not depend on the byte-string bound.

(defun fn-record-item-encode (value)
  (declare (xargs :guard t))
  (fn-cbor-encode-bounded value *fn-record-max-octets*))

; The logical definition refuses a non-octet input; the executable one does
; not look, because the guard (discharged once, by the whole-record check in
; `fn-record-decode-exact-impl') already says so.
(defun fn-record-item-decode (octets)
  (declare (xargs :guard (fn-cbor-octet-listp octets)))
  (mbe :logic (if (fn-cbor-octet-listp octets)
                  (fn-cbor-decode-prechecked octets *fn-record-max-octets*)
                (fn-cbor-error :malformed))
       :exec (fn-cbor-decode-prechecked octets *fn-record-max-octets*)))

; -----------------------------------------------------------------------------
; Encoder

(defun fn-record-encode-groups (groups)
  (if (consp groups)
      (append (fn-record-item-encode
               (cons :bytes (fn-record-string-octets (car groups))))
              (fn-record-encode-groups (cdr groups)))
    nil))

; Admitting this defun computes its type prescription over a fourteen-way
; nested APPEND; with TRUE-LISTP-APPEND's type rule enabled beside
; BINARY-APPEND's, type-set revisits every tail twice per level (6.4 s of
; type reasoning, 3.9 million tries, for "no constraints").  Withdrawn for
; the admission only; the derived type is the same.
(local (in-theory (disable (:type-prescription true-listp-append))))
(defun fn-record-encode-impl (record)
  (if (not (fn-record-p record))
      nil
    (let ((octets
           (append
            (fn-record-item-encode (cons :bytes *fn-record-magic*))
            (fn-cbor-encode (cons :uint (fn-record-schema-octet record)))
            (fn-cbor-encode (cons :uint (fn-record-sequence record)))
            (fn-cbor-encode (cons :uint (fn-record-txid record)))
            (fn-cbor-encode (cons :uint (fn-record-generation record)))
            (fn-record-item-encode (cons :bytes
                                  (fn-record-string-octets
                                   (fn-record-msgid record))))
            (fn-record-item-encode (cons :bytes (fn-record-payload record)))
            (fn-cbor-encode (cons :uint (len (fn-record-groups record))))
            (fn-record-encode-groups (fn-record-groups record))
            (fn-record-item-encode (cons :bytes
                                  (fn-record-string-octets
                                   (fn-record-obligation-id record))))
            (fn-record-item-encode (cons :bytes
                                  (fn-record-string-octets
                                   (fn-record-content-subject record))))
            (fn-record-item-encode (cons :bytes
                                  (fn-record-string-octets
                                   (fn-record-release-evidence record))))
            (fn-cbor-encode (cons :uint (fn-record-charge record)))
            (if (equal (fn-record-stamp record) :legacy)
                nil
              (fn-cbor-encode (cons :uint (fn-record-stamp record)))))))
      (if (fn-cbor-at-mostp octets *fn-record-max-octets*) octets nil))))
(local (in-theory (enable (:type-prescription true-listp-append))))

(defun fn-record-schema0-encode (record)
  (fn-record-encode-impl (fn-record-with-stamp record :legacy)))


(defun fn-record-read-uint (octets)
  (declare (xargs :guard (fn-cbor-octet-listp octets)
                  :verify-guards nil))
  (let ((decoded (fn-record-item-decode octets)))
    (if (not (fn-cbor-result-okp decoded))
        (fn-record-parse-error (car (cdr decoded)))
      (let ((value (fn-cbor-result-value decoded)))
        (if (and (consp value) (equal (car value) :uint))
            (fn-record-parse-ok (cdr value) (fn-cbor-result-rest decoded))
          (fn-record-parse-error :field-type))))))

(defun fn-record-read-bytes (octets)
  (declare (xargs :guard (fn-cbor-octet-listp octets)
                  :verify-guards nil))
  (let ((decoded (fn-record-item-decode octets)))
    (if (not (fn-cbor-result-okp decoded))
        (fn-record-parse-error (car (cdr decoded)))
      (let ((value (fn-cbor-result-value decoded)))
        (if (and (consp value) (equal (car value) :bytes))
            (fn-record-parse-ok (cdr value) (fn-cbor-result-rest decoded))
          (fn-record-parse-error :field-type))))))

(defun fn-record-parse-groups (count octets)
  (declare (xargs :guard (and (natp count) (fn-cbor-octet-listp octets))
                  :verify-guards nil))
  (if (zp count)
      (fn-record-parse-ok nil octets)
    (let ((first (fn-record-read-bytes octets)))
      (if (not (fn-record-parse-okp first))
          first
        (let ((name (fn-record-octets-string (fn-record-parse-value first))))
          (if (not (fn-record-group-namep name))
              (fn-record-parse-error :group)
            (let ((tail (fn-record-parse-groups
                         (1- count) (fn-record-parse-rest first))))
              (if (not (fn-record-parse-okp tail))
                  tail
                (if (member-equal name (fn-record-parse-value tail))
                    (fn-record-parse-error :duplicate-group)
                  (fn-record-parse-ok
                   (cons name (fn-record-parse-value tail))
                   (fn-record-parse-rest tail)))))))))))

(defun fn-record-decode-tail (schema sequence txid generation msgid payload octets)
  (declare (xargs :guard (and (or (equal schema 0) (equal schema 1))
                              (fn-record-uint32p sequence)
                              (fn-record-uint32p txid)
                              (fn-record-uint32p generation)
                              (fn-record-msgidp msgid)
                              (fn-record-payloadp payload)
                              (fn-cbor-octet-listp octets))
                  :verify-guards nil))
  (let ((count-result (fn-record-read-uint octets)))
    (if (not (fn-record-parse-okp count-result))
        (fn-record-parse-error :group-count)
      (let ((count (fn-record-parse-value count-result)))
        (if (< *fn-record-max-groups* count)
            (fn-record-parse-error :groups-limit)
          (let ((groups-result
                 (fn-record-parse-groups count
                                         (fn-record-parse-rest count-result))))
            (if (not (fn-record-parse-okp groups-result))
                groups-result
              (let ((id-result
                     (fn-record-read-bytes (fn-record-parse-rest groups-result))))
                (if (not (fn-record-parse-okp id-result))
                    id-result
                  (let ((subject-result
                         (fn-record-read-bytes (fn-record-parse-rest id-result))))
                    (if (not (fn-record-parse-okp subject-result))
                        subject-result
                      (let ((evidence-result
                             (fn-record-read-bytes
                              (fn-record-parse-rest subject-result))))
                        (if (not (fn-record-parse-okp evidence-result))
                            evidence-result
                          (let ((charge-result
                                 (fn-record-read-uint
                                  (fn-record-parse-rest evidence-result))))
                            (if (not (fn-record-parse-okp charge-result))
                                charge-result
                              (let* ((stamp-result
                                      (if (equal schema 0)
                                          (fn-record-parse-ok :legacy
                                                              (fn-record-parse-rest charge-result))
                                        (fn-record-read-uint
                                         (fn-record-parse-rest charge-result))))
                                     (id (fn-record-octets-string
                                          (fn-record-parse-value id-result)))
                                     (subject (fn-record-octets-string
                                               (fn-record-parse-value subject-result)))
                                     (evidence (fn-record-octets-string
                                                (fn-record-parse-value evidence-result)))
                                     (record
                                      (fn-record-make
                                       sequence txid generation msgid payload
                                       (fn-record-parse-value groups-result)
                                       id subject evidence
                                       (fn-record-parse-value charge-result)
                                       (fn-record-parse-value stamp-result))))
                                (if (not (fn-record-parse-okp stamp-result))
                                    stamp-result
                                  (if (not (null (fn-record-parse-rest stamp-result)))
                                    (fn-record-parse-error :trailing)
                                  (if (fn-record-p record)
                                      (fn-record-parse-ok record nil)
                                    (fn-record-parse-error :invalid))))))))))))))))))))

(defun fn-record-decode-after-header (schema octets)
  (declare (xargs :guard (and (or (equal schema 0) (equal schema 1))
                              (fn-cbor-octet-listp octets))
                  :verify-guards nil))
  (let ((sequence-result (fn-record-read-uint octets)))
    (if (not (fn-record-parse-okp sequence-result))
        sequence-result
      (let ((txid-result
             (fn-record-read-uint (fn-record-parse-rest sequence-result))))
        (if (not (fn-record-parse-okp txid-result))
            txid-result
          (let ((generation-result
                 (fn-record-read-uint (fn-record-parse-rest txid-result))))
            (if (not (fn-record-parse-okp generation-result))
                generation-result
              (let ((msgid-result
                     (fn-record-read-bytes
                      (fn-record-parse-rest generation-result))))
                (if (not (fn-record-parse-okp msgid-result))
                    msgid-result
                  (let ((msgid (fn-record-octets-string
                                (fn-record-parse-value msgid-result))))
                    (if (not (fn-record-msgidp msgid))
                        (fn-record-parse-error :msgid)
                      (let ((payload-result
                             (fn-record-read-bytes
                              (fn-record-parse-rest msgid-result))))
                        (if (not (fn-record-parse-okp payload-result))
                            payload-result
                          (let ((payload (fn-record-parse-value payload-result)))
                            (if (not (fn-record-payloadp payload))
                                (fn-record-parse-error :payload)
                              (fn-record-decode-tail
                               schema
                               (fn-record-parse-value sequence-result)
                               (fn-record-parse-value txid-result)
                               (fn-record-parse-value generation-result)
                               msgid payload
                               (fn-record-parse-rest payload-result)))))))))))))))))

(defun fn-record-decode-exact-impl (octets)
  (if (not (fn-cbor-at-mostp octets *fn-record-max-octets*))
      (fn-record-parse-error :limit)
    (if (not (fn-cbor-octet-listp octets))
        (fn-record-parse-error :malformed)
      (let ((magic-result (fn-record-read-bytes octets)))
        (if (not (fn-record-parse-okp magic-result))
            magic-result
          (if (not (equal (fn-record-parse-value magic-result)
                          *fn-record-magic*))
              (fn-record-parse-error :magic)
            (let ((version-result
                   (fn-record-read-uint (fn-record-parse-rest magic-result))))
              (if (not (fn-record-parse-okp version-result))
                  version-result
                (if (not (member-equal (fn-record-parse-value version-result)
                                       '(0 1)))
                    (fn-record-parse-error :unknown-version)
                  (let ((parsed
                         (fn-record-decode-after-header
                          (fn-record-parse-value version-result)
                          (fn-record-parse-rest version-result))))
                    (if (fn-record-parse-okp parsed)
                        (fn-record-result-ok (fn-record-parse-value parsed))
                      parsed)))))))))))

(verify-guards fn-record-encode-groups)
(verify-guards fn-record-encode-impl
  :hints (("Goal" :use fn-record-cbor-octet-list-true-listp)))

(defthm fn-record-cbor-decode-argument-success-domain
  (implies
   (and (natp additional)
        (fn-cbor-octet-listp xs)
        (fn-cbor-result-okp (fn-cbor-decode-argument additional xs)))
   (and (natp (fn-cbor-result-value
               (fn-cbor-decode-argument additional xs)))
        (fn-cbor-octet-listp
         (fn-cbor-result-rest
          (fn-cbor-decode-argument additional xs)))))
  :hints (("Goal"
           :in-theory (enable fn-cbor-decode-argument
                              fn-cbor-result-okp
                              fn-cbor-result-value
                              fn-cbor-result-rest
                              fn-cbor-ok fn-cbor-error
                              fn-cbor-octet-listp))))

(defthm fn-record-cbor-decode-unsigned-success-domain
  (implies
   (and (natp additional)
        (fn-cbor-octet-listp tail)
        (fn-cbor-result-okp (fn-cbor-decode-unsigned additional tail)))
   (and (consp (fn-cbor-result-value
                (fn-cbor-decode-unsigned additional tail)))
        (equal (car (fn-cbor-result-value
                     (fn-cbor-decode-unsigned additional tail)))
               :uint)
        (natp (cdr (fn-cbor-result-value
                    (fn-cbor-decode-unsigned additional tail))))
        (<= (cdr (fn-cbor-result-value
                  (fn-cbor-decode-unsigned additional tail)))
            *fn-cbor-max-uint*)
        (fn-cbor-octet-listp
         (fn-cbor-result-rest
          (fn-cbor-decode-unsigned additional tail)))))
  :hints (("Goal"
           :use ((:instance
                  fn-record-cbor-decode-argument-success-domain
                  (xs tail)))
           :in-theory (e/d (fn-cbor-decode-unsigned
                              fn-cbor-result-okp
                              fn-cbor-canonical-argumentp)
                             (fn-cbor-decode-argument
                              fn-cbor-result-value
                              fn-cbor-result-rest
                              fn-cbor-ok fn-cbor-error)))))

(defthm fn-record-cbor-decode-bytes-success-domain
  (implies
   (and (natp additional)
        (fn-cbor-octet-listp tail)
        (fn-cbor-result-okp (fn-cbor-decode-bytes additional tail)))
   (and (consp (fn-cbor-result-value
                (fn-cbor-decode-bytes additional tail)))
        (equal (car (fn-cbor-result-value
                     (fn-cbor-decode-bytes additional tail)))
               :bytes)
        (fn-cbor-octet-listp
         (cdr (fn-cbor-result-value
               (fn-cbor-decode-bytes additional tail))))
        (<= (len (cdr (fn-cbor-result-value
                       (fn-cbor-decode-bytes additional tail))))
            *fn-cbor-max-bytes*)
        (fn-cbor-octet-listp
         (fn-cbor-result-rest
          (fn-cbor-decode-bytes additional tail)))))
  :hints (("Goal"
           :use ((:instance
                  fn-record-cbor-decode-argument-success-domain
                  (xs tail)))
           :in-theory (e/d (fn-cbor-decode-bytes
                              fn-cbor-result-okp
                              fn-cbor-canonical-argumentp)
                             (fn-cbor-decode-argument
                              fn-cbor-result-value
                              fn-cbor-result-rest
                              fn-cbor-ok fn-cbor-error
                              take nthcdr)))))

(defthm fn-record-cbor-decode-success-domain
  (implies
   (and (fn-cbor-octet-listp octets)
        (fn-cbor-result-okp (fn-cbor-decode octets)))
   (and (fn-cbor-valuep
         (fn-cbor-result-value (fn-cbor-decode octets)))
        (fn-cbor-octet-listp
         (fn-cbor-result-rest (fn-cbor-decode octets)))))
  :hints (("Goal"
           :use ((:instance
                  fn-record-cbor-decode-unsigned-success-domain
                  (additional (car octets)) (tail (cdr octets)))
                 (:instance
                  fn-record-cbor-decode-bytes-success-domain
                  (additional (- (car octets) 64)) (tail (cdr octets))))
           :in-theory (e/d (fn-cbor-decode fn-cbor-valuep)
                            (fn-cbor-decode-unsigned
                             fn-cbor-decode-bytes
                             fn-cbor-result-value
                             fn-cbor-result-rest)))))

; The same two facts for the bounded byte-string reader at any budget, and
; for the record's item decoder: what `fn-record-read-uint' and
; `fn-record-read-bytes' now call.
(defthm fn-record-cbor-decode-bytes-bounded-success-domain
  (implies
   (and (natp additional)
        (fn-cbor-octet-listp tail)
        (natp max-bytes)
        (fn-cbor-result-okp
         (fn-cbor-decode-bytes-bounded additional tail max-bytes)))
   (and (consp (fn-cbor-result-value
                (fn-cbor-decode-bytes-bounded additional tail max-bytes)))
        (equal (car (fn-cbor-result-value
                     (fn-cbor-decode-bytes-bounded additional tail
                                                   max-bytes)))
               :bytes)
        (fn-cbor-octet-listp
         (cdr (fn-cbor-result-value
               (fn-cbor-decode-bytes-bounded additional tail max-bytes))))
        (<= (len (cdr (fn-cbor-result-value
                       (fn-cbor-decode-bytes-bounded additional tail
                                                     max-bytes))))
            max-bytes)
        (fn-cbor-octet-listp
         (fn-cbor-result-rest
          (fn-cbor-decode-bytes-bounded additional tail max-bytes)))))
  :hints (("Goal"
           :use ((:instance
                  fn-record-cbor-decode-argument-success-domain
                  (xs tail)))
           :in-theory (e/d (fn-cbor-decode-bytes-bounded
                              fn-cbor-result-okp
                              fn-cbor-canonical-argumentp)
                             (fn-cbor-decode-argument
                              fn-cbor-result-value
                              fn-cbor-result-rest
                              fn-cbor-ok fn-cbor-error
                              take nthcdr)))))

(defthm fn-record-item-decode-success-domain
  (implies
   (fn-cbor-result-okp (fn-record-item-decode octets))
   (and (fn-cbor-valuep-bounded
         (fn-cbor-result-value (fn-record-item-decode octets))
         *fn-record-max-octets*)
        (fn-cbor-octet-listp
         (fn-cbor-result-rest (fn-record-item-decode octets)))))
  :hints (("Goal"
           :use ((:instance
                  fn-record-cbor-decode-unsigned-success-domain
                  (additional (car octets)) (tail (cdr octets)))
                 (:instance
                  fn-record-cbor-decode-bytes-bounded-success-domain
                  (additional (- (car octets) 64)) (tail (cdr octets))
                  (max-bytes *fn-record-max-octets*)))
           :in-theory (e/d (fn-record-item-decode
                            fn-cbor-decode-prechecked
                            fn-cbor-valuep-bounded)
                            (fn-cbor-decode-unsigned
                             fn-cbor-decode-bytes-bounded
                             fn-cbor-result-value
                             fn-cbor-result-rest)))))

(defthm fn-record-read-uint-is-true-list
  (true-listp (fn-record-read-uint octets))
  :hints (("Goal"
           :in-theory (enable fn-record-read-uint
                              fn-record-parse-ok fn-record-parse-error))))

(defthm fn-record-read-bytes-is-true-list
  (true-listp (fn-record-read-bytes octets))
  :hints (("Goal"
           :in-theory (enable fn-record-read-bytes
                              fn-record-parse-ok fn-record-parse-error))))


(defthm fn-record-read-uint-success-domain
  (implies
   (and (fn-cbor-octet-listp octets)
        (fn-record-parse-okp (fn-record-read-uint octets)))
   (and (natp (fn-record-parse-value (fn-record-read-uint octets)))
        (<= (fn-record-parse-value (fn-record-read-uint octets))
            *fn-cbor-max-uint*)
        (fn-cbor-octet-listp
         (fn-record-parse-rest (fn-record-read-uint octets)))))
  :hints (("Goal"
           :use ((:instance fn-record-item-decode-success-domain))
           :in-theory (e/d (fn-record-read-uint
                              fn-record-parse-okp
                              fn-record-parse-value fn-record-parse-rest
                              fn-record-parse-ok fn-record-parse-error
                              fn-cbor-valuep-bounded)
                             (fn-record-item-decode)))))

(defthm fn-record-read-uint-success-is-rational
  (implies
   (and (fn-cbor-octet-listp octets)
        (fn-record-parse-okp (fn-record-read-uint octets)))
   (rationalp (fn-record-parse-value (fn-record-read-uint octets))))
  :hints (("Goal"
           :use ((:instance fn-record-read-uint-success-domain))
           :in-theory (disable fn-record-read-uint
                               fn-record-parse-okp
                               fn-record-parse-value
                               fn-cbor-octet-listp))))

(defthm fn-record-read-uint-success-is-uint32
  (implies
   (and (fn-cbor-octet-listp octets)
        (fn-record-parse-okp (fn-record-read-uint octets)))
   (fn-record-uint32p
    (fn-record-parse-value (fn-record-read-uint octets))))
  :hints (("Goal"
           :use ((:instance fn-record-read-uint-success-domain))
           :in-theory (e/d (fn-record-uint32p)
                            (fn-record-read-uint
                             fn-record-parse-okp
                             fn-record-parse-value
                             fn-cbor-octet-listp)))))

(defthm fn-record-read-bytes-success-domain
  (implies
   (and (fn-cbor-octet-listp octets)
        (fn-record-parse-okp (fn-record-read-bytes octets)))
   (and (fn-cbor-octet-listp
         (fn-record-parse-value (fn-record-read-bytes octets)))
        (fn-cbor-octet-listp
         (fn-record-parse-rest (fn-record-read-bytes octets)))))
  :hints (("Goal"
           :use ((:instance fn-record-item-decode-success-domain))
           :in-theory (e/d (fn-record-read-bytes
                              fn-record-parse-okp
                              fn-record-parse-value fn-record-parse-rest
                              fn-record-parse-ok fn-record-parse-error
                              fn-cbor-valuep-bounded)
                             (fn-record-item-decode)))))

(defthm fn-record-parse-groups-is-true-list
  (true-listp (fn-record-parse-groups count octets))
  :hints (("Goal" :induct (fn-record-parse-groups count octets)
           :in-theory (enable fn-record-parse-groups
                              fn-record-parse-ok fn-record-parse-error))))

(defthm fn-record-parse-groups-success-domain
  (implies
   (and (natp count)
        (fn-cbor-octet-listp octets)
        (fn-record-parse-okp (fn-record-parse-groups count octets)))
   (and (true-listp
         (fn-record-parse-value (fn-record-parse-groups count octets)))
        (fn-cbor-octet-listp
         (fn-record-parse-rest (fn-record-parse-groups count octets)))))
  :hints (("Goal" :induct (fn-record-parse-groups count octets)
           :in-theory
           (e/d (fn-record-parse-groups fn-record-parse-okp)
                (fn-record-read-bytes fn-record-octets-string
                 fn-record-group-namep fn-record-parse-value
                 fn-record-parse-rest fn-record-parse-ok
                 fn-record-parse-error)))))

(verify-guards fn-record-read-uint
  :hints (("Goal" :use fn-record-item-decode-success-domain
           :in-theory (disable fn-record-item-decode))))
(verify-guards fn-record-read-bytes
  :hints (("Goal" :use fn-record-item-decode-success-domain
           :in-theory (disable fn-record-item-decode))))
(verify-guards fn-record-parse-groups
  :hints (("Goal"
           :in-theory (disable fn-record-read-bytes
                               fn-record-octets-string
                               fn-record-group-namep
                               fn-record-parse-okp
                               fn-record-parse-value
                               fn-record-parse-rest
                               fn-record-uint32p
                               fn-record-msgidp
                               fn-record-payloadp
                               fn-cbor-octet-listp
                               true-listp))))
(verify-guards fn-record-decode-tail
  :hints (("Goal"
           :in-theory (disable fn-record-read-uint fn-record-read-bytes
                               fn-record-parse-groups
                               fn-record-octets-string
                               fn-record-parse-okp
                               fn-record-parse-value
                               fn-record-parse-rest
                               fn-record-uint32p
                               fn-record-msgidp
                               fn-record-payloadp
                               fn-cbor-octet-listp
                               true-listp))))
(verify-guards fn-record-decode-after-header
  :hints (("Goal"
           :in-theory (disable fn-record-read-uint fn-record-read-bytes
                               fn-record-decode-tail
                               fn-record-octets-string
                               fn-record-parse-okp
                               fn-record-parse-value
                               fn-record-parse-rest
                               fn-record-uint32p
                               fn-record-msgidp
                               fn-record-payloadp
                               fn-cbor-octet-listp
                               true-listp))))
(verify-guards fn-record-decode-exact-impl
  :hints (("Goal"
           :in-theory (disable fn-record-read-uint fn-record-read-bytes
                               fn-record-decode-after-header
                               fn-record-parse-okp
                               fn-record-parse-value
                               fn-record-parse-rest
                               fn-cbor-octet-listp
                               true-listp))))

; A certified end-to-end schema-0 vector.  The broader all-record round-trip
; property remains proof work because it includes the exact ACL2 string/octet
; conversion and bounded variable group sequence.
; A witness, not a rewrite rule: it is one ground vector, cited by name.
(defthm fn-record-schema0-golden-round-trip
  (equal (fn-record-decode-exact-impl
          (fn-record-encode-impl
           (fn-record-make 1 2 3 "<a>" '(9 8) '("g") "o" "s" "e" 4 :legacy)))
         (fn-record-result-ok
          (fn-record-make 1 2 3 "<a>" '(9 8) '("g") "o" "s" "e" 4 :legacy)))
  :rule-classes nil)

; The same vector as exact wire octets: the concrete conformance fact the
; seam cannot carry (review 2026-09-22-bp-node-machine-2 §4: a round trip
; and canonicality hold of any length-preserving permutation of the
; encodings, so they do not identify this wire language).  Magic h'44666e2d72'
; ("fn-r"), schema 0, sequence 1, txid 2, generation 3, msgid h'433c613e'
; ("<a>"), payload h'420908', one group h'4167', obligation, subject and
; evidence h'416f' h'4173' h'4165', charge 4 -- the layout of
; specs/encoding.md, octet for octet.
(defconst *fn-record-schema0-golden-octets*
  '(68 102 110 45 114 0 1 2 3 67 60 97 62 66 9 8 1 65 103
    65 111 65 115 65 101 4))

(defthm fn-record-schema0-golden-octets-are-the-encoding
  (equal (fn-record-encode-impl
          (fn-record-make 1 2 3 "<a>" '(9 8) '("g") "o" "s" "e" 4 :legacy))
         *fn-record-schema0-golden-octets*)
  :rule-classes nil)

(defthm fn-record-schema0-golden-octets-decode
  (equal (fn-record-decode-exact-impl *fn-record-schema0-golden-octets*)
         (fn-record-result-ok
          (fn-record-make 1 2 3 "<a>" '(9 8) '("g") "o" "s" "e" 4 :legacy)))
  :rule-classes nil)

; Grammar conformance at the header: a wrong magic octet and a version
; octet other than 0 are refused with their own errors, before any field.
(defthm fn-record-schema0-golden-grammar-refusals
  (and (equal (fn-record-decode-exact-impl '(68 102 110 45 115 0))
              (fn-record-parse-error :magic))
       (equal (fn-record-decode-exact-impl '(68 102 110 45 114 2))
              (fn-record-parse-error :unknown-version)))
  :rule-classes nil)

; Schema 1 preserves every schema-0 field byte and appends one canonical uint.
(defconst *fn-record-schema1-golden-octets*
  '(68 102 110 45 114 1 1 2 3 67 60 97 62 66 9 8 1 65 103
    65 111 65 115 65 101 4 5))

(defthm fn-record-schema1-golden-octets-are-the-encoding
  (equal (fn-record-encode-impl
          (fn-record-make 1 2 3 "<a>" '(9 8) '("g") "o" "s" "e" 4 5))
         *fn-record-schema1-golden-octets*)
  :rule-classes nil)

(defthm fn-record-schema1-golden-octets-decode
  (equal (fn-record-decode-exact-impl *fn-record-schema1-golden-octets*)
         (fn-record-result-ok
          (fn-record-make 1 2 3 "<a>" '(9 8) '("g") "o" "s" "e" 4 5)))
  :rule-classes nil)




; -----------------------------------------------------------------------------
; Export theory.
;
; Enabled on include: the golden round trip.  The codec is proof vocabulary
; for the codec's own books (`records-invariants', `records-canonicality')
; and for nothing above the seam.  `fn-record-codec-vocabulary' still names
; the record recognizers beside the implementation, so a book that opened it
; before the seam existed opens the same recognizers now; a book above the
; seam opens `fn-record-shape-vocabulary' (records-shape) instead, and
; `tools/theory_check.py' counts every top-level opening of this one.
; The item codec (`fn-record-item-encode', `-decode') is in neither theory:
; a proof that needs its definition names it in a hint, so a book that opens
; the codec vocabulary still sees the byte-string item as one closed term.

(deftheory fn-record-codec-vocabulary
  (union-theories
   (theory 'fn-record-shape-vocabulary)
   '((:d fn-record-encode-groups) (:d fn-record-encode-impl)
     (:d fn-record-read-uint) (:d fn-record-read-bytes)
     (:d fn-record-parse-groups) (:d fn-record-decode-tail)
     (:d fn-record-decode-after-header) (:d fn-record-decode-exact-impl))))

(deftheory fn-record-guard-vocabulary
  '(fn-record-cbor-octet-list-true-listp fn-record-cbor-octet-listp-of-nthcdr
    fn-record-cbor-octet-listp-of-take fn-record-len-of-take-within-list
    fn-record-cbor-decode-argument-success-domain
    fn-record-cbor-decode-unsigned-success-domain
    fn-record-cbor-decode-bytes-success-domain
    fn-record-cbor-decode-success-domain
    fn-record-cbor-decode-bytes-bounded-success-domain
    fn-record-item-decode-success-domain fn-record-read-uint-is-true-list
    fn-record-read-bytes-is-true-list fn-record-read-uint-success-domain
    fn-record-read-uint-success-is-rational
    fn-record-read-uint-success-is-uint32 fn-record-read-bytes-success-domain
    fn-record-parse-groups-is-true-list
    fn-record-parse-groups-success-domain))

(in-theory (disable (:d fn-record-item-encode) (:d fn-record-item-decode)
                    (:d fn-record-encode-groups) (:d fn-record-encode-impl)
                    (:d fn-record-read-uint) (:d fn-record-read-bytes)
                    (:d fn-record-parse-groups) (:d fn-record-decode-tail)
                    (:d fn-record-decode-after-header)
                    (:d fn-record-decode-exact-impl)
                    fn-record-cbor-decode-argument-success-domain
                    fn-record-cbor-decode-unsigned-success-domain
                    fn-record-cbor-decode-bytes-success-domain
                    fn-record-cbor-decode-success-domain
                    fn-record-cbor-decode-bytes-bounded-success-domain
                    fn-record-item-decode-success-domain
                    fn-record-read-uint-is-true-list
                    fn-record-read-bytes-is-true-list
                    fn-record-read-uint-success-domain
                    fn-record-read-uint-success-is-rational
                    fn-record-read-uint-success-is-uint32
                    fn-record-read-bytes-success-domain
                    fn-record-parse-groups-is-true-list
                    fn-record-parse-groups-success-domain))
