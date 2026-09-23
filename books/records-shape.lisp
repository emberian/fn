; fn: the schema-0 transaction record's shape, without its codec.
;
; The logical record is the ten-element tuple
;   (sequence txid generation msgid payload groups obligation-id
;    content-subject release-evidence charge)
; where all text-like fields are ACL2 strings.  `msgid` and every group name
; are ASCII.  The three metadata fields are nonempty octet-domain strings:
; every character has a code in 0..255.  `payload` alone is an arbitrary list
; of octets.  The byte grammar is `books/records.lisp'.
;
; This book is what a book above the codec seam may see of a record: the
; bounds, the field domains, the opaque record (`fn-defrecord': shape,
; constructor, ten accessors, recognizer `fn-record-p'), and the two result
; shapes a decoder returns (a parse step `(:ok value rest)' and a final
; `(:ok record)', each with its record lemmas).  None of these is a codec: the
; recognizers and accessors stay concrete everywhere, and a book above the
; seam opens `fn-record-shape-vocabulary' for them, never the codec.  The
; encoder and the exact decoder are `books/records.lisp' (their definitions)
; and `books/records-seam.lisp' (the constrained functions every book above
; the seam calls); the split is plan 2026-09-22 §4.1, step T1.

(in-package "ACL2")
(include-book "cbor")
(include-book "defrecord")

(defconst *fn-record-magic* '(102 110 45 114))
(defconst *fn-record-schema-version* 0)
(defconst *fn-record-max-msgid* 250)
(defconst *fn-record-max-payload* 32768)
(defconst *fn-record-max-group-name* 128)
(defconst *fn-record-max-groups* 16)
(defconst *fn-record-max-metadata* 256)
(defconst *fn-record-max-octets* 65538)
;
; The five octets every accepted record begins with: the CBOR byte-string
; head of length 4 (h'44') and "fn-r".  The sixth octet is the schema
; version, and which one a record needs is a fact about the record, not
; about the codec: `fn-record-schema-octet' below.  Both are named here so
; the seam (books/records-seam.lisp) can state its dispatch constraints
; without opening the codec.
(defconst *fn-record-magic-octets* '(68 102 110 45 114))

; -----------------------------------------------------------------------------
; Exact string/octet domains

(defun fn-record-string-octets-aux (chars)
  (declare (xargs :guard (character-listp chars)))
  (if (consp chars)
      (cons (char-code (car chars))
            (fn-record-string-octets-aux (cdr chars)))
    nil))

(defun fn-record-string-octets (text)
  (if (stringp text)
      (fn-record-string-octets-aux (coerce text 'list))
    nil))

(defun fn-record-octets-chars (octets)
  (declare (xargs :guard (fn-cbor-octet-listp octets)))
  (if (consp octets)
      (cons (code-char (car octets))
            (fn-record-octets-chars (cdr octets)))
    nil))

(defun fn-record-octets-string (octets)
  (if (fn-cbor-octet-listp octets)
      (coerce (fn-record-octets-chars octets) 'string)
    ""))

(defun fn-record-ascii-octetp (x)
  (and (fn-cbor-octetp x) (<= x 127)))

(defun fn-record-ascii-octet-listp (xs)
  (if (consp xs)
      (and (fn-record-ascii-octetp (car xs))
           (fn-record-ascii-octet-listp (cdr xs)))
    (null xs)))

(defun fn-record-ascii-stringp (text)
  (and (stringp text)
       (fn-record-ascii-octet-listp (fn-record-string-octets text))))

(defun fn-record-octet-stringp (text)
  (and (stringp text)
       (fn-cbor-octet-listp (fn-record-string-octets text))))

(defun fn-record-nonempty-at-mostp (xs bound)
  (declare (xargs :guard (natp bound)))
  (and (consp xs) (<= (len xs) bound)))

(defun fn-record-msgidp (text)
  (and (fn-record-ascii-stringp text)
       (fn-record-nonempty-at-mostp (fn-record-string-octets text)
                                    *fn-record-max-msgid*)))

(defun fn-record-payloadp (octets)
  (and (fn-cbor-octet-listp octets)
       (<= (len octets) *fn-record-max-payload*)))

(defun fn-record-group-namep (text)
  (and (fn-record-ascii-stringp text)
       (fn-record-nonempty-at-mostp (fn-record-string-octets text)
                                    *fn-record-max-group-name*)))

(defun fn-record-no-duplicatesp (xs)
  (declare (xargs :guard (true-listp xs)))
  (if (consp xs)
      (and (not (member-equal (car xs) (cdr xs)))
           (fn-record-no-duplicatesp (cdr xs)))
    t))

(defun fn-record-group-listp (groups)
  (if (consp groups)
      (and (fn-record-group-namep (car groups))
           (fn-record-group-listp (cdr groups)))
    (null groups)))

(defun fn-record-groupsp (groups)
  (and (true-listp groups)
       (<= (len groups) *fn-record-max-groups*)
       (fn-record-group-listp groups)
       (fn-record-no-duplicatesp groups)))

(defun fn-record-groups-validp (groups)
  (fn-record-groupsp groups))

(defun fn-record-metadata-bytes-p (text)
  (and (fn-record-octet-stringp text)
       (fn-record-nonempty-at-mostp (fn-record-string-octets text)
                                    *fn-record-max-metadata*)))

(defun fn-record-uint32p (n)
  (and (natp n) (<= n *fn-cbor-max-uint*)))

; The schema octet a record's encoding carries.  At schema 0 every record
; needs version 0.  The acceptance stamp (specs/acceptance-stamp.md §1.4)
; makes it a function of the stamp's kind (0 for a `:legacy' stamp, 1 for a
; natural one); the seam constraint `fn-record-accepted-schema-is-the-stamp-kind'
; is stated through this function so that the change is a change here and
; behind the seam, and no statement above the seam moves.  Withdrawn on
; export with the recognizers: no book above the seam may depend on the
; value 0.
(defun fn-record-schema-octet (record)
  (declare (xargs :guard t)
           (ignore record))
  0)

; -----------------------------------------------------------------------------
; Logical record and field accessors

; The stored record is an opaque record: a shape, a constructor and ten
; total accessors.  Below the withdrawal at the end of this section nothing
; opens it; rules are stated in accessor vocabulary.

; What opacity takes away (docs/proof-style.md, s1): while the accessors
; opened, type reasoning gave `(true-listp record)' from `(fn-record-p
; record)' for free, and a caller's guard -- `fn-replay-apply-record' takes
; `(true-listp record)' -- closed on it.  fn-defrecord exports both facts
; back, and the per-accessor consp family this book used to omit, as
; `:forward-chaining' only, so they land in the context when a record is
; mentioned and no rule about `consp' or `true-listp' leaves this book as a
; rewrite.  An includer that wrote a local bridge for either one deletes it.

(fn-defrecord fn-record
  :constructor (fn-record-make sequence txid generation msgid payload groups
                               obligation-id content-subject release-evidence
                               charge)
  :fields ((fn-record-sequence fn-record-uint32p)
           (fn-record-txid fn-record-uint32p)
           (fn-record-generation fn-record-uint32p)
           (fn-record-msgid fn-record-msgidp)
           (fn-record-payload fn-record-payloadp)
           (fn-record-groups fn-record-groups-validp)
           (fn-record-obligation-id fn-record-metadata-bytes-p)
           (fn-record-content-subject fn-record-metadata-bytes-p)
           (fn-record-release-evidence fn-record-metadata-bytes-p)
           (fn-record-charge fn-record-uint32p))
  :recognizer fn-record-p
  :recognizer-verify-guards nil
  :car-fn fn-cbor-ag-car
  :cdr-fn fn-cbor-ag-cdr)


; -----------------------------------------------------------------------------
; Bounded sequential decoder.  Parse results carry a value and unconsumed
; octets as (:ok value rest); final public results omit the rest.

(defun fn-record-parse-shapep (result)
  (declare (xargs :guard t))
  (and (true-listp result) (consp result)
       (or (equal (len result) 2) (equal (len result) 3))))

(defun fn-record-parse-ok (value rest)
  (declare (xargs :guard t))
  (list :ok value rest))

(defun fn-record-parse-error (code)
  (declare (xargs :guard t))
  (list :error code))

(defun fn-record-parse-okp (result)
  (declare (xargs :guard t))
  (and (consp result) (equal (fn-cbor-ag-car result) :ok)))

(defun fn-record-parse-value (result)
  (declare (xargs :guard t :verify-guards nil))
  (mbe :logic (car (cdr result))
       :exec (fn-cbor-ag-car (fn-cbor-ag-cdr result))))

(defun fn-record-parse-rest (result)
  (declare (xargs :guard t :verify-guards nil))
  (mbe :logic (car (cdr (cdr result)))
       :exec (fn-cbor-ag-car (fn-cbor-ag-cdr (fn-cbor-ag-cdr result)))))

; The public final result: a success carries only the decoded record.  A
; failure is the parse error that produced it, propagated unchanged.
(defun fn-record-result-ok (record)
  (declare (xargs :guard t))
  (list :ok record))

(defun fn-record-result-okp (result)
  (declare (xargs :guard t))
  (and (consp result) (equal (fn-cbor-ag-car result) :ok)))

(defun fn-record-result-record (result)
  (declare (xargs :guard t :verify-guards nil))
  (mbe :logic (car (cdr result))
       :exec (fn-cbor-ag-car (fn-cbor-ag-cdr result))))

(verify-guards fn-record-string-octets-aux)
(verify-guards fn-record-string-octets)
(verify-guards fn-record-octets-chars)
(verify-guards fn-record-octets-string)
(verify-guards fn-record-ascii-octetp)
(verify-guards fn-record-ascii-octet-listp)
(verify-guards fn-record-ascii-stringp)
(verify-guards fn-record-octet-stringp)
(verify-guards fn-record-nonempty-at-mostp)
(verify-guards fn-record-msgidp)
(verify-guards fn-record-payloadp)
(verify-guards fn-record-group-namep)
(verify-guards fn-record-no-duplicatesp)
(verify-guards fn-record-group-listp)
(verify-guards fn-record-groupsp)
(verify-guards fn-record-groups-validp)
(verify-guards fn-record-metadata-bytes-p)
(verify-guards fn-record-uint32p)
(verify-guards fn-record-p)
(defthm fn-record-cbor-octet-list-true-listp
  (implies (fn-cbor-octet-listp xs)
           (true-listp xs))
  :hints (("Goal" :induct (fn-cbor-octet-listp xs))))

(verify-guards fn-record-parse-shapep)
(verify-guards fn-record-parse-ok)
(verify-guards fn-record-parse-error)
(verify-guards fn-record-parse-okp)
(verify-guards fn-record-parse-value)
(verify-guards fn-record-parse-rest)
(verify-guards fn-record-result-ok)
(verify-guards fn-record-result-okp)
(verify-guards fn-record-result-record)

; Successful CBOR streaming decodes retain an octet-list remainder.  Keeping
; these lemmas at the codec boundary prevents later record-parser guard proofs
; from unfolding the complete bounded CBOR decoder.
(defthm fn-record-cbor-octet-listp-of-nthcdr
  (implies (and (natp n) (fn-cbor-octet-listp xs))
           (fn-cbor-octet-listp (nthcdr n xs)))
  :hints (("Goal" :induct (nthcdr n xs)
           :in-theory (enable fn-cbor-octet-listp))))

(defthm fn-record-cbor-octet-listp-of-take
  (implies (and (natp n)
                (<= n (len xs))
                (fn-cbor-octet-listp xs))
           (fn-cbor-octet-listp (take n xs)))
  :hints (("Goal" :induct (take n xs)
           :in-theory (enable fn-cbor-octet-listp))))

(defthm fn-record-len-of-take-within-list
  (implies (and (natp n) (<= n (len xs)))
           (equal (len (take n xs)) n))
  :hints (("Goal" :induct (take n xs))))


(defthm fn-record-parse-okp-of-ok
  (fn-record-parse-okp (fn-record-parse-ok value rest))
  :hints (("Goal" :in-theory (enable fn-record-parse-okp
                                      fn-record-parse-ok))))

(defthm fn-record-parse-value-of-ok
  (equal (fn-record-parse-value (fn-record-parse-ok value rest)) value)
  :hints (("Goal" :in-theory (enable fn-record-parse-value
                                      fn-record-parse-ok))))

(defthm fn-record-parse-rest-of-ok
  (equal (fn-record-parse-rest (fn-record-parse-ok value rest)) rest)
  :hints (("Goal" :in-theory (enable fn-record-parse-rest
                                      fn-record-parse-ok))))

; The remaining record lemmas for both results, and the withdrawal.  Below
; this point a parse result and a final result are opaque: every rule about
; them is stated through `fn-record-parse-okp', `-value', `-rest',
; `fn-record-result-okp' and `fn-record-result-record'.

(defthm fn-record-parse-shapep-of-ok
  (fn-record-parse-shapep (fn-record-parse-ok value rest))
  :hints (("Goal" :in-theory (enable fn-record-parse-shapep
                                     fn-record-parse-ok))))

(defthm fn-record-parse-shapep-of-error
  (fn-record-parse-shapep (fn-record-parse-error code))
  :hints (("Goal" :in-theory (enable fn-record-parse-shapep
                                     fn-record-parse-error))))

(defthm fn-record-parse-error-is-failure
  (not (fn-record-parse-okp (fn-record-parse-error code)))
  :hints (("Goal" :in-theory (enable fn-record-parse-okp
                                     fn-record-parse-error))))

(defthm fn-record-parse-ok-is-injective
  (equal (equal (fn-record-parse-ok value rest)
                (fn-record-parse-ok value2 rest2))
         (and (equal value value2) (equal rest rest2)))
  :hints (("Goal" :in-theory (enable fn-record-parse-ok))))

(defthm fn-record-result-okp-of-result-ok
  (fn-record-result-okp (fn-record-result-ok record))
  :hints (("Goal" :in-theory (enable fn-record-result-okp
                                     fn-record-result-ok))))

(defthm fn-record-result-record-of-result-ok
  (equal (fn-record-result-record (fn-record-result-ok record)) record)
  :hints (("Goal" :in-theory (enable fn-record-result-record
                                     fn-record-result-ok))))

(defthm fn-record-result-error-is-failure
  (not (fn-record-result-okp (fn-record-parse-error code)))
  :hints (("Goal" :in-theory (enable fn-record-result-okp
                                     fn-record-parse-error))))

(defthm fn-record-result-ok-is-injective
  (equal (equal (fn-record-result-ok record) (fn-record-result-ok record2))
         (equal record record2))
  :hints (("Goal" :in-theory (enable fn-record-result-ok))))

(in-theory (disable (:d fn-record-parse-shapep) (:d fn-record-parse-ok)
                    (:d fn-record-parse-error) (:d fn-record-parse-okp)
                    (:d fn-record-parse-value) (:d fn-record-parse-rest)
                    (:d fn-record-result-ok) (:d fn-record-result-okp)
                    (:d fn-record-result-record)))

; -----------------------------------------------------------------------------
; Export theory.
;
; Enabled on include: the record lemmas above and the small total helpers
; over strings and octets that proofs induct on.  The recognizers and bounds
; are proof vocabulary, withdrawn below; a book that reasons about a field's
; domain enables `fn-record-shape-vocabulary' locally.  Neither theory
; contains a codec: opening them unfolds no encoder and no decoder.

(deftheory fn-record-record-vocabulary
  '((:d fn-record-shapep) (:d fn-record-make) (:d fn-record-sequence)
    (:d fn-record-txid) (:d fn-record-generation) (:d fn-record-msgid)
    (:d fn-record-payload) (:d fn-record-groups) (:d fn-record-obligation-id)
    (:d fn-record-content-subject) (:d fn-record-release-evidence)
    (:d fn-record-charge) (:d fn-record-parse-shapep) (:d fn-record-parse-ok)
    (:d fn-record-parse-error) (:d fn-record-parse-okp)
    (:d fn-record-parse-value) (:d fn-record-parse-rest)
    (:d fn-record-result-ok) (:d fn-record-result-okp)
    (:d fn-record-result-record)))

(deftheory fn-record-shape-vocabulary
  '((:d fn-record-p) (:d fn-record-msgidp) (:d fn-record-payloadp)
    (:d fn-record-group-namep) (:d fn-record-groupsp)
    (:d fn-record-groups-validp) (:d fn-record-metadata-bytes-p)
    (:d fn-record-uint32p) (:d fn-record-ascii-stringp)
    (:d fn-record-octet-stringp) (:d fn-record-nonempty-at-mostp)
    (:d fn-record-schema-octet)))

(in-theory (disable (:d fn-record-p) (:d fn-record-msgidp)
                    (:d fn-record-payloadp) (:d fn-record-group-namep)
                    (:d fn-record-groupsp) (:d fn-record-groups-validp)
                    (:d fn-record-metadata-bytes-p) (:d fn-record-uint32p)
                    (:d fn-record-ascii-stringp) (:d fn-record-octet-stringp)
                    (:d fn-record-nonempty-at-mostp)
                    (:d fn-record-schema-octet)
                    fn-record-cbor-octet-list-true-listp
                    fn-record-cbor-octet-listp-of-nthcdr
                    fn-record-cbor-octet-listp-of-take
                    fn-record-len-of-take-within-list))

