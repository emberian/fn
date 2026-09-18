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

(in-package "ACL2")
(include-book "cbor")

(defconst *fn-record-magic* '(102 110 45 114))
(defconst *fn-record-schema-version* 0)
(defconst *fn-record-max-msgid* 250)
(defconst *fn-record-max-payload* 32768)
(defconst *fn-record-max-group-name* 128)
(defconst *fn-record-max-groups* 16)
(defconst *fn-record-max-metadata* 256)
(defconst *fn-record-max-octets* 65538)

; -----------------------------------------------------------------------------
; Exact string/octet domains

(defun fn-record-string-octets-aux (chars)
  (if (consp chars)
      (cons (char-code (car chars))
            (fn-record-string-octets-aux (cdr chars)))
    nil))

(defun fn-record-string-octets (text)
  (if (stringp text)
      (fn-record-string-octets-aux (coerce text 'list))
    nil))

(defun fn-record-octets-chars (octets)
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

; -----------------------------------------------------------------------------
; Logical record and field accessors

(defun fn-record-sequence (record) (car record))
(defun fn-record-txid (record) (car (cdr record)))
(defun fn-record-generation (record) (car (cdr (cdr record))))
(defun fn-record-msgid (record) (car (cdr (cdr (cdr record)))))
(defun fn-record-payload (record) (car (cdr (cdr (cdr (cdr record))))))
(defun fn-record-groups (record) (car (cdr (cdr (cdr (cdr (cdr record)))))))
(defun fn-record-obligation-id (record)
  (car (cdr (cdr (cdr (cdr (cdr (cdr record))))))))
(defun fn-record-content-subject (record)
  (car (cdr (cdr (cdr (cdr (cdr (cdr (cdr record)))))))))
(defun fn-record-release-evidence (record)
  (car (cdr (cdr (cdr (cdr (cdr (cdr (cdr (cdr record))))))))))
(defun fn-record-charge (record)
  (car (cdr (cdr (cdr (cdr (cdr (cdr (cdr (cdr (cdr record)))))))))))

(defun fn-record-make (sequence txid generation msgid payload groups
                                 obligation-id content-subject release-evidence
                                 charge)
  (list sequence txid generation msgid payload groups obligation-id
        content-subject release-evidence charge))

(defun fn-record-p (record)
  (and (true-listp record)
       (equal (len record) 10)
       (fn-record-uint32p (fn-record-sequence record))
       (fn-record-uint32p (fn-record-txid record))
       (fn-record-uint32p (fn-record-generation record))
       (fn-record-msgidp (fn-record-msgid record))
       (fn-record-payloadp (fn-record-payload record))
       (fn-record-groups-validp (fn-record-groups record))
       (fn-record-metadata-bytes-p (fn-record-obligation-id record))
       (fn-record-metadata-bytes-p (fn-record-content-subject record))
       (fn-record-metadata-bytes-p (fn-record-release-evidence record))
       (fn-record-uint32p (fn-record-charge record))))

; -----------------------------------------------------------------------------
; Encoder

(defun fn-record-encode-groups (groups)
  (if (consp groups)
      (append (fn-cbor-encode
               (cons :bytes (fn-record-string-octets (car groups))))
              (fn-record-encode-groups (cdr groups)))
    nil))

(defun fn-record-encode (record)
  (if (not (fn-record-p record))
      nil
    (let ((octets
           (append
            (fn-cbor-encode (cons :bytes *fn-record-magic*))
            (fn-cbor-encode (cons :uint *fn-record-schema-version*))
            (fn-cbor-encode (cons :uint (fn-record-sequence record)))
            (fn-cbor-encode (cons :uint (fn-record-txid record)))
            (fn-cbor-encode (cons :uint (fn-record-generation record)))
            (fn-cbor-encode (cons :bytes
                                  (fn-record-string-octets
                                   (fn-record-msgid record))))
            (fn-cbor-encode (cons :bytes (fn-record-payload record)))
            (fn-cbor-encode (cons :uint (len (fn-record-groups record))))
            (fn-record-encode-groups (fn-record-groups record))
            (fn-cbor-encode (cons :bytes
                                  (fn-record-string-octets
                                   (fn-record-obligation-id record))))
            (fn-cbor-encode (cons :bytes
                                  (fn-record-string-octets
                                   (fn-record-content-subject record))))
            (fn-cbor-encode (cons :bytes
                                  (fn-record-string-octets
                                   (fn-record-release-evidence record))))
            (fn-cbor-encode (cons :uint (fn-record-charge record))))))
      (if (fn-cbor-at-mostp octets *fn-record-max-octets*) octets nil))))

; -----------------------------------------------------------------------------
; Bounded sequential decoder.  Parse results carry a value and unconsumed
; octets as (:ok value rest); final public results omit the rest.

(defun fn-record-parse-ok (value rest)
  (list :ok value rest))

(defun fn-record-parse-error (code)
  (list :error code))

(defun fn-record-parse-okp (result)
  (and (consp result) (equal (car result) :ok)))

(defun fn-record-parse-value (result)
  (car (cdr result)))

(defun fn-record-parse-rest (result)
  (car (cdr (cdr result))))

; Public final-result helpers.  A successful final result contains a
; `fn-record-p` record; error results carry only a symbolic rejection code.
(defun fn-record-result-okp (result)
  (and (consp result) (equal (car result) :ok)))

(defun fn-record-result-record (result)
  (car (cdr result)))

(defun fn-record-read-uint (octets)
  (let ((decoded (fn-cbor-decode octets)))
    (if (not (fn-cbor-result-okp decoded))
        (fn-record-parse-error (car (cdr decoded)))
      (let ((value (fn-cbor-result-value decoded)))
        (if (and (consp value) (equal (car value) :uint))
            (fn-record-parse-ok (cdr value) (fn-cbor-result-rest decoded))
          (fn-record-parse-error :field-type))))))

(defun fn-record-read-bytes (octets)
  (let ((decoded (fn-cbor-decode octets)))
    (if (not (fn-cbor-result-okp decoded))
        (fn-record-parse-error (car (cdr decoded)))
      (let ((value (fn-cbor-result-value decoded)))
        (if (and (consp value) (equal (car value) :bytes))
            (fn-record-parse-ok (cdr value) (fn-cbor-result-rest decoded))
          (fn-record-parse-error :field-type))))))

(defun fn-record-parse-groups (count octets)
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

(defun fn-record-decode-tail (sequence txid generation msgid payload octets)
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
                              (let* ((id (fn-record-octets-string
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
                                       (fn-record-parse-value charge-result))))
                                (if (not (null (fn-record-parse-rest charge-result)))
                                    (fn-record-parse-error :trailing)
                                  (if (fn-record-p record)
                                      (fn-record-parse-ok record nil)
                                    (fn-record-parse-error :invalid)))))))))))))))))))

(defun fn-record-decode-after-header (octets)
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
                               (fn-record-parse-value sequence-result)
                               (fn-record-parse-value txid-result)
                               (fn-record-parse-value generation-result)
                               msgid payload
                               (fn-record-parse-rest payload-result)))))))))))))))))

(defun fn-record-decode-exact (octets)
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
                (if (not (equal (fn-record-parse-value version-result)
                                *fn-record-schema-version*))
                    (fn-record-parse-error :unknown-version)
                  (let ((parsed
                         (fn-record-decode-after-header
                          (fn-record-parse-rest version-result))))
                    (if (fn-record-parse-okp parsed)
                        (list :ok (fn-record-parse-value parsed))
                      parsed)))))))))))

; A certified end-to-end schema-0 vector.  The broader all-record round-trip
; property remains proof work because it includes the exact ACL2 string/octet
; conversion and bounded variable group sequence.
(defthm fn-record-schema0-golden-round-trip
  (equal (fn-record-decode-exact
          (fn-record-encode
           (fn-record-make 1 2 3 "<a>" '(9 8) '("g") "o" "s" "e" 4)))
         (list :ok
               (fn-record-make 1 2 3 "<a>" '(9 8) '("g") "o" "s" "e" 4))))
