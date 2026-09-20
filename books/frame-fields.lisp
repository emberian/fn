; fn frame, part 2 of 4: the generic frame and its field grammar.
;
; Field specifications, the field parse result, the whole-frame encoder and
; decoder, and the frame result record.  Nothing here knows a journal kind.
; See `books/frame.lisp' for the layout and the trailer assumption.

(in-package "ACL2")
(include-book "frame-octets")
(include-book "wildmat")
(local (include-book "arithmetic/top" :dir :system))

(local (in-theory (enable fn-cbor-invariants-vocabulary)))
(local (in-theory (enable fn-frame-octet-vocabulary)))

; -----------------------------------------------------------------------------
; Field grammar for journal payloads
;
; A field specification is one of
;   :text          u16 length (1..512) then that many octets, valid UTF-8
;   :blob          u32 length (1..131072) then that many octets
;   :nat           eight octets, big-endian
;   (:enum . ks)   one octet, the 1-based position of a keyword in `ks`
; and a record payload is a list of specifications with a positional list of
; values.  The enumerations are 1-based positions so that code injectivity is
; a consequence of the keyword list having no duplicates rather than a second
; hand-maintained table.

(defun fn-frame-enum-specp (spec)
  (declare (xargs :guard t))
  (and (consp spec)
       (equal (car spec) :enum)
       (symbol-listp (cdr spec))
       (consp (cdr spec))
       (no-duplicatesp-equal (cdr spec))
       (<= (len (cdr spec)) 255)))

(defun fn-frame-specp (spec)
  (declare (xargs :guard t))
  (or (equal spec :text)
      (equal spec :blob)
      (equal spec :nat)
      (fn-frame-enum-specp spec)))

(defun fn-frame-spec-listp (specs)
  (declare (xargs :guard t))
  (if (consp specs)
      (and (fn-frame-specp (car specs))
           (fn-frame-spec-listp (cdr specs)))
    (null specs)))

; Text is UTF-8 by the wildmat book's RFC 3629 decoder.  The bound in front
; of it is this book's, so no second UTF-8 table exists anywhere in the tree.
(defun fn-frame-textp (octets)
  (declare (xargs :guard t))
  (and (fn-cbor-at-mostp octets *fn-frame-max-text*)
       (fn-cbor-octet-listp octets)
       (consp octets)
       (fn-wildmat-result-okp (fn-wildmat-decode-aux octets nil))))

(defun fn-frame-blobp (octets)
  (declare (xargs :guard t))
  (and (fn-cbor-at-mostp octets *fn-frame-max-blob*)
       (fn-cbor-octet-listp octets)
       (consp octets)))

(defun fn-frame-natp (n)
  (declare (xargs :guard t))
  (and (natp n) (<= n *fn-frame-max-nat*)))

(defun fn-frame-enum-index (value keys)
  ; 1-based position, or 0 when absent.
  (declare (xargs :guard (true-listp keys)))
  (if (consp keys)
      (if (equal value (car keys))
          1
        (let ((rest (fn-frame-enum-index value (cdr keys))))
          (if (equal rest 0) 0 (+ 1 rest))))
    0))

(defthm fn-frame-enum-index-natp
  (natp (fn-frame-enum-index value keys))
  :rule-classes (:rewrite :type-prescription))

(defthm fn-frame-enum-index-bound
  (<= (fn-frame-enum-index value keys) (len keys))
  :rule-classes :linear)

(defun fn-frame-field-okp (spec value)
  (declare (xargs :guard t :verify-guards nil))
  (if (equal spec :text)
      (fn-frame-textp value)
    (if (equal spec :blob)
        (fn-frame-blobp value)
      (if (equal spec :nat)
          (fn-frame-natp value)
        (and (fn-frame-enum-specp spec)
             (not (equal (fn-frame-enum-index value (cdr spec)) 0)))))))

(verify-guards fn-frame-field-okp)

(defun fn-frame-field-octets (spec value)
  (declare (xargs :guard (fn-frame-field-okp spec value)
                  :verify-guards nil))
  (if (equal spec :text)
      (append (fn-cbor-u16-bytes (len value)) value)
    (if (equal spec :blob)
        (append (fn-cbor-u32-bytes (len value)) value)
      (if (equal spec :nat)
          (fn-frame-u64-bytes value)
        (list (fn-frame-enum-index value (cdr spec)))))))

(verify-guards fn-frame-field-octets)

(defun fn-frame-parse-ok (value rest)
  (declare (xargs :guard t))
  (list :ok value rest))
(defun fn-frame-parse-error (reason)
  (declare (xargs :guard t))
  (list :error reason))
(defun fn-frame-parse-okp (x)
  (declare (xargs :guard t))
  (and (consp x) (equal (car x) :ok)))
(defun fn-frame-parse-value (x)
  (declare (xargs :guard t))
  (fn-frame-item 1 x))
(defun fn-frame-parse-rest (x)
  (declare (xargs :guard t))
  (fn-frame-item 2 x))

; Record lemmas for a field parse result.  Below the export theory in
; `frame.lisp' nothing opens one: a result is read only through
; `fn-frame-parse-okp', `fn-frame-parse-value' and `fn-frame-parse-rest'.

(defun fn-frame-parse-shapep (x)
  (declare (xargs :guard t))
  (and (true-listp x) (consp x)
       (or (equal (len x) 2) (equal (len x) 3))))

(defthm fn-frame-parse-shapep-of-ok
  (fn-frame-parse-shapep (fn-frame-parse-ok value rest)))
(defthm fn-frame-parse-shapep-of-error
  (fn-frame-parse-shapep (fn-frame-parse-error reason)))
(defthm fn-frame-parse-okp-of-ok
  (fn-frame-parse-okp (fn-frame-parse-ok value rest)))
(defthm fn-frame-parse-error-is-failure
  (not (fn-frame-parse-okp (fn-frame-parse-error reason))))
(defthm fn-frame-parse-value-of-ok
  (equal (fn-frame-parse-value (fn-frame-parse-ok value rest)) value))
(defthm fn-frame-parse-rest-of-ok
  (equal (fn-frame-parse-rest (fn-frame-parse-ok value rest)) rest))
(defthm fn-frame-parse-ok-is-injective
  (equal (equal (fn-frame-parse-ok value rest)
                (fn-frame-parse-ok value2 rest2))
         (and (equal value value2) (equal rest rest2))))

(defun fn-frame-parse-counted (octets count maximum)
  ; Shared tail of the two length-prefixed field types.  The declared count is
  ; compared with its cap before the split allocates anything.
  (declare (xargs :guard (and (fn-cbor-octet-listp octets)
                              (natp count) (natp maximum))))
  (if (or (equal count 0) (< maximum count))
      (fn-frame-parse-error :field-length)
    (let ((split (fn-frame-split count octets)))
      (if (null split)
          (fn-frame-parse-error :truncated)
        (fn-frame-parse-ok (car split) (cdr split))))))

(defun fn-frame-field-parse (spec octets)
  (declare (xargs :guard (and (fn-frame-specp spec)
                              (fn-cbor-octet-listp octets))
                  :verify-guards nil))
  (if (equal spec :text)
      (let ((head (fn-frame-split 2 octets)))
        (if (null head)
            (fn-frame-parse-error :truncated)
          (let ((parsed (fn-frame-parse-counted
                         (cdr head) (nfix (fn-cbor-u16-from (car head)))
                         *fn-frame-max-text*)))
            (if (not (fn-frame-parse-okp parsed))
                parsed
              (if (not (fn-frame-textp (fn-frame-parse-value parsed)))
                  (fn-frame-parse-error :malformed-utf8)
                parsed)))))
    (if (equal spec :blob)
        (let ((head (fn-frame-split 4 octets)))
          (if (null head)
              (fn-frame-parse-error :truncated)
            (fn-frame-parse-counted (cdr head)
                                    (nfix (fn-cbor-u32-from (car head)))
                                    *fn-frame-max-blob*)))
      (if (equal spec :nat)
          (let ((head (fn-frame-split 8 octets)))
            (if (null head)
                (fn-frame-parse-error :truncated)
              (fn-frame-parse-ok (fn-frame-u64-from (car head)) (cdr head))))
        (if (not (consp octets))
            (fn-frame-parse-error :truncated)
          (let ((code (car octets)))
            (if (or (not (posp code)) (< (len (cdr spec)) code))
                (fn-frame-parse-error :unknown-enumeration)
              (fn-frame-parse-ok (fn-frame-item (- code 1) (cdr spec))
                                 (cdr octets)))))))))

(verify-guards fn-frame-field-parse
  :hints (("Goal" :in-theory (disable fn-cbor-u16-from fn-cbor-u32-from))))

(defthm fn-frame-field-parse-rest-octets
  (implies (and (fn-cbor-octet-listp octets)
                (fn-frame-parse-okp (fn-frame-field-parse spec octets)))
           (fn-cbor-octet-listp
            (fn-frame-parse-rest (fn-frame-field-parse spec octets)))))

(defun fn-frame-values-okp (specs values)
  (declare (xargs :guard (fn-frame-spec-listp specs) :verify-guards nil))
  (if (consp specs)
      (and (consp values)
           (fn-frame-field-okp (car specs) (car values))
           (fn-frame-values-okp (cdr specs) (cdr values)))
    (null values)))

(verify-guards fn-frame-values-okp)

(defun fn-frame-fields-octets (specs values)
  (declare (xargs :guard (and (fn-frame-spec-listp specs)
                              (fn-frame-values-okp specs values))
                  :verify-guards nil))
  (if (consp specs)
      (append (fn-frame-field-octets (car specs) (car values))
              (fn-frame-fields-octets (cdr specs) (cdr values)))
    nil))

(verify-guards fn-frame-fields-octets)

(defthm fn-frame-field-octets-are-octets
  (implies (and (fn-frame-specp spec) (fn-frame-field-okp spec value))
           (fn-cbor-octet-listp (fn-frame-field-octets spec value)))
  :hints (("Goal" :in-theory (e/d (fn-frame-field-octets fn-frame-field-okp
                                   fn-frame-specp fn-frame-textp
                                   fn-frame-blobp fn-frame-natp
                                   fn-frame-enum-specp)
                                  (floor mod fn-cbor-u16-bytes
                                   fn-cbor-u32-bytes fn-frame-u64-bytes)))))

(defthm fn-frame-fields-octets-are-octets
  (implies (and (fn-frame-spec-listp specs)
                (fn-frame-values-okp specs values))
           (fn-cbor-octet-listp (fn-frame-fields-octets specs values)))
  :hints (("Goal" :induct (fn-frame-values-okp specs values)
           :in-theory (disable fn-frame-field-octets))))

(defun fn-frame-fields-parse-aux (specs octets)
  (declare (xargs :guard (and (fn-frame-spec-listp specs)
                              (fn-cbor-octet-listp octets))
                  :verify-guards nil))
  (if (consp specs)
      (let ((parsed (fn-frame-field-parse (car specs) octets)))
        (if (not (fn-frame-parse-okp parsed))
            parsed
          (let ((rest (fn-frame-fields-parse-aux
                       (cdr specs) (fn-frame-parse-rest parsed))))
            (if (not (fn-frame-parse-okp rest))
                rest
              (fn-frame-parse-ok (cons (fn-frame-parse-value parsed)
                                       (fn-frame-parse-value rest))
                                 (fn-frame-parse-rest rest))))))
    (fn-frame-parse-ok nil octets)))

(verify-guards fn-frame-fields-parse-aux)

(defun fn-frame-fields-parse (specs octets)
  ; A record payload is exactly its fields: a trailing octet is a refusal,
  ; not a value silently disregarded.
  (declare (xargs :guard (and (fn-frame-spec-listp specs)
                              (fn-cbor-octet-listp octets))))
  (let ((parsed (fn-frame-fields-parse-aux specs octets)))
    (if (not (fn-frame-parse-okp parsed))
        parsed
      (if (null (fn-frame-parse-rest parsed))
          parsed
        (fn-frame-parse-error :trailing)))))

; -----------------------------------------------------------------------------
; Frame encoder

(defun fn-frame-header (magic version kind length)
  (declare (xargs :guard (and (fn-frame-magicp magic)
                              (fn-cbor-octetp version)
                              (fn-cbor-octetp kind)
                              (natp length)
                              (<= length *fn-cbor-max-uint*))
                  :verify-guards nil))
  (append magic (cons version (cons kind (fn-cbor-u32-bytes length)))))

(verify-guards fn-frame-header)

(defun fn-frame-inputp (magic version kind payload max-payload)
  (declare (xargs :guard t))
  (and (fn-frame-magicp magic)
       (fn-cbor-octetp version)
       (fn-cbor-octetp kind)
       (fn-cbor-octet-listp payload)
       (natp max-payload)
       (<= max-payload *fn-frame-max-payload*)
       (<= (len payload) max-payload)))

(defun fn-frame-protected (magic version kind payload)
  (declare (xargs :guard (and (fn-frame-magicp magic)
                              (fn-cbor-octetp version)
                              (fn-cbor-octetp kind)
                              (fn-cbor-octet-listp payload)
                              (<= (len payload) *fn-cbor-max-uint*))
                  :verify-guards nil))
  (append (fn-frame-header magic version kind (len payload)) payload))

(verify-guards fn-frame-protected)

(defun fn-frame-encode (magic version kind payload digest)
  ; The host entry point.  `digest` is the host's 32 octets over the protected
  ; prefix; `fn-frame-encode-is-seal` says what must be true of it.
  (declare (xargs :guard (and (fn-frame-magicp magic)
                              (fn-cbor-octetp version)
                              (fn-cbor-octetp kind)
                              (fn-cbor-octet-listp payload)
                              (<= (len payload) *fn-cbor-max-uint*)
                              (fn-frame-digestp digest))
                  :verify-guards nil))
  (append (fn-frame-protected magic version kind payload) digest))

(verify-guards fn-frame-encode)

(defun fn-frame-seal (magic version kind payload)
  ; The specification encoder, stated against A-CRYPTO.  Not executable.
  (declare (xargs :guard (and (fn-frame-magicp magic)
                              (fn-cbor-octetp version)
                              (fn-cbor-octetp kind)
                              (fn-cbor-octet-listp payload)
                              (<= (len payload) *fn-cbor-max-uint*))
                  :verify-guards nil))
  (fn-frame-encode magic version kind payload
                   (fn-frame-digest
                    (fn-frame-protected magic version kind payload))))

(verify-guards fn-frame-seal)

; -----------------------------------------------------------------------------
; Frame decoder

(defun fn-frame-ok (magic version kind payload)
  (declare (xargs :guard t))
  (list :ok magic version kind payload))
(defun fn-frame-error (reason)
  (declare (xargs :guard t))
  (list :error reason))
(defun fn-frame-result-okp (x)
  (declare (xargs :guard t))
  (and (consp x) (equal (car x) :ok)))
(defun fn-frame-result-magic (x)
  (declare (xargs :guard t))
  (fn-frame-item 1 x))
(defun fn-frame-result-version (x)
  (declare (xargs :guard t))
  (fn-frame-item 2 x))
(defun fn-frame-result-kind (x)
  (declare (xargs :guard t))
  (fn-frame-item 3 x))
(defun fn-frame-result-payload (x)
  (declare (xargs :guard t))
  (fn-frame-item 4 x))

; Record lemmas for a decoded frame.  The same discipline: `fn-frame-ok' and
; `fn-frame-error' are the only constructors and the four accessors are the
; only readers.

(defun fn-frame-result-shapep (x)
  (declare (xargs :guard t))
  (and (true-listp x) (consp x)
       (or (equal (len x) 2) (equal (len x) 5))))

(defthm fn-frame-result-shapep-of-ok
  (fn-frame-result-shapep (fn-frame-ok magic version kind payload)))
(defthm fn-frame-result-shapep-of-error
  (fn-frame-result-shapep (fn-frame-error reason)))
(defthm fn-frame-result-okp-of-ok
  (fn-frame-result-okp (fn-frame-ok magic version kind payload)))
(defthm fn-frame-error-is-failure
  (not (fn-frame-result-okp (fn-frame-error reason))))
(defthm fn-frame-result-magic-of-ok
  (equal (fn-frame-result-magic (fn-frame-ok magic version kind payload))
         magic))
(defthm fn-frame-result-version-of-ok
  (equal (fn-frame-result-version (fn-frame-ok magic version kind payload))
         version))
(defthm fn-frame-result-kind-of-ok
  (equal (fn-frame-result-kind (fn-frame-ok magic version kind payload))
         kind))
(defthm fn-frame-result-payload-of-ok
  (equal (fn-frame-result-payload (fn-frame-ok magic version kind payload))
         payload))
(defthm fn-frame-ok-is-injective
  (equal (equal (fn-frame-ok magic version kind payload)
                (fn-frame-ok magic2 version2 kind2 payload2))
         (and (equal magic magic2) (equal version version2)
              (equal kind kind2) (equal payload payload2))))

(defun fn-frame-head-fields (head)
  ; (magic version kind length-octets) from a 10-octet header, or nil.
  (declare (xargs :guard (fn-cbor-octet-listp head) :verify-guards nil))
  (let ((magic (fn-frame-split *fn-frame-magic-octets* head)))
    (if (null magic)
        nil
      (let ((version-kind (fn-frame-split 2 (cdr magic))))
        (if (null version-kind)
            nil
          (let ((length-octets (fn-frame-split 4 (cdr version-kind))))
            (if (or (null length-octets) (cdr length-octets))
                nil
              (list (car magic)
                    (fn-frame-item 0 (car version-kind))
                    (fn-frame-item 1 (car version-kind))
                    (car length-octets)))))))))

(verify-guards fn-frame-head-fields)

(defthm fn-frame-head-fields-shape
  (implies (and (fn-cbor-octet-listp head) (fn-frame-head-fields head))
           (and (fn-cbor-octet-listp
                 (fn-frame-item 3 (fn-frame-head-fields head)))
                (equal (len (fn-frame-item 3 (fn-frame-head-fields head)))
                       4))))

(defun fn-frame-decode (octets digest max-payload)
  ; The host entry point.  Every bound is checked before the corresponding
  ; split allocates: the cons preflight before octet validation, the declared
  ; payload length against `max-payload` and against the actual remainder
  ; before the payload split.
  (declare (xargs :guard t :verify-guards nil))
  (if (not (and (natp max-payload) (<= max-payload *fn-frame-max-payload*)))
      (fn-frame-error :bound)
    (if (not (fn-cbor-at-mostp octets
                               (+ *fn-frame-overhead-octets* max-payload)))
        (fn-frame-error :limit)
      (if (not (fn-cbor-octet-listp octets))
          (fn-frame-error :malformed)
        (let ((head (fn-frame-split *fn-frame-header-octets* octets)))
          (if (null head)
              (fn-frame-error :truncated)
            (let ((fields (fn-frame-head-fields (car head))))
              (if (null fields)
                  (fn-frame-error :truncated)
                (let ((declared (nfix (fn-cbor-u32-from
                                       (fn-frame-item 3 fields)))))
                  (if (< max-payload declared)
                      (fn-frame-error :limit)
                    (if (not (equal (len (cdr head))
                                    (+ declared *fn-frame-trailer-octets*)))
                        ; A header that declares more payload than the octets
                        ; still hold is a cut frame, not a disagreement about
                        ; a bound: `:truncated` there, and `:length` only for
                        ; octets past the frame the header describes.
                        (if (< (len (cdr head))
                               (+ declared *fn-frame-trailer-octets*))
                            (fn-frame-error :truncated)
                          (fn-frame-error :length))
                      (if (not (fn-frame-digestp digest))
                          (fn-frame-error :digest)
                        (let ((body (fn-frame-split declared (cdr head))))
                          (if (null body)
                              (fn-frame-error :truncated)
                            (if (not (equal (cdr body) digest))
                                (fn-frame-error :integrity)
                              (fn-frame-ok (fn-frame-item 0 fields)
                                           (fn-frame-item 1 fields)
                                           (fn-frame-item 2 fields)
                                           (car body)))))))))))))))))

(verify-guards fn-frame-decode
  :hints (("Goal" :in-theory (disable fn-cbor-u32-from
                                      fn-frame-head-fields))))

(defthm fn-frame-decode-payload-octets
  (implies (fn-frame-result-okp (fn-frame-decode octets digest max-payload))
           (fn-cbor-octet-listp
            (fn-frame-result-payload (fn-frame-decode octets digest
                                                      max-payload))))
  :hints (("Goal" :in-theory (disable fn-cbor-u32-from
                                      fn-frame-head-fields))))

(defun fn-frame-protected-prefix (octets)
  ; Everything a trailer covers: the frame minus its last 32 octets.
  (declare (xargs :guard (fn-cbor-octet-listp octets) :verify-guards nil))
  (let ((split (fn-frame-split
                (nfix (- (len octets) *fn-frame-trailer-octets*)) octets)))
    (if (null split) nil (car split))))

(verify-guards fn-frame-protected-prefix)

(defun fn-frame-open (octets max-payload)
  ; The specification decoder, stated against A-CRYPTO.  Not executable.
  (declare (xargs :guard (fn-cbor-octet-listp octets)))
  (fn-frame-decode octets
                   (fn-frame-digest (fn-frame-protected-prefix octets))
                   max-payload))

; -----------------------------------------------------------------------------
; Export theory.
;
; The record lemmas of the two results stay enabled; they are the vocabulary
; every book above reasons in.  These seven are shape and bound facts about
; the field grammar, which is proof vocabulary.

(deftheory fn-frame-fields-vocabulary
  '(    fn-frame-enum-index-natp fn-frame-enum-index-bound
    fn-frame-field-parse-rest-octets fn-frame-field-octets-are-octets
    fn-frame-fields-octets-are-octets fn-frame-head-fields-shape
    fn-frame-decode-payload-octets))

(in-theory (disable fn-frame-enum-index-natp fn-frame-enum-index-bound
             fn-frame-field-parse-rest-octets
             fn-frame-field-octets-are-octets
             fn-frame-fields-octets-are-octets fn-frame-head-fields-shape
             fn-frame-decode-payload-octets))
