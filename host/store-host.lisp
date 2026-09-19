; Trusted bounded marshalling helpers for the composed store bridge.
; Stateful acceptance/recovery/completion live only in store-node-host.lisp.
; No untrusted input is read as Lisp: the process interface supplies decimal
; octets and fixed operation names after Python boundary validation.
;
; Every decision this file used to share with Python now has one owner in a
; certified book: framing and the integrity trailer comparison in
; `books/frame`, content identity and the charge policy in `books/identity`,
; the group table in `books/store-config`, and the Message-ID grammar in
; `books/article-fields`.  The wrappers below only marshal.

(in-package "ACL2")
(include-book "../books/replay")
(include-book "../books/store-config")
(include-book "../books/identity")
(include-book "../books/article-fields")

(defconst *fn-store-capacity* 1048576)

(defconst *fn-store-max-text* 512)

(defconst *fn-store-max-payload* 32768)

(defun fn-store-text-octetsp-tail (xs)
  (if (consp xs)
      (and (fn-octetp (car xs)) (<= 33 (car xs)) (<= (car xs) 126)
           (fn-store-text-octetsp-tail (cdr xs)))
    (null xs)))

(defun fn-store-text-octetsp (xs)
  (and (consp xs)
       (<= (len xs) *fn-store-max-text*)
       (fn-octet-listp xs)
       (<= 33 (car xs)) (<= (car xs) 126)
       (fn-store-text-octetsp-tail (cdr xs))))

; One Message-ID bound for the whole system.  `books/article-fields` owns the
; RFC 5536 section 3.1.3 grammar and its 250-octet limit; this wrapper adds
; nothing and subtracts nothing.
(defun fn-store-msgid-octetsp (xs)
  (fn-af-message-idp xs))

(defun fn-store-octets->string (xs)
  (fn-record-octets-string xs))

(defun fn-store-decode-records (octet-records)
  (declare (xargs :mode :program))
  (if (consp octet-records)
      (let ((decoded (fn-record-decode-exact (car octet-records))))
        (if (and (consp decoded) (equal (car decoded) :ok)
                 (consp (cdr decoded)) (fn-record-p (car (cdr decoded))))
            (let ((rest (fn-store-decode-records (cdr octet-records))))
              (if (equal rest :bad) :bad (cons (car (cdr decoded)) rest)))
          :bad))
    (if (null octet-records) nil :bad)))

(defun fn-store-record-sequence (octets)
  (declare (xargs :mode :program))
  (let ((decoded (fn-record-decode-exact octets)))
    (if (and (consp decoded) (equal (car decoded) :ok)
             (consp (cdr decoded)) (fn-record-p (car (cdr decoded))))
        (fn-record-sequence (car (cdr decoded)))
      -1)))

(defun fn-store-record-txid (octets)
  (declare (xargs :mode :program))
  (let ((decoded (fn-record-decode-exact octets)))
    (if (and (consp decoded) (equal (car decoded) :ok)
             (consp (cdr decoded)) (fn-record-p (car (cdr decoded))))
        (fn-record-txid (car (cdr decoded)))
      -1)))

(defun fn-store-article-match (msgid payload groups node)
  (let ((article (fn-find-article msgid
                                  (fn-state-articles (fn-node-acceptance node)))))
    (if article
        (if (and (equal payload (fn-article-payload article))
                 (equal groups (fn-article-groups article)))
            :duplicate
          :conflict)
      nil)))

; -----------------------------------------------------------------------------
; Frame bridge
;
; Python supplies octets and the SHA-256 digest of the protected prefix
; (A-CRYPTO); ACL2 supplies magic, version, kind, the length field, every
; bound and the trailer comparison.  Encoders answer an octet list or :bad;
; decoders answer (:ok ...) or (:error reason), so a refusal reaches Python
; with its reason rather than as an absence.

(defun fn-store-frame-constants ()
  ; The layout numbers Python needs in order to slice a file it does not
  ; interpret: header, trailer and total overhead, then the per-schema caps.
  (list *fn-frame-header-octets* *fn-frame-trailer-octets*
        *fn-frame-overhead-octets* *fn-frame-max-store-payload*
        *fn-frame-max-workflow-payload* *fn-frame-max-receipt-payload*
        *fn-frame-max-inbound-payload* *fn-frame-max-text*
        *fn-frame-max-blob* *fn-frame-max-identity*))

(defun fn-store-frame-result (frame)
  ; (:ok payload) or (:error reason) for a frame whose payload is opaque.
  (if (fn-frame-result-okp frame)
      (list :ok (fn-frame-result-payload frame))
    frame))

(defun fn-store-frame-record-result (frame)
  ; (:ok kind values) or (:error reason) for a journal record.
  (if (fn-frame-result-okp frame)
      (list :ok (fn-frame-result-kind frame) (fn-frame-result-payload frame))
    frame))

(defun fn-store-frame-store-protected (record)
  (fn-frame-store-protected record))

(defun fn-store-frame-workflow-protected (kind values)
  (fn-frame-workflow-protected kind values))

(defun fn-store-frame-receipt-protected (kind values)
  (fn-frame-receipt-protected kind values))

(defun fn-store-frame-names-octets (names)
  (if (consp names)
      (cons (fn-record-string-octets (car names))
            (fn-store-frame-names-octets (cdr names)))
    nil))

(defun fn-store-frame-schema (kind names-table spec-table)
  ; (:ok (field-name-octets ...) (field-specification ...)) or (:error :kind).
  (let ((names (fn-frame-spec-for kind names-table))
        (spec (fn-frame-spec-for kind spec-table)))
    (if (or (equal names :none) (equal spec :none))
        (list :error :kind)
      (list :ok (fn-store-frame-names-octets names) spec))))

(defun fn-store-frame-workflow-schema (kind)
  (fn-store-frame-schema kind *fn-frame-workflow-field-names*
                         *fn-frame-workflow-specs*))

(defun fn-store-frame-receipt-schema (kind)
  (fn-store-frame-schema kind *fn-frame-receipt-field-names*
                         *fn-frame-receipt-specs*))

(defun fn-store-frame-workflow-kinds ()
  *fn-frame-workflow-kinds*)

(defun fn-store-frame-receipt-kinds ()
  *fn-frame-receipt-kinds*)

(defun fn-store-frame-store-encode (record digest)
  (fn-frame-store-encode record digest))

(defun fn-store-frame-store-decode (octets digest)
  (fn-store-frame-result (fn-frame-store-decode octets digest)))

(defun fn-store-frame-workflow-encode (kind values digest)
  (fn-frame-workflow-encode kind values digest))

(defun fn-store-frame-workflow-decode (octets digest)
  (fn-store-frame-record-result (fn-frame-workflow-decode octets digest)))

(defun fn-store-frame-receipt-encode (kind values digest)
  (fn-frame-receipt-encode kind values digest))

(defun fn-store-frame-receipt-decode (octets digest)
  (fn-store-frame-record-result (fn-frame-receipt-decode octets digest)))

(defun fn-store-frame-inbound-prefix (bid identity bundle-length)
  (fn-frame-inbound-prefix bid identity bundle-length))

(defun fn-store-frame-inbound-open (head total-length trailer digest)
  (let ((frame (fn-frame-inbound-open head total-length trailer digest)))
    (if (fn-frame-result-okp frame)
        ; kind slot carries (BID identity), payload slot the bundle length.
        (list :ok (car (fn-frame-result-kind frame))
              (car (cdr (fn-frame-result-kind frame)))
              (fn-frame-result-payload frame))
      frame)))

; -----------------------------------------------------------------------------
; Identity, charge and group bridge

(defun fn-store-subject-id (digest)
  (if (fn-id-digestp digest) (fn-id-subject digest) nil))

(defun fn-store-obligation-preimage (msgid subject)
  (if (and (fn-cbor-octet-listp msgid) (fn-cbor-octet-listp subject))
      (fn-id-obligation-preimage msgid subject)
    nil))

(defun fn-store-obligation-id (digest)
  (if (fn-id-digestp digest) (fn-id-obligation digest) nil))

(defun fn-store-charge (length)
  (if (natp length) (fn-charge-for-payload length) 0))

(defun fn-store-msgid-validp (octets)
  (if (fn-store-msgid-octetsp octets) t nil))

(defun fn-store-group-name-octets (groups)
  (if (consp groups)
      (cons (fn-record-string-octets (car groups))
            (fn-store-group-name-octets (cdr groups)))
    nil))

(defun fn-store-group-names ()
  ; The configured group list as octets, for the one call Python makes at open.
  (fn-store-group-name-octets *fn-store-groups*))

(defun fn-store-group-table-id ()
  *fn-store-group-table-id*)

(defun fn-store-octet-lists->strings (xs)
  (if (consp xs)
      (if (not (fn-cbor-octet-listp (car xs)))
          :bad
        (let ((rest (fn-store-octet-lists->strings (cdr xs))))
          (if (equal rest :bad)
              :bad
            (cons (fn-store-octets->string (car xs)) rest))))
    (if (null xs) nil :bad)))

(defun fn-store-group-codes (name-octets)
  ; Distinct configured group names, given as octet lists, become codes.
  (let ((names (fn-store-octet-lists->strings name-octets)))
    (if (equal names :bad)
        :bad
      (fn-store-codes-from-groups names))))

; The whole POST admission boundary in one call.  Every bound it applies has
; one owner: the Message-ID grammar is `books/article-fields`, the payload cap
; is this file's configured maximum, the group count is the record codec's
; `*fn-record-max-groups*` and the charge range is the record codec's uint32
; field.  Python no longer restates any of them.
(defun fn-store-post-boundary (msgid payload-length group-count charge)
  (if (not (fn-store-msgid-octetsp msgid))
      :bad-message-id
    (if (or (not (natp payload-length))
            (< *fn-store-max-payload* payload-length))
        :payload-bound
      (if (or (not (posp group-count))
              (< *fn-record-max-groups* group-count))
          :group-bound
        (if (or (not (posp charge)) (< *fn-cbor-max-uint* charge))
            :charge-bound
          :ok)))))
