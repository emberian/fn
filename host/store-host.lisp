; Trusted bounded marshalling helpers for the composed store bridge.
; Stateful acceptance/recovery/completion live only in store-node-host.lisp.
; No untrusted input is read as Lisp: the process interface supplies decimal
; octets and fixed operation names after Python boundary validation.
;
; Every decision this file used to share with Python now has one owner in a
; certified book: framing and the integrity trailer comparison in
; `books/frame`, content identity and the charge policy in `books/identity`,
; the group table in the store's replayed configuration (`books/config`,
; `books/node-config`; `books/store-config` keeps the name/code inversion),
; and the Message-ID grammar in `books/article-fields`.  The wrappers below
; only marshal.

(in-package "ACL2")
(include-book "../books/replay")
(include-book "../books/store-config")
(include-book "../books/identity")
(include-book "../books/crypto-attach")
(include-book "../books/frame-trailer")
(include-book "../books/byte-store-frame")
(include-book "../books/byte-store-txn-name")
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

; The final transaction namespace is an ACL2 value.  The native host consumes
; the string wrapper; the Python bridge consumes octets so no Lisp string
; reader or duplicate decimal formatter sits on its persistence path.
(defun fn-store-txn-name (sequence)
  (if (natp sequence) (fn-bs-txn-name sequence) ""))

(defun fn-store-txn-name-octets (sequence)
  (fn-record-string-octets (fn-store-txn-name sequence)))

; A final namespace observation is not parsed by the native adapter.  The
; bounded host enumeration is sorted only to make its representation stable.
; This conversion only validates octets before the scan policy compares names.
(defun fn-store-octet-lists->strings (xs)
  (if (consp xs)
      (if (not (fn-cbor-octet-listp (car xs)))
          :bad
        (let ((rest (fn-store-octet-lists->strings (cdr xs))))
          (if (equal rest :bad)
              :bad
            (cons (fn-store-octets->string (car xs)) rest))))
    (if (null xs) nil :bad)))

(defun fn-store-txn-observation (observed maximum)
  (declare (xargs :mode :program))
  (let ((names (fn-store-octet-lists->strings observed)))
    (if (and (natp maximum) (true-listp observed)
             (not (equal names :bad)) (<= (len names) maximum))
        ;; The byte-store scan owns exact names and contiguous sequences.
        (fn-bs-txn-observation-pairs names 0)
      :invalid)))

(defun fn-store-txn-observation-selected (observed maximum selected-lower)
  (declare (xargs :mode :program))
  (let ((names (fn-store-octet-lists->strings observed)))
    (if (and (natp maximum) (natp selected-lower) (true-listp observed)
             (not (equal names :bad)) (<= (len names) maximum))
        (fn-bs-txn-observation-selected names selected-lower)
      :invalid)))

(defun fn-store-txn-covered-names (pairs selected-lower)
  (declare (xargs :mode :program))
  (if (consp pairs)
      (if (< (first (car pairs)) selected-lower)
          (cons (second (car pairs))
                (fn-store-txn-covered-names (cdr pairs) selected-lower))
        nil)
    nil))

(defun fn-store-txn-prefix-reclaim-plan (observed maximum selected-lower)
  (declare (xargs :mode :program))
  (let ((names (fn-store-octet-lists->strings observed)))
    (if (and (natp maximum) (natp selected-lower) (true-listp observed)
             (not (equal names :bad)) (<= (len names) maximum)
             (not (equal (fn-bs-txn-observation-selected names selected-lower)
                         :invalid)))
        (let ((pairs (third (fn-bs-txn-observation-selected names selected-lower))))
          (fn-store-txn-covered-names pairs selected-lower))
      :invalid)))

(defun fn-store-decode-records (octet-records)
  (declare (xargs :mode :program))
  (if (consp octet-records)
      (let ((decoded (fn-store-event-decode-exact (car octet-records))))
        (if (and (consp decoded) (equal (car decoded) :ok)
                 (consp (cdr decoded)) (fn-store-event-p (car (cdr decoded))))
            (let ((rest (fn-store-decode-records (cdr octet-records))))
              (if (equal rest :bad) :bad (cons (car (cdr decoded)) rest)))
          :bad))
    (if (null octet-records) nil :bad)))

(defun fn-store-record-sequence (octets)
  (declare (xargs :mode :program))
  (let ((decoded (fn-store-event-decode-exact octets)))
    (if (and (consp decoded) (equal (car decoded) :ok)
             (consp (cdr decoded)) (fn-store-event-p (car (cdr decoded))))
        (fn-store-event-sequence (car (cdr decoded)))
      -1)))

(defun fn-store-record-txid (octets)
  (declare (xargs :mode :program))
  (let ((decoded (fn-store-event-decode-exact octets)))
    (if (and (consp decoded) (equal (car decoded) :ok)
             (consp (cdr decoded)) (fn-store-event-p (car (cdr decoded))))
        (fn-store-event-txid (car (cdr decoded)))
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

; Native application journals hold the logical record values used by
; bp-workflow-records and bp-receipt-records: text fields are ACL2 strings.
; The durable frame grammar holds text octets.  Keep that representation
; conversion here, beside the schema ACL2 owns, instead of copying field
; positions or types into raw Lisp.
(defun fn-store-frame-logical-to-wire-values (spec values)
  (declare (xargs :mode :program))
  (if (and (consp spec) (consp values))
      (cons (if (equal (car spec) :text)
                (if (stringp (car values))
                    (fn-record-string-octets (car values))
                  (car values))
              (if (and (consp (car spec))
                       (equal (cdr (car spec)) *fn-frame-authorized*)
                       (equal (car values) t))
                  :authorized
                (car values)))
            (fn-store-frame-logical-to-wire-values (cdr spec) (cdr values)))
    (if (and (null spec) (null values)) nil :bad)))

(defun fn-store-frame-wire-to-logical-values (spec values)
  (declare (xargs :mode :program))
  (if (and (consp spec) (consp values))
      (cons (if (equal (car spec) :text)
                (fn-record-octets-string (car values))
              (if (and (consp (car spec))
                       (equal (cdr (car spec)) *fn-frame-authorized*)
                       (equal (car values) :authorized))
                  t
                (car values)))
            (fn-store-frame-wire-to-logical-values (cdr spec) (cdr values)))
    (if (and (null spec) (null values)) nil :bad)))

(defun fn-store-frame-workflow-logical-protected (kind values)
  (declare (xargs :mode :program))
  (let ((spec (fn-frame-spec-for kind *fn-frame-workflow-specs*)))
    (if (equal spec :none) :bad
      (fn-frame-workflow-protected
       kind (fn-store-frame-logical-to-wire-values spec values)))))

(defun fn-store-frame-receipt-logical-protected (kind values)
  (declare (xargs :mode :program))
  (let ((spec (fn-frame-spec-for kind *fn-frame-receipt-specs*)))
    (if (equal spec :none) :bad
      (fn-frame-receipt-protected
       kind (fn-store-frame-logical-to-wire-values spec values)))))

(defun fn-store-frame-logical-result (answer table)
  (declare (xargs :mode :program))
  (if (and (consp answer) (equal (car answer) :ok))
      (let* ((kind (car (cdr answer)))
             (values (car (cdr (cdr answer))))
             (spec (fn-frame-spec-for kind table)))
        (if (equal spec :none) (list :error :kind)
          (list :ok kind
                (fn-store-frame-wire-to-logical-values spec values))))
    answer))

(defun fn-store-frame-store-encode (record digest)
  (fn-frame-store-encode record digest))

(defun fn-store-frame-store-decode (octets digest)
  (fn-store-frame-result (fn-frame-store-decode octets digest)))

(defun fn-store-frame-workflow-encode (kind values digest)
  (fn-frame-workflow-encode kind values digest))

(defun fn-store-frame-workflow-decode (octets digest)
  (fn-store-frame-record-result (fn-frame-workflow-decode octets digest)))

(defun fn-store-frame-workflow-logical-decode (octets digest)
  (declare (xargs :mode :program))
  (fn-store-frame-logical-result
   (fn-store-frame-workflow-decode octets digest)
   *fn-frame-workflow-specs*))

(defun fn-store-frame-receipt-encode (kind values digest)
  (fn-frame-receipt-encode kind values digest))

(defun fn-store-frame-receipt-decode (octets digest)
  (fn-store-frame-record-result (fn-frame-receipt-decode octets digest)))

(defun fn-store-frame-receipt-logical-decode (octets digest)
  (declare (xargs :mode :program))
  (fn-store-frame-logical-result
   (fn-store-frame-receipt-decode octets digest)
   *fn-frame-receipt-specs*))

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

; The identity derivation, whole, in logic.
;
; Until books/crypto-attach.lisp existed, `fn-frame-digest' was a constrained
; function with no realiser, so the host had to hash: ACL2 handed back the
; fixed preimage head and Python (tools/frame_bridge.py) or the native host
; (host/native/io.lisp) appended the payload and ran its own SHA-256.  That
; was a second owner for a value ACL2 defines, which AGENTS.md forbids.  The
; two wrappers below derive the identity end to end from the payload, and the
; two prefix/digest wrappers that follow are kept ONLY so an old session
; script does not break; nothing in this tree calls them any more.
(defun fn-store-subject-id-of-payload (payload)
  ; The canonical subject-v1 identity of an article payload, preimage and
  ; digest both in ACL2.  The payload crosses the bridge; see
  ; planning/lanes/HANDOFF-w9-digest.md for the measured cost.
  (if (and (fn-cbor-octet-listp payload)
           (<= (len payload) *fn-cbor-max-uint*))
      (fn-id-subject-of-payload payload)
    nil))

(defun fn-store-obligation-id-of (msgid subject)
  ; The canonical obligation-v1 identity, preimage and digest both in ACL2.
  (if (and (fn-cbor-octet-listp msgid)
           (<= (len msgid) *fn-cbor-max-uint*)
           (fn-cbor-octet-listp subject)
           (<= (len subject) *fn-cbor-max-uint*))
      (fn-id-obligation-of msgid subject)
    nil))

(defun fn-store-subject-prefix (length)
  ; Superseded by fn-store-subject-id-of-payload; retained for compatibility.
  (if (and (natp length) (<= length *fn-cbor-max-uint*))
      (fn-id-subject-prefix length)
    nil))

(defun fn-store-subject-id (digest)
  (if (fn-id-digestp digest) (fn-id-subject digest) nil))

(defun fn-store-obligation-preimage (msgid subject)
  (if (and (fn-cbor-octet-listp msgid)
           (<= (len msgid) *fn-cbor-max-uint*)
           (fn-cbor-octet-listp subject)
           (<= (len subject) *fn-cbor-max-uint*))
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

(defun fn-store-identity-text (identity)
  ; The one rendering of a canonical identity into a string, for the three
  ; boundaries that cannot carry octets: the store record metadata fields, the
  ; workflow journal JSON and the NNTP header value.
  (if (fn-cbor-octet-listp identity) (fn-id-text identity) nil))

(defun fn-store-format-id ()
  *fn-store-format-id*)

; Durable store metadata.  `tools/run_store.py' calls only these wrappers for
; config.json and allocation-frontier.json.  Their grammar, bounds, profile
; table, CBOR frontier encoding, integrity trailer and decoder are all in
; books/byte-store-frame.lisp; this host file only gives the bridge stable
; entry-point names.
(defun fn-store-metadata-config-frame (profile)
  (fn-bs-config-frame-for-profile profile))

(defun fn-store-metadata-config-decode (octets)
  (fn-bs-config-decode octets))

(defun fn-store-metadata-frontier-frame (n)
  (fn-bs-frontier-encode-impl n))

(defun fn-store-metadata-frontier-decode (octets)
  (fn-bs-frontier-decode-impl octets))

(defun fn-store-metadata-frontier-next (n)
  (fn-bs-frontier-next n))

(defun fn-store-publication-admissibility (profile committed-count
                                                   committed-octets
                                                   prospective-payload-octets)
  (if (fn-bs-publication-admissiblep profile committed-count
                                     committed-octets prospective-payload-octets)
      :admissible
    :refused))


(defun fn-store-group-codes (name-octets domain-octets)
  ; Distinct group names, as octet lists, become their codes in the replayed
  ; allocation domain the caller was handed at open (`fn-store-cfg-domain').
  ; Python carries that list back verbatim; it never computes a code.
  (let ((names (fn-store-octet-lists->strings name-octets))
        (domain (fn-store-octet-lists->strings domain-octets)))
    (if (or (equal names :bad) (equal domain :bad))
        :bad
      (fn-store-codes-from-groups names domain))))

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
