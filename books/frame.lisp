; fn: the one durable frame grammar, owned by ACL2.
;
; Four Python-only grammars previously decided how a durable byte string was
; framed: FNST (the store transaction file), FNWF (the sender workflow
; journal), FNRJ (the receiver journal) and FNBI (a staged inbound bundle).
; This book replaces all four with a single layout and one pair of functions.
;
;   FRAME := MAGIC(4) VERSION(1) KIND(1) LENGTH(4, big-endian) PAYLOAD(LENGTH)
;            TRAILER(32)
;
; Representation choice: a direct octet layout, not `fn-cbor-*` items.  Two
; reasons, both structural.  First, the frame's job is to bound the payload
; before anything allocates; building it on the CBOR decoder would make that
; bound depend on the very parser the frame exists to protect, and the store
; payload is itself a CBOR record, so the frame would parse its own contents.
; Second, a fixed-width big-endian field has exactly one encoding of each
; accepted value, so canonicality here is structural rather than a rejected
; alternative form: `fn-frame-encode-of-decode` is proved, not assumed.  The
; CBOR primitives are still reused for the octet recognizers, for the
; big-endian conversions, and for the cons-bounded preflight.
;
; FNWF and FNRJ frames under this grammar are byte-identical to the Python
; frames they replace.  FNST gains the kind octet it lacked (the store config
; format moves to `fn-store-experiment-3`) and FNBI moves its BID length into
; a payload text field.
;
; The 32-octet trailer is SHA-256 in deployment.  ACL2 does not compute it:
; `fn-frame-digest` is a constrained function whose only constraints are its
; output shape, recorded as A-CRYPTO.  The host supplies candidate digest
; octets and ACL2 owns every other frame decision, including the comparison.
; `fn-frame-seal` and `fn-frame-open` state the specification against the
; constrained function; `fn-frame-encode` and `fn-frame-decode` are what the
; host calls, and the theorems relating them name `fn-frame-digest` and its
; hypothesis explicitly.
(in-package "ACL2")
(include-book "frame-journal")
(local (include-book "arithmetic/top" :dir :system))

(local (in-theory (enable fn-cbor-invariants-vocabulary
                          fn-frame-octet-vocabulary
                          fn-frame-fields-vocabulary
                          fn-frame-journal-vocabulary)))

; The canonical primary-block identity of a staged inbound bundle, as
; `books/bp-primary.lisp` encodes it: a CBOR array of an endpoint ID and three
; or five unsigned integers.  The endpoint's scheme-specific part is the only
; unbounded part and that codec caps it at 1024 octets, so this cap leaves
; room for the array and integer heads and still keeps the frame head small
; enough to cross the decimal octet bridge in one call.
(defconst *fn-frame-max-identity* 1152)

; An inbound bundle is up to four mebibytes, which cannot cross the decimal
; octet bridge.  ACL2 still owns every decision about the frame: it builds the
; whole protected prefix through the BID text field, and on the way back in it
; validates magic, version, kind, the declared length, the BID field and the
; trailer.  The host concatenates and compares bytes it never interprets.
(defun fn-frame-inbound-prefix (bid ident bundle-length)
  (declare (xargs :guard t :verify-guards nil))
  (if (not (and (fn-frame-textp bid)
                (fn-frame-blobp ident)
                (<= (len ident) *fn-frame-max-identity*)
                (natp bundle-length)
                (<= (+ 2 (len bid) 4 (len ident) bundle-length)
                    *fn-frame-max-inbound-payload*)))
      :bad
    (let ((fields (append (fn-frame-field-octets :text bid)
                          (fn-frame-field-octets :blob ident))))
      (append (fn-frame-header *fn-frame-magic-inbound* *fn-frame-version*
                               *fn-frame-inbound-kind*
                               (+ (len fields) bundle-length))
              fields))))

(verify-guards fn-frame-inbound-prefix)

(defun fn-frame-inbound-open (head total-length trailer digest)
  ; `head` is a bounded prefix of the stored frame (the host sends at most
  ; header + the two ident fields), `total-length` its whole size, `trailer`
  ; its last 32 octets and `digest` the host's digest over everything but those
  ; 32.  The BID is the transport handle the agent issued; the ident is what
  ; the bundle itself says it is, and the two are returned together so that a
  ; caller cannot read one without the other.
  (declare (xargs :guard t :verify-guards nil))
  (if (not (and (fn-cbor-octet-listp head)
                (fn-cbor-at-mostp head (+ *fn-frame-header-octets* 2
                                          *fn-frame-max-text* 4
                                          *fn-frame-max-identity*))
                (natp total-length)
                (fn-frame-digestp trailer)
                (fn-frame-digestp digest)))
      (fn-frame-error :malformed)
    (if (not (equal trailer digest))
        (fn-frame-error :integrity)
      (let ((split (fn-frame-split *fn-frame-header-octets* head)))
        (if (null split)
            (fn-frame-error :truncated)
          (let ((fields (fn-frame-head-fields (car split))))
            (if (null fields)
                (fn-frame-error :truncated)
              (if (not (and (equal (fn-frame-item 0 fields)
                                   *fn-frame-magic-inbound*)
                            (equal (fn-frame-item 1 fields) *fn-frame-version*)
                            (equal (fn-frame-item 2 fields)
                                   *fn-frame-inbound-kind*)))
                  (fn-frame-error :magic)
                (let ((declared (nfix (fn-cbor-u32-from
                                       (fn-frame-item 3 fields)))))
                  (if (< *fn-frame-max-inbound-payload* declared)
                      (fn-frame-error :limit)
                    (if (not (equal total-length
                                    (+ *fn-frame-overhead-octets* declared)))
                        ; Same distinction as `fn-frame-decode`: fewer octets
                        ; than the header declares is truncation.
                        (if (< total-length
                               (+ *fn-frame-overhead-octets* declared))
                            (fn-frame-error :truncated)
                          (fn-frame-error :length))
                      (let ((parsed (fn-frame-field-parse :text (cdr split))))
                        (if (not (fn-frame-parse-okp parsed))
                            (fn-frame-error :field-length)
                          (let ((blob (fn-frame-field-parse
                                         :blob (fn-frame-parse-rest parsed))))
                            (if (not (fn-frame-parse-okp blob))
                                (fn-frame-error :field-length)
                              (let ((bid (fn-frame-parse-value parsed))
                                    (ident (fn-frame-parse-value blob)))
                                (if (< *fn-frame-max-identity* (len ident))
                                    (fn-frame-error :limit)
                                  (if (< declared
                                         (+ 2 (len bid) 4 (len ident)))
                                      (fn-frame-error :length)
                                    (fn-frame-ok
                                     *fn-frame-magic-inbound*
                                     *fn-frame-version*
                                     (list bid ident)
                                     (- declared
                                        (+ 2 (len bid)
                                           4 (len ident))))))))))))))))))))))

(verify-guards fn-frame-inbound-open
  :hints (("Goal" :in-theory (disable fn-cbor-u16-from fn-cbor-u32-from
                                      fn-frame-head-fields))))

; -----------------------------------------------------------------------------
; Protected prefixes
;
; The host computes the trailer, so it needs the exact octets the trailer
; covers.  These return that prefix; appending 32 digest octets to it is
; `fn-frame-encode`, which `fn-frame-*-encode-is-protected-plus-digest` in
; `frame-invariants` proves.  No other part of the frame is the host's.

(defun fn-frame-store-protected (record)
  (declare (xargs :guard t :verify-guards nil))
  (if (or (not (fn-cbor-octet-listp record))
          (not (fn-cbor-at-mostp record *fn-frame-max-store-payload*)))
      :bad
    (fn-frame-protected *fn-frame-magic-store* *fn-frame-version*
                        *fn-frame-store-kind* record)))

(verify-guards fn-frame-store-protected)

(defun fn-frame-workflow-protected (kind values)
  (declare (xargs :guard t :verify-guards nil))
  (if (not (fn-frame-workflow-record-okp kind values))
      :bad
    (let ((code (fn-frame-enum-index kind *fn-frame-workflow-kinds*))
          (payload (fn-frame-fields-octets
                    (fn-frame-spec-for kind *fn-frame-workflow-specs*) values)))
      (if (or (equal code 0)
              (not (fn-cbor-at-mostp payload *fn-frame-max-workflow-payload*)))
          :bad
        (fn-frame-protected *fn-frame-magic-workflow* *fn-frame-version* code
                            payload)))))

(verify-guards fn-frame-workflow-protected)

(defun fn-frame-receipt-protected (kind values)
  (declare (xargs :guard t :verify-guards nil))
  (if (not (fn-frame-receipt-record-okp kind values))
      :bad
    (let ((code (fn-frame-enum-index kind *fn-frame-receipt-kinds*))
          (payload (fn-frame-fields-octets
                    (fn-frame-spec-for kind *fn-frame-receipt-specs*) values)))
      (if (or (equal code 0)
              (not (fn-cbor-at-mostp payload *fn-frame-max-receipt-payload*)))
          :bad
        (fn-frame-protected *fn-frame-magic-receipt* *fn-frame-version* code
                            payload)))))

(verify-guards fn-frame-receipt-protected)

; -----------------------------------------------------------------------------
; The field names a host uses to label a decoded record
;
; The names are presentation only; the grammar above decides every byte.  They
; live here so that no adapter keeps its own ordered field list: the host asks
; for the names and the specification together, and `frame-tests` checks that
; the two lists have the same length for every kind.

(defconst *fn-frame-workflow-field-names*
  (list
   (cons :config '("local-eid" "peer-eid" "policy-id" "receipt-authority"
                   "bp-lifetime" "incarnation" "authorization-context"))
   (cons :enqueue '("txid" "tx-generation" "work-id" "msgid"
                    "immutable-subject" "archive-obligation-id"
                    "forward-obligation-id" "peer-eid" "policy-id" "terms-id"))
   (cons :attempt '("txid" "tx-generation" "work-id" "attempt-id"
                    "attempt-generation" "local-eid" "peer-eid" "policy-id"
                    "bp-lifetime"))
   (cons :transport '("work-id" "attempt-id" "attempt-generation" "status"))
   (cons :receipt-intent '("txid" "tx-generation" "receipt-id" "work-id"
                           "immutable-subject" "issuer-eid" "peer-eid"
                           "policy-id" "incarnation" "authorization-context"
                           "terms-id"))
   (cons :outcome '("txid" "tx-generation" "phase" "result"))
   (cons :retry-request '("work-id" "attempt-id" "attempt-generation"
                          "policy-id"))))

(defconst *fn-frame-receipt-field-names*
  (list
   (cons :config '("destination-eid" "policy-id" "issuer-eid"))
   (cons :request-context '("inbound-bid" "request-adu" "store-record"
                            "policy-authorized"))
   (cons :request-intent '("inbound-bid" "request-adu"
                           "owner-config-generation" "owner-next-txid"
                           "application-result"))
   (cons :request-context-v2 '("inbound-bid" "request-adu" "store-record"
                               "owner-config-generation" "store-txid"
                               "store-generation" "policy-authorized"
                               "application-result"))
   (cons :receipt-intent '("work-id" "receipt-id" "receipt-adu"
                           "policy-authorized"))
   (cons :receipt-decision '("work-id" "receipt-id" "outcome"))))

; -----------------------------------------------------------------------------
; Export theory for the whole frame cluster.
;
; Enabled on include: the record lemmas of the two results, the keystones
; (`fn-frame-decode-of-encode', `fn-frame-encode-of-decode' and the journal
; round trips live in `frame-invariants'), and the recursive list vocabulary.
; Withdrawn: the splitter shape rules that backchain into `len' and `consp',
; which cost `frame-invariants' 108 s on one `append' goal and
; `identity-invariants' 619 s before they were disabled by hand
; (planning/lanes/LANEDUMP-twins-into-acl2.md, 3.1b); the result accessors and
; constructors; and the grammar itself.  A book that must open one of these
; enables the vocabulary it names and says why.

(deftheory fn-frame-record-vocabulary
  '(    (:d fn-frame-parse-shapep) (:d fn-frame-parse-ok)
    (:d fn-frame-parse-error) (:d fn-frame-parse-okp)
    (:d fn-frame-parse-value) (:d fn-frame-parse-rest)
    (:d fn-frame-result-shapep) (:d fn-frame-ok) (:d fn-frame-error)
    (:d fn-frame-result-okp) (:d fn-frame-result-magic)
    (:d fn-frame-result-version) (:d fn-frame-result-kind)
    (:d fn-frame-result-payload)))

(deftheory fn-frame-codec-vocabulary
  '(    (:d fn-frame-digestp) (:d fn-frame-magicp) (:d fn-frame-textp)
    (:d fn-frame-blobp) (:d fn-frame-natp) (:d fn-frame-enum-specp)
    (:d fn-frame-specp) (:d fn-frame-spec-listp) (:d fn-frame-field-okp)
    (:d fn-frame-field-octets) (:d fn-frame-field-parse)
    (:d fn-frame-parse-counted) (:d fn-frame-values-okp)
    (:d fn-frame-fields-octets) (:d fn-frame-fields-parse-aux)
    (:d fn-frame-fields-parse) (:d fn-frame-header) (:d fn-frame-inputp)
    (:d fn-frame-protected) (:d fn-frame-encode) (:d fn-frame-seal)
    (:d fn-frame-head-fields) (:d fn-frame-decode)
    (:d fn-frame-protected-prefix) (:d fn-frame-open)
    (:d fn-frame-spec-for) (:d fn-frame-outcome-pairp)
    (:d fn-frame-workflow-record-okp) (:d fn-frame-receipt-record-okp)
    (:d fn-frame-store-encode) (:d fn-frame-store-decode)
    (:d fn-frame-workflow-encode) (:d fn-frame-workflow-decode)
    (:d fn-frame-receipt-encode) (:d fn-frame-receipt-decode)
    (:d fn-frame-inbound-prefix) (:d fn-frame-inbound-open)
    (:d fn-frame-store-protected) (:d fn-frame-workflow-protected)
    (:d fn-frame-receipt-protected)))

(in-theory (disable (:d fn-frame-parse-shapep) (:d fn-frame-parse-ok)
             (:d fn-frame-parse-error) (:d fn-frame-parse-okp)
             (:d fn-frame-parse-value) (:d fn-frame-parse-rest)
             (:d fn-frame-result-shapep) (:d fn-frame-ok)
             (:d fn-frame-error) (:d fn-frame-result-okp)
             (:d fn-frame-result-magic) (:d fn-frame-result-version)
             (:d fn-frame-result-kind) (:d fn-frame-result-payload)))

(in-theory (disable (:d fn-frame-digestp) (:d fn-frame-magicp)
             (:d fn-frame-textp) (:d fn-frame-blobp) (:d fn-frame-natp)
             (:d fn-frame-enum-specp) (:d fn-frame-specp)
             (:d fn-frame-spec-listp) (:d fn-frame-field-okp)
             (:d fn-frame-field-octets) (:d fn-frame-field-parse)
             (:d fn-frame-parse-counted) (:d fn-frame-values-okp)
             (:d fn-frame-fields-octets) (:d fn-frame-fields-parse-aux)
             (:d fn-frame-fields-parse) (:d fn-frame-header)
             (:d fn-frame-inputp) (:d fn-frame-protected)
             (:d fn-frame-encode) (:d fn-frame-seal)
             (:d fn-frame-head-fields) (:d fn-frame-decode)
             (:d fn-frame-protected-prefix) (:d fn-frame-open)
             (:d fn-frame-spec-for) (:d fn-frame-outcome-pairp)
             (:d fn-frame-workflow-record-okp)
             (:d fn-frame-receipt-record-okp) (:d fn-frame-store-encode)
             (:d fn-frame-store-decode) (:d fn-frame-workflow-encode)
             (:d fn-frame-workflow-decode) (:d fn-frame-receipt-encode)
             (:d fn-frame-receipt-decode) (:d fn-frame-inbound-prefix)
             (:d fn-frame-inbound-open) (:d fn-frame-store-protected)
             (:d fn-frame-workflow-protected)
             (:d fn-frame-receipt-protected)))
