; fn frame, part 3 of 4: the journal field grammars.
;
; The four magics, the workflow and receipt field tables, the record
; well-formedness predicates and the concrete entry points the host wrappers
; call.  See `books/frame.lisp' for the layout and the export theory.

(in-package "ACL2")
(include-book "frame-fields")
(local (include-book "arithmetic/top" :dir :system))

(local (in-theory (enable fn-cbor-invariants-vocabulary)))
(local (in-theory (enable fn-frame-octet-vocabulary
                          fn-frame-fields-vocabulary)))

; -----------------------------------------------------------------------------
; Whole records: a kind selects a field specification, and a frame carries the
; encoded fields.  The two journal schemas below are the ones the durable
; adapters use; the store frame's payload is an opaque CBOR record and needs
; no field specification.

(defconst *fn-frame-magic-store* '(70 78 83 84))    ; FNST
(defconst *fn-frame-magic-workflow* '(70 78 87 70)) ; FNWF
(defconst *fn-frame-magic-receipt* '(70 78 82 74))  ; FNRJ
(defconst *fn-frame-magic-inbound* '(70 78 66 73))  ; FNBI
(defconst *fn-frame-magic-bundle-store* '(70 78 66 83)) ; FNBS

(defconst *fn-frame-version* 1)

(defconst *fn-frame-store-kind* 1)
(defconst *fn-frame-inbound-kind* 1)

; The physical FNST ceiling: the frame LENGTH field's u32 width.  It is not a
; bound on a record: the persisted Store profile's per-record ceiling
; (`fn-bs-profile-record-ceiling', books/byte-store-frame) is, applied before
; publication (`fn-bs-publication-admissiblep') and at open, where the host
; reads each transaction file in one bounded read of that ceiling plus the
; frame overhead (host/native/io.lisp `fnn-durable-records').
(defconst *fn-frame-max-store-payload* 4294967295)
(defconst *fn-frame-max-workflow-payload* 16342)
(defconst *fn-frame-max-receipt-payload* 269958)
; The BP inbound journal's physical ceiling, the u32 LENGTH width; the
; bundle's own bound is the BP layer's (books/bp-bundle.lisp).
(defconst *fn-frame-max-inbound-payload* 4294967295)
(defconst *fn-frame-max-bundle-store-payload* 8)

(defconst *fn-frame-transport-statuses*
  '(:intent :bpa-submit-replied :bpa-accepted :attempted :forwarded
    :delivered :deleted :expired :unknown :no-contact :inbound-persisted
    :dequeued :restart-observed))
(defconst *fn-frame-phases* '(:ordinary :recovery))
(defconst *fn-frame-results* '(:durable :aborted :committed :absent))
(defconst *fn-frame-receipt-outcomes* '(:committed :absent))
(defconst *fn-frame-authorized* '(:authorized))
(defconst *fn-frame-application-results* '(:accepted :duplicate))

(defconst *fn-frame-workflow-kinds*
  '(:config :enqueue :attempt :transport :receipt-intent :outcome
    :retry-request :undertake :release :ion-route :ion-observed))

(defconst *fn-frame-workflow-specs*
  (list
   (cons :config '(:text :text :text :text :nat :text :text))
   (cons :enqueue '(:nat :nat :text :text :text :text :text :text :text :text))
   (cons :attempt '(:nat :nat :text :text :nat :text :text :text :nat))
   (cons :transport
         (list :text :text :nat (cons :enum *fn-frame-transport-statuses*)))
   (cons :receipt-intent
         '(:nat :nat :text :text :text :text :text :text :text :text :text))
   (cons :outcome
         (list :nat :nat (cons :enum *fn-frame-phases*)
               (cons :enum *fn-frame-results*)))
   (cons :retry-request '(:text :text :nat :text))
   ; Append-only kinds: the seven existing FNWF codes retain their bytes.
   (cons :undertake '(:text :nat))
   (cons :release '(:text :text :text :text :text :text :text))
   (cons :ion-route '(:text :text :nat :text :text :text))
   (cons :ion-observed '(:text :text :nat :text :text :text :nat :nat))))

(defconst *fn-frame-receipt-kinds*
  ; Append-only: the first four codes are the deployed version-1 FNRJ
  ; vocabulary.  Native application ingress adds intent/context-v2 without
  ; changing any legacy code or byte string.
  '(:config :request-context :receipt-intent :receipt-decision
    :request-intent :request-context-v2
    :request-transit-intent :request-transit-context))

(defconst *fn-frame-receipt-specs*
  (list
   (cons :config '(:text :text :text))
   (cons :request-context
         (list :text :blob :blob (cons :enum *fn-frame-authorized*)))
   (cons :request-intent
         (list :text :blob :nat :nat
               (cons :enum *fn-frame-application-results*)))
   (cons :request-context-v2
         (list :text :blob :blob :nat :nat :nat
               (cons :enum *fn-frame-authorized*)
               (cons :enum *fn-frame-application-results*)))
   (cons :request-transit-intent
         (list :text :blob :nat :nat
               (cons :enum *fn-frame-application-results*)
               :text :text :text :blob))
   (cons :request-transit-context
         (list :text :blob :blob :nat :nat :nat
               (cons :enum *fn-frame-application-results*)))
   (cons :receipt-intent
         (list :text :text :blob (cons :enum *fn-frame-authorized*)))
   (cons :receipt-decision
         (list :text :text (cons :enum *fn-frame-receipt-outcomes*)))))

; FNBS is deliberately narrow in this packet.  It carries the durable creation
; sequence frontier and no bundle lifecycle record: the latter belongs to the
; still-open fn-bpn-step machine in specs/bp-design.md section 1.5.
(defconst *fn-frame-bundle-store-kinds* '(:sequence))
(defconst *fn-frame-bundle-store-specs* (list (cons :sequence '(:nat))))

(defun fn-frame-spec-for (kind table)
  (declare (xargs :guard t))
  (if (consp table)
      (if (and (consp (car table)) (equal (car (car table)) kind))
          (cdr (car table))
        (fn-frame-spec-for kind (cdr table)))
    :none))

(defthm fn-frame-spec-for-workflow-is-spec-list
  (implies (not (equal (fn-frame-spec-for kind *fn-frame-workflow-specs*) :none))
           (fn-frame-spec-listp
            (fn-frame-spec-for kind *fn-frame-workflow-specs*))))

(defthm fn-frame-spec-for-receipt-is-spec-list
  (implies (not (equal (fn-frame-spec-for kind *fn-frame-receipt-specs*) :none))
           (fn-frame-spec-listp
            (fn-frame-spec-for kind *fn-frame-receipt-specs*))))

(defthm fn-frame-spec-for-bundle-store-is-spec-list
  (implies (not (equal (fn-frame-spec-for kind *fn-frame-bundle-store-specs*) :none))
           (fn-frame-spec-listp
            (fn-frame-spec-for kind *fn-frame-bundle-store-specs*))))

; The outcome record's phase and result are not independent: an ordinary
; outcome is durable or aborted and a recovery outcome is committed or absent.
; Both the encoder and the decoder apply this, so a journal cannot hold a
; combination replay would have to interpret.
(defun fn-frame-outcome-pairp (phase result)
  (declare (xargs :guard t))
  (or (and (equal phase :ordinary)
           (or (equal result :durable) (equal result :aborted)))
      (and (equal phase :recovery)
           (or (equal result :committed) (equal result :absent)))))

(defun fn-frame-workflow-record-okp (kind values)
  (declare (xargs :guard t :verify-guards nil))
  (let ((spec (fn-frame-spec-for kind *fn-frame-workflow-specs*)))
    (and (not (equal spec :none))
         (fn-frame-values-okp spec values)
         (or (not (equal kind :outcome))
             (fn-frame-outcome-pairp (fn-frame-item 2 values)
                                     (fn-frame-item 3 values))))))

(verify-guards fn-frame-workflow-record-okp)

(defun fn-frame-receipt-record-okp (kind values)
  (declare (xargs :guard t :verify-guards nil))
  (let ((spec (fn-frame-spec-for kind *fn-frame-receipt-specs*)))
    (and (not (equal spec :none))
         (fn-frame-values-okp spec values))))

(verify-guards fn-frame-receipt-record-okp)

; What an entry point's guard reads of a well-formed record: its kind's
; specification is a spec list and its values satisfy it.  The table lookup
; and the field recognizer stay closed behind these, so a guard does not
; unroll every kind's field list (`fn-frame-workflow-encode' did: 7.3 million
; steps, 37 s).  Disabled on export below; a proof names them.
(defthm fn-frame-workflow-record-okp-fields
  (implies (fn-frame-workflow-record-okp kind values)
           (and (fn-frame-spec-listp
                 (fn-frame-spec-for kind *fn-frame-workflow-specs*))
                (fn-frame-values-okp
                 (fn-frame-spec-for kind *fn-frame-workflow-specs*) values)))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (e/d (fn-frame-workflow-record-okp
                                   fn-frame-spec-for-workflow-is-spec-list)
                                  (fn-frame-spec-for fn-frame-values-okp
                                   fn-frame-spec-listp)))))

(defthm fn-frame-receipt-record-okp-fields
  (implies (fn-frame-receipt-record-okp kind values)
           (and (fn-frame-spec-listp
                 (fn-frame-spec-for kind *fn-frame-receipt-specs*))
                (fn-frame-values-okp
                 (fn-frame-spec-for kind *fn-frame-receipt-specs*) values)))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (e/d (fn-frame-receipt-record-okp
                                   fn-frame-spec-for-receipt-is-spec-list)
                                  (fn-frame-spec-for fn-frame-values-okp
                                   fn-frame-spec-listp)))))

; The encoded length of a well-formed record, for the guard's
; `(<= (len payload) *fn-cbor-max-uint*)': no field encodes to more than a
; blob's four length octets and its cap, and no workflow kind has more than
; eleven fields.
(local (defthm fn-frame-field-octets-length-bound
  (implies (fn-frame-field-okp spec value)
           (<= (len (fn-frame-field-octets spec value))
               (+ 4 *fn-frame-max-blob*)))
  :rule-classes :linear
  :hints (("Goal" :in-theory (enable fn-frame-field-okp fn-frame-field-octets
                                     fn-frame-textp fn-frame-blobp)))))

(local (defthm fn-frame-fields-octets-length-bound
  (implies (fn-frame-values-okp specs values)
           (<= (len (fn-frame-fields-octets specs values))
               (* (+ 4 *fn-frame-max-blob*) (len specs))))
  :rule-classes :linear
  :hints (("Goal" :induct (fn-frame-values-okp specs values)
           :in-theory (disable fn-frame-field-octets fn-frame-field-okp)))))

(local (defthm fn-frame-spec-for-workflow-length
  (<= (len (fn-frame-spec-for kind *fn-frame-workflow-specs*)) 11)
  :rule-classes :linear))

(defun fn-frame-bundle-store-record-okp (kind values)
  (declare (xargs :guard t :verify-guards nil))
  (let ((spec (fn-frame-spec-for kind *fn-frame-bundle-store-specs*)))
    (and (not (equal spec :none))
         (fn-frame-values-okp spec values))))

(verify-guards fn-frame-bundle-store-record-okp)

(defun fn-frame-bundle-store-protected (kind values)
  (declare (xargs :guard t :verify-guards nil))
  (if (not (fn-frame-bundle-store-record-okp kind values))
      :bad
    (let ((code (fn-frame-enum-index kind *fn-frame-bundle-store-kinds*))
          (payload (fn-frame-fields-octets
                    (fn-frame-spec-for kind *fn-frame-bundle-store-specs*) values)))
      (if (or (equal code 0)
              (not (fn-cbor-at-mostp payload *fn-frame-max-bundle-store-payload*)))
          :bad
        (fn-frame-protected *fn-frame-magic-bundle-store* *fn-frame-version* code
                            payload)))))

(verify-guards fn-frame-bundle-store-protected)

; -----------------------------------------------------------------------------
; The concrete entry points the host wrappers call

(defun fn-frame-store-encode (record digest)
  (declare (xargs :guard t :verify-guards nil))
  (if (or (not (fn-cbor-octet-listp record))
          (not (fn-cbor-at-mostp record *fn-frame-max-store-payload*))
          (not (fn-frame-digestp digest)))
      :bad
    (fn-frame-encode *fn-frame-magic-store* *fn-frame-version*
                     *fn-frame-store-kind* record digest)))

(verify-guards fn-frame-store-encode)

(defun fn-frame-store-decode (octets digest)
  (declare (xargs :guard t))
  (let ((frame (fn-frame-decode octets digest *fn-frame-max-store-payload*)))
    (if (not (fn-frame-result-okp frame))
        frame
      (if (not (and (equal (fn-frame-result-magic frame) *fn-frame-magic-store*)
                    (equal (fn-frame-result-version frame) *fn-frame-version*)
                    (equal (fn-frame-result-kind frame) *fn-frame-store-kind*)))
          (fn-frame-error :magic)
        frame))))

(defun fn-frame-workflow-encode (kind values digest)
  (declare (xargs :guard t :verify-guards nil))
  (if (not (and (fn-frame-workflow-record-okp kind values)
                (fn-frame-digestp digest)))
      :bad
    (let ((code (fn-frame-enum-index kind *fn-frame-workflow-kinds*)))
      (if (equal code 0)
          :bad
        (fn-frame-encode *fn-frame-magic-workflow* *fn-frame-version* code
                         (fn-frame-fields-octets
                          (fn-frame-spec-for kind *fn-frame-workflow-specs*)
                          values)
                         digest)))))

(verify-guards fn-frame-workflow-encode
  :hints (("Goal" :in-theory (e/d (fn-frame-workflow-record-okp-fields)
                                  (fn-frame-workflow-record-okp
                                   fn-frame-spec-for fn-frame-values-okp
                                   fn-frame-fields-octets)))))

(defun fn-frame-workflow-decode (octets digest)
  (declare (xargs :guard t :verify-guards nil))
  (let ((frame (fn-frame-decode octets digest
                                *fn-frame-max-workflow-payload*)))
    (if (not (fn-frame-result-okp frame))
        frame
      (if (not (and (equal (fn-frame-result-magic frame)
                           *fn-frame-magic-workflow*)
                    (equal (fn-frame-result-version frame) *fn-frame-version*)))
          (fn-frame-error :magic)
        (let ((code (fn-frame-result-kind frame)))
          (if (or (not (posp code)) (< (len *fn-frame-workflow-kinds*) code))
              (fn-frame-error :kind)
            (let* ((kind (fn-frame-item (- code 1)
                                        *fn-frame-workflow-kinds*))
                   (spec (fn-frame-spec-for kind *fn-frame-workflow-specs*)))
              (if (equal spec :none)
                  (fn-frame-error :kind)
                (let ((parsed (fn-frame-fields-parse
                               spec (fn-frame-result-payload frame))))
                  (if (not (fn-frame-parse-okp parsed))
                      (fn-frame-error (fn-frame-parse-value parsed))
                    (if (not (fn-frame-workflow-record-okp
                              kind (fn-frame-parse-value parsed)))
                        (fn-frame-error :outcome-pair)
                      (fn-frame-ok *fn-frame-magic-workflow* *fn-frame-version*
                                   kind
                                   (fn-frame-parse-value parsed)))))))))))))

(verify-guards fn-frame-workflow-decode
  :hints (("Goal" :in-theory (disable fn-frame-spec-for fn-frame-values-okp
                                      fn-frame-fields-octets))))

(defun fn-frame-receipt-encode (kind values digest)
  (declare (xargs :guard t :verify-guards nil))
  (if (not (and (fn-frame-receipt-record-okp kind values)
                (fn-frame-digestp digest)))
      :bad
    (let ((code (fn-frame-enum-index kind *fn-frame-receipt-kinds*)))
      (if (equal code 0)
          :bad
        (fn-frame-encode *fn-frame-magic-receipt* *fn-frame-version* code
                         (fn-frame-fields-octets
                          (fn-frame-spec-for kind *fn-frame-receipt-specs*)
                          values)
                         digest)))))

(verify-guards fn-frame-receipt-encode
  :hints (("Goal" :in-theory (e/d (fn-frame-receipt-record-okp-fields)
                                  (fn-frame-receipt-record-okp
                                   fn-frame-spec-for fn-frame-values-okp
                                   fn-frame-fields-octets)))))

(defun fn-frame-receipt-decode (octets digest)
  (declare (xargs :guard t :verify-guards nil))
  (let ((frame (fn-frame-decode octets digest
                                *fn-frame-max-receipt-payload*)))
    (if (not (fn-frame-result-okp frame))
        frame
      (if (not (and (equal (fn-frame-result-magic frame)
                           *fn-frame-magic-receipt*)
                    (equal (fn-frame-result-version frame) *fn-frame-version*)))
          (fn-frame-error :magic)
        (let ((code (fn-frame-result-kind frame)))
          (if (or (not (posp code)) (< (len *fn-frame-receipt-kinds*) code))
              (fn-frame-error :kind)
            (let* ((kind (fn-frame-item (- code 1)
                                        *fn-frame-receipt-kinds*))
                   (spec (fn-frame-spec-for kind *fn-frame-receipt-specs*)))
              (if (equal spec :none)
                  (fn-frame-error :kind)
                (let ((parsed (fn-frame-fields-parse
                               spec (fn-frame-result-payload frame))))
                  (if (not (fn-frame-parse-okp parsed))
                      (fn-frame-error (fn-frame-parse-value parsed))
                    (fn-frame-ok *fn-frame-magic-receipt* *fn-frame-version*
                                 kind
                                 (fn-frame-parse-value parsed))))))))))))

(verify-guards fn-frame-receipt-decode
  :hints (("Goal" :in-theory (disable fn-frame-spec-for fn-frame-values-okp
                                      fn-frame-fields-octets))))

(defun fn-frame-bundle-store-encode (kind values digest)
  (declare (xargs :guard t :verify-guards nil))
  (if (not (and (fn-frame-bundle-store-record-okp kind values)
                (fn-frame-digestp digest)))
      :bad
    (let ((code (fn-frame-enum-index kind *fn-frame-bundle-store-kinds*)))
      (if (equal code 0)
          :bad
        (fn-frame-encode *fn-frame-magic-bundle-store* *fn-frame-version* code
                         (fn-frame-fields-octets
                          (fn-frame-spec-for kind *fn-frame-bundle-store-specs*)
                          values)
                         digest)))))

(verify-guards fn-frame-bundle-store-encode)

(defun fn-frame-bundle-store-decode (octets digest)
  (declare (xargs :guard t :verify-guards nil))
  (let ((frame (fn-frame-decode octets digest
                                *fn-frame-max-bundle-store-payload*)))
    (if (not (fn-frame-result-okp frame))
        frame
      (if (not (and (equal (fn-frame-result-magic frame)
                           *fn-frame-magic-bundle-store*)
                    (equal (fn-frame-result-version frame) *fn-frame-version*)))
          (fn-frame-error :magic)
        (let ((code (fn-frame-result-kind frame)))
          (if (or (not (posp code)) (< (len *fn-frame-bundle-store-kinds*) code))
              (fn-frame-error :kind)
            (let* ((kind (fn-frame-item (- code 1)
                                        *fn-frame-bundle-store-kinds*))
                   (spec (fn-frame-spec-for kind *fn-frame-bundle-store-specs*)))
              (if (equal spec :none)
                  (fn-frame-error :kind)
                (let ((parsed (fn-frame-fields-parse
                               spec (fn-frame-result-payload frame))))
                  (if (not (fn-frame-parse-okp parsed))
                      (fn-frame-error (fn-frame-parse-value parsed))
                    (fn-frame-ok *fn-frame-magic-bundle-store*
                                 *fn-frame-version* kind
                                 (fn-frame-parse-value parsed))))))))))))

(verify-guards fn-frame-bundle-store-decode)

; -----------------------------------------------------------------------------
; Export theory.  Both facts are about the two constant specification tables
; and exist for the guard proofs below them.

(deftheory fn-frame-journal-vocabulary
  '(    fn-frame-spec-for-workflow-is-spec-list
    fn-frame-spec-for-receipt-is-spec-list
    fn-frame-spec-for-bundle-store-is-spec-list))

(in-theory (disable fn-frame-workflow-record-okp-fields
             fn-frame-receipt-record-okp-fields
             fn-frame-spec-for-workflow-is-spec-list
             fn-frame-spec-for-receipt-is-spec-list
             fn-frame-spec-for-bundle-store-is-spec-list))
