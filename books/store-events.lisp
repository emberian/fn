; Authoritative Store transaction-event grammar.
;
; Legacy article transactions remain the exact schema-0 `fn-r' byte grammar.
; New event kinds use a disjoint `fn-e' envelope.  Both occupy the same
; immutable, contiguous Store transaction namespace; the filesystem machine
; therefore supplies one publication and recovery order rather than a second
; obligation log.
(in-package "ACL2")
(include-book "records-seam")
(include-book "stx-accept-records")
(include-book "consumer-store-events")
(include-book "topic-history-store-events")

(defconst *fn-store-event-magic* '(102 110 45 101)) ; fn-e
(defconst *fn-store-event-version* 0)
(defconst *fn-store-event-undertake-code* 0)
(defconst *fn-store-event-release-code* 1)
(defconst *fn-store-event-max-octets* 4096)

; Pre-reservation callers know the event kind before its final bytes exist.
; This table is the ACL2-owned conservative payload presented to the persisted
; profile gate.  The final publication path separately checks actual bytes.
(defun fn-store-publication-ceiling (kind)
  (declare (xargs :guard t))
  (cond ((equal kind :article) *fn-record-max-octets*)
        ((or (equal kind :undertake) (equal kind :release))
         *fn-store-event-max-octets*)
        ((equal kind :statement-verdict) *fn-stxe-max-octets*)
        ((equal kind :keyring-snapshot) *fn-stxk-max-octets*)
        ((equal kind :accepted-statement) *fn-stxa-max-octets*)
        ((equal kind :consumer) *fn-cpe-max-octets*)
        ((member-eq kind '(:topic-anchor :topic-admit))
         *fn-th-topic-max-octets*)
        (t 0)))

; Retention event:
; (:retention kind sequence txid generation obligation-id subject evidence charge)
(defun fn-store-retention-event-make
  (kind sequence txid generation obligation-id subject evidence charge)
  (declare (xargs :guard t :verify-guards nil))
  (list :retention kind sequence txid generation obligation-id subject evidence charge))

(defun fn-store-event-nth (n x)
  (declare (xargs :guard (natp n) :measure (nfix n)))
  (if (zp n) (if (consp x) (car x) nil)
    (fn-store-event-nth (1- n) (if (consp x) (cdr x) nil))))

(defun fn-store-retention-event-p (x)
  (declare (xargs :guard t :verify-guards nil))
  (and (true-listp x) (equal (len x) 9)
       (equal (fn-store-event-nth 0 x) :retention)
       (member-equal (fn-store-event-nth 1 x) '(:undertake :release))
       (fn-record-uint32p (fn-store-event-nth 2 x))
       (fn-record-uint32p (fn-store-event-nth 3 x))
       (fn-record-uint32p (fn-store-event-nth 4 x))
       (fn-record-metadata-bytes-p (fn-store-event-nth 5 x))
       (fn-record-metadata-bytes-p (fn-store-event-nth 6 x))
       (fn-record-metadata-bytes-p (fn-store-event-nth 7 x))
       (fn-record-uint32p (fn-store-event-nth 8 x))
       (if (equal (fn-store-event-nth 1 x) :undertake)
           (posp (fn-store-event-nth 8 x))
         (equal (fn-store-event-nth 8 x) 0))))

(defun fn-store-event-p (x)
  (declare (xargs :guard t :verify-guards nil))
  (or (fn-record-p x) (fn-store-retention-event-p x)
      (fn-stxe-p x) (fn-stxk-p x) (fn-stxa-p x) (fn-cpe-eventp x)
      (fn-th-topic-eventp x)))

; The new five-field envelope cannot be mistaken for an older event.  These
; shape facts let replay/Store proofs dispatch without opening every codec.
(defthm fn-cpe-is-disjoint-from-old-event-kinds-by-shape
  (implies (fn-cpe-eventp x)
           (and (not (fn-record-p x))
                (not (fn-store-retention-event-p x))
                (not (fn-stxe-p x))
                (not (fn-stxk-p x))
                (not (fn-stxa-p x))))
  :hints (("Goal" :in-theory
           (enable fn-cpe-eventp fn-record-p fn-record-shapep
                   fn-store-retention-event-p
                   fn-stxe-shapep fn-stxk-shapep fn-stxa-shapep))))

(defun fn-store-event-kind (x)
  (declare (xargs :guard t :verify-guards nil))
  (cond ((fn-record-p x) :article)
        ((fn-store-retention-event-p x) (fn-store-event-nth 1 x))
        ((fn-stxe-p x) :statement-verdict)
        ((fn-stxk-p x) :keyring-snapshot)
        ((fn-stxa-p x) :accepted-statement)
        ((fn-cpe-eventp x) :consumer)
        ((fn-th-topic-eventp x) (fn-th-at 0 x))
        (t nil)))
(defun fn-store-event-sequence (x)
  (declare (xargs :guard t :verify-guards nil))
  (cond ((fn-record-p x) (fn-record-sequence x))
        ((fn-store-retention-event-p x) (fn-store-event-nth 2 x))
        ((fn-stxe-p x) (fn-stxe-sequence x))
        ((fn-stxk-p x) (fn-stxk-sequence x))
        ((fn-stxa-p x) (fn-stxa-sequence x))
        ((fn-cpe-eventp x) (fn-cpe-sequence x))
        ((fn-th-topic-eventp x) (fn-th-at 1 x))
        (t nil)))
(defun fn-store-event-txid (x)
  (declare (xargs :guard t :verify-guards nil))
  (cond ((fn-record-p x) (fn-record-txid x))
        ((fn-store-retention-event-p x) (fn-store-event-nth 3 x))
        ((fn-stxe-p x) (fn-stxe-txid x))
        ((fn-stxk-p x) (fn-stxk-txid x))
        ((fn-stxa-p x) (fn-stxa-txid x))
        ((fn-cpe-eventp x) (fn-cpe-txid x))
        ((fn-th-topic-eventp x) (fn-th-at 2 x))
        (t nil)))
(defun fn-store-event-generation (x)
  (declare (xargs :guard t :verify-guards nil))
  (cond ((fn-record-p x) (fn-record-generation x))
        ((fn-store-retention-event-p x) (fn-store-event-nth 4 x))
        ((fn-stxe-p x) (fn-stxe-generation x))
        ((fn-stxk-p x) (fn-stxk-generation x))
        ((fn-stxa-p x) (fn-stxa-generation x))
        ((fn-cpe-eventp x) (fn-cpe-generation x))
        ((fn-th-topic-eventp x) (fn-th-at 3 x))
        (t nil)))
(defun fn-store-event-obligation-id (x) (declare (xargs :guard t :verify-guards nil)) (fn-store-event-nth 5 x))
(defun fn-store-event-subject (x) (declare (xargs :guard t :verify-guards nil)) (fn-store-event-nth 6 x))
(defun fn-store-event-evidence (x) (declare (xargs :guard t :verify-guards nil)) (fn-store-event-nth 7 x))
(defun fn-store-event-charge (x) (declare (xargs :guard t :verify-guards nil)) (fn-store-event-nth 8 x))

(verify-guards fn-store-retention-event-p)
(verify-guards fn-store-event-p)
(verify-guards fn-store-event-kind)
(verify-guards fn-store-event-sequence)
(verify-guards fn-store-event-txid)
(verify-guards fn-store-event-generation)
(verify-guards fn-store-event-obligation-id)
(verify-guards fn-store-event-subject)
(verify-guards fn-store-event-evidence)
(verify-guards fn-store-event-charge)

(defun fn-store-event-kind-code (kind)
  (declare (xargs :guard t :verify-guards nil))
  (if (equal kind :undertake) *fn-store-event-undertake-code*
    (if (equal kind :release) *fn-store-event-release-code* 2)))

(defun fn-store-retention-event-encode (event)
  (declare (xargs :guard t :verify-guards nil))
  (if (not (fn-store-retention-event-p event)) nil
    (append
     (fn-cbor-encode (cons :bytes *fn-store-event-magic*))
     (fn-cbor-encode (cons :uint *fn-store-event-version*))
     (fn-cbor-encode (cons :uint (fn-store-event-kind-code (fn-store-event-kind event))))
     (fn-cbor-encode (cons :uint (fn-store-event-sequence event)))
     (fn-cbor-encode (cons :uint (fn-store-event-txid event)))
     (fn-cbor-encode (cons :uint (fn-store-event-generation event)))
     (fn-cbor-encode (cons :bytes (fn-record-string-octets (fn-store-event-obligation-id event))))
     (fn-cbor-encode (cons :bytes (fn-record-string-octets (fn-store-event-subject event))))
     (fn-cbor-encode (cons :bytes (fn-record-string-octets (fn-store-event-evidence event))))
     (fn-cbor-encode (cons :uint (fn-store-event-charge event))))))

(defun fn-store-event-encode (event)
  (declare (xargs :guard t :verify-guards nil))
  (cond ((fn-record-p event) (fn-record-encode event))
        ((fn-store-retention-event-p event)
         (fn-store-retention-event-encode event))
        ((fn-stxe-p event) (fn-stxe-encode event))
        ((fn-stxk-p event) (fn-stxk-encode event))
        ((fn-stxa-p event) (fn-stxa-encode event))
        ((fn-cpe-eventp event) (fn-cpe-encode event))
        ((fn-th-topic-eventp event) (fn-th-topic-event-encode event))
        (t nil)))

(defthm fn-store-event-article-encoding-is-legacy-record-encoding
  (implies (fn-record-p record)
           (equal (fn-store-event-encode record) (fn-record-encode record))))

; Decoder helper returns (:ok values rest), retaining the unconsumed suffix so
; the public decoder can reject trailing data.
(defun fn-store-event-decode-items (octets count values)
  (declare (xargs :guard t :verify-guards nil :measure (nfix count)))
  (if (zp count) (list :ok (reverse values) octets)
    (if (not (fn-cbor-octet-listp octets)) (list :error :octets)
      (let ((one (fn-cbor-decode octets)))
        (if (not (fn-cbor-result-okp one)) (list :error :field)
          (fn-store-event-decode-items
           (fn-cbor-result-rest one) (1- count)
           (cons (fn-cbor-result-value one) values)))))))

(defun fn-store-event-item-value (n values)
  (declare (xargs :guard t :verify-guards nil))
  (let ((item (fn-store-event-nth n values)))
    (if (consp item) (cdr item) nil)))

(defun fn-store-event-item-tagp (n tag values)
  (declare (xargs :guard t :verify-guards nil))
  (let ((item (fn-store-event-nth n values)))
    (and (consp item) (equal (car item) tag))))

(defun fn-store-retention-event-from-values (values)
  (declare (xargs :guard t :verify-guards nil))
  (let* ((code (fn-store-event-item-value 2 values))
         (kind (if (equal code *fn-store-event-undertake-code*) :undertake
                 (if (equal code *fn-store-event-release-code*) :release nil)))
         (event (fn-store-retention-event-make
                 kind
                 (fn-store-event-item-value 3 values)
                 (fn-store-event-item-value 4 values)
                 (fn-store-event-item-value 5 values)
                 (fn-record-octets-string (fn-store-event-item-value 6 values))
                 (fn-record-octets-string (fn-store-event-item-value 7 values))
                 (fn-record-octets-string (fn-store-event-item-value 8 values))
                 (fn-store-event-item-value 9 values))))
    (if (and (true-listp values) (equal (len values) 10)
             (fn-store-event-item-tagp 0 :bytes values)
             (fn-store-event-item-tagp 1 :uint values)
             (fn-store-event-item-tagp 2 :uint values)
             (fn-store-event-item-tagp 3 :uint values)
             (fn-store-event-item-tagp 4 :uint values)
             (fn-store-event-item-tagp 5 :uint values)
             (fn-store-event-item-tagp 6 :bytes values)
             (fn-store-event-item-tagp 7 :bytes values)
             (fn-store-event-item-tagp 8 :bytes values)
             (fn-store-event-item-tagp 9 :uint values)
             (equal (fn-store-event-nth 0 values) (cons :bytes *fn-store-event-magic*))
             (equal (fn-store-event-nth 1 values) (cons :uint *fn-store-event-version*))
             (member-equal code (list *fn-store-event-undertake-code*
                                      *fn-store-event-release-code*))
             (fn-store-retention-event-p event))
        event nil)))

(defun fn-store-retention-event-decode-exact (octets)
  (declare (xargs :guard t :verify-guards nil))
  (if (or (not (fn-cbor-octet-listp octets))
          (not (fn-cbor-at-mostp octets *fn-store-event-max-octets*)))
      (list :error :octets)
    (let ((parsed (fn-store-event-decode-items octets 10 nil)))
      (if (or (not (equal (car parsed) :ok))
              (consp (fn-store-event-nth 2 parsed)))
          (list :error :grammar)
        (let ((event (fn-store-retention-event-from-values
                      (fn-store-event-nth 1 parsed))))
          (if event (list :ok event) (list :error :record)))))))

(defun fn-store-event-decode-exact (octets)
  (declare (xargs :guard t :verify-guards nil))
  (let ((legacy (fn-record-decode-exact octets)))
    (if (fn-record-result-okp legacy) legacy
      (let ((retention (fn-store-retention-event-decode-exact octets)))
        (if (equal (car retention) :ok) retention
          (let ((verdict (fn-stxe-decode-exact octets)))
            (if (fn-stmt-okp verdict) verdict
              (let ((snapshot (fn-stxk-decode-exact octets)))
                (if (fn-stmt-okp snapshot) snapshot
                  (let ((accepted (fn-stxa-decode-exact octets)))
                    (if (fn-stmt-okp accepted) accepted
                      (let ((consumer (fn-cpe-decode-exact octets)))
                        (if (fn-stmt-okp consumer) consumer
                          (fn-th-topic-event-decode-exact octets))))))))))))))

; Export withdrawal.  Every book above reasons about an event through this
; recognizer, never by opening it: `fn-store-event-p' unfolds into five kind
; recognizers, and `fn-record-p', `fn-stxe-p', `fn-stxk-p' and `fn-stxa-p'
; each unfold into a codec that the bounded CBOR profile made much larger.  A
; goal that merely dispatches on the event kind then carries the whole record
; and statement codec.  Measured 2026-09-22: `fn-sfg-record-values-are-a-true-
; list' (books/store-files) and the guard of `fn-config-aware-loop'
; (books/config-records) each ran past 900 s at one subgoal, and the closure
; above them missed the 1800 s and 2400 s per-book limits on hbox
; (run-20260922T031236Z-c1fb, certify-20260922T034701Z-2641627).  A book that
; needs the definition enables it by name, as books/store-files already does
; for its field typing lemmas.
(in-theory (disable (:d fn-store-event-p) (:d fn-store-retention-event-p)
                    (:d fn-store-event-kind) (:d fn-store-event-sequence)
                    (:d fn-store-event-txid) (:d fn-store-event-generation)
                    (:d fn-store-event-obligation-id)
                    (:d fn-store-event-subject) (:d fn-store-event-evidence)
                    (:d fn-store-event-charge)))
