; fn: isolated BP ingress experiment for exact legacy NNTP article ADUs.
;
; A BP implementation stages a bounded ADU non-destructively before calling this
; model.  The ADU is an exact legacy article octet list, not an fn transaction
; record, native BP envelope, or signed receipt.  BP source EID, lifetime, and
; BPA bundle ID are observed transport provenance only; none authenticates an
; author or contributes an fn article identity.
(in-package "ACL2")
(include-book "article-fields")
(include-book "store-node")

; Policy: (destination endpoint group-map archive-id immutable-subject
;          release-evidence charge policy-id terms-id issuer-eid).
; A group-map entry is (parsed-newsgroup-octets local-store-group-string).
(defun fn-bpi-policy-destination (x) (car x))
(defun fn-bpi-policy-endpoint (x) (car (cdr x)))
(defun fn-bpi-policy-group-map (x) (car (cdr (cdr x))))
(defun fn-bpi-policy-archive-id (x) (car (cdr (cdr (cdr x)))))
(defun fn-bpi-policy-subject (x) (car (cdr (cdr (cdr (cdr x))))))
(defun fn-bpi-policy-evidence (x) (car (cdr (cdr (cdr (cdr (cdr x)))))))
(defun fn-bpi-policy-charge (x) (car (cdr (cdr (cdr (cdr (cdr (cdr x))))))))
(defun fn-bpi-policy-id (x) (car (cdr (cdr (cdr (cdr (cdr (cdr (cdr x)))))))))
(defun fn-bpi-policy-terms-id (x) (car (cdr (cdr (cdr (cdr (cdr (cdr (cdr (cdr x))))))))))
(defun fn-bpi-policy-issuer-eid (x) (car (cdr (cdr (cdr (cdr (cdr (cdr (cdr (cdr (cdr x)))))))))))
(defun fn-bpi-make-policy (destination endpoint group-map archive-id subject
                                        evidence charge policy-id terms-id issuer-eid)
  (list destination endpoint group-map archive-id subject evidence charge
        policy-id terms-id issuer-eid))

; Transport context: (destination-eid source-eid bpa-bundle-id bp-lifetime).
; It records what the host observed.  Source EID is deliberately not an
; author/signer input, and BPA bundle IDs remain local transport references.
(defun fn-bpi-context-destination (x) (car x))
(defun fn-bpi-context-source-eid (x) (car (cdr x)))
(defun fn-bpi-context-bundle-id (x) (car (cdr (cdr x))))
(defun fn-bpi-context-lifetime (x) (car (cdr (cdr (cdr x)))))
(defun fn-bpi-make-context (destination source-eid bundle-id lifetime)
  (list destination source-eid bundle-id lifetime))

(defun fn-bpi-group-map-entryp (entry)
  (and (true-listp entry) (equal (len entry) 2)
       (fn-af-newsgroup-namep (car entry))
       (fn-record-group-namep (car (cdr entry)))))
(defun fn-bpi-group-mapp (entries)
  (if (consp entries)
      (and (fn-bpi-group-map-entryp (car entries))
           (fn-bpi-group-mapp (cdr entries)))
    (null entries)))
(defun fn-bpi-map-values (entries)
  (if (consp entries)
      (cons (car (cdr (car entries))) (fn-bpi-map-values (cdr entries)))
    nil))
(defun fn-bpi-find-group (name entries)
  (if (consp entries)
      (if (equal name (car (car entries)))
          (car entries)
        (fn-bpi-find-group name (cdr entries)))
    nil))
(defun fn-bpi-map-one (name entries)
  (let ((entry (fn-bpi-find-group name entries)))
    (if entry (list :ok (car (cdr entry))) (list :error :unknown-group))))
(defun fn-bpi-map-groups (names entries)
  (if (consp names)
      (let ((one (fn-bpi-map-one (car names) entries)))
        (if (equal (car one) :ok)
            (let ((tail (fn-bpi-map-groups (cdr names) entries)))
              (if (equal (car tail) :ok)
                  (list :ok (cons (car (cdr one)) (car (cdr tail))))
                tail))
          one))
    (list :ok nil)))

(defun fn-bpi-policy-p (policy)
  (and (true-listp policy) (equal (len policy) 10)
       (fn-record-metadata-bytes-p (fn-bpi-policy-destination policy))
       (fn-record-metadata-bytes-p (fn-bpi-policy-endpoint policy))
       (fn-bpi-group-mapp (fn-bpi-policy-group-map policy))
       (fn-string-listp (fn-bpi-map-values (fn-bpi-policy-group-map policy)))
       (fn-no-duplicatesp (fn-bpi-map-values (fn-bpi-policy-group-map policy)))
       (fn-record-metadata-bytes-p (fn-bpi-policy-archive-id policy))
       (fn-record-metadata-bytes-p (fn-bpi-policy-subject policy))
       (fn-record-metadata-bytes-p (fn-bpi-policy-evidence policy))
       (fn-record-uint32p (fn-bpi-policy-charge policy))
       (posp (fn-bpi-policy-charge policy))
       (fn-record-metadata-bytes-p (fn-bpi-policy-id policy))
       (fn-record-metadata-bytes-p (fn-bpi-policy-terms-id policy))
       (fn-record-metadata-bytes-p (fn-bpi-policy-issuer-eid policy))))

(defun fn-bpi-context-p (context)
  (and (true-listp context) (equal (len context) 4)
       (fn-record-metadata-bytes-p (fn-bpi-context-destination context))
       (fn-record-metadata-bytes-p (fn-bpi-context-source-eid context))
       (fn-record-metadata-bytes-p (fn-bpi-context-bundle-id context))
       (fn-record-uint32p (fn-bpi-context-lifetime context))))

(defun fn-bpi-policy-appliesp (store policy context)
  (and (fn-sn-statep store) (fn-bpi-policy-p policy) (fn-bpi-context-p context)
       (equal (fn-bpi-context-destination context)
              (fn-bpi-policy-destination policy))
       (equal (fn-bpi-policy-endpoint policy)
              (fn-bpi-policy-destination policy))
       (equal (fn-bpi-map-values (fn-bpi-policy-group-map policy))
              (fn-sn-groups store))))

(defun fn-bpi-record-for (store policy msgid-octets group-octets adu)
  ; fn-record-octets-string is exact for this validated ASCII Message-ID.  The
  ; original ADU itself remains the Store payload without reconstruction.
  (fn-record-make (len (fn-sf-records (fn-sn-files store)))
                  (1- (fn-sf-frontier (fn-sn-files store)))
                  (1- (fn-sf-frontier (fn-sn-files store)))
                  (fn-record-octets-string msgid-octets)
                  adu
                  (car (cdr (fn-bpi-map-groups group-octets
                                                (fn-bpi-policy-group-map policy))))
                  (fn-bpi-policy-archive-id policy)
                  (fn-bpi-policy-subject policy)
                  (fn-bpi-policy-evidence policy)
                  (fn-bpi-policy-charge policy)))

; Result: (:rejected reason) or (:prepared store record).  The caller must
; already have completed the Store's durable allocator reservation sequence;
; this function neither treats BP inbox staging nor a transport ACK as durable
; fn acceptance.
(defun fn-bpi-ingress-prepare (store policy context adu)
  (if (not (fn-bpi-policy-appliesp store policy context))
      (list :rejected :policy-or-destination)
    (if (not (and (fn-cbor-octet-listp adu)
                  (<= (len adu) *fn-article-max-octets*)
                  (equal (fn-sf-phase (fn-sn-files store)) :reserved)))
        (list :rejected :adu-or-store-phase)
      (let ((parsed (fn-article-parse adu)))
        (if (not (fn-article-result-okp parsed))
            (list :rejected :article-syntax)
          (let ((proto (fn-af-proto-article-check
                        (fn-article-result-article parsed))))
            (if (not (equal (car proto) :ok))
                (list :rejected (car (cdr proto)))
              (let ((msgid (car (cdr proto)))
                    (groups (car (cdr (cdr proto)))))
                (if (not msgid)
                    (list :rejected :message-id-missing)
                  (let ((mapped (fn-bpi-map-groups
                                 groups (fn-bpi-policy-group-map policy))))
                    (if (not (equal (car mapped) :ok))
                        (list :rejected (car (cdr mapped)))
                      (let ((record (fn-bpi-record-for store policy msgid groups adu)))
                        (if (and (fn-record-p record)
                                 (fn-selection-validp (fn-record-groups record)
                                                      (fn-sn-groups store)))
                            (let ((next (fn-sn-prepare store record)))
                              (if (equal next store)
                                  (list :rejected :store-refused)
                                (list :prepared next record)))
                          (list :rejected :groups-or-record))))))))))))))

(defun fn-bpi-result-kind (result) (car result))
(defun fn-bpi-result-store (result) (car (cdr result)))
(defun fn-bpi-result-record (result) (car (cdr (cdr result))))

; Testable application of the existing record publication phases.  Each :ok is
; a file-kernel observation, not a BP acknowledgement.  The only final step is
; the actual fn-sn-finish durable-node completion.
(defun fn-bpi-finish-prepared (store)
  (fn-sn-finish
   (fn-sn-io
    (fn-sn-io
     (fn-sn-io store :record-file :ok)
     :record-link :ok)
    :record-directory :ok)))

(defun fn-bpi-node-record-committedp (node record)
  ; This unfolds the actual node's published article and archive binding; it
  ; does not rely on an external completion word or transport acknowledgement.
  (let ((article (fn-find-article
                  (fn-record-msgid record)
                  (fn-state-articles (fn-node-acceptance node))))
        (binding (fn-node-find-binding
                  (fn-record-msgid record) (fn-node-bindings node))))
    (and (fn-node-statep node) (consp article) (consp binding)
         (equal (fn-article-payload article) (fn-record-payload record))
         (equal (fn-article-groups article) (fn-record-groups record))
         (equal (fn-node-binding-subject binding)
                (fn-record-content-subject record))
         (equal (fn-node-binding-id binding)
                (fn-record-obligation-id record)))))

(defun fn-bpi-durably-acceptedp (store record)
  (and (fn-sn-statep store) (fn-record-p record)
       (fn-bpi-node-record-committedp (fn-sn-node store) record)
       (member-equal (fn-sf-record-pair record)
                     (fn-sf-successes (fn-sn-files store)))))

; This bounded replay query uses the same parser, field policy, group map, and
; node binding as preparation.  It is suitable for a host to recognize an
; exact already-durable staged ADU before reserving another local transaction.
; It never equates BPA identifiers or transport provenance with article
; identity; the node predicate compares the parsed Message-ID, exact payload,
; groups, archive obligation, and immutable subject.
(defun fn-bpi-adu-durably-acceptedp (store policy context adu)
  (if (not (and (fn-bpi-policy-appliesp store policy context)
                (fn-cbor-octet-listp adu)
                (<= (len adu) *fn-article-max-octets*)))
      nil
    (let ((parsed (fn-article-parse adu)))
      (if (not (fn-article-result-okp parsed))
          nil
        (let ((proto (fn-af-proto-article-check
                      (fn-article-result-article parsed))))
          (if (not (equal (car proto) :ok))
              nil
            (let ((msgid (car (cdr proto)))
                  (groups (car (cdr (cdr proto)))))
              (if (not msgid)
                  nil
                (let ((mapped (fn-bpi-map-groups
                               groups (fn-bpi-policy-group-map policy))))
                  (and (equal (car mapped) :ok)
                       (fn-bpi-node-record-committedp
                        (fn-sn-node store)
                        (fn-bpi-record-for store policy msgid groups adu))))))))))))

; This is only an unsigned receipt-eligibility context.  Current records do
; not carry the separate durable receipt-intent/decision required for an
; application receipt, its A-POLICY authorization, or a signature grammar.
(defun fn-bpi-receipt-eligibility (store record policy context)
  (if (and (fn-bpi-durably-acceptedp store record)
           (fn-bpi-policy-appliesp store policy context)
           (equal (fn-record-content-subject record)
                  (fn-bpi-policy-subject policy))
           (equal (fn-record-obligation-id record)
                  (fn-bpi-policy-archive-id policy)))
      (list :eligible (fn-record-msgid record) (fn-bpi-policy-subject policy)
            (fn-bpi-policy-archive-id policy) (fn-bpi-policy-id policy)
            (fn-bpi-policy-terms-id policy) (fn-bpi-policy-issuer-eid policy)
            (fn-bpi-context-source-eid context))
    nil))
