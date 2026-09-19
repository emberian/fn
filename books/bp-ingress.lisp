; fn: isolated BP ingress experiment for exact legacy NNTP article ADUs.
;
; A BP implementation stages a bounded ADU non-destructively before calling this
; model.  The ADU is an exact legacy article octet list, not an fn transaction
; record, native BP envelope, or signed receipt.  BP source EID, lifetime, and
; BPA bundle ID are observed transport provenance only; none authenticates an
; author or contributes an fn article identity.
(in-package "ACL2")
(include-book "article-fields")
(include-book "article-properties")
(include-book "store-node")

; -----------------------------------------------------------------------------
; Total, guard-t counterparts used only inside :exec branches below.  Each is
; proven equal to the named, narrower-guarded reader by unfolding that
; reader's own (non-recursive) definition from records.lisp/article.lisp, so
; every :logic branch below keeps the exact original body and reads through
; the real accessor; only the executable substitute differs.

(defun fn-bpi-ag-dec (x)
  (declare (xargs :guard t))
  (if (acl2-numberp x) (1- x) -1))
(defthm fn-bpi-ag-dec-is-1-
  (equal (fn-bpi-ag-dec x) (1- x)))

(defun fn-bpi-ag-result-article (result)
  (declare (xargs :guard t))
  (fn-ag-car (fn-ag-cdr result)))
(defthm fn-bpi-ag-result-article-is-fn-article-result-article
  (equal (fn-bpi-ag-result-article result) (fn-article-result-article result))
  :hints (("Goal" :in-theory (enable fn-article-result-article))))

(defun fn-bpi-ag-record-msgid (record)
  (declare (xargs :guard t))
  (fn-ag-car (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr record)))))
(defthm fn-bpi-ag-record-msgid-is-fn-record-msgid
  (equal (fn-bpi-ag-record-msgid record) (fn-record-msgid record))
  :hints (("Goal" :in-theory (enable fn-record-msgid))))

(defun fn-bpi-ag-record-payload (record)
  (declare (xargs :guard t))
  (fn-ag-car (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr record))))))
(defthm fn-bpi-ag-record-payload-is-fn-record-payload
  (equal (fn-bpi-ag-record-payload record) (fn-record-payload record))
  :hints (("Goal" :in-theory (enable fn-record-payload))))

(defun fn-bpi-ag-record-groups (record)
  (declare (xargs :guard t))
  (fn-ag-car (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr record)))))))
(defthm fn-bpi-ag-record-groups-is-fn-record-groups
  (equal (fn-bpi-ag-record-groups record) (fn-record-groups record))
  :hints (("Goal" :in-theory (enable fn-record-groups))))

(defun fn-bpi-ag-record-obligation-id (record)
  (declare (xargs :guard t))
  (fn-ag-car (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr record))))))))
(defthm fn-bpi-ag-record-obligation-id-is-fn-record-obligation-id
  (equal (fn-bpi-ag-record-obligation-id record) (fn-record-obligation-id record))
  :hints (("Goal" :in-theory (enable fn-record-obligation-id))))

(defun fn-bpi-ag-record-content-subject (record)
  (declare (xargs :guard t))
  (fn-ag-car (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr record)))))))))
(defthm fn-bpi-ag-record-content-subject-is-fn-record-content-subject
  (equal (fn-bpi-ag-record-content-subject record) (fn-record-content-subject record))
  :hints (("Goal" :in-theory (enable fn-record-content-subject))))

; Policy: (destination endpoint group-map archive-id immutable-subject
;          release-evidence charge policy-id terms-id issuer-eid).
; A group-map entry is (parsed-newsgroup-octets local-store-group-string).
(defun fn-bpi-policy-destination (x)
  (declare (xargs :guard t :verify-guards nil))
  (mbe :logic (car x)
       :exec (fn-ag-car x)))
(verify-guards fn-bpi-policy-destination)
(defun fn-bpi-policy-endpoint (x)
  (declare (xargs :guard t :verify-guards nil))
  (mbe :logic (car (cdr x))
       :exec (fn-ag-car (fn-ag-cdr x))))
(verify-guards fn-bpi-policy-endpoint)
(defun fn-bpi-policy-group-map (x)
  (declare (xargs :guard t :verify-guards nil))
  (mbe :logic (car (cdr (cdr x)))
       :exec (fn-ag-car (fn-ag-cdr (fn-ag-cdr x)))))
(verify-guards fn-bpi-policy-group-map)
(defun fn-bpi-policy-archive-id (x)
  (declare (xargs :guard t :verify-guards nil))
  (mbe :logic (car (cdr (cdr (cdr x))))
       :exec (fn-ag-car (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr x))))))
(verify-guards fn-bpi-policy-archive-id)
(defun fn-bpi-policy-subject (x)
  (declare (xargs :guard t :verify-guards nil))
  (mbe :logic (car (cdr (cdr (cdr (cdr x)))))
       :exec (fn-ag-car (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr x)))))))
(verify-guards fn-bpi-policy-subject)
(defun fn-bpi-policy-evidence (x)
  (declare (xargs :guard t :verify-guards nil))
  (mbe :logic (car (cdr (cdr (cdr (cdr (cdr x))))))
       :exec (fn-ag-car (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr x))))))))
(verify-guards fn-bpi-policy-evidence)
(defun fn-bpi-policy-charge (x)
  (declare (xargs :guard t :verify-guards nil))
  (mbe :logic (car (cdr (cdr (cdr (cdr (cdr (cdr x)))))))
       :exec (fn-ag-car (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr x)))))))))
(verify-guards fn-bpi-policy-charge)
(defun fn-bpi-policy-id (x)
  (declare (xargs :guard t :verify-guards nil))
  (mbe :logic (car (cdr (cdr (cdr (cdr (cdr (cdr (cdr x))))))))
       :exec (fn-ag-car (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr x))))))))))
(verify-guards fn-bpi-policy-id)
(defun fn-bpi-policy-terms-id (x)
  (declare (xargs :guard t :verify-guards nil))
  (mbe :logic (car (cdr (cdr (cdr (cdr (cdr (cdr (cdr (cdr x)))))))))
       :exec (fn-ag-car (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr x)))))))))))
(verify-guards fn-bpi-policy-terms-id)
(defun fn-bpi-policy-issuer-eid (x)
  (declare (xargs :guard t :verify-guards nil))
  (mbe :logic (car (cdr (cdr (cdr (cdr (cdr (cdr (cdr (cdr (cdr x))))))))))
       :exec (fn-ag-car (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr x))))))))))))
(verify-guards fn-bpi-policy-issuer-eid)
(defun fn-bpi-make-policy (destination endpoint group-map archive-id subject
                                        evidence charge policy-id terms-id issuer-eid)
  (declare (xargs :guard t))
  (list destination endpoint group-map archive-id subject evidence charge
        policy-id terms-id issuer-eid))
(verify-guards fn-bpi-make-policy)

; Transport context: (destination-eid source-eid bpa-bundle-id bp-lifetime).
; It records what the host observed.  Source EID is deliberately not an
; author/signer input, and BPA bundle IDs remain local transport references.
(defun fn-bpi-context-destination (x)
  (declare (xargs :guard t :verify-guards nil))
  (mbe :logic (car x)
       :exec (fn-ag-car x)))
(verify-guards fn-bpi-context-destination)
(defun fn-bpi-context-source-eid (x)
  (declare (xargs :guard t :verify-guards nil))
  (mbe :logic (car (cdr x))
       :exec (fn-ag-car (fn-ag-cdr x))))
(verify-guards fn-bpi-context-source-eid)
(defun fn-bpi-context-bundle-id (x)
  (declare (xargs :guard t :verify-guards nil))
  (mbe :logic (car (cdr (cdr x)))
       :exec (fn-ag-car (fn-ag-cdr (fn-ag-cdr x)))))
(verify-guards fn-bpi-context-bundle-id)
(defun fn-bpi-context-lifetime (x)
  (declare (xargs :guard t :verify-guards nil))
  (mbe :logic (car (cdr (cdr (cdr x))))
       :exec (fn-ag-car (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr x))))))
(verify-guards fn-bpi-context-lifetime)
(defun fn-bpi-make-context (destination source-eid bundle-id lifetime)
  (declare (xargs :guard t))
  (list destination source-eid bundle-id lifetime))
(verify-guards fn-bpi-make-context)

(defun fn-bpi-group-map-entryp (entry)
  (declare (xargs :guard t :verify-guards nil))
  (mbe :logic
(and (true-listp entry) (equal (len entry) 2)
       (fn-af-newsgroup-namep (car entry))
       (fn-record-group-namep (car (cdr entry))))
       :exec
(and (true-listp entry) (equal (len entry) 2)
       (fn-af-newsgroup-namep (fn-ag-car entry))
       (fn-record-group-namep (fn-ag-car (fn-ag-cdr entry))))))
(verify-guards fn-bpi-group-map-entryp)

(defun fn-bpi-group-mapp (entries)
  (declare (xargs :guard t :verify-guards nil))
  (mbe :logic
(if (consp entries)
      (and (fn-bpi-group-map-entryp (car entries))
           (fn-bpi-group-mapp (cdr entries)))
    (null entries))
       :exec
(if (consp entries)
      (and (fn-bpi-group-map-entryp (fn-ag-car entries))
           (fn-bpi-group-mapp (fn-ag-cdr entries)))
    (null entries))))
(verify-guards fn-bpi-group-mapp)

(defun fn-bpi-map-values (entries)
  (declare (xargs :guard t :verify-guards nil))
  (mbe :logic
(if (consp entries)
      (cons (car (cdr (car entries))) (fn-bpi-map-values (cdr entries)))
    nil)
       :exec
(if (consp entries)
      (cons (fn-ag-car (fn-ag-cdr (fn-ag-car entries)))
            (fn-bpi-map-values (fn-ag-cdr entries)))
    nil)))
(verify-guards fn-bpi-map-values)

(defun fn-bpi-find-group (name entries)
  (declare (xargs :guard t :verify-guards nil))
  (mbe :logic
(if (consp entries)
      (if (equal name (car (car entries)))
          (car entries)
        (fn-bpi-find-group name (cdr entries)))
    nil)
       :exec
(if (consp entries)
      (if (equal name (fn-ag-car (fn-ag-car entries)))
          (fn-ag-car entries)
        (fn-bpi-find-group name (fn-ag-cdr entries)))
    nil)))
(verify-guards fn-bpi-find-group)

(defun fn-bpi-map-one (name entries)
  (declare (xargs :guard t :verify-guards nil))
  (mbe :logic
(let ((entry (fn-bpi-find-group name entries)))
    (if entry (list :ok (car (cdr entry))) (list :error :unknown-group)))
       :exec
(let ((entry (fn-bpi-find-group name entries)))
    (if entry (list :ok (fn-ag-car (fn-ag-cdr entry))) (list :error :unknown-group)))))
(verify-guards fn-bpi-map-one)

(defun fn-bpi-map-groups (names entries)
  (declare (xargs :guard t :verify-guards nil))
  (mbe :logic
(if (consp names)
      (let ((one (fn-bpi-map-one (car names) entries)))
        (if (equal (car one) :ok)
            (let ((tail (fn-bpi-map-groups (cdr names) entries)))
              (if (equal (car tail) :ok)
                  (list :ok (cons (car (cdr one)) (car (cdr tail))))
                tail))
          one))
    (list :ok nil))
       :exec
(if (consp names)
      (let ((one (fn-bpi-map-one (fn-ag-car names) entries)))
        (if (equal (fn-ag-car one) :ok)
            (let ((tail (fn-bpi-map-groups (fn-ag-cdr names) entries)))
              (if (equal (fn-ag-car tail) :ok)
                  (list :ok (cons (fn-ag-car (fn-ag-cdr one))
                                  (fn-ag-car (fn-ag-cdr tail))))
                tail))
          one))
    (list :ok nil))))
(verify-guards fn-bpi-map-groups)

(defun fn-bpi-policy-p (policy)
  (declare (xargs :guard t))
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
(verify-guards fn-bpi-policy-p)

(defun fn-bpi-context-p (context)
  (declare (xargs :guard t))
  (and (true-listp context) (equal (len context) 4)
       (fn-record-metadata-bytes-p (fn-bpi-context-destination context))
       (fn-record-metadata-bytes-p (fn-bpi-context-source-eid context))
       (fn-record-metadata-bytes-p (fn-bpi-context-bundle-id context))
       (fn-record-uint32p (fn-bpi-context-lifetime context))))
(verify-guards fn-bpi-context-p)

(defun fn-bpi-policy-appliesp (store policy context)
  (declare (xargs :guard t))
  (and (fn-sn-statep store) (fn-bpi-policy-p policy) (fn-bpi-context-p context)
       (equal (fn-bpi-context-destination context)
              (fn-bpi-policy-destination policy))
       (equal (fn-bpi-policy-endpoint policy)
              (fn-bpi-policy-destination policy))
       (equal (fn-bpi-map-values (fn-bpi-policy-group-map policy))
              (fn-sn-groups store))))
(verify-guards fn-bpi-policy-appliesp)

(defun fn-bpi-record-for (store policy msgid-octets group-octets adu)
  (declare (xargs :guard t :verify-guards nil))
  ; fn-record-octets-string is exact for this validated ASCII Message-ID.  The
  ; original ADU itself remains the Store payload without reconstruction.
  (mbe :logic
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
                  (fn-bpi-policy-charge policy))
       :exec
(fn-record-make (len (fn-sf-records (fn-sn-files store)))
                  (fn-bpi-ag-dec (fn-sf-frontier (fn-sn-files store)))
                  (fn-bpi-ag-dec (fn-sf-frontier (fn-sn-files store)))
                  (fn-record-octets-string msgid-octets)
                  adu
                  (fn-ag-car (fn-ag-cdr (fn-bpi-map-groups group-octets
                                                (fn-bpi-policy-group-map policy))))
                  (fn-bpi-policy-archive-id policy)
                  (fn-bpi-policy-subject policy)
                  (fn-bpi-policy-evidence policy)
                  (fn-bpi-policy-charge policy))))
(verify-guards fn-bpi-record-for)

; Result: (:rejected reason) or (:prepared store record).  The caller must
; already have completed the Store's durable allocator reservation sequence;
; this function neither treats BP inbox staging nor a transport ACK as durable
; fn acceptance.
(defun fn-bpi-ingress-prepare (store policy context adu)
  (declare (xargs :guard t :verify-guards nil
                  :guard-hints
                  (("Goal"
                    :use ((:instance fn-article-successful-parse-syntax-p
                                     (octets adu)))
                    :in-theory (e/d (fn-article-result-article)
                                    (fn-article-successful-parse-syntax-p))))))
  (mbe :logic
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
                          (list :rejected :groups-or-record)))))))))))))
       :exec
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
                        (fn-bpi-ag-result-article parsed))))
            (if (not (equal (fn-ag-car proto) :ok))
                (list :rejected (fn-ag-car (fn-ag-cdr proto)))
              (let ((msgid (fn-ag-car (fn-ag-cdr proto)))
                    (groups (fn-ag-car (fn-ag-cdr (fn-ag-cdr proto)))))
                (if (not msgid)
                    (list :rejected :message-id-missing)
                  (let ((mapped (fn-bpi-map-groups
                                 groups (fn-bpi-policy-group-map policy))))
                    (if (not (equal (fn-ag-car mapped) :ok))
                        (list :rejected (fn-ag-car (fn-ag-cdr mapped)))
                      (let ((record (fn-bpi-record-for store policy msgid groups adu)))
                        (if (and (fn-record-p record)
                                 (fn-selection-validp (fn-bpi-ag-record-groups record)
                                                      (fn-sn-groups store)))
                            (let ((next (fn-sn-prepare store record)))
                              (if (equal next store)
                                  (list :rejected :store-refused)
                                (list :prepared next record)))
                          (list :rejected :groups-or-record)))))))))))))))
(verify-guards fn-bpi-ingress-prepare)

(defun fn-bpi-result-kind (result)
  (declare (xargs :guard t :verify-guards nil))
  (mbe :logic (car result) :exec (fn-ag-car result)))
(verify-guards fn-bpi-result-kind)

(defun fn-bpi-result-store (result)
  (declare (xargs :guard t :verify-guards nil))
  (mbe :logic (car (cdr result)) :exec (fn-ag-car (fn-ag-cdr result))))
(verify-guards fn-bpi-result-store)

(defun fn-bpi-result-record (result)
  (declare (xargs :guard t :verify-guards nil))
  (mbe :logic (car (cdr (cdr result)))
       :exec (fn-ag-car (fn-ag-cdr (fn-ag-cdr result)))))
(verify-guards fn-bpi-result-record)

; Testable application of the existing record publication phases.  Each :ok is
; a file-kernel observation, not a BP acknowledgement.  The only final step is
; the actual fn-sn-finish durable-node completion.
(defun fn-bpi-finish-prepared (store)
  (declare (xargs :guard t))
  (fn-sn-finish
   (fn-sn-io
    (fn-sn-io
     (fn-sn-io store :record-file :ok)
     :record-link :ok)
    :record-directory :ok)))
(verify-guards fn-bpi-finish-prepared)

(defun fn-bpi-node-record-committedp (node record)
  (declare (xargs :guard t :verify-guards nil))
  ; This unfolds the actual node's published article and archive binding; it
  ; does not rely on an external completion word or transport acknowledgement.
  (mbe :logic
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
                (fn-record-obligation-id record))))
       :exec
(let ((article (fn-find-article
                  (fn-bpi-ag-record-msgid record)
                  (fn-state-articles (fn-node-acceptance node))))
        (binding (fn-node-find-binding
                  (fn-bpi-ag-record-msgid record) (fn-node-bindings node))))
    (and (fn-node-statep node) (consp article) (consp binding)
         (equal (fn-article-payload article) (fn-bpi-ag-record-payload record))
         (equal (fn-article-groups article) (fn-bpi-ag-record-groups record))
         (equal (fn-node-binding-subject binding)
                (fn-bpi-ag-record-content-subject record))
         (equal (fn-node-binding-id binding)
                (fn-bpi-ag-record-obligation-id record))))))
(verify-guards fn-bpi-node-record-committedp)

(defun fn-bpi-durably-acceptedp (store record)
  (declare (xargs :guard t :verify-guards nil))
  (mbe :logic
(and (fn-sn-statep store) (fn-record-p record)
       (fn-bpi-node-record-committedp (fn-sn-node store) record)
       (member-equal (fn-sf-record-pair record)
                     (fn-sf-successes (fn-sn-files store))))
       :exec
(and (fn-sn-statep store) (fn-record-p record)
       (fn-bpi-node-record-committedp (fn-sn-node store) record)
       (fn-ag-member (fn-sf-record-pair record)
                     (fn-sf-successes (fn-sn-files store))))))
(verify-guards fn-bpi-durably-acceptedp)

; This bounded replay query uses the same parser, field policy, group map, and
; node binding as preparation.  It is suitable for a host to recognize an
; exact already-durable staged ADU before reserving another local transaction.
; It never equates BPA identifiers or transport provenance with article
; identity; the node predicate compares the parsed Message-ID, exact payload,
; groups, archive obligation, and immutable subject.
(defun fn-bpi-adu-durably-acceptedp (store policy context adu)
  (declare (xargs :guard t :verify-guards nil
                  :guard-hints
                  (("Goal"
                    :use ((:instance fn-article-successful-parse-syntax-p
                                     (octets adu)))
                    :in-theory (e/d (fn-article-result-article)
                                    (fn-article-successful-parse-syntax-p))))))
  (mbe :logic
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
                        (fn-bpi-record-for store policy msgid groups adu)))))))))))
       :exec
(if (not (and (fn-bpi-policy-appliesp store policy context)
                (fn-cbor-octet-listp adu)
                (<= (len adu) *fn-article-max-octets*)))
      nil
    (let ((parsed (fn-article-parse adu)))
      (if (not (fn-article-result-okp parsed))
          nil
        (let ((proto (fn-af-proto-article-check
                      (fn-bpi-ag-result-article parsed))))
          (if (not (equal (fn-ag-car proto) :ok))
              nil
            (let ((msgid (fn-ag-car (fn-ag-cdr proto)))
                  (groups (fn-ag-car (fn-ag-cdr (fn-ag-cdr proto)))))
              (if (not msgid)
                  nil
                (let ((mapped (fn-bpi-map-groups
                               groups (fn-bpi-policy-group-map policy))))
                  (and (equal (fn-ag-car mapped) :ok)
                       (fn-bpi-node-record-committedp
                        (fn-sn-node store)
                        (fn-bpi-record-for store policy msgid groups adu)))))))))))))
(verify-guards fn-bpi-adu-durably-acceptedp)

; This is only an unsigned receipt-eligibility context.  Current records do
; not carry the separate durable receipt-intent/decision required for an
; application receipt, its A-POLICY authorization, or a signature grammar.
(defun fn-bpi-receipt-eligibility (store record policy context)
  (declare (xargs :guard t :verify-guards nil))
  (mbe :logic
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
    nil)
       :exec
(if (and (fn-bpi-durably-acceptedp store record)
           (fn-bpi-policy-appliesp store policy context)
           (equal (fn-bpi-ag-record-content-subject record)
                  (fn-bpi-policy-subject policy))
           (equal (fn-bpi-ag-record-obligation-id record)
                  (fn-bpi-policy-archive-id policy)))
      (list :eligible (fn-bpi-ag-record-msgid record) (fn-bpi-policy-subject policy)
            (fn-bpi-policy-archive-id policy) (fn-bpi-policy-id policy)
            (fn-bpi-policy-terms-id policy) (fn-bpi-policy-issuer-eid policy)
            (fn-bpi-context-source-eid context))
    nil)))
(verify-guards fn-bpi-receipt-eligibility)
