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
; article-properties is included locally: this book cites one of its
; theorems (fn-article-successful-parse-syntax-p) in two guard proofs and
; nothing else.  Included non-locally, its fn-article-successful-parse-*
; rules (a conclusion over a bare variable under the hypothesis
; (fn-article-result-okp (fn-article-parse octets))) backchained into the
; parser from every fn-cbor-octet-listp and len goal in every book above
; this one; bp-receiver-evolving-store-invariants went from six minutes to
; an 1800 s timeout on the include alone (measured 2026-09-19).
(local (include-book "article-properties"))
; codecs withdrew the record and cbor proof vocabularies at export (2026-09-19);
; this book reasons under them, so open them here, locally.
(local (in-theory (enable fn-record-record-vocabulary fn-record-codec-vocabulary fn-record-guard-vocabulary
                          fn-cbor-record-vocabulary fn-cbor-codec-vocabulary)))
; fn-node-statep is withdrawn at node's export (core, 2026-09-19); the guards below open it.
(local (in-theory (enable fn-node-statep)))

; -----------------------------------------------------------------------------
; Total, guard-t readers used only inside :exec branches below.  Each is its
; narrower-guarded reader by mbe: the :logic branch is the real accessor, so
; opening the helper is the equality and no -is- rule leaves this book.

(defun fn-bpi-ag-dec (x)
  (declare (xargs :guard t))
  (mbe :logic (1- x)
       :exec (if (acl2-numberp x) (1- x) -1)))

(defun fn-bpi-ag-result-article (result)
  (declare (xargs :guard t :verify-guards nil))
  (mbe :logic (fn-article-result-article result)
       :exec (fn-ag-car (fn-ag-cdr result))))
(verify-guards fn-bpi-ag-result-article
  :hints (("Goal" :in-theory (enable fn-article-result-article))))

(defun fn-bpi-ag-record-msgid (record)
  (declare (xargs :guard t :verify-guards nil))
  (mbe :logic (fn-record-msgid record)
       :exec (fn-ag-car (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr record))))))
(verify-guards fn-bpi-ag-record-msgid
  :hints (("Goal" :in-theory (enable fn-record-msgid))))

(defun fn-bpi-ag-record-payload (record)
  (declare (xargs :guard t :verify-guards nil))
  (mbe :logic (fn-record-payload record)
       :exec (fn-ag-car (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr record)))))))
(verify-guards fn-bpi-ag-record-payload
  :hints (("Goal" :in-theory (enable fn-record-payload))))

(defun fn-bpi-ag-record-groups (record)
  (declare (xargs :guard t :verify-guards nil))
  (mbe :logic (fn-record-groups record)
       :exec (fn-ag-car (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr record))))))))
(verify-guards fn-bpi-ag-record-groups
  :hints (("Goal" :in-theory (enable fn-record-groups))))

(defun fn-bpi-ag-record-obligation-id (record)
  (declare (xargs :guard t :verify-guards nil))
  (mbe :logic (fn-record-obligation-id record)
       :exec (fn-ag-car (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr record)))))))))
(verify-guards fn-bpi-ag-record-obligation-id
  :hints (("Goal" :in-theory (enable fn-record-obligation-id))))

(defun fn-bpi-ag-record-content-subject (record)
  (declare (xargs :guard t :verify-guards nil))
  (mbe :logic (fn-record-content-subject record)
       :exec (fn-ag-car (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr record))))))))))
(verify-guards fn-bpi-ag-record-content-subject
  :hints (("Goal" :in-theory (enable fn-record-content-subject))))

; Policy: (destination endpoint group-map archive-id immutable-subject
;          release-evidence charge policy-id terms-id issuer-eid).
; A group-map entry is (parsed-newsgroup-octets local-store-group-string).
(defun fn-bpi-policy-shapep (x)
  (declare (xargs :guard t))
  (and (true-listp x) (equal (len x) 10)))
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

(defthm fn-bpi-policy-shapep-of-fn-bpi-make-policy
  (fn-bpi-policy-shapep (fn-bpi-make-policy destination endpoint group-map archive-id subject
                                        evidence charge policy-id terms-id issuer-eid)))
(defthm fn-bpi-policy-destination-of-fn-bpi-make-policy
  (equal (fn-bpi-policy-destination (fn-bpi-make-policy destination endpoint group-map archive-id subject
                                        evidence charge policy-id terms-id issuer-eid))
         destination))
(defthm fn-bpi-policy-endpoint-of-fn-bpi-make-policy
  (equal (fn-bpi-policy-endpoint (fn-bpi-make-policy destination endpoint group-map archive-id subject
                                        evidence charge policy-id terms-id issuer-eid))
         endpoint))
(defthm fn-bpi-policy-group-map-of-fn-bpi-make-policy
  (equal (fn-bpi-policy-group-map (fn-bpi-make-policy destination endpoint group-map archive-id subject
                                        evidence charge policy-id terms-id issuer-eid))
         group-map))
(defthm fn-bpi-policy-archive-id-of-fn-bpi-make-policy
  (equal (fn-bpi-policy-archive-id (fn-bpi-make-policy destination endpoint group-map archive-id subject
                                        evidence charge policy-id terms-id issuer-eid))
         archive-id))
(defthm fn-bpi-policy-subject-of-fn-bpi-make-policy
  (equal (fn-bpi-policy-subject (fn-bpi-make-policy destination endpoint group-map archive-id subject
                                        evidence charge policy-id terms-id issuer-eid))
         subject))
(defthm fn-bpi-policy-evidence-of-fn-bpi-make-policy
  (equal (fn-bpi-policy-evidence (fn-bpi-make-policy destination endpoint group-map archive-id subject
                                        evidence charge policy-id terms-id issuer-eid))
         evidence))
(defthm fn-bpi-policy-charge-of-fn-bpi-make-policy
  (equal (fn-bpi-policy-charge (fn-bpi-make-policy destination endpoint group-map archive-id subject
                                        evidence charge policy-id terms-id issuer-eid))
         charge))
(defthm fn-bpi-policy-id-of-fn-bpi-make-policy
  (equal (fn-bpi-policy-id (fn-bpi-make-policy destination endpoint group-map archive-id subject
                                        evidence charge policy-id terms-id issuer-eid))
         policy-id))
(defthm fn-bpi-policy-terms-id-of-fn-bpi-make-policy
  (equal (fn-bpi-policy-terms-id (fn-bpi-make-policy destination endpoint group-map archive-id subject
                                        evidence charge policy-id terms-id issuer-eid))
         terms-id))
(defthm fn-bpi-policy-issuer-eid-of-fn-bpi-make-policy
  (equal (fn-bpi-policy-issuer-eid (fn-bpi-make-policy destination endpoint group-map archive-id subject
                                        evidence charge policy-id terms-id issuer-eid))
         issuer-eid))
(defthm fn-bpi-policy-shapep-forward-shape
  (implies (fn-bpi-policy-shapep x) (and (consp x) (true-listp x)))
  :rule-classes :forward-chaining)
(defthm fn-bpi-policy-accessors-forward-consp
  (and (implies (fn-bpi-policy-destination x) (consp x))
       (implies (fn-bpi-policy-endpoint x) (consp x))
       (implies (fn-bpi-policy-group-map x) (consp x))
       (implies (fn-bpi-policy-archive-id x) (consp x))
       (implies (fn-bpi-policy-subject x) (consp x))
       (implies (fn-bpi-policy-evidence x) (consp x))
       (implies (fn-bpi-policy-charge x) (consp x))
       (implies (fn-bpi-policy-id x) (consp x))
       (implies (fn-bpi-policy-terms-id x) (consp x))
       (implies (fn-bpi-policy-issuer-eid x) (consp x)))
  :rule-classes ((:forward-chaining :corollary (implies (fn-bpi-policy-destination x) (consp x))
                                    :trigger-terms ((fn-bpi-policy-destination x)))
                 (:forward-chaining :corollary (implies (fn-bpi-policy-endpoint x) (consp x))
                                    :trigger-terms ((fn-bpi-policy-endpoint x)))
                 (:forward-chaining :corollary (implies (fn-bpi-policy-group-map x) (consp x))
                                    :trigger-terms ((fn-bpi-policy-group-map x)))
                 (:forward-chaining :corollary (implies (fn-bpi-policy-archive-id x) (consp x))
                                    :trigger-terms ((fn-bpi-policy-archive-id x)))
                 (:forward-chaining :corollary (implies (fn-bpi-policy-subject x) (consp x))
                                    :trigger-terms ((fn-bpi-policy-subject x)))
                 (:forward-chaining :corollary (implies (fn-bpi-policy-evidence x) (consp x))
                                    :trigger-terms ((fn-bpi-policy-evidence x)))
                 (:forward-chaining :corollary (implies (fn-bpi-policy-charge x) (consp x))
                                    :trigger-terms ((fn-bpi-policy-charge x)))
                 (:forward-chaining :corollary (implies (fn-bpi-policy-id x) (consp x))
                                    :trigger-terms ((fn-bpi-policy-id x)))
                 (:forward-chaining :corollary (implies (fn-bpi-policy-terms-id x) (consp x))
                                    :trigger-terms ((fn-bpi-policy-terms-id x)))
                 (:forward-chaining :corollary (implies (fn-bpi-policy-issuer-eid x) (consp x))
                                    :trigger-terms ((fn-bpi-policy-issuer-eid x)))))
(in-theory (disable (:d fn-bpi-policy-shapep) (:d fn-bpi-policy-destination) (:d fn-bpi-policy-endpoint) (:d fn-bpi-policy-group-map) (:d fn-bpi-policy-archive-id) (:d fn-bpi-policy-subject) (:d fn-bpi-policy-evidence) (:d fn-bpi-policy-charge) (:d fn-bpi-policy-id) (:d fn-bpi-policy-terms-id) (:d fn-bpi-policy-issuer-eid)
                    (:d fn-bpi-make-policy)))

; Transport context: (destination-eid source-eid bpa-bundle-id bp-lifetime).
; It records what the host observed.  Source EID is deliberately not an
; author/signer input, and BPA bundle IDs remain local transport references.
(defun fn-bpi-context-shapep (x)
  (declare (xargs :guard t))
  (and (true-listp x) (equal (len x) 4)))
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

(defthm fn-bpi-context-shapep-of-fn-bpi-make-context
  (fn-bpi-context-shapep (fn-bpi-make-context destination source-eid bundle-id lifetime)))
(defthm fn-bpi-context-destination-of-fn-bpi-make-context
  (equal (fn-bpi-context-destination (fn-bpi-make-context destination source-eid bundle-id lifetime)) destination))
(defthm fn-bpi-context-source-eid-of-fn-bpi-make-context
  (equal (fn-bpi-context-source-eid (fn-bpi-make-context destination source-eid bundle-id lifetime)) source-eid))
(defthm fn-bpi-context-bundle-id-of-fn-bpi-make-context
  (equal (fn-bpi-context-bundle-id (fn-bpi-make-context destination source-eid bundle-id lifetime)) bundle-id))
(defthm fn-bpi-context-lifetime-of-fn-bpi-make-context
  (equal (fn-bpi-context-lifetime (fn-bpi-make-context destination source-eid bundle-id lifetime)) lifetime))
(defthm fn-bpi-context-shapep-forward-shape
  (implies (fn-bpi-context-shapep x) (and (consp x) (true-listp x)))
  :rule-classes :forward-chaining)
(defthm fn-bpi-context-accessors-forward-consp
  (and (implies (fn-bpi-context-destination x) (consp x))
       (implies (fn-bpi-context-source-eid x) (consp x))
       (implies (fn-bpi-context-bundle-id x) (consp x))
       (implies (fn-bpi-context-lifetime x) (consp x)))
  :rule-classes ((:forward-chaining :corollary (implies (fn-bpi-context-destination x) (consp x))
                                    :trigger-terms ((fn-bpi-context-destination x)))
                 (:forward-chaining :corollary (implies (fn-bpi-context-source-eid x) (consp x))
                                    :trigger-terms ((fn-bpi-context-source-eid x)))
                 (:forward-chaining :corollary (implies (fn-bpi-context-bundle-id x) (consp x))
                                    :trigger-terms ((fn-bpi-context-bundle-id x)))
                 (:forward-chaining :corollary (implies (fn-bpi-context-lifetime x) (consp x))
                                    :trigger-terms ((fn-bpi-context-lifetime x)))))
(in-theory (disable (:d fn-bpi-context-shapep) (:d fn-bpi-context-destination) (:d fn-bpi-context-source-eid) (:d fn-bpi-context-bundle-id) (:d fn-bpi-context-lifetime)
                    (:d fn-bpi-make-context)))

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
  (and (fn-bpi-policy-shapep policy)
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
(defthm fn-bpi-policy-p-forward-shape
  (implies (fn-bpi-policy-p x) (and (consp x) (true-listp x)))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable fn-bpi-policy-p fn-bpi-policy-shapep))))

(defun fn-bpi-context-p (context)
  (declare (xargs :guard t))
  (and (fn-bpi-context-shapep context)
       (fn-record-metadata-bytes-p (fn-bpi-context-destination context))
       (fn-record-metadata-bytes-p (fn-bpi-context-source-eid context))
       (fn-record-metadata-bytes-p (fn-bpi-context-bundle-id context))
       (fn-record-uint32p (fn-bpi-context-lifetime context))))
(verify-guards fn-bpi-context-p)
(defthm fn-bpi-context-p-forward-shape
  (implies (fn-bpi-context-p x) (and (consp x) (true-listp x)))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable fn-bpi-context-p fn-bpi-context-shapep))))

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
                    ; The article-syntax obligation is exactly an instance of
                    ; fn-article-successful-parse-syntax-p, so cite it and keep
                    ; the parser closed: opening fn-article-parse (or the
                    ; result/syntax readers) turns a one-step match into a
                    ; multi-minute case explosion.  fn-bpi-ag-result-article
                    ; opens to fn-article-result-article (its :logic branch),
                    ; which is what makes the instance line up.
                    :use ((:instance fn-article-successful-parse-syntax-p
                                     (octets adu)))
                    :in-theory (disable fn-article-successful-parse-syntax-p
                                        fn-article-parse
                                        fn-article-syntax-p
                                        fn-article-result-okp
                                        fn-article-result-article)))))
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
                    ; The article-syntax obligation is exactly an instance of
                    ; fn-article-successful-parse-syntax-p, so cite it and keep
                    ; the parser closed: opening fn-article-parse (or the
                    ; result/syntax readers) turns a one-step match into a
                    ; multi-minute case explosion.  fn-bpi-ag-result-article
                    ; opens to fn-article-result-article (its :logic branch),
                    ; which is what makes the instance line up.
                    :use ((:instance fn-article-successful-parse-syntax-p
                                     (octets adu)))
                    :in-theory (disable fn-article-successful-parse-syntax-p
                                        fn-article-parse
                                        fn-article-syntax-p
                                        fn-article-result-okp
                                        fn-article-result-article)))))
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

; Export theory.  Recognizers, the ingress transition, the result and
; commitment readers and the durable-acceptance queries are proof vocabulary
; for the receiver books, which open what they need locally.  What stays
; enabled: the record lemmas above, the fn-bpi-ag- helpers (their :logic
; branch is the real reader) and the group-map list vocabulary
; (fn-bpi-group-mapp, fn-bpi-map-values, fn-bpi-find-group, fn-bpi-map-one,
; fn-bpi-map-groups), which proofs induct on.
(in-theory (disable fn-bpi-group-map-entryp fn-bpi-policy-p fn-bpi-context-p
                    fn-bpi-policy-appliesp fn-bpi-record-for
                    fn-bpi-ingress-prepare fn-bpi-result-kind
                    fn-bpi-result-store fn-bpi-result-record
                    fn-bpi-finish-prepared fn-bpi-node-record-committedp
                    fn-bpi-durably-acceptedp fn-bpi-adu-durably-acceptedp
                    fn-bpi-receipt-eligibility))
