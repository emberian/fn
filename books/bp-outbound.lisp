; Experimental sender composition from durable workflow work to the portable
; BP ADU profile, and from a returned receipt ADU to a local receipt intent.
;
; This book performs no BP transport, storage publication, signature check, or
; A-POLICY decision.  The caller supplies an explicit trusted policy result.
(in-package "ACL2")
(include-book "bp-workflow-records")
(include-book "bp-adu")

; Result: (:ok value) or (:error reason).
(defun fn-bpo-make-ok (value)
  (declare (xargs :guard t))
  (list :ok value))

(defun fn-bpo-make-error (reason)
  (declare (xargs :guard t))
  (list :error reason))

(defun fn-bpo-result-okp (result)
  (declare (xargs :guard t))
  (and (consp result) (equal (fn-bp-nth 0 result) :ok)))

(defun fn-bpo-result-value (result)
  (declare (xargs :guard t))
  (fn-bp-nth 1 result))

; Only the exact current durable-attempt identity may obtain the ADU that the
; host pairs with its one-shot :submit effect.
(defun fn-bpo-current-attemptp (work attempt-id attempt-generation)
  (declare (xargs :guard t))
  (let ((attempt (fn-bp-work-attempt work)))
    (and (consp attempt)
         (equal (fn-bp-attempt-id attempt) attempt-id)
         (equal (fn-bp-attempt-generation attempt) attempt-generation)
         (equal (fn-bp-attempt-status attempt) :intent))))

(defun fn-bpo-request-message (s work-id attempt-id attempt-generation)
  (declare (xargs :guard t))
  (if (or (not (fn-bp-statep s))
          (consp (fn-bp-state-pending s))
          (fn-bp-state-fenced s))
      nil
    (let* ((work (fn-bp-find-work work-id (fn-bp-state-works s)))
           (node (fn-bp-state-node s))
           (article
            (fn-find-article
             (fn-bp-work-msgid work)
             (fn-state-articles (fn-node-acceptance node)))))
      (if (or (not (fn-bp-work-outstandingp work))
              (not (fn-bpo-current-attemptp
                    work attempt-id attempt-generation))
              (not (fn-bp-work-boundp node work))
              (not (consp article)))
          nil
        (let ((request
               (fn-bpa-make-request
                (fn-bp-work-id work)
                (fn-bp-work-subject work)
                (fn-bp-config-local-eid (fn-bp-state-config s))
                (fn-bp-work-peer-eid work)
                (fn-bp-work-policy-id work)
                (fn-bp-work-incarnation work)
                (fn-bp-work-auth-context work)
                (fn-bp-work-terms-id work)
                (fn-article-payload article))))
          ; This is also the portable metadata and exact article-size gate.
          (if (fn-bpa-requestp request) request nil))))))

(defun fn-bpo-request-adu (s work-id attempt-id attempt-generation)
  (declare (xargs :guard t))
  (let ((request
         (fn-bpo-request-message s work-id attempt-id attempt-generation)))
    (if (consp request)
        (fn-bpo-make-ok (fn-bpa-encode request))
      (fn-bpo-make-error :request-refused))))

; Convert only a successfully decoded kind-1 portable value.  The tag is
; removed because fn-bp receipts are the current nine untagged fields.
(defun fn-bpo-adu-receipt-to-bp (message)
  (declare (xargs :guard t))
  (fn-bp-make-receipt
   (fn-bpa-receipt-id message)
   (fn-bpa-receipt-work-id message)
   (fn-bpa-receipt-subject message)
   (fn-bpa-receipt-issuer message)
   (fn-bpa-receipt-peer-eid message)
   (fn-bpa-receipt-policy-id message)
   (fn-bpa-receipt-incarnation message)
   (fn-bpa-receipt-auth-context message)
   (fn-bpa-receipt-terms-id message)))

(defun fn-bpo-decode-receipt (octets)
  (declare (xargs :guard t :verify-guards nil))
  (let ((decoded (fn-bpa-decode-exact octets)))
    (if (not (fn-bpa-result-okp decoded))
        nil
      (let ((message (fn-bpa-result-message decoded)))
        (if (fn-bpa-receiptp message)
            (fn-bpo-adu-receipt-to-bp message)
          nil)))))
(verify-guards fn-bpo-decode-receipt)

; txid and generation are local journal allocation inputs.  They occur only in
; this local record and are never read from or written to the portable ADU.
(defun fn-bpo-make-receipt-intent-record (txid generation receipt)
  (declare (xargs :guard t))
  (list :receipt-intent txid generation
        (fn-bp-receipt-id receipt)
        (fn-bp-receipt-work-id receipt)
        (fn-bp-receipt-subject receipt)
        (fn-bp-receipt-issuer receipt)
        (fn-bp-receipt-peer-eid receipt)
        (fn-bp-receipt-policy-id receipt)
        (fn-bp-receipt-incarnation receipt)
        (fn-bp-receipt-auth-context receipt)
        (fn-bp-receipt-terms-id receipt)))

(defun fn-bpo-receipt-intent-record
  (s txid generation receipt-octets policy-authorizedp)
  (declare (xargs :guard t :verify-guards nil))
  ; The actual workflow journal transition owns all identity, authority,
  ; pending/fence and local transaction-pair checks.
  (mbe :logic
(if (not (equal policy-authorizedp t))
      (fn-bpo-make-error :policy-refused)
    (let ((receipt (fn-bpo-decode-receipt receipt-octets)))
      (if (not (consp receipt))
          (fn-bpo-make-error :receipt-refused)
        (let* ((record
                (fn-bpo-make-receipt-intent-record
                 txid generation receipt))
               (applied (fn-bp-apply-journal-record s record)))
          (if (car applied)
              (fn-bpo-make-ok record)
            (fn-bpo-make-error :receipt-refused))))))
       :exec
(if (not (equal policy-authorizedp t))
      (fn-bpo-make-error :policy-refused)
    (let ((receipt (fn-bpo-decode-receipt receipt-octets)))
      (if (not (consp receipt))
          (fn-bpo-make-error :receipt-refused)
        (let* ((record
                (fn-bpo-make-receipt-intent-record
                 txid generation receipt))
               (applied (fn-bp-apply-journal-record s record)))
          (if (fn-ag-car applied)
              (fn-bpo-make-ok record)
            (fn-bpo-make-error :receipt-refused)))))) ))
(verify-guards fn-bpo-receipt-intent-record)

; ---------------------------------------------------------------------------
; Composition properties

(defthm fn-bpo-request-message-is-request
  (implies
   (consp (fn-bpo-request-message
           s work-id attempt-id attempt-generation))
   (fn-bpa-requestp
    (fn-bpo-request-message
     s work-id attempt-id attempt-generation)))
  :hints (("Goal"
           :in-theory
           (e/d (fn-bpo-request-message)
                (fn-bp-statep fn-bp-state-pending fn-bp-state-fenced
                 fn-bp-find-work fn-bp-state-works fn-bp-state-node
                 fn-bp-work-msgid fn-state-articles fn-node-acceptance
                 fn-find-article fn-bp-work-outstandingp
                 fn-bpo-current-attemptp fn-bp-work-boundp
                 fn-bpa-requestp fn-bpa-make-request)))))

(defthm fn-bpo-request-result-okp
  (equal
   (fn-bpo-result-okp
    (fn-bpo-request-adu s work-id attempt-id attempt-generation))
   (consp (fn-bpo-request-message
           s work-id attempt-id attempt-generation)))
  :hints (("Goal"
           :in-theory
           (e/d (fn-bpo-request-adu fn-bpo-result-okp
                                    fn-bpo-make-ok fn-bpo-make-error)
                (fn-bpo-request-message fn-bpa-encode)))))

(defthm fn-bpo-request-result-value
  (implies
   (consp (fn-bpo-request-message
           s work-id attempt-id attempt-generation))
   (equal
    (fn-bpo-result-value
     (fn-bpo-request-adu s work-id attempt-id attempt-generation))
    (fn-bpa-encode
     (fn-bpo-request-message
      s work-id attempt-id attempt-generation))))
  :hints (("Goal"
           :in-theory
           (e/d (fn-bpo-request-adu fn-bpo-result-value fn-bpo-make-ok)
                (fn-bpo-request-message fn-bpa-encode)))))

(defthm fn-bpo-request-success-decodes-exactly
  (implies
   (fn-bpo-result-okp
    (fn-bpo-request-adu s work-id attempt-id attempt-generation))
   (equal
    (fn-bpa-decode-exact
     (fn-bpo-result-value
      (fn-bpo-request-adu s work-id attempt-id attempt-generation)))
    (list :ok
          (fn-bpo-request-message
           s work-id attempt-id attempt-generation))))
  :hints (("Goal"
           :use ((:instance fn-bpa-round-trip
                            (message
                             (fn-bpo-request-message
                              s work-id attempt-id attempt-generation))))
           :in-theory (disable fn-bpa-round-trip
                               fn-bpa-decode-exact
                               fn-bpa-encode
                               fn-bpo-request-adu
                               fn-bpo-request-message
                               fn-bpo-result-okp
                               fn-bpo-result-value))))

(defthm fn-bpo-request-message-is-exact-construction
  (implies
   (consp (fn-bpo-request-message
           s work-id attempt-id attempt-generation))
   (let* ((work (fn-bp-find-work work-id (fn-bp-state-works s)))
          (article
           (fn-find-article
            (fn-bp-work-msgid work)
            (fn-state-articles
             (fn-node-acceptance (fn-bp-state-node s))))))
     (equal
      (fn-bpo-request-message s work-id attempt-id attempt-generation)
      (fn-bpa-make-request
       (fn-bp-work-id work)
       (fn-bp-work-subject work)
       (fn-bp-config-local-eid (fn-bp-state-config s))
       (fn-bp-work-peer-eid work)
       (fn-bp-work-policy-id work)
       (fn-bp-work-incarnation work)
       (fn-bp-work-auth-context work)
       (fn-bp-work-terms-id work)
       (fn-article-payload article)))))
  :hints (("Goal"
           :in-theory
           (e/d (fn-bpo-request-message)
                (fn-bp-statep fn-bp-state-pending fn-bp-state-fenced
                 fn-bp-find-work fn-bp-state-works fn-bp-state-node
                 fn-bp-state-config fn-bp-work-msgid fn-state-articles
                 fn-node-acceptance fn-find-article
                 fn-bp-work-outstandingp fn-bpo-current-attemptp
                 fn-bp-work-boundp fn-bpa-requestp
                 fn-bpa-make-request)))))

(defthm fn-bpo-request-success-preserves-context-and-article
  (implies
   (fn-bpo-result-okp
    (fn-bpo-request-adu s work-id attempt-id attempt-generation))
   (let* ((request
           (fn-bpo-request-message
            s work-id attempt-id attempt-generation))
          (work (fn-bp-find-work work-id (fn-bp-state-works s)))
          (article
           (fn-find-article
            (fn-bp-work-msgid work)
            (fn-state-articles
             (fn-node-acceptance (fn-bp-state-node s))))))
     (and (equal (fn-bpa-request-work-id request) (fn-bp-work-id work))
          (equal (fn-bpa-request-subject request) (fn-bp-work-subject work))
          (equal (fn-bpa-request-source-eid request)
                 (fn-bp-config-local-eid (fn-bp-state-config s)))
          (equal (fn-bpa-request-destination-eid request)
                 (fn-bp-work-peer-eid work))
          (equal (fn-bpa-request-policy-id request)
                 (fn-bp-work-policy-id work))
          (equal (fn-bpa-request-incarnation request)
                 (fn-bp-work-incarnation work))
          (equal (fn-bpa-request-auth-context request)
                 (fn-bp-work-auth-context work))
          (equal (fn-bpa-request-terms-id request)
                 (fn-bp-work-terms-id work))
          (equal (fn-bpa-request-article request)
                 (fn-article-payload article)))))
  :hints (("Goal"
           :use ((:instance fn-bpo-request-message-is-exact-construction))
           :in-theory (disable fn-bpo-request-adu
                               fn-bpo-request-message
                               fn-bpo-result-okp
                               fn-bp-find-work
                               fn-bp-state-works
                               fn-bp-state-node
                               fn-bp-state-config
                               fn-bp-work-msgid
                               fn-state-articles
                               fn-node-acceptance
                               fn-find-article))))

(defthm fn-bpo-receipt-success-requires-local-policy
  (implies
   (fn-bpo-result-okp
    (fn-bpo-receipt-intent-record
     s txid generation receipt-octets policy-authorizedp))
   (equal policy-authorizedp t))
  :rule-classes nil
  :hints (("Goal"
           :in-theory
           (e/d (fn-bpo-receipt-intent-record
                 fn-bpo-result-okp fn-bpo-make-error fn-bpo-make-ok)
                (fn-bpo-decode-receipt
                 fn-bpo-make-receipt-intent-record
                 fn-bp-apply-journal-record)))))

(defthm fn-bpo-journal-apply-success-has-record
  (implies (car (fn-bp-apply-journal-record s record))
           (fn-bp-journal-recordp record))
  :hints (("Goal"
           :in-theory
           (e/d (fn-bp-apply-journal-record)
                (fn-bp-journal-recordp
                 fn-bp-record-event fn-bp-record-contextp
                 fn-bp-step fn-bp-result-state fn-bp-result-effects)))))

(defthm fn-bpo-receipt-success-is-actual-journal-preparation
  (implies
   (fn-bpo-result-okp
    (fn-bpo-receipt-intent-record
     s txid generation receipt-octets policy-authorizedp))
   (let ((record
          (fn-bpo-result-value
           (fn-bpo-receipt-intent-record
            s txid generation receipt-octets policy-authorizedp))))
     (and (fn-bp-journal-recordp record)
          (car (fn-bp-apply-journal-record s record))
          (equal (fn-bp-journal-nth 1 record) txid)
          (equal (fn-bp-journal-nth 2 record) generation)
          (equal (fn-bp-journal-nth 4 record)
                 (fn-bp-receipt-work-id
                  (fn-bpo-decode-receipt receipt-octets))))))
  :hints (("Goal"
           :use ((:instance fn-bpo-journal-apply-success-has-record
                            (record
                             (fn-bpo-result-value
                              (fn-bpo-receipt-intent-record
                               s txid generation receipt-octets
                               policy-authorizedp)))))
           :in-theory
           (e/d (fn-bpo-receipt-intent-record
                 fn-bpo-result-okp fn-bpo-result-value
                 fn-bpo-make-error fn-bpo-make-ok
                 fn-bpo-make-receipt-intent-record)
                (fn-bpo-decode-receipt
                 fn-bp-apply-journal-record
                 fn-bp-journal-recordp)))))

(defthm fn-bpo-portable-receipt-fields-exclude-local-transaction
  (equal (nthcdr 3 (fn-bpo-make-receipt-intent-record
                    txid generation receipt))
         (list (fn-bp-receipt-id receipt)
               (fn-bp-receipt-work-id receipt)
               (fn-bp-receipt-subject receipt)
               (fn-bp-receipt-issuer receipt)
               (fn-bp-receipt-peer-eid receipt)
               (fn-bp-receipt-policy-id receipt)
               (fn-bp-receipt-incarnation receipt)
               (fn-bp-receipt-auth-context receipt)
               (fn-bp-receipt-terms-id receipt))))
