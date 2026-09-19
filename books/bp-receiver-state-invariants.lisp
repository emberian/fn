; Recognizer preservation for the experimental BP receiver state machine and
; its local journal replay.  Receiver decisions remain in the base books.
(in-package "ACL2")
(include-book "bp-receipt-records")

(defthm fn-bpr-statep-components
  (implies (fn-bpr-statep st)
           (and (fn-bpr-configp (fn-bpr-state-config st))
                (fn-bpr-context-listp
                 (fn-bpr-state-config st) (fn-bpr-state-contexts st))
                (fn-bpr-receipt-listp
                 (fn-bpr-state-config st) (fn-bpr-state-receipts st))
                (or (null (fn-bpr-state-pending st))
                    (fn-bpr-receipt-entryp
                     (fn-bpr-state-config st)
                     (fn-bpr-state-pending st)))))
  :rule-classes :forward-chaining)

(defthm fn-bpr-statep-of-constructor
  (equal (fn-bpr-statep
          (fn-bpr-make-state config contexts receipts pending))
         (and (fn-bpr-configp config)
              (fn-bpr-context-listp config contexts)
              (fn-bpr-receipt-listp config receipts)
              (or (null pending)
                  (fn-bpr-receipt-entryp config pending)))))

(defthm fn-bpr-receipt-entryp-of-constructor
  (equal (fn-bpr-receipt-entryp
          config (fn-bpr-make-receipt-entry context receipt))
         (and (fn-bpr-contextp config context)
              (fn-bpa-receiptp receipt))))

(defthm fn-bpr-initial-state-preserves-statep
  (implies (fn-bpr-configp config)
           (fn-bpr-statep (fn-bpr-initial-state config))))

(defthm fn-bpr-record-metadata-is-bpa-metadata
  (equal (fn-record-metadata-bytes-p text)
         (fn-bpa-metadatap text)))

(defthm fn-bpr-record-msgid-is-bpa-metadata
  (implies (fn-record-msgidp text)
           (fn-bpa-metadatap text)))

(defthm fn-bpr-request-context-components
  (implies
   (fn-bpa-requestp request)
   (and (fn-bpa-metadatap (fn-bpa-request-work-id request))
        (fn-bpa-metadatap (fn-bpa-request-subject request))
        (fn-bpa-metadatap (fn-bpa-request-source-eid request))
        (fn-bpa-metadatap (fn-bpa-request-policy-id request))
        (fn-bpa-metadatap (fn-bpa-request-incarnation request))
        (fn-bpa-metadatap (fn-bpa-request-auth-context request))
        (fn-bpa-metadatap (fn-bpa-request-terms-id request))))
  :rule-classes :forward-chaining)

(defthm fn-bpr-record-context-components
  (implies
   (fn-record-p record)
   (and (fn-bpa-metadatap (fn-record-msgid record))
        (fn-bpa-metadatap (fn-record-obligation-id record))))
  :rule-classes :forward-chaining)

(defthm fn-bpr-contextp-of-constructor
  (equal
   (fn-bpr-contextp
    config
    (fn-bpr-make-context work-id msgid subject archive-id peer policy
                         incarnation auth-context terms request))
   (and (fn-bpa-metadatap work-id)
        (fn-bpa-metadatap msgid)
        (fn-bpa-metadatap subject)
        (fn-bpa-metadatap archive-id)
        (fn-bpa-metadatap peer)
        (equal policy (fn-bpr-config-policy-id config))
        (fn-bpa-metadatap incarnation)
        (fn-bpa-metadatap auth-context)
        (fn-bpa-metadatap terms)
        (fn-bpa-requestp request)))
  :hints (("Goal"
           :in-theory
           (e/d (fn-bpr-contextp fn-bpr-make-context)
                (fn-bpa-metadatap fn-bpa-requestp)))))

(defthm fn-bpr-context-from-request-is-constructor
  (equal
   (fn-bpr-context-from-request record request)
   (fn-bpr-make-context
    (fn-bpa-request-work-id request)
    (fn-record-msgid record)
    (fn-bpa-request-subject request)
    (fn-record-obligation-id record)
    (fn-bpa-request-source-eid request)
    (fn-bpa-request-policy-id request)
    (fn-bpa-request-incarnation request)
    (fn-bpa-request-auth-context request)
    (fn-bpa-request-terms-id request)
    request))
  :hints (("Goal"
           :in-theory
           (union-theories '(fn-bpr-context-from-request)
                           (theory 'minimal-theory)))))

(defthm fn-bpr-context-from-components
  (implies
   (and (fn-bpa-metadatap (fn-bpa-request-work-id request))
        (fn-bpa-metadatap (fn-record-msgid record))
        (fn-bpa-metadatap (fn-bpa-request-subject request))
        (fn-bpa-metadatap (fn-record-obligation-id record))
        (fn-bpa-metadatap (fn-bpa-request-source-eid request))
        (equal (fn-bpa-request-policy-id request)
               (fn-bpr-config-policy-id config))
        (fn-bpa-metadatap (fn-bpa-request-incarnation request))
        (fn-bpa-metadatap (fn-bpa-request-auth-context request))
        (fn-bpa-metadatap (fn-bpa-request-terms-id request))
        (fn-bpa-requestp request))
   (fn-bpr-contextp
    config (fn-bpr-context-from-request record request)))
  :hints (("Goal"
           :use ((:instance fn-bpr-contextp-of-constructor
                            (work-id (fn-bpa-request-work-id request))
                            (msgid (fn-record-msgid record))
                            (subject (fn-bpa-request-subject request))
                            (archive-id (fn-record-obligation-id record))
                            (peer (fn-bpa-request-source-eid request))
                            (policy (fn-bpa-request-policy-id request))
                            (incarnation
                             (fn-bpa-request-incarnation request))
                            (auth-context
                             (fn-bpa-request-auth-context request))
                            (terms (fn-bpa-request-terms-id request)))
                 (:instance fn-bpr-context-from-request-is-constructor))
           :in-theory (theory 'minimal-theory))))

(defthm fn-bpr-context-from-typed-inputs
  (implies
   (and (fn-bpr-configp config)
        (fn-record-p record)
        (fn-bpa-requestp request)
        (equal (fn-bpa-request-policy-id request)
               (fn-bpr-config-policy-id config)))
   (fn-bpr-contextp
    config (fn-bpr-context-from-request record request)))
  :hints (("Goal"
           :use ((:instance fn-bpr-request-context-components)
                 (:instance fn-bpr-record-context-components)
                 (:instance fn-bpr-context-from-components))
           :in-theory
           (disable fn-bpr-contextp fn-bpr-context-from-request
                    fn-bpr-configp fn-record-p fn-bpa-requestp
                    fn-bpa-metadatap))))

(defthm fn-bpr-acceptable-contextp
  (implies
   (fn-bpr-request-acceptablep
    store config record request policy-authorizedp)
   (fn-bpr-contextp
    config (fn-bpr-context-from-request record request)))
  :hints (("Goal"
           :use ((:instance fn-bpr-context-from-typed-inputs))
           :in-theory
           (e/d (fn-bpr-request-acceptablep)
                (fn-bpr-store-record-acceptedp
                 fn-bpr-contextp fn-bpr-context-from-request
                 fn-bpr-configp fn-record-p fn-bpa-requestp)))))

(defthm fn-bpr-context-list-cons
  (equal (fn-bpr-context-listp config (cons context contexts))
         (and (fn-bpr-contextp config context)
              (fn-bpr-context-listp config contexts)))
  :hints (("Goal"
           :expand ((fn-bpr-context-listp
                     config (cons context contexts)))
           :in-theory
           (disable fn-bpr-context-listp fn-bpr-contextp))))

(defthm fn-bpr-result-state
  (equal (fn-bpa-nth 1 (list tag st)) st))

(defthm fn-bpr-accept-request-preserves-statep
  (implies
   (fn-bpr-statep st)
   (fn-bpr-statep
    (fn-bpa-nth
     1 (fn-bpr-accept-request
        st store record request policy-authorizedp))))
  :hints (("Goal"
           :use ((:instance fn-bpr-statep-components)
                 (:instance fn-bpr-acceptable-contextp
                            (config (fn-bpr-state-config st))))
           :in-theory
           (union-theories
            (theory 'minimal-theory)
            '(fn-bpr-accept-request fn-bpa-nth fn-bpa-car fn-bpa-cdr
              fn-bpr-context-listp fn-bpr-statep-of-constructor
              fn-bpr-result-state fn-bpr-context-list-cons)))))

(defthm fn-bpr-found-context-typed
  (implies (and (fn-bpr-context-listp config contexts)
                (fn-bpr-find-context work-id contexts))
           (fn-bpr-contextp config
                            (fn-bpr-find-context work-id contexts)))
  :hints (("Goal"
           :induct (fn-bpr-find-context work-id contexts)
           :in-theory
           (e/d (fn-bpr-find-context fn-bpr-context-listp)
                (fn-bpr-contextp fn-bpr-context-work-id)))))

(defthm fn-bpr-prepare-receipt-preserves-statep
  (implies (fn-bpr-statep st)
           (fn-bpr-statep
            (fn-bpr-prepare-receipt
             st work-id receipt-id policy-authorizedp)))
  :hints (("Goal"
           :use ((:instance fn-bpr-statep-components)
                 (:instance fn-bpr-found-context-typed
                            (config (fn-bpr-state-config st))
                            (contexts (fn-bpr-state-contexts st))))
           :in-theory
           (union-theories
            '(fn-bpr-prepare-receipt fn-bpr-statep-of-constructor
              fn-bpr-receipt-entryp-of-constructor)
            (theory 'minimal-theory)))))

(defthm fn-bpr-receipt-list-cons
  (equal (fn-bpr-receipt-listp config (cons entry entries))
         (and (fn-bpr-receipt-entryp config entry)
              (fn-bpr-receipt-listp config entries)))
  :hints (("Goal"
           :expand ((fn-bpr-receipt-listp config (cons entry entries)))
           :in-theory
           (disable fn-bpr-receipt-listp fn-bpr-receipt-entryp))))

(defthm fn-bpr-receipt-list-nil
  (fn-bpr-receipt-listp config nil)
  :hints (("Goal" :in-theory (enable fn-bpr-receipt-listp))))

(defthm fn-bpr-commit-receipt-preserves-statep
  (implies (fn-bpr-statep st)
           (fn-bpr-statep
            (fn-bpr-commit-receipt st work-id receipt-id outcome)))
  :hints (("Goal"
           :use ((:instance fn-bpr-statep-components))
           :in-theory
           (union-theories
            '(fn-bpr-commit-receipt fn-bpr-statep-of-constructor
              fn-bpr-receipt-list-cons fn-bpr-receipt-list-nil)
            (theory 'minimal-theory)))))

(defthm fn-bprr-result-state
  (equal (fn-bprr-nth 1 (list tag st)) st))

(defthm fn-bprr-nth-one
  (equal (fn-bprr-nth 1 x) (cadr x)))

(defthm fn-bpa-nth-one
  (equal (fn-bpa-nth 1 x) (cadr x)))

(defthm fn-bpr-accept-request-preserves-statep-for-bprr-nth
  (implies
   (fn-bpr-statep st)
   (fn-bpr-statep
    (fn-bprr-nth
     1 (fn-bpr-accept-request
        st store record request policy-authorizedp))))
  :hints (("Goal"
           :use ((:instance fn-bpr-accept-request-preserves-statep))
           :in-theory
           (union-theories
            '(fn-bprr-nth-one fn-bpa-nth-one)
            (theory 'minimal-theory)))))

(defthm fn-bprr-apply-record-preserves-statep
  (implies (fn-bpr-statep st)
           (fn-bpr-statep
            (fn-bprr-nth 1 (fn-bprr-apply-record st store record))))
  :hints (("Goal"
           :use ((:instance
                  fn-bpr-accept-request-preserves-statep-for-bprr-nth
                            (request
                             (fn-bprr-decode-value
                              (fn-bprr-nth 2 record) :request))
                            (record
                             (fn-bprr-decode-value
                              (fn-bprr-nth 3 record) :record))
                            (policy-authorizedp
                             (fn-bprr-nth 4 record)))
                 (:instance fn-bpr-prepare-receipt-preserves-statep
                            (work-id (fn-bprr-nth 1 record))
                            (receipt-id (fn-bprr-nth 2 record))
                            (policy-authorizedp
                             (fn-bprr-nth 4 record)))
                 (:instance fn-bpr-commit-receipt-preserves-statep
                            (work-id (fn-bprr-nth 1 record))
                            (receipt-id (fn-bprr-nth 2 record))
                            (outcome (fn-bprr-nth 3 record))))
           :in-theory
           (union-theories
            '(fn-bprr-apply-record fn-bprr-result-state)
            (theory 'minimal-theory)))))

(defthm fn-bprr-replay-rest-preserves-statep
  (implies (fn-bpr-statep st)
           (fn-bpr-statep
            (fn-bprr-nth 1 (fn-bprr-replay-rest st store records))))
  :hints (("Goal"
           :induct (fn-bprr-replay-rest st store records)
           :in-theory
           (union-theories
            '(fn-bprr-replay-rest fn-bprr-result-state
              fn-bprr-apply-record-preserves-statep)
            (theory 'minimal-theory)))))

(defthm fn-bprr-successful-replay-has-statep
  (implies (car (fn-bprr-replay store records))
           (fn-bpr-statep
            (fn-bprr-nth 1 (fn-bprr-replay store records))))
  :hints (("Goal"
           :use ((:instance fn-bprr-replay-rest-preserves-statep
                            (st (fn-bpr-initial-state
                                 (fn-bprr-config (car records))))
                            (records (cdr records))))
           :in-theory
           (union-theories
            '(fn-bprr-replay fn-bprr-result-state)
            (theory 'minimal-theory)))))
