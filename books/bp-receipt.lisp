; Experimental receiver-side BP request context and durable receipt decision.
; The request codec is fn-bpa; Store article admission remains fn-bpi.  This is
; deliberately separate from fn-bp's sender-side receipt-evidence workflow.
(in-package "ACL2")
(include-book "bp-adu")
(include-book "bp-ingress")

; Local receiver configuration: (destination-eid policy-id issuer-eid).
(defun fn-bpr-config-shapep (x)
  (declare (xargs :guard t))
  (and (true-listp x) (equal (len x) 3)))
(defun fn-bpr-config-destination (x) (fn-bpa-nth 0 x))
(defun fn-bpr-config-policy-id (x) (fn-bpa-nth 1 x))
(defun fn-bpr-config-issuer (x) (fn-bpa-nth 2 x))
(defun fn-bpr-make-config (destination policy issuer)
  (list destination policy issuer))

(defthm fn-bpr-config-shapep-of-fn-bpr-make-config
  (fn-bpr-config-shapep (fn-bpr-make-config destination policy issuer)))
(defthm fn-bpr-config-destination-of-fn-bpr-make-config
  (equal (fn-bpr-config-destination (fn-bpr-make-config destination policy issuer)) destination))
(defthm fn-bpr-config-policy-id-of-fn-bpr-make-config
  (equal (fn-bpr-config-policy-id (fn-bpr-make-config destination policy issuer)) policy))
(defthm fn-bpr-config-issuer-of-fn-bpr-make-config
  (equal (fn-bpr-config-issuer (fn-bpr-make-config destination policy issuer)) issuer))
(in-theory (disable (:d fn-bpr-config-shapep) (:d fn-bpr-config-destination) (:d fn-bpr-config-policy-id) (:d fn-bpr-config-issuer)
                    (:d fn-bpr-make-config)))
(defun fn-bpr-configp (x)
  (and (fn-bpr-config-shapep x)
       (fn-bpa-metadatap (fn-bpr-config-destination x))
       (fn-bpa-metadatap (fn-bpr-config-policy-id x))
       (fn-bpa-metadatap (fn-bpr-config-issuer x))))

; Durable request context: (work-id msgid subject archive-id peer-eid policy-id
; origin-incarnation authorization-context terms-id exact-request).
(defun fn-bpr-context-shapep (x)
  (declare (xargs :guard t))
  (and (true-listp x) (equal (len x) 10)))
(defun fn-bpr-context-work-id (x) (fn-bpa-nth 0 x))
(defun fn-bpr-context-msgid (x) (fn-bpa-nth 1 x))
(defun fn-bpr-context-subject (x) (fn-bpa-nth 2 x))
(defun fn-bpr-context-archive-id (x) (fn-bpa-nth 3 x))
(defun fn-bpr-context-peer-eid (x) (fn-bpa-nth 4 x))
(defun fn-bpr-context-policy-id (x) (fn-bpa-nth 5 x))
(defun fn-bpr-context-incarnation (x) (fn-bpa-nth 6 x))
(defun fn-bpr-context-auth-context (x) (fn-bpa-nth 7 x))
(defun fn-bpr-context-terms-id (x) (fn-bpa-nth 8 x))
(defun fn-bpr-context-request (x) (fn-bpa-nth 9 x))
(defun fn-bpr-make-context (work-id msgid subject archive-id peer policy
                                     incarnation auth-context terms request)
  (list work-id msgid subject archive-id peer policy incarnation auth-context
        terms request))

(defthm fn-bpr-context-shapep-of-fn-bpr-make-context
  (fn-bpr-context-shapep (fn-bpr-make-context work-id msgid subject archive-id peer policy
                                     incarnation auth-context terms request)))
(defthm fn-bpr-context-work-id-of-fn-bpr-make-context
  (equal (fn-bpr-context-work-id (fn-bpr-make-context work-id msgid subject archive-id peer policy
                                     incarnation auth-context terms request)) work-id))
(defthm fn-bpr-context-msgid-of-fn-bpr-make-context
  (equal (fn-bpr-context-msgid (fn-bpr-make-context work-id msgid subject archive-id peer policy
                                     incarnation auth-context terms request)) msgid))
(defthm fn-bpr-context-subject-of-fn-bpr-make-context
  (equal (fn-bpr-context-subject (fn-bpr-make-context work-id msgid subject archive-id peer policy
                                     incarnation auth-context terms request)) subject))
(defthm fn-bpr-context-archive-id-of-fn-bpr-make-context
  (equal (fn-bpr-context-archive-id (fn-bpr-make-context work-id msgid subject archive-id peer policy
                                     incarnation auth-context terms request)) archive-id))
(defthm fn-bpr-context-peer-eid-of-fn-bpr-make-context
  (equal (fn-bpr-context-peer-eid (fn-bpr-make-context work-id msgid subject archive-id peer policy
                                     incarnation auth-context terms request)) peer))
(defthm fn-bpr-context-policy-id-of-fn-bpr-make-context
  (equal (fn-bpr-context-policy-id (fn-bpr-make-context work-id msgid subject archive-id peer policy
                                     incarnation auth-context terms request)) policy))
(defthm fn-bpr-context-incarnation-of-fn-bpr-make-context
  (equal (fn-bpr-context-incarnation (fn-bpr-make-context work-id msgid subject archive-id peer policy
                                     incarnation auth-context terms request)) incarnation))
(defthm fn-bpr-context-auth-context-of-fn-bpr-make-context
  (equal (fn-bpr-context-auth-context (fn-bpr-make-context work-id msgid subject archive-id peer policy
                                     incarnation auth-context terms request)) auth-context))
(defthm fn-bpr-context-terms-id-of-fn-bpr-make-context
  (equal (fn-bpr-context-terms-id (fn-bpr-make-context work-id msgid subject archive-id peer policy
                                     incarnation auth-context terms request)) terms))
(defthm fn-bpr-context-request-of-fn-bpr-make-context
  (equal (fn-bpr-context-request (fn-bpr-make-context work-id msgid subject archive-id peer policy
                                     incarnation auth-context terms request)) request))
(in-theory (disable (:d fn-bpr-context-shapep) (:d fn-bpr-context-work-id) (:d fn-bpr-context-msgid) (:d fn-bpr-context-subject) (:d fn-bpr-context-archive-id) (:d fn-bpr-context-peer-eid) (:d fn-bpr-context-policy-id) (:d fn-bpr-context-incarnation) (:d fn-bpr-context-auth-context) (:d fn-bpr-context-terms-id) (:d fn-bpr-context-request)
                    (:d fn-bpr-make-context)))

(defun fn-bpr-contextp (config x)
  (and (fn-bpr-context-shapep x)
       (fn-bpa-metadatap (fn-bpr-context-work-id x))
       (fn-bpa-metadatap (fn-bpr-context-msgid x))
       (fn-bpa-metadatap (fn-bpr-context-subject x))
       (fn-bpa-metadatap (fn-bpr-context-archive-id x))
       (fn-bpa-metadatap (fn-bpr-context-peer-eid x))
       (equal (fn-bpr-context-policy-id x) (fn-bpr-config-policy-id config))
       (fn-bpa-metadatap (fn-bpr-context-incarnation x))
       (fn-bpa-metadatap (fn-bpr-context-auth-context x))
       (fn-bpa-metadatap (fn-bpr-context-terms-id x))
       (fn-bpa-requestp (fn-bpr-context-request x))))
(defun fn-bpr-context-listp (config xs)
  (if (consp xs)
      (and (fn-bpr-contextp config (car xs))
           (fn-bpr-context-listp config (cdr xs)))
    (null xs)))
(defun fn-bpr-find-context (work-id xs)
  (if (consp xs)
      (if (equal work-id (fn-bpr-context-work-id (car xs)))
          (car xs)
        (fn-bpr-find-context work-id (cdr xs)))
    nil))
(defun fn-bpr-find-context-msgid (msgid xs)
  (if (consp xs)
      (if (equal msgid (fn-bpr-context-msgid (car xs)))
          (car xs)
        (fn-bpr-find-context-msgid msgid (cdr xs)))
    nil))

; State: (config durable-contexts durable-receipts pending-receipt).
(defun fn-bpr-state-shapep (x)
  (declare (xargs :guard t))
  (and (true-listp x) (equal (len x) 4)))
(defun fn-bpr-state-config (x) (fn-bpa-nth 0 x))
(defun fn-bpr-state-contexts (x) (fn-bpa-nth 1 x))
(defun fn-bpr-state-receipts (x) (fn-bpa-nth 2 x))
(defun fn-bpr-state-pending (x) (fn-bpa-nth 3 x))
(defun fn-bpr-make-state (config contexts receipts pending)
  (list config contexts receipts pending))

(defthm fn-bpr-state-shapep-of-fn-bpr-make-state
  (fn-bpr-state-shapep (fn-bpr-make-state config contexts receipts pending)))
(defthm fn-bpr-state-config-of-fn-bpr-make-state
  (equal (fn-bpr-state-config (fn-bpr-make-state config contexts receipts pending)) config))
(defthm fn-bpr-state-contexts-of-fn-bpr-make-state
  (equal (fn-bpr-state-contexts (fn-bpr-make-state config contexts receipts pending)) contexts))
(defthm fn-bpr-state-receipts-of-fn-bpr-make-state
  (equal (fn-bpr-state-receipts (fn-bpr-make-state config contexts receipts pending)) receipts))
(defthm fn-bpr-state-pending-of-fn-bpr-make-state
  (equal (fn-bpr-state-pending (fn-bpr-make-state config contexts receipts pending)) pending))
(in-theory (disable (:d fn-bpr-state-shapep) (:d fn-bpr-state-config) (:d fn-bpr-state-contexts) (:d fn-bpr-state-receipts) (:d fn-bpr-state-pending)
                    (:d fn-bpr-make-state)))
(defun fn-bpr-receipt-entry-shapep (x)
  (declare (xargs :guard t))
  (and (true-listp x) (equal (len x) 2)))
(defun fn-bpr-receipt-entry-context (x) (fn-bpa-nth 0 x))
(defun fn-bpr-receipt-entry-receipt (x) (fn-bpa-nth 1 x))
(defun fn-bpr-make-receipt-entry (context receipt) (list context receipt))

(defthm fn-bpr-receipt-entry-shapep-of-fn-bpr-make-receipt-entry
  (fn-bpr-receipt-entry-shapep (fn-bpr-make-receipt-entry context receipt)))
(defthm fn-bpr-receipt-entry-context-of-fn-bpr-make-receipt-entry
  (equal (fn-bpr-receipt-entry-context (fn-bpr-make-receipt-entry context receipt)) context))
(defthm fn-bpr-receipt-entry-receipt-of-fn-bpr-make-receipt-entry
  (equal (fn-bpr-receipt-entry-receipt (fn-bpr-make-receipt-entry context receipt)) receipt))
(in-theory (disable (:d fn-bpr-receipt-entry-shapep) (:d fn-bpr-receipt-entry-context) (:d fn-bpr-receipt-entry-receipt)
                    (:d fn-bpr-make-receipt-entry)))
(defun fn-bpr-receipt-entryp (config x)
  (and (fn-bpr-receipt-entry-shapep x)
       (fn-bpr-contextp config (fn-bpr-receipt-entry-context x))
       (fn-bpa-receiptp (fn-bpr-receipt-entry-receipt x))))
(defun fn-bpr-receipt-listp (config xs)
  (if (consp xs)
      (and (fn-bpr-receipt-entryp config (car xs))
           (fn-bpr-receipt-listp config (cdr xs)))
    (null xs)))
(defun fn-bpr-statep (x)
  (and (fn-bpr-state-shapep x)
       (fn-bpr-configp (fn-bpr-state-config x))
       (fn-bpr-context-listp (fn-bpr-state-config x) (fn-bpr-state-contexts x))
       (fn-bpr-receipt-listp (fn-bpr-state-config x) (fn-bpr-state-receipts x))
       (or (null (fn-bpr-state-pending x))
           (fn-bpr-receipt-entryp (fn-bpr-state-config x)
                                  (fn-bpr-state-pending x)))))
(defun fn-bpr-initial-state (config)
  (if (fn-bpr-configp config) (fn-bpr-make-state config nil nil nil) nil))

(defun fn-bpr-context-from-request (record request)
  (fn-bpr-make-context
   (fn-bpa-request-work-id request) (fn-record-msgid record)
   (fn-bpa-request-subject request) (fn-record-obligation-id record)
   (fn-bpa-request-source-eid request) (fn-bpa-request-policy-id request)
   (fn-bpa-request-incarnation request) (fn-bpa-request-auth-context request)
   (fn-bpa-request-terms-id request) request))

; The explicit A-POLICY value is trusted laboratory input.  Request wire fields
; are checked for exact contextual agreement but never authorize acceptance.
(defun fn-bpr-store-record-acceptedp (store record)
  ; Store file completion history is deliberately transient: recovery rebuilds
  ; the durable node from its published namespace and bindings.  Receiver
  ; context replay therefore grounds acceptance in that recovered durable
  ; article/archive binding and authoritative recovered record list, rather
  ; than in a pre-crash success observation.  A non-ready file machine cannot
  ; issue a receiver receipt, even if its node still has a matching article.
  (and (fn-sn-statep store) (fn-record-p record)
       (equal (fn-sf-phase (fn-sn-files store)) :ready)
       (member-equal record (fn-sf-records (fn-sn-files store)))
       (fn-bpi-node-record-committedp (fn-sn-node store) record)))
(defun fn-bpr-request-acceptablep (store config record request policy-authorizedp)
  (and (equal policy-authorizedp t) (fn-bpr-configp config)
       (fn-bpa-requestp request) (fn-record-p record)
       (fn-bpr-store-record-acceptedp store record)
       (equal (fn-bpa-request-destination-eid request)
              (fn-bpr-config-destination config))
       (equal (fn-bpa-request-policy-id request)
              (fn-bpr-config-policy-id config))
       (equal (fn-bpa-request-subject request)
              (fn-record-content-subject record))
       (equal (fn-bpa-request-article request) (fn-record-payload record))))

; Result tags: :accepted, :duplicate, :conflict, :refused.  The context is
; retained only after actual Store durable acceptance and a local A-POLICY.
(defun fn-bpr-accept-request (st store record request policy-authorizedp)
  (if (not (and (fn-bpr-statep st) (not (consp (fn-bpr-state-pending st)))
                (fn-bpr-request-acceptablep store (fn-bpr-state-config st)
                                             record request policy-authorizedp)))
      (list :refused st)
    (let* ((context (fn-bpr-context-from-request record request))
           (prior (fn-bpr-find-context (fn-bpr-context-work-id context)
                                       (fn-bpr-state-contexts st)))
           (by-msgid (fn-bpr-find-context-msgid (fn-bpr-context-msgid context)
                                                (fn-bpr-state-contexts st))))
      (if prior
          (if (equal prior context) (list :duplicate st) (list :conflict st))
        (if by-msgid
            (list :conflict st)
          (list :accepted
                (fn-bpr-make-state
                 (fn-bpr-state-config st)
                 (cons context (fn-bpr-state-contexts st))
                 (fn-bpr-state-receipts st) nil)))))))

(defun fn-bpr-receipt-for (context config receipt-id)
  (fn-bpa-make-receipt receipt-id (fn-bpr-context-work-id context)
                       (fn-bpr-context-subject context)
                       (fn-bpr-config-issuer config)
                       ; The receipt goes to the receiver endpoint (the
                       ; request destination), not to its source transport
                       ; provenance.  Source remains retained in context.
                       (fn-bpr-config-destination config)
                       (fn-bpr-context-policy-id context)
                       (fn-bpr-context-incarnation context)
                       (fn-bpr-context-auth-context context)
                       (fn-bpr-context-terms-id context)))
(defun fn-bpr-find-receipt (work-id entries)
  (if (consp entries)
      (if (equal work-id (fn-bpr-context-work-id
                          (fn-bpr-receipt-entry-context (car entries))))
          (car entries)
        (fn-bpr-find-receipt work-id (cdr entries)))
    nil))

; Receipt intent must be persisted before its committed publication decision.
(defun fn-bpr-prepare-receipt (st work-id receipt-id policy-authorizedp)
  (if (or (not (fn-bpr-statep st)) (not (equal policy-authorizedp t))
          (consp (fn-bpr-state-pending st)))
      st
    (let ((context (fn-bpr-find-context work-id (fn-bpr-state-contexts st))))
      (if (or (not context) (fn-bpr-find-receipt work-id (fn-bpr-state-receipts st)))
          st
        (let ((receipt (fn-bpr-receipt-for context (fn-bpr-state-config st) receipt-id)))
          (if (fn-bpa-receiptp receipt)
              (fn-bpr-make-state (fn-bpr-state-config st)
                                 (fn-bpr-state-contexts st)
                                 (fn-bpr-state-receipts st)
                                 (fn-bpr-make-receipt-entry context receipt))
            st))))))
(defun fn-bpr-commit-receipt (st work-id receipt-id outcome)
  (if (not (and (fn-bpr-statep st) (consp (fn-bpr-state-pending st))))
      st
    (let ((pending (fn-bpr-state-pending st)))
      ; Completion identifies the exact pending receipt.  A stale completion
      ; cannot resolve a later intent for a different work/receipt pair.
      (if (not (and (equal work-id
                          (fn-bpr-context-work-id
                           (fn-bpr-receipt-entry-context pending)))
                    (equal receipt-id
                          (fn-bpa-receipt-id
                           (fn-bpr-receipt-entry-receipt pending)))))
          st
        (if (equal outcome :committed)
            (fn-bpr-make-state (fn-bpr-state-config st)
                               (fn-bpr-state-contexts st)
                               (cons pending (fn-bpr-state-receipts st)) nil)
          (if (equal outcome :absent)
              (fn-bpr-make-state (fn-bpr-state-config st)
                                 (fn-bpr-state-contexts st)
                                 (fn-bpr-state-receipts st) nil)
            st))))))

; Regeneration requires the same exact accepted request context and a committed
; receipt.  The new BP BID is purposely not an input to this article/receipt
; decision; transport retry cannot create a second charge or decision.
(defun fn-bpr-receipt-adu (st request)
  (let ((context (and (fn-bpa-requestp request)
                      (fn-bpr-find-context (fn-bpa-request-work-id request)
                                           (fn-bpr-state-contexts st)))))
    (if (and (fn-bpr-statep st) context
             (equal request (fn-bpr-context-request context)))
        (let ((entry (fn-bpr-find-receipt (fn-bpr-context-work-id context)
                                          (fn-bpr-state-receipts st))))
          (if entry (fn-bpa-encode (fn-bpr-receipt-entry-receipt entry)) nil))
      nil)))

; Export theory.  Records are opaque above (shape and accessor-of-constructor
; lemmas exported, definitions withdrawn).  Recognizers, the initial state and
; the receiver transitions are proof vocabulary: the receiver books open what
; they need locally (fn-bp-receiver-vocabulary).  The list vocabulary
; (fn-bpr-context-listp, fn-bpr-receipt-listp, the three finders) stays
; enabled: proofs induct on it.
(deftheory fn-bp-receiver-vocabulary
  '(fn-bpr-configp fn-bpr-contextp fn-bpr-receipt-entryp fn-bpr-statep
    fn-bpr-initial-state fn-bpr-context-from-request
    fn-bpr-store-record-acceptedp fn-bpr-request-acceptablep
    fn-bpr-accept-request fn-bpr-receipt-for fn-bpr-prepare-receipt
    fn-bpr-commit-receipt fn-bpr-receipt-adu))
(in-theory (disable fn-bp-receiver-vocabulary))
