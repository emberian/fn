; Carried-invariant execution for the native BP application join.
;
; Recovery validates the complete retained journal once.  Served operations
; thereafter validate the current external request/record and rely on the
; invariant preserved by every successful transition; they do not re-run the
; recognizers over all retained contexts, receipts, intents, or facts.
(in-package "ACL2")
(include-book "bp-native-app")
(local (include-book "bp-receiver-state-invariants"))
(set-verify-guards-eagerness 0)

; Fast counterparts of the receiver transitions.  These are deliberately
; local to the joined application machine: the checked public receiver model
; remains the recovery/specification function.
; The carried premise of the indexed lookups (PRF-144 part 1): the Store's
; derived index corresponds to its committed history.  Never evaluated on a
; served path; established by every open (`fn-cei-build' of the history the
; open read) and preserved by every Store transition
; (books/consumer-event-index-store-invariants.lisp, `fn-ceis-relatedp' in
; every phase but :replaying and :fault).
(defun fn-bpaj-store-indexedp (store)
  (declare (xargs :guard t :verify-guards nil))
  (fn-cei-correspondencep (fn-sn-event-index store)
                          (fn-sf-records (fn-sn-files store))))

; Store membership through the Message-ID index: the record's own
; Message-ID selects its candidates, so no walk of the history and no decode
; of a composite happens here (PKT-291).
(defun fn-bpaj-store-record-accepted-fast (store record)
  (declare (xargs :guard t))
  (and (fn-record-p record)
       (equal (fn-sf-phase (fn-sn-files store)) :ready)
       (member-equal record
                     (fn-cei-msgid-records (fn-record-msgid record)
                                           (fn-sn-event-index store)))
       (fn-bpi-node-record-committedp (fn-sn-node store) record)))

(defun fn-bpaj-request-acceptable-fast
    (store config record request policy-authorizedp)
  (declare (xargs :guard t))
  (and (equal policy-authorizedp t)
       (fn-bpr-configp config)
       (fn-bpa-requestp request)
       (fn-record-p record)
       (fn-bpaj-store-record-accepted-fast store record)
       (equal (fn-bpa-request-destination-eid request)
              (fn-bpr-config-destination config))
       (equal (fn-bpa-request-policy-id request)
              (fn-bpr-config-policy-id config))
       (equal (fn-bpa-request-subject request)
              (fn-record-content-subject record))
       (equal (fn-bpa-request-article request) (fn-record-payload record))))

(defun fn-bpaj-bpr-accept-request-fast
    (st store record request policy-authorizedp)
  (declare (xargs :guard t))
  (if (not (and (not (consp (fn-bpr-state-pending st)))
                (fn-bpaj-request-acceptable-fast
                 store (fn-bpr-state-config st) record request
                 policy-authorizedp)))
      (list :refused st)
    (let* ((context (fn-bpr-context-from-request record request))
           (prior (fn-bpr-find-context (fn-bpr-context-work-id context)
                                       (fn-bpr-state-contexts st)))
           (by-msgid (fn-bpr-find-context-msgid
                      (fn-bpr-context-msgid context)
                      (fn-bpr-state-contexts st))))
      (if prior
          (if (equal prior context) (list :duplicate st)
            (list :conflict st))
        (if by-msgid
            (list :conflict st)
          (list :accepted
                (fn-bpr-make-state
                 (fn-bpr-state-config st)
                 (cons context (fn-bpr-state-contexts st))
                 (fn-bpr-state-receipts st) nil)))))))

(defun fn-bpaj-projected-request-acceptable-fast
    (store config record request stored-octets policy-authorizedp)
  (declare (xargs :guard t))
  (and (equal policy-authorizedp t)
       (fn-bpr-configp config)
       (fn-bpa-requestp request)
       (fn-record-p record)
       (fn-bpaj-store-record-accepted-fast store record)
       (equal (fn-bpa-request-destination-eid request)
              (fn-bpr-config-destination config))
       (equal (fn-bpa-request-policy-id request)
              (fn-bpr-config-policy-id config))
       (equal stored-octets (fn-record-payload record))))

(defun fn-bpaj-bpr-accept-projected-request-fast
    (st store record request stored-octets policy-authorizedp)
  (declare (xargs :guard t))
  (if (not (and (not (consp (fn-bpr-state-pending st)))
                (fn-bpaj-projected-request-acceptable-fast
                 store (fn-bpr-state-config st) record request
                 stored-octets policy-authorizedp)))
      (list :refused st)
    (fn-bpr-bind-request-context st record request)))

(defun fn-bpaj-transit-context-matches-intent-fastp
    (store context intent)
  (declare (xargs :guard t))
  (let* ((request (fn-bpaj-request (fn-bpaj-nth 2 context)))
         (record (fn-bprr-decode-value (fn-bpaj-nth 3 context) :record))
         (fields (fn-bpaj-transit-article-fields request)))
    (and (fn-bpaj-transit-contextp context)
         (fn-bpaj-transit-intentp intent)
         (equal (fn-bpaj-nth 1 context) (fn-bpaj-nth 1 intent))
         (equal (fn-bpaj-nth 2 context) (fn-bpaj-nth 2 intent))
         (equal (fn-bpaj-nth 4 context) (fn-bpaj-nth 3 intent))
         (equal (fn-bpaj-nth 7 context) (fn-bpaj-nth 5 intent))
         (fn-record-p record)
         (fn-bpa-requestp request)
         (fn-bpaj-store-record-accepted-fast store record)
         (equal (fn-record-payload record) (fn-bpaj-nth 9 intent))
         (equal (car fields) :ok)
         (equal (fn-record-msgid record)
                (fn-record-octets-string (cadr fields)))
         (equal (fn-record-txid record) (fn-bpaj-nth 5 context))
         (equal (fn-record-generation record) (fn-bpaj-nth 6 context))
         (or (equal (fn-bpaj-nth 5 intent) :duplicate)
             (equal (fn-record-txid record) (fn-bpaj-nth 4 intent))))))

(defun fn-bpaj-bpr-prepare-receipt-fast
    (st work-id receipt-id policy-authorizedp)
  (declare (xargs :guard t))
  (if (or (not (equal policy-authorizedp t))
          (consp (fn-bpr-state-pending st)))
      st
    (let ((context (fn-bpr-find-context work-id
                                        (fn-bpr-state-contexts st))))
      (if (or (not context)
              (fn-bpr-find-receipt work-id (fn-bpr-state-receipts st)))
          st
        (let ((receipt (fn-bpr-receipt-for
                        context (fn-bpr-state-config st) receipt-id)))
          (if (fn-bpa-receiptp receipt)
              (fn-bpr-make-state
               (fn-bpr-state-config st)
               (fn-bpr-state-contexts st)
               (fn-bpr-state-receipts st)
               (fn-bpr-make-receipt-entry context receipt))
            st))))))

(defun fn-bpaj-bpr-commit-receipt-fast (st work-id receipt-id outcome)
  (declare (xargs :guard t))
  (if (not (consp (fn-bpr-state-pending st)))
      st
    (let ((pending (fn-bpr-state-pending st)))
      (if (not (and
                (equal work-id
                       (fn-bpr-context-work-id
                        (fn-bpr-receipt-entry-context pending)))
                (equal receipt-id
                       (fn-bpa-receipt-id
                        (fn-bpr-receipt-entry-receipt pending)))))
          st
        (if (equal outcome :committed)
            (fn-bpr-make-state
             (fn-bpr-state-config st)
             (fn-bpr-state-contexts st)
             (cons pending (fn-bpr-state-receipts st)) nil)
          (if (equal outcome :absent)
              (fn-bpr-make-state
               (fn-bpr-state-config st)
               (fn-bpr-state-contexts st)
               (fn-bpr-state-receipts st) nil)
            st))))))

(defun fn-bpaj-bpr-receipt-adu-fast (st request)
  (declare (xargs :guard t))
  (let ((context (and (fn-bpa-requestp request)
                      (fn-bpr-find-context
                       (fn-bpa-request-work-id request)
                       (fn-bpr-state-contexts st)))))
    (if (and context (equal request (fn-bpr-context-request context)))
        (let ((entry (fn-bpr-find-receipt
                      (fn-bpr-context-work-id context)
                      (fn-bpr-state-receipts st))))
          (if entry (fn-bpa-encode (fn-bpr-receipt-entry-receipt entry)) nil))
      nil)))

(defun fn-bpaj-bprr-apply-record-fast (st store r)
  (declare (xargs :guard t))
  (if (not (fn-bprr-recordp r)) (list nil st)
    (let ((kind (car r)))
      (cond
       ((equal kind :request-context)
        (let* ((request (fn-bprr-decode-value (fn-bprr-nth 2 r) :request))
               (record (fn-bprr-decode-value (fn-bprr-nth 3 r) :record))
               (answer (fn-bpaj-bpr-accept-request-fast
                        st store record request (fn-bprr-nth 4 r))))
          (if (equal (car answer) :accepted)
              (list t (fn-bprr-nth 1 answer))
            (list nil st))))
       ((equal kind :receipt-intent)
        (let* ((next (fn-bpaj-bpr-prepare-receipt-fast
                      st (fn-bprr-nth 1 r) (fn-bprr-nth 2 r)
                      (fn-bprr-nth 4 r)))
               (pending (fn-bpr-state-pending next))
               (expected
                (and (consp pending)
                     (fn-bpa-encode
                      (fn-bpr-receipt-entry-receipt pending)))))
          (if (and (not (equal next st))
                   (equal expected (fn-bprr-nth 3 r)))
              (list t next)
            (list nil st))))
       ((equal kind :receipt-decision)
        (let* ((pending (fn-bpr-state-pending st))
               (receipt (and (consp pending)
                             (fn-bpr-receipt-entry-receipt pending)))
               (next (fn-bpaj-bpr-commit-receipt-fast
                      st (fn-bprr-nth 1 r) (fn-bprr-nth 2 r)
                      (fn-bprr-nth 3 r))))
          (if (and (consp pending)
                   (equal (fn-bpa-receipt-work-id receipt)
                          (fn-bprr-nth 1 r))
                   (equal (fn-bpa-receipt-id receipt)
                          (fn-bprr-nth 2 r))
                   (not (equal next st)))
              (list t next)
            (list nil st))))
       (t (list nil st))))))

(defun fn-bpaj-apply-record-fast (joined store r)
  (declare (xargs :guard t))
  (let ((kind (fn-bpaj-nth 0 r)))
    (cond
     ((equal kind :request-transit-intent)
      (if (not (fn-bpaj-transit-intentp r)) (list nil joined)
        (let* ((work-id (fn-bpaj-intent-work-id r))
               (prior (fn-bpaj-find-intent work-id
                                           (fn-bpaj-intents joined)))
               (context (fn-bpr-find-context
                         work-id
                         (fn-bpr-state-contexts
                          (fn-bpaj-receiver joined)))))
          (if (or prior context) (list nil joined)
            (list t (fn-bpaj-make-state
                     (fn-bpaj-receiver joined)
                     (append (fn-bpaj-intents joined) (list r))
                     (fn-bpaj-facts joined) t))))))
     ((equal kind :request-transit-context)
      (let ((intent (fn-bpaj-context-intent joined r)))
        (if (not (and intent
                      (fn-bpaj-transit-context-matches-intent-fastp
                       store r intent)))
            (list nil joined)
          (let* ((request (fn-bpaj-request (fn-bpaj-nth 2 r)))
                 (record (fn-bprr-decode-value (fn-bpaj-nth 3 r) :record))
                 (answer (fn-bpaj-bpr-accept-projected-request-fast
                          (fn-bpaj-receiver joined) store record request
                          (fn-bpaj-nth 9 intent) t)))
            (if (not (equal (car answer) :accepted)) (list nil joined)
              (list t (fn-bpaj-make-state
                       (fn-bprr-nth 1 answer)
                       (fn-bpaj-intents joined)
                       (append (fn-bpaj-facts joined) (list r)) t)))))))
     ((equal kind :request-intent)
      (if (not (fn-bpaj-intentp r)) (list nil joined)
        (let* ((work-id (fn-bpaj-intent-work-id r))
               (prior (fn-bpaj-find-intent work-id
                                           (fn-bpaj-intents joined)))
               (context (fn-bpr-find-context
                         work-id
                         (fn-bpr-state-contexts
                          (fn-bpaj-receiver joined)))))
          (if (or prior context) (list nil joined)
            (list t (fn-bpaj-make-state
                     (fn-bpaj-receiver joined)
                     (append (fn-bpaj-intents joined) (list r))
                     (fn-bpaj-facts joined) t))))))
     ((equal kind :request-context-v2)
      (let ((intent (fn-bpaj-context-intent joined r)))
        (if (not (and intent
                      (fn-bpaj-context-matches-intentp r intent)))
            (list nil joined)
          (let ((answer (fn-bpaj-bprr-apply-record-fast
                         (fn-bpaj-receiver joined) store
                         (fn-bpaj-base-record r))))
            (if (not (car answer)) (list nil joined)
              (list t (fn-bpaj-make-state
                       (fn-bprr-nth 1 answer)
                       (fn-bpaj-intents joined)
                       (append (fn-bpaj-facts joined) (list r)) t)))))))
     ((equal kind :request-context)
      (if (fn-bpaj-strictp joined) (list nil joined)
        (let ((answer (fn-bpaj-bprr-apply-record-fast
                       (fn-bpaj-receiver joined) store r)))
          (if (not (car answer)) (list nil joined)
            (list t (fn-bpaj-make-state
                     (fn-bprr-nth 1 answer)
                     (fn-bpaj-intents joined)
                     (fn-bpaj-facts joined) nil))))))
     (t
      (let ((answer (fn-bpaj-bprr-apply-record-fast
                     (fn-bpaj-receiver joined) store r)))
        (if (not (car answer)) (list nil joined)
          (list t (fn-bpaj-make-state
                   (fn-bprr-nth 1 answer)
                   (fn-bpaj-intents joined)
                   (fn-bpaj-facts joined)
                   (fn-bpaj-strictp joined)))))))))

(defun fn-bpaj-request-status-fast (joined request-octets)
  (declare (xargs :guard t))
  (let* ((request (fn-bpaj-request request-octets))
         (receiver (fn-bpaj-receiver joined)))
    (if (not request) :malformed
      (if (not (and
                (equal (fn-bpa-request-destination-eid request)
                       (fn-bpr-config-destination
                        (fn-bpr-state-config receiver)))
                (equal (fn-bpa-request-policy-id request)
                       (fn-bpr-config-policy-id
                        (fn-bpr-state-config receiver)))))
          :refused
        (let* ((work-id (fn-bpa-request-work-id request))
               (context (fn-bpr-find-context
                         work-id (fn-bpr-state-contexts receiver)))
               (intent (fn-bpaj-find-intent
                        work-id (fn-bpaj-intents joined)))
               (pending (fn-bpr-state-pending receiver)))
          (cond ((and context
                      (not (equal request
                                  (fn-bpr-context-request context))))
                 :conflict)
                ((and intent
                      (not (equal request
                                  (fn-bpaj-request
                                   (fn-bpaj-nth 2 intent)))))
                 :conflict)
                ((and context
                      (fn-bpaj-bpr-receipt-adu-fast receiver request))
                 :committed)
                ((consp pending)
                 (if (equal work-id
                            (fn-bpr-context-work-id
                             (fn-bpr-receipt-entry-context pending)))
                     :pending-receipt :blocked))
                (context :context)
                (intent :intent)
                (t :new)))))))

(defun fn-bpaj-pending-receipt-resolution-fast (joined)
  (declare (xargs :guard t))
  (let* ((pending (fn-bpr-state-pending (fn-bpaj-receiver joined)))
         (context (and (consp pending)
                       (fn-bpr-receipt-entry-context pending)))
         (receipt (and (consp pending)
                       (fn-bpr-receipt-entry-receipt pending))))
    (and context receipt
         (list :receipt-decision (fn-bpr-context-work-id context)
               (fn-bpa-receipt-id receipt) :absent))))

(defun fn-bpaj-config-status (joined destination policy issuer)
  (declare (xargs :guard t))
  (if (not (fn-bpaj-statep joined))
      :absent
    (if (equal (fn-bpr-state-config (fn-bpaj-receiver joined))
               (fn-bpr-make-config destination policy issuer))
        :match
      :conflict)))

(defun fn-bpaj-config-status-fast (joined destination policy issuer)
  (declare (xargs :guard t))
  ;; fn-bprj-reset installs NIL when no FNRJ configuration exists yet.
  ;; This is a reachable startup state, before the replay invariant holds.
  (if (null joined)
      :absent
    (if (equal (fn-bpr-state-config (fn-bpaj-receiver joined))
               (fn-bpr-make-config destination policy issuer))
        :match
      :conflict)))

(defun fn-bpaj-record-matches-request-fast (store record request)
  (declare (xargs :guard t))
  (and (fn-record-p record) (fn-bpa-requestp request)
       (equal (fn-record-payload record) (fn-bpa-request-article request))
       (equal (fn-record-content-subject record)
              (fn-bpa-request-subject request))
       (fn-bpaj-store-record-accepted-fast store record)))

; The existing semantic search and conflict rule, over the Store's
; maintained Message-ID index instead of a walk of the history
; (`fn-bpaj-record-lookup-fast-is-checked' under `fn-bpaj-store-indexedp').
(defun fn-bpaj-record-lookup-fast (store request)
  (declare (xargs :guard t))
  (let ((fields (fn-bpaj-article-fields request)))
    (if (not (equal (car fields) :ok)) (list :conflict)
      (let ((records (fn-cei-msgid-records
                      (fn-record-octets-string (cadr fields))
                      (fn-sn-event-index store))))
        (cond ((endp records) (list :absent))
              ((consp (cdr records)) (list :conflict))
              ((fn-bpaj-record-matches-request-fast
                store (car records) request)
               (list :found (car records)))
              (t (list :conflict)))))))

(defun fn-bpaj-transit-record-lookup-fast (store request intent)
  (declare (xargs :guard t))
  (let ((fields (fn-bpaj-transit-article-fields request)))
    (if (not (and (equal (car fields) :ok)
                  (fn-bpaj-transit-intentp intent)))
        (list :conflict)
      (let ((records (fn-cei-msgid-records
                      (fn-record-octets-string (cadr fields))
                      (fn-sn-event-index store))))
        (cond ((endp records) (list :absent))
              ((consp (cdr records)) (list :conflict))
              ((and (fn-record-p (car records))
                    (fn-bpa-requestp request)
                    (fn-bpaj-store-record-accepted-fast store (car records))
                    (equal (fn-record-payload (car records))
                           (fn-bpaj-nth 9 intent))
                    (equal (fn-record-msgid (car records))
                           (fn-record-octets-string (cadr fields))))
               (list :found (car records)))
              (t (list :conflict)))))))

(defun fn-bpaj-dispatch-fast
    (joined store request-octets current-generation)
  (declare (xargs :guard t))
  (let* ((request (fn-bpaj-request request-octets))
         (status (fn-bpaj-request-status-fast joined request-octets)))
    (case status
      (:new (list :persist-intent))
      (:intent
       (let* ((intent (fn-bpaj-request-intent joined request-octets))
              (lookup (if (equal (fn-bpaj-nth 0 intent)
                                 :request-transit-intent)
                          (fn-bpaj-transit-record-lookup-fast
                           store request intent)
                        (fn-bpaj-record-lookup-fast store request))))
         (if (and (not (equal (fn-bpaj-nth 0 intent)
                              :request-transit-intent))
                  (not (equal current-generation
                              (fn-bpaj-request-generation
                               joined request-octets))))
             (list :refused :stale-owner-generation)
           (case (car lookup)
             (:absent
              (cond ((not (equal current-generation
                                 (fn-bpaj-request-generation
                                  joined request-octets)))
                     (list :refused :stale-owner-generation))
                    ((equal (fn-bpaj-request-planned-result
                             joined request-octets) :accepted)
                     (list :submit))
                    (t (list :refused :missing-duplicate-record))))
             (:found
              (if (and (equal (fn-bpaj-request-planned-result
                               joined request-octets) :accepted)
                       (not (equal (fn-record-txid (cadr lookup))
                                   (fn-bpaj-request-planned-txid
                                    joined request-octets))))
                  (list :refused :store-binding-conflict)
                (list :bind (cadr lookup))))
             (otherwise (list :refused :store-conflict))))))
      (:context (list :prepare-receipt))
      (:pending-receipt (list :resolve-absent))
      (:committed (list :return-receipt))
      (:blocked (list :busy))
      (otherwise (list :refused status)))))

; Equations justify every fast function under the invariant established by a
; successful replay.  The host does not manufacture a second boolean.
(defthm fn-bpaj-statep-components
  (implies (fn-bpaj-statep joined)
           (and (fn-bpr-statep (fn-bpaj-receiver joined))
                (fn-bpaj-intent-listp (fn-bpaj-intents joined))
                (fn-bpaj-context-v2-listp (fn-bpaj-facts joined))
                (booleanp (fn-bpaj-strictp joined))))
  :rule-classes (:rewrite :forward-chaining)
  :hints (("Goal" :in-theory (enable fn-bpaj-statep))))

(defthm fn-bpaj-statep-of-constructor
  (equal (fn-bpaj-statep
          (fn-bpaj-make-state receiver intents facts strictp))
         (and (fn-bpr-statep receiver)
              (fn-bpaj-intent-listp intents)
              (fn-bpaj-context-v2-listp facts)))
  :hints (("Goal" :in-theory (enable fn-bpaj-statep))))

(defthm fn-bpaj-nth-one-of-two-list
  (equal (fn-bpaj-nth 1 (list first second)) second)
  :hints (("Goal" :in-theory (enable fn-bpaj-nth))))

(defthm fn-bpaj-bprr-nth-one-is-bpa-nth
  (equal (fn-bprr-nth 1 x) (fn-bpa-nth 1 x))
  :hints (("Goal" :in-theory
           (enable fn-bprr-nth fn-bpa-nth fn-bpa-car fn-bpa-cdr))))

(defthm fn-bpaj-intent-listp-append-one
  (implies (and (fn-bpaj-intent-listp intents)
                (or (fn-bpaj-intentp intent)
                    (fn-bpaj-transit-intentp intent)))
           (fn-bpaj-intent-listp (append intents (list intent))))
  :hints (("Goal" :induct (fn-bpaj-intent-listp intents)
           :in-theory (e/d (fn-bpaj-intent-listp append)
                           (fn-bpaj-intentp fn-bpaj-transit-intentp)))))

(defthm fn-bpaj-context-v2-listp-append-one
  (implies (and (fn-bpaj-context-v2-listp facts)
                (or (fn-bpaj-context-v2p fact)
                    (fn-bpaj-transit-contextp fact)))
           (fn-bpaj-context-v2-listp (append facts (list fact))))
  :hints (("Goal" :induct (fn-bpaj-context-v2-listp facts)
           :in-theory (e/d (fn-bpaj-context-v2-listp append)
                           (fn-bpaj-context-v2p
                            fn-bpaj-transit-contextp)))))

(defthm fn-bpaj-context-match-implies-context-v2p
  (implies (fn-bpaj-context-matches-intentp context intent)
           (fn-bpaj-context-v2p context))
  :hints (("Goal" :in-theory
           (enable fn-bpaj-context-matches-intentp))))

(defthm fn-bpaj-transit-context-match-implies-contextp
  (implies (fn-bpaj-transit-context-matches-intentp store context intent)
           (fn-bpaj-transit-contextp context))
  :hints (("Goal" :in-theory
           (union-theories
            (theory 'minimal-theory)
            '(fn-bpaj-transit-context-matches-intentp)))))

;; ---------------------------------------------------------------------------
;; The Message-ID index (PRF-144 part 1): under the carried premise the
;; index's answer is the walk's.  The record codec and the composite decoder
;; stay closed.

(defthm fn-bpaj-record-for-msgid-is-cei-fold
  (equal (fn-bpaj-record-for-msgid msgid events)
         (fn-cei-article-records-for msgid events))
  :hints (("Goal" :induct (fn-bpaj-record-for-msgid msgid events)
           :in-theory (e/d (fn-bpaj-record-for-msgid
                            fn-cei-article-records-for
                            fn-bpr-event-article fn-cei-event-article)
                           (fn-record-p fn-replay-composite-record
                            fn-stxa-p)))))

(local
 (defthm fn-bpaj-member-fold-is-member-article-records
   (implies (fn-record-p record)
            (iff (member-equal record
                               (fn-cei-article-records-for
                                (fn-record-msgid record) events))
                 (member-equal record (fn-bpr-article-records events))))
   :hints (("Goal" :induct (fn-bpr-article-records events)
            :in-theory (e/d (fn-bpr-article-records
                             fn-cei-article-records-for
                             fn-bpr-event-article fn-cei-event-article)
                            (fn-record-p fn-replay-composite-record
                             fn-stxa-p))))))

(local
 (defthm fn-bpaj-record-msgid-is-a-string
   (implies (fn-record-p record) (stringp (fn-record-msgid record)))
   :hints (("Goal" :in-theory (enable fn-record-p)))))

; The lookup reads the index; under the premise it is the walk.
(defthm fn-bpaj-indexed-records-are-the-walk
  (implies (and (fn-bpaj-store-indexedp store) (stringp msgid))
           (equal (fn-cei-msgid-records msgid (fn-sn-event-index store))
                  (fn-bpaj-record-for-msgid
                   msgid (fn-sf-records (fn-sn-files store)))))
  :hints (("Goal" :use ((:instance fn-cei-msgid-records-of-correspondence
                                   (index (fn-sn-event-index store))
                                   (events (fn-sf-records
                                            (fn-sn-files store)))))
           :in-theory (e/d (fn-bpaj-store-indexedp)
                           (fn-cei-msgid-records-of-correspondence
                            fn-cei-msgid-records fn-cei-correspondencep
                            fn-bpaj-record-for-msgid
                            fn-cei-article-records-for)))))

(local
 (defthm fn-bpaj-indexed-membership-is-history-membership
   (implies (and (fn-bpaj-store-indexedp store) (fn-record-p record))
            (iff (member-equal record
                               (fn-cei-msgid-records
                                (fn-record-msgid record)
                                (fn-sn-event-index store)))
                 (member-equal record
                               (fn-bpr-article-records
                                (fn-sf-records (fn-sn-files store))))))
   :hints (("Goal" :use ((:instance fn-cei-msgid-records-of-correspondence
                                    (msgid (fn-record-msgid record))
                                    (index (fn-sn-event-index store))
                                    (events (fn-sf-records
                                             (fn-sn-files store))))
                         fn-bpaj-record-msgid-is-a-string
                         (:instance fn-bpaj-member-fold-is-member-article-records
                                    (events (fn-sf-records
                                             (fn-sn-files store)))))
            :in-theory (e/d (fn-bpaj-store-indexedp)
                            (fn-cei-msgid-records-of-correspondence
                             fn-bpaj-member-fold-is-member-article-records
                             fn-bpaj-record-msgid-is-a-string
                             fn-cei-msgid-records fn-cei-correspondencep
                             fn-record-p fn-cei-article-records-for
                             fn-bpr-article-records))))))

(in-theory (disable fn-bpaj-record-for-msgid-is-cei-fold))

(defthm fn-bpaj-store-record-accepted-fast-is-checked
  (implies (and (fn-sn-statep store) (fn-bpaj-store-indexedp store))
           (equal (fn-bpaj-store-record-accepted-fast store record)
                  (fn-bpr-store-record-acceptedp store record)))
  :hints (("Goal" :in-theory
           (union-theories
            (theory 'minimal-theory)
            '(fn-bpaj-store-record-accepted-fast
              fn-bpr-store-record-acceptedp
              fn-bpaj-indexed-membership-is-history-membership)))))

(defthm fn-bpaj-request-acceptable-fast-is-checked
  (implies (and (fn-sn-statep store) (fn-bpaj-store-indexedp store))
           (equal (fn-bpaj-request-acceptable-fast
                   store config record request policy-authorizedp)
                  (fn-bpr-request-acceptablep
                   store config record request policy-authorizedp)))
  :hints (("Goal" :in-theory
           (union-theories
            (theory 'minimal-theory)
            '(fn-bpaj-request-acceptable-fast
              fn-bpr-request-acceptablep
              fn-bpaj-store-record-accepted-fast-is-checked)))))

(defthm fn-bpaj-bpr-accept-request-fast-is-checked
  (implies (and (fn-bpr-statep st) (fn-sn-statep store)
                (fn-bpaj-store-indexedp store))
           (equal (fn-bpaj-bpr-accept-request-fast
                   st store record request policy-authorizedp)
                  (fn-bpr-accept-request
                   st store record request policy-authorizedp)))
  :hints (("Goal" :in-theory
           (enable fn-bpaj-bpr-accept-request-fast
                   fn-bpr-accept-request
                   fn-bpr-bind-request-context))))

(defthm fn-bpaj-bpr-prepare-receipt-fast-is-checked
  (implies (fn-bpr-statep st)
           (equal (fn-bpaj-bpr-prepare-receipt-fast
                   st work-id receipt-id policy-authorizedp)
                  (fn-bpr-prepare-receipt
                   st work-id receipt-id policy-authorizedp)))
  :hints (("Goal" :in-theory
           (enable fn-bpaj-bpr-prepare-receipt-fast
                   fn-bpr-prepare-receipt))))

(defthm fn-bpaj-bpr-commit-receipt-fast-is-checked
  (implies (fn-bpr-statep st)
           (equal (fn-bpaj-bpr-commit-receipt-fast
                   st work-id receipt-id outcome)
                  (fn-bpr-commit-receipt st work-id receipt-id outcome)))
  :hints (("Goal" :in-theory
           (enable fn-bpaj-bpr-commit-receipt-fast
                   fn-bpr-commit-receipt))))

(defthm fn-bpaj-bpr-receipt-adu-fast-is-checked
  (implies (fn-bpr-statep st)
           (equal (fn-bpaj-bpr-receipt-adu-fast st request)
                  (fn-bpr-receipt-adu st request)))
  :hints (("Goal" :in-theory
           (enable fn-bpaj-bpr-receipt-adu-fast
                   fn-bpr-receipt-adu))))

(defthm fn-bpaj-bprr-apply-record-fast-is-checked
  (implies (and (fn-bpr-statep st) (fn-sn-statep store)
                (fn-bpaj-store-indexedp store))
           (equal (fn-bpaj-bprr-apply-record-fast st store r)
                  (fn-bprr-apply-record st store r)))
  :hints (("Goal" :in-theory
           (enable fn-bpaj-bprr-apply-record-fast fn-bprr-apply-record))))

(defthm fn-bpaj-projected-request-acceptable-fast-is-checked
  (implies (and (fn-sn-statep store) (fn-bpaj-store-indexedp store))
           (equal (fn-bpaj-projected-request-acceptable-fast
                   store config record request stored-octets authorizedp)
                  (fn-bpr-projected-request-acceptablep
                   store config record request stored-octets authorizedp)))
  :hints (("Goal" :in-theory
           (enable fn-bpaj-projected-request-acceptable-fast
                   fn-bpr-projected-request-acceptablep
                   fn-bpaj-store-record-accepted-fast-is-checked))))

(defthm fn-bpaj-bpr-accept-projected-request-fast-is-checked
  (implies (and (fn-bpr-statep st) (fn-sn-statep store)
                (fn-bpaj-store-indexedp store))
           (equal (fn-bpaj-bpr-accept-projected-request-fast
                   st store record request stored-octets authorizedp)
                  (fn-bpr-accept-projected-request
                   st store record request stored-octets authorizedp)))
  :hints (("Goal" :in-theory
           (enable fn-bpaj-bpr-accept-projected-request-fast
                   fn-bpr-accept-projected-request
                   fn-bpaj-projected-request-acceptable-fast-is-checked))))

(defthm fn-bpaj-transit-context-matches-intent-fast-is-checked
  (implies (and (fn-sn-statep store) (fn-bpaj-store-indexedp store))
           (equal (fn-bpaj-transit-context-matches-intent-fastp
                   store context intent)
                  (fn-bpaj-transit-context-matches-intentp
                   store context intent)))
  :hints (("Goal" :in-theory
           (e/d (fn-bpaj-transit-context-matches-intent-fastp
                 fn-bpaj-transit-context-matches-intentp
                 fn-bpaj-transit-record-matchp)
                (fn-bpaj-transit-intentp fn-bpaj-transit-contextp
                 fn-bpaj-request fn-bpaj-transit-article-fields
                 fn-bprr-decode-value
                 fn-bpr-store-record-acceptedp)))))

(defthm fn-bpaj-apply-record-fast-is-checked
  (implies (and (fn-bpaj-statep joined) (fn-sn-statep store)
                (fn-bpaj-store-indexedp store))
           (equal (fn-bpaj-apply-record-fast joined store r)
                  (fn-bpaj-apply-record joined store r)))
  :hints (("Goal"
           :use ((:instance fn-bpaj-bprr-apply-record-fast-is-checked
                            (st (fn-bpaj-receiver joined))
                            (r r))
                 (:instance fn-bpaj-bprr-apply-record-fast-is-checked
                            (st (fn-bpaj-receiver joined))
                            (r (fn-bpaj-base-record r)))
                 (:instance fn-bpaj-bpr-accept-projected-request-fast-is-checked
                            (st (fn-bpaj-receiver joined))
                            (record (fn-bprr-decode-value
                                     (fn-bpaj-nth 3 r) :record))
                            (request (fn-bpaj-request (fn-bpaj-nth 2 r)))
                            (stored-octets
                             (fn-bpaj-nth 9 (fn-bpaj-context-intent joined r)))
                            (authorizedp t))
                 (:instance fn-bpaj-transit-context-matches-intent-fast-is-checked
                            (context r)
                            (intent (fn-bpaj-context-intent joined r)))
                 (:instance fn-bpaj-statep-components))
           :cases ((equal (fn-bpaj-nth 0 r) :request-intent)
                   (equal (fn-bpaj-nth 0 r) :request-transit-intent)
                   (equal (fn-bpaj-nth 0 r) :request-context-v2)
                   (equal (fn-bpaj-nth 0 r) :request-transit-context)
                   (equal (fn-bpaj-nth 0 r) :request-context))
           :in-theory
           (union-theories
            (theory 'minimal-theory)
            '(fn-bpaj-apply-record-fast fn-bpaj-apply-record)))))

(defthm fn-bpaj-request-status-fast-is-checked
  (implies (fn-bpaj-statep joined)
           (equal (fn-bpaj-request-status-fast joined request-octets)
                  (fn-bpaj-request-status joined request-octets)))
  :hints (("Goal"
           :use ((:instance fn-bpaj-statep-components)
                 (:instance fn-bpaj-bpr-receipt-adu-fast-is-checked
                            (st (fn-bpaj-receiver joined))
                            (request (fn-bpaj-request request-octets))))
           :in-theory
           (union-theories
            (theory 'minimal-theory)
            '(fn-bpaj-request-status-fast fn-bpaj-request-status)))))

(defthm fn-bpaj-pending-resolution-fast-is-checked
  (implies (fn-bpaj-statep joined)
           (equal (fn-bpaj-pending-receipt-resolution-fast joined)
                  (fn-bpaj-pending-receipt-resolution joined)))
  :hints (("Goal" :in-theory
           (union-theories
            (theory 'minimal-theory)
            '(fn-bpaj-pending-receipt-resolution-fast
              fn-bpaj-pending-receipt-resolution)))))

(defthm fn-bpaj-config-status-fast-is-checked
  (implies (or (null joined) (fn-bpaj-statep joined))
           (equal (fn-bpaj-config-status-fast
                   joined destination policy issuer)
                  (fn-bpaj-config-status
                   joined destination policy issuer)))
  :hints (("Goal" :in-theory
           (enable fn-bpaj-config-status-fast fn-bpaj-config-status))))

(defthm fn-bpaj-record-matches-request-fast-is-checked
  (implies (and (fn-sn-statep store) (fn-bpaj-store-indexedp store))
           (equal (fn-bpaj-record-matches-request-fast store record request)
                  (fn-bpaj-record-matches-requestp store record request)))
  :hints (("Goal" :in-theory
           (union-theories
            (theory 'minimal-theory)
            '(fn-bpaj-record-matches-request-fast
              fn-bpaj-record-matches-requestp
              fn-bpaj-store-record-accepted-fast-is-checked)))))

(defthm fn-bpaj-record-lookup-fast-is-checked
  (implies (and (fn-sn-statep store) (fn-bpaj-store-indexedp store))
           (equal (fn-bpaj-record-lookup-fast store request)
                  (fn-bpaj-record-lookup store request)))
  :hints (("Goal" :in-theory
           (union-theories
            (theory 'minimal-theory)
            '(fn-bpaj-record-lookup-fast fn-bpaj-record-lookup
              fn-bpaj-record-matches-request-fast-is-checked
              fn-bpaj-indexed-records-are-the-walk
              (:type-prescription fn-record-octets-string))))))

(defthm fn-bpaj-transit-record-lookup-fast-is-checked
  (implies (and (fn-sn-statep store) (fn-bpaj-store-indexedp store))
           (equal (fn-bpaj-transit-record-lookup-fast store request intent)
                  (fn-bpaj-transit-record-lookup store request intent)))
  :hints (("Goal" :in-theory
           (e/d (fn-bpaj-transit-record-lookup-fast
                 fn-bpaj-transit-record-lookup
                 fn-bpaj-transit-record-matchp)
                (fn-bpaj-transit-intentp fn-bpaj-transit-article-fields
                 fn-bpaj-record-for-msgid fn-bpr-store-record-acceptedp
                 fn-bpaj-record-for-msgid-is-cei-fold
                 fn-cei-msgid-records fn-bpaj-store-indexedp)))))

(defthm fn-bpaj-dispatch-fast-is-checked
  (implies (and (fn-bpaj-statep joined) (fn-sn-statep store)
                (fn-bpaj-store-indexedp store))
           (equal (fn-bpaj-dispatch-fast
                   joined store request-octets current-generation)
                  (fn-bpaj-dispatch
                   joined store request-octets current-generation)))
  :hints (("Goal" :in-theory
           (union-theories
            (theory 'minimal-theory)
            '(fn-bpaj-dispatch-fast fn-bpaj-dispatch
              fn-bpaj-request-status-fast-is-checked
              fn-bpaj-record-lookup-fast-is-checked
              fn-bpaj-transit-record-lookup-fast-is-checked)))))

(defthm fn-bpaj-apply-record-preserves-statep
  (implies (and (fn-bpaj-statep joined)
                (car (fn-bpaj-apply-record joined store r)))
           (fn-bpaj-statep
            (fn-bpaj-nth 1 (fn-bpaj-apply-record joined store r))))
  :hints (("Goal"
           :use ((:instance fn-bpaj-statep-components)
                 (:instance fn-bprr-apply-record-preserves-statep
                            (st (fn-bpaj-receiver joined))
                            (record r))
                 (:instance fn-bprr-apply-record-preserves-statep
                            (st (fn-bpaj-receiver joined))
                            (record (fn-bpaj-base-record r)))
                 (:instance fn-bpr-accept-projected-request-preserves-statep
                            (st (fn-bpaj-receiver joined))
                            (record (fn-bprr-decode-value
                                     (fn-bpaj-nth 3 r) :record))
                            (request (fn-bpaj-request (fn-bpaj-nth 2 r)))
                            (stored-octets
                             (fn-bpaj-nth 9 (fn-bpaj-context-intent joined r)))
                            (policy-authorizedp t)))
           :cases ((equal (fn-bpaj-nth 0 r) :request-intent)
                   (equal (fn-bpaj-nth 0 r) :request-transit-intent)
                   (equal (fn-bpaj-nth 0 r) :request-context-v2)
                   (equal (fn-bpaj-nth 0 r) :request-transit-context)
                   (equal (fn-bpaj-nth 0 r) :request-context))
           :in-theory
           (union-theories
            (theory 'minimal-theory)
            '(car-cons cdr-cons fn-bpaj-nth-one-of-two-list
              fn-bpaj-bprr-nth-one-is-bpa-nth
              fn-bpaj-apply-record
              fn-bpaj-statep-of-constructor
              fn-bpaj-intent-listp-append-one
              fn-bpaj-context-v2-listp-append-one
              fn-bpaj-transit-context-match-implies-contextp
              fn-bpaj-context-match-implies-context-v2p)))))

(defthm fn-bpaj-apply-record-fast-preserves-statep
  (implies (and (fn-bpaj-statep joined)
                (fn-sn-statep store)
                (fn-bpaj-store-indexedp store)
                (car (fn-bpaj-apply-record-fast joined store r)))
           (fn-bpaj-statep
            (fn-bpaj-nth 1
                         (fn-bpaj-apply-record-fast joined store r))))
  :hints (("Goal"
           :use ((:instance fn-bpaj-apply-record-fast-is-checked)
                 (:instance fn-bpaj-apply-record-preserves-statep))
           :in-theory (theory 'minimal-theory))))

(defthm fn-bpaj-replay-rest-preserves-statep
  (implies (and (fn-bpaj-statep joined)
                (car (fn-bpaj-replay-rest joined store records)))
           (fn-bpaj-statep
            (fn-bpaj-nth 1
                         (fn-bpaj-replay-rest joined store records))))
  :hints (("Goal"
           :induct (fn-bpaj-replay-rest joined store records)
           :in-theory (enable fn-bpaj-replay-rest))))

(defthm fn-bpaj-successful-replay-has-statep
  (implies (car (fn-bpaj-replay store records))
           (fn-bpaj-statep
            (fn-bpaj-nth 1 (fn-bpaj-replay store records))))
  :hints (("Goal"
           :use ((:instance fn-bpaj-replay-rest-preserves-statep
                            (joined
                             (fn-bpaj-make-state
                              (fn-bpr-initial-state
                               (fn-bprr-config (car records)))
                              nil nil nil))
                            (records (cdr records))))
           :in-theory
           (union-theories
            (theory 'minimal-theory)
            '(fn-bpaj-replay fn-bpaj-statep-of-constructor
              fn-bpaj-intent-listp fn-bpaj-context-v2-listp
              fn-bpaj-nth-one-of-two-list car-cons cdr-cons)))))

(in-theory (disable fn-bpaj-bpr-accept-request-fast
                    fn-bpaj-store-record-accepted-fast
                    fn-bpaj-request-acceptable-fast
                    fn-bpaj-bpr-prepare-receipt-fast
                    fn-bpaj-bpr-commit-receipt-fast
                    fn-bpaj-bpr-receipt-adu-fast
                    fn-bpaj-bprr-apply-record-fast
                    fn-bpaj-apply-record-fast
                    fn-bpaj-request-status-fast
                    fn-bpaj-pending-receipt-resolution-fast
                    fn-bpaj-config-status
                    fn-bpaj-config-status-fast
                    fn-bpaj-record-matches-request-fast
                    fn-bpaj-record-lookup-fast
                    fn-bpaj-dispatch-fast
                    fn-bpaj-store-record-accepted-fast-is-checked
                    fn-bpaj-request-acceptable-fast-is-checked
                    fn-bpaj-bpr-accept-request-fast-is-checked
                    fn-bpaj-bpr-prepare-receipt-fast-is-checked
                    fn-bpaj-bpr-commit-receipt-fast-is-checked
                    fn-bpaj-bpr-receipt-adu-fast-is-checked
                    fn-bpaj-bprr-apply-record-fast-is-checked
                    fn-bpaj-apply-record-fast-is-checked
                    fn-bpaj-request-status-fast-is-checked
                    fn-bpaj-pending-resolution-fast-is-checked
                    fn-bpaj-config-status-fast-is-checked
                    fn-bpaj-record-matches-request-fast-is-checked
                    fn-bpaj-record-lookup-fast-is-checked
                    fn-bpaj-dispatch-fast-is-checked))
