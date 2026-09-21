; Carried-invariant execution for the native BP application join.
;
; Recovery validates the complete retained journal once.  Served operations
; thereafter validate the current external request/record and rely on the
; invariant preserved by every successful transition; they do not re-run the
; recognizers over all retained contexts, receipts, intents, or facts.
(in-package "ACL2")
(include-book "bp-native-app")
(include-book "bp-receiver-state-invariants")
(set-verify-guards-eagerness 0)

; Fast counterparts of the receiver transitions.  These are deliberately
; local to the joined application machine: the checked public receiver model
; remains the recovery/specification function.
(defun fn-bpaj-store-record-accepted-fast (store record)
  (declare (xargs :guard t))
  (and (fn-record-p record)
       (equal (fn-sf-phase (fn-sn-files store)) :ready)
       (member-equal record (fn-sf-records (fn-sn-files store)))
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

(defun fn-bpaj-record-matches-request-fast (store record request)
  (declare (xargs :guard t))
  (and (fn-record-p record) (fn-bpa-requestp request)
       (equal (fn-record-payload record) (fn-bpa-request-article request))
       (equal (fn-record-content-subject record)
              (fn-bpa-request-subject request))
       (fn-bpaj-store-record-accepted-fast store record)))

; This keeps the existing semantic search and conflict rule.  A maintained
; index can remove that linear lookup later; this function removes only the
; unrelated whole-Store recognizer from the served path.
(defun fn-bpaj-record-lookup-fast (store request)
  (declare (xargs :guard t))
  (let ((fields (fn-bpaj-article-fields request)))
    (if (not (equal (car fields) :ok)) (list :conflict)
      (let ((records (fn-bpaj-record-for-msgid
                      (fn-record-octets-string (cadr fields))
                      (fn-sf-records (fn-sn-files store)))))
        (cond ((endp records) (list :absent))
              ((consp (cdr records)) (list :conflict))
              ((fn-bpaj-record-matches-request-fast
                store (car records) request)
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
       (if (not (equal current-generation
                       (fn-bpaj-request-generation joined request-octets)))
           (list :refused :stale-owner-generation)
         (let ((lookup (fn-bpaj-record-lookup-fast store request)))
           (case (car lookup)
             (:absent
              (if (equal (fn-bpaj-request-planned-result
                          joined request-octets) :accepted)
                  (list :submit)
                (list :refused :missing-duplicate-record)))
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

(defthm fn-bpaj-intent-listp-append-one
  (implies (and (fn-bpaj-intent-listp intents)
                (fn-bpaj-intentp intent))
           (fn-bpaj-intent-listp (append intents (list intent))))
  :hints (("Goal" :induct (fn-bpaj-intent-listp intents)
           :in-theory (enable fn-bpaj-intent-listp append))))

(defthm fn-bpaj-context-v2-listp-append-one
  (implies (and (fn-bpaj-context-v2-listp facts)
                (fn-bpaj-context-v2p fact))
           (fn-bpaj-context-v2-listp (append facts (list fact))))
  :hints (("Goal" :induct (fn-bpaj-context-v2-listp facts)
           :in-theory (enable fn-bpaj-context-v2-listp append))))

(defthm fn-bpaj-context-match-implies-context-v2p
  (implies (fn-bpaj-context-matches-intentp context intent)
           (fn-bpaj-context-v2p context))
  :hints (("Goal" :in-theory
           (enable fn-bpaj-context-matches-intentp))))

(defthm fn-bpaj-store-record-accepted-fast-is-checked
  (implies (fn-sn-statep store)
           (equal (fn-bpaj-store-record-accepted-fast store record)
                  (fn-bpr-store-record-acceptedp store record)))
  :hints (("Goal" :in-theory
           (enable fn-bpaj-store-record-accepted-fast
                   fn-bpr-store-record-acceptedp))))

(defthm fn-bpaj-request-acceptable-fast-is-checked
  (implies (fn-sn-statep store)
           (equal (fn-bpaj-request-acceptable-fast
                   store config record request policy-authorizedp)
                  (fn-bpr-request-acceptablep
                   store config record request policy-authorizedp)))
  :hints (("Goal" :in-theory
           (enable fn-bpaj-request-acceptable-fast
                   fn-bpr-request-acceptablep))))

(defthm fn-bpaj-bpr-accept-request-fast-is-checked
  (implies (and (fn-bpr-statep st) (fn-sn-statep store))
           (equal (fn-bpaj-bpr-accept-request-fast
                   st store record request policy-authorizedp)
                  (fn-bpr-accept-request
                   st store record request policy-authorizedp)))
  :hints (("Goal" :in-theory
           (enable fn-bpaj-bpr-accept-request-fast
                   fn-bpr-accept-request))))

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
  (implies (and (fn-bpr-statep st) (fn-sn-statep store))
           (equal (fn-bpaj-bprr-apply-record-fast st store r)
                  (fn-bprr-apply-record st store r)))
  :hints (("Goal" :in-theory
           (enable fn-bpaj-bprr-apply-record-fast fn-bprr-apply-record))))

(defthm fn-bpaj-apply-record-fast-is-checked
  (implies (and (fn-bpaj-statep joined) (fn-sn-statep store))
           (equal (fn-bpaj-apply-record-fast joined store r)
                  (fn-bpaj-apply-record joined store r)))
  :hints (("Goal"
           :use ((:instance fn-bpaj-bprr-apply-record-fast-is-checked
                            (st (fn-bpaj-receiver joined))
                            (r r))
                 (:instance fn-bpaj-bprr-apply-record-fast-is-checked
                            (st (fn-bpaj-receiver joined))
                            (r (fn-bpaj-base-record r)))
                 (:instance fn-bpaj-statep-components))
           :cases ((equal (fn-bpaj-nth 0 r) :request-intent)
                   (equal (fn-bpaj-nth 0 r) :request-context-v2)
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

(defthm fn-bpaj-record-matches-request-fast-is-checked
  (implies (fn-sn-statep store)
           (equal (fn-bpaj-record-matches-request-fast store record request)
                  (fn-bpaj-record-matches-requestp store record request)))
  :hints (("Goal" :in-theory
           (union-theories
            (theory 'minimal-theory)
            '(fn-bpaj-record-matches-request-fast
              fn-bpaj-record-matches-requestp
              fn-bpaj-store-record-accepted-fast-is-checked)))))

(defthm fn-bpaj-record-lookup-fast-is-checked
  (implies (fn-sn-statep store)
           (equal (fn-bpaj-record-lookup-fast store request)
                  (fn-bpaj-record-lookup store request)))
  :hints (("Goal" :in-theory
           (union-theories
            (theory 'minimal-theory)
            '(fn-bpaj-record-lookup-fast fn-bpaj-record-lookup
              fn-bpaj-record-matches-request-fast-is-checked)))))

(defthm fn-bpaj-dispatch-fast-is-checked
  (implies (and (fn-bpaj-statep joined) (fn-sn-statep store))
           (equal (fn-bpaj-dispatch-fast
                   joined store request-octets current-generation)
                  (fn-bpaj-dispatch
                   joined store request-octets current-generation)))
  :hints (("Goal" :in-theory
           (union-theories
            (theory 'minimal-theory)
            '(fn-bpaj-dispatch-fast fn-bpaj-dispatch
              fn-bpaj-request-status-fast-is-checked
              fn-bpaj-record-lookup-fast-is-checked)))))

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
                            (record (fn-bpaj-base-record r))))
           :cases ((equal (fn-bpaj-nth 0 r) :request-intent)
                   (equal (fn-bpaj-nth 0 r) :request-context-v2)
                   (equal (fn-bpaj-nth 0 r) :request-context))
           :in-theory
           (union-theories
            (theory 'minimal-theory)
            '(car-cons cdr-cons fn-bpaj-nth-one-of-two-list
              fn-bpaj-apply-record
              fn-bpaj-statep-of-constructor
              fn-bpaj-intent-listp-append-one
              fn-bpaj-context-v2-listp-append-one
              fn-bpaj-context-match-implies-context-v2p)))))

(defthm fn-bpaj-apply-record-fast-preserves-statep
  (implies (and (fn-bpaj-statep joined)
                (fn-sn-statep store)
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
           :in-theory (enable fn-bpaj-replay fn-bpaj-statep
                              fn-bpaj-intent-listp
                              fn-bpaj-context-v2-listp))))

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
                    fn-bpaj-record-matches-request-fast
                    fn-bpaj-record-lookup-fast
                    fn-bpaj-dispatch-fast))
