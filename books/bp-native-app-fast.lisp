; Carried-invariant execution for the native BP application join.
;
; Recovery validates the complete retained journal once.  Served operations
; thereafter validate the current external request/record and rely on the
; invariant preserved by every successful transition; they do not re-run the
; recognizers over all retained contexts, receipts, intents, or facts.
(in-package "ACL2")
(include-book "bp-native-app")
(include-book "store-files-traces")
(include-book "history-columns-relation")
(include-book "byte-store-scan")
(local (include-book "bp-receiver-state-invariants"))

;; The tau system is off in this book (lane tau-pass, tools/tau_cost.py).
;; Its work is proof time no prover step counts (docs/proof-style.md
;; 9.1); planning/evidence/tau-cost-*.json has this book's figures.
(local (in-theory (disable (tau-system))))

(set-verify-guards-eagerness 0)

; Fast counterparts of the receiver transitions.  These are deliberately
; local to the joined application machine: the checked public receiver model
; remains the recovery/specification function.
; The premise of the indexed lookups (PRF-144): R, the history stobj is the
; Store's committed history (books/history-columns-relation.lisp; the store
; node's derived index, field 13, is retired).  The lemmas below are
; the refinement layer and take it as a hypothesis on any Store; the
; theorems about the Store the host dispatches over discharge it:
; books/owner-store-indexed.lisp establishes it at the host's open and
; carries it across every owner transition the host installs
; (fn-osi-live-owner-store-is-indexed).  Never evaluated on a served path.

; The node's committed-record check with the node recognizer carried, not
; evaluated (PKT-448 (a), PRF-220).  fn-bpi-node-record-committedp
; (books/bp-ingress.lisp) conjoins fn-node-statep of the node it is handed,
; which walks and conses the whole article list, the bindings and the
; retention ledger on every call.  The Store the host dispatches over already
; carries that invariant: fn-sn-statep conjoins fn-node-statep of its node,
; and the configured owner's relation carries fn-sn-statep from open across
; every transition (fn-bpaj-ocl-relation-carries-sn-statep,
; books/owner-store-indexed.lisp).  This is
; the same check without that conjunct; it is fn-bpi-node-record-committedp
; on every node satisfying fn-node-statep
; (fn-bpaj-node-record-committed-carriedp-is-committedp).  The two lookups
; that remain are pointer walks that allocate nothing (PKT-638).
(defun fn-bpaj-node-record-committed-carriedp (node record fn-arena)
  (declare (xargs :stobjs fn-arena :guard t :verify-guards nil))
  (mbe :logic
       (let ((article (fn-find-article
                       (fn-record-msgid record)
                       (fn-state-articles (fn-node-acceptance node))))
             (binding (fn-node-find-binding
                       (fn-record-msgid record) (fn-node-bindings node))))
         (and (consp article) (consp binding)
              (equal (fn-handle-bytes (fn-article-payload article) fn-arena)
                     (fn-record-payload record))
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
         (and (consp article) (consp binding)
              (equal (fn-handle-bytes (fn-article-payload article) fn-arena)
                     (fn-bpi-ag-record-payload record))
              (equal (fn-article-groups article)
                     (fn-bpi-ag-record-groups record))
              (equal (fn-node-binding-subject binding)
                     (fn-bpi-ag-record-content-subject record))
              (equal (fn-node-binding-id binding)
                     (fn-bpi-ag-record-obligation-id record))))))
(verify-guards fn-bpaj-node-record-committed-carriedp)

; KEYSTONE (PRF-220): on a node satisfying the recognizer, the carried check
; is the checked one (the node's article bytes read through the arena,
; records-flip: fn-bpi-node-wire-committedp).  No other hypothesis.
(defthm fn-bpaj-node-record-committed-carriedp-is-committedp
  (implies (fn-node-statep node)
           (equal (fn-bpaj-node-record-committed-carriedp node record fn-arena)
                  (fn-bpi-node-wire-committedp node record fn-arena)))
  :hints (("Goal" :in-theory
           (union-theories
            (theory 'minimal-theory)
            '(fn-bpaj-node-record-committed-carriedp
              fn-bpi-node-wire-committedp)))))

(defthm fn-bpaj-sn-statep-carries-node-statep
  (implies (fn-sn-statep store)
           (fn-node-statep (fn-sn-node store)))
  :hints (("Goal" :in-theory (e/d (fn-sn-statep) (fn-node-statep)))))

; Store membership through the Message-ID index: the record's own
; Message-ID selects its candidates, so no walk of the history and no decode
; of a composite happens here (PKT-291).  The node check is the carried one:
; no whole-node recognizer runs per request (PRF-220).
; The index's candidates are retained rows (records-flip): RECORD, a WIRE
; record, must stand for one of them (`fn-bpr-rows-stand-for': a held row
; whose wire form through the arena is RECORD).
(defun fn-bpaj-store-record-accepted-fast (store record fn-arena fn-hist)
  (declare (xargs :stobjs (fn-arena fn-hist) :guard t))
  (and (fn-record-p record)
       (equal (fn-sf-phase (fn-sn-files store)) :ready)
       (fn-bpr-rows-stand-for record
                              (fn-hist-msgid-records (fn-record-msgid record) fn-hist)
                              fn-arena)
       (fn-bpaj-node-record-committed-carriedp (fn-sn-node store) record fn-arena)))

(defun fn-bpaj-request-acceptable-fast
    (store config record request policy-authorizedp fn-arena fn-hist)
  (declare (xargs :stobjs (fn-arena fn-hist) :guard t))
  (and (equal policy-authorizedp t)
       (fn-bpr-configp config)
       (fn-bpa-requestp request)
       (fn-record-p record)
       (fn-bpaj-store-record-accepted-fast store record fn-arena fn-hist)
       (equal (fn-bpa-request-destination-eid request)
              (fn-bpr-config-destination config))
       (equal (fn-bpa-request-policy-id request)
              (fn-bpr-config-policy-id config))
       (equal (fn-bpa-request-subject request)
              (fn-record-content-subject record))
       (equal (fn-bpa-request-article request) (fn-record-payload record))))

(defun fn-bpaj-bpr-accept-request-fast
    (st store record request policy-authorizedp fn-arena fn-hist)
  (declare (xargs :stobjs (fn-arena fn-hist) :guard t))
  (if (not (and (not (consp (fn-bpr-state-pending st)))
                (fn-bpaj-request-acceptable-fast
                 store (fn-bpr-state-config st) record request
                 policy-authorizedp fn-arena fn-hist)))
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

(defun fn-bpaj-projected-ref-acceptable-fast
    (store config record ref stored-length stored-digest policy-authorizedp fn-arena fn-hist)
  (declare (xargs :stobjs (fn-arena fn-hist) :guard t))
  (let ((m (fn-bpaj-ref-metadata ref)))
    (and (equal policy-authorizedp t)
         (fn-bpr-configp config)
         (fn-bpaj-request-refp ref)
         (fn-record-p record)
         (fn-bpaj-store-record-accepted-fast store record fn-arena fn-hist)
         (equal (fn-bpa-request-destination-eid m)
                (fn-bpr-config-destination config))
         (equal (fn-bpa-request-policy-id m)
                (fn-bpr-config-policy-id config))
         (equal (len (fn-record-payload record)) stored-length)
         (equal (fn-frame-digest (fn-record-payload record)) stored-digest))))

(defun fn-bpaj-bpr-accept-projected-ref-fast
    (st store record ref stored-length stored-digest policy-authorizedp fn-arena fn-hist)
  (declare (xargs :stobjs (fn-arena fn-hist) :guard t))
  (if (not (and (not (consp (fn-bpr-state-pending st)))
                (fn-bpaj-projected-ref-acceptable-fast
                 store (fn-bpr-state-config st) record ref
                 stored-length stored-digest policy-authorizedp fn-arena fn-hist)))
      (list :refused st)
    (fn-bpr-bind-context st (fn-bpr-context-from-ref record ref))))

; The Store record a context names, through the Message-ID index
; (`fn-bpaj-context-record-fast-is-checked').
(defun fn-bpaj-context-record-fast (store r fn-arena fn-hist)
  (declare (xargs :stobjs (fn-arena fn-hist) :guard t)
           (ignorable store))
  (and (stringp (fn-bpaj-nth 3 r))
       (fn-bpaj-context-record-of
        (fn-hist-msgid-records (fn-bpaj-nth 3 r) fn-hist)
        r fn-arena)))

(defun fn-bpaj-transit-context-matches-intent-fastp
    (store context intent fn-arena fn-hist)
  (declare (xargs :stobjs (fn-arena fn-hist) :guard t))
  (let ((record (fn-bpaj-context-record-fast store context fn-arena fn-hist)))
    (and (fn-bpaj-transit-contextp context)
         (fn-bpaj-transit-intentp intent)
         (equal (fn-bpaj-nth 1 context) (fn-bpaj-nth 1 intent))
         (equal (fn-bpaj-context-ref context) (fn-bpaj-intent-ref intent))
         (equal (fn-bpaj-nth 4 context) (fn-bpaj-nth 3 intent))
         (equal (fn-bpaj-nth 7 context) (fn-bpaj-nth 5 intent))
         (fn-record-p record)
         (fn-bpaj-store-record-accepted-fast store record fn-arena fn-hist)
         (equal (len (fn-record-payload record)) (fn-bpaj-nth 11 intent))
         (equal (fn-frame-digest (fn-record-payload record))
                (fn-bpaj-nth 12 intent))
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
    (if (and context (equal (fn-bpaj-request-ref request)
                            (fn-bpr-context-request-ref context)))
        (let ((entry (fn-bpr-find-receipt
                      (fn-bpr-context-work-id context)
                      (fn-bpr-state-receipts st))))
          (if entry (fn-bpa-encode (fn-bpr-receipt-entry-receipt entry)) nil))
      nil)))

(defun fn-bpaj-bprr-apply-record-fast (st store r fn-arena fn-hist)
  (declare (xargs :stobjs (fn-arena fn-hist) :guard t))
  (if (not (fn-bprr-recordp r)) (list nil st)
    (let ((kind (car r)))
      (cond
       ((equal kind :request-context)
        (let* ((request (fn-bprr-decode-value (fn-bprr-nth 2 r) :request))
               (record (fn-bprr-decode-value (fn-bprr-nth 3 r) :record))
               (answer (fn-bpaj-bpr-accept-request-fast
                        st store record request (fn-bprr-nth 4 r) fn-arena fn-hist)))
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

(defun fn-bpaj-apply-record-fast (joined store r fn-arena fn-hist)
  (declare (xargs :stobjs (fn-arena fn-hist) :guard t))
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
                     (fn-bpaj-snoc (fn-bpaj-intents joined) r)
                     (fn-bpaj-facts joined) t))))))
     ((equal kind :request-transit-context)
      (let ((intent (fn-bpaj-context-intent joined r)))
        (if (not (and intent
                      (fn-bpaj-transit-context-matches-intent-fastp
                       store r intent fn-arena fn-hist)))
            (list nil joined)
          (let* ((record (fn-bpaj-context-record-fast store r fn-arena fn-hist))
                 (answer (fn-bpaj-bpr-accept-projected-ref-fast
                          (fn-bpaj-receiver joined) store record
                          (fn-bpaj-context-ref r)
                          (fn-bpaj-nth 11 intent) (fn-bpaj-nth 12 intent)
                          t fn-arena fn-hist)))
            (if (not (equal (car answer) :accepted)) (list nil joined)
              (list t (fn-bpaj-make-state
                       (fn-bprr-nth 1 answer)
                       (fn-bpaj-intents joined)
                       (fn-bpaj-snoc (fn-bpaj-facts joined) r) t)))))))
     ((equal kind :request-context)
      (if (fn-bpaj-strictp joined) (list nil joined)
        (let ((answer (fn-bpaj-bprr-apply-record-fast
                       (fn-bpaj-receiver joined) store r fn-arena fn-hist)))
          (if (not (car answer)) (list nil joined)
            (list t (fn-bpaj-make-state
                     (fn-bprr-nth 1 answer)
                     (fn-bpaj-intents joined)
                     (fn-bpaj-facts joined) nil))))))
     (t
      (let ((answer (fn-bpaj-bprr-apply-record-fast
                     (fn-bpaj-receiver joined) store r fn-arena fn-hist)))
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
                      (not (equal (fn-bpaj-request-ref request)
                                  (fn-bpr-context-request-ref context))))
                 :conflict)
                ((and intent
                      (not (fn-bpaj-intent-names-requestp intent request)))
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

(defun fn-bpaj-record-matches-request-fast (store record request fn-arena fn-hist)
  (declare (xargs :stobjs (fn-arena fn-hist) :guard t))
  (and (fn-record-p record) (fn-bpa-requestp request)
       (equal (fn-record-payload record) (fn-bpa-request-article request))
       (equal (fn-record-content-subject record)
              (fn-bpa-request-subject request))
       (fn-bpaj-store-record-accepted-fast store record fn-arena fn-hist)))

; The existing semantic search and conflict rule, over the Store's
; maintained Message-ID index instead of a walk of the history
; (`fn-bpaj-record-lookup-fast-is-checked' under R, fn-hist-of-storep).
(defun fn-bpaj-record-lookup-fast (store request fn-arena fn-hist)
  (declare (xargs :stobjs (fn-arena fn-hist) :guard t))
  (let ((fields (fn-bpaj-article-fields request)))
    (if (not (equal (car fields) :ok)) (list :conflict)
      (let ((records (fn-hist-msgid-records (fn-record-octets-string (cadr fields)) fn-hist)))
        (cond ((endp records) (list :absent))
              ((consp (cdr records)) (list :conflict))
              ((fn-bpaj-record-matches-request-fast
                store (fn-row-wire-of (car records) fn-arena) request fn-arena fn-hist)
               (list :found (fn-row-wire-of (car records) fn-arena)))
              (t (list :conflict)))))))

(defun fn-bpaj-transit-record-lookup-fast (store request intent fn-arena fn-hist)
  (declare (xargs :stobjs (fn-arena fn-hist) :guard t))
  (let ((fields (fn-bpaj-transit-article-fields request)))
    (if (not (and (equal (car fields) :ok)
                  (fn-bpaj-transit-intentp intent)))
        (list :conflict)
      (let ((records (fn-hist-msgid-records (fn-record-octets-string (cadr fields)) fn-hist)))
        (cond ((endp records) (list :absent))
              ((consp (cdr records)) (list :conflict))
              ((and (fn-record-p (fn-row-wire-of (car records) fn-arena))
                    (fn-bpa-requestp request)
                    (fn-bpaj-store-record-accepted-fast store (fn-row-wire-of (car records) fn-arena) fn-arena fn-hist)
                    (equal (len (fn-record-payload (fn-row-wire-of (car records) fn-arena)))
                           (fn-bpaj-nth 11 intent))
                    (equal (fn-frame-digest (fn-record-payload (fn-row-wire-of (car records) fn-arena)))
                           (fn-bpaj-nth 12 intent))
                    (equal (fn-record-msgid (fn-row-wire-of (car records) fn-arena))
                           (fn-record-octets-string (cadr fields))))
               (list :found (fn-row-wire-of (car records) fn-arena)))
              (t (list :conflict)))))))

(defun fn-bpaj-dispatch-fast
    (joined store request-octets current-generation fn-arena fn-hist)
  (declare (xargs :stobjs (fn-arena fn-hist) :guard t))
  (let* ((request (fn-bpaj-request request-octets))
         (status (fn-bpaj-request-status-fast joined request-octets)))
    (case status
      (:new (list :persist-intent))
      (:intent
       (let* ((intent (fn-bpaj-request-intent joined request-octets))
              (lookup (fn-bpaj-transit-record-lookup-fast
                       store request intent fn-arena fn-hist)))
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
             (otherwise (list :refused :store-conflict)))))
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
                (fn-bpaj-fact-listp (fn-bpaj-facts joined))
                (booleanp (fn-bpaj-strictp joined))))
  :rule-classes (:rewrite :forward-chaining)
  :hints (("Goal" :in-theory (enable fn-bpaj-statep))))

(defthm fn-bpaj-statep-of-constructor
  (equal (fn-bpaj-statep
          (fn-bpaj-make-state receiver intents facts strictp))
         (and (fn-bpr-statep receiver)
              (fn-bpaj-intent-listp intents)
              (fn-bpaj-fact-listp facts)))
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
                (fn-bpaj-transit-intentp intent))
           (fn-bpaj-intent-listp (append intents (list intent))))
  :hints (("Goal" :induct (fn-bpaj-intent-listp intents)
           :in-theory (e/d (fn-bpaj-intent-listp append)
                           (fn-bpaj-transit-intentp)))))

(defthm fn-bpaj-fact-listp-append-one
  (implies (and (fn-bpaj-fact-listp facts)
                (fn-bpaj-transit-contextp fact))
           (fn-bpaj-fact-listp (append facts (list fact))))
  :hints (("Goal" :induct (fn-bpaj-fact-listp facts)
           :in-theory (e/d (fn-bpaj-fact-listp append)
                           (fn-bpaj-transit-contextp)))))

(defthm fn-bpaj-transit-context-match-implies-contextp
  (implies (fn-bpaj-transit-context-matches-intentp store context intent fn-arena)
           (fn-bpaj-transit-contextp context))
  :hints (("Goal" :in-theory
           (union-theories
            (theory 'minimal-theory)
            '(fn-bpaj-transit-context-matches-intentp)))))

;; ---------------------------------------------------------------------------
;; The Message-ID index (PRF-144 part 1): under the carried premise the
;; index's answer is the walk's.  The record codec and the composite decoder
;; stay closed.

; After the records flip the history's articles are held rows: a wire
; record (a composite's decoded article, or a raw kind-4 composite) is none.
(local (defthm fn-bpaj-record-is-not-held
  (implies (fn-record-p x) (not (fn-held-p x)))
  :hints (("Goal" :in-theory (enable fn-record-p fn-record-shapep fn-held-p fn-held-shapep
                                     fn-record-payloadp)))))
(local (defthm fn-bpaj-composite-record-is-not-held
  (not (fn-held-p (fn-replay-composite-record e)))
  :hints (("Goal" :in-theory (e/d (fn-replay-composite-record) (fn-held-p fn-record-p))
           :use ((:instance fn-bpaj-record-is-not-held
                            (x (fn-replay-composite-record e)))
                 (:instance fn-record-decode-exact-yields-a-record
                            (octets (fn-stxa-article-record e))))))))
(local (defthm fn-bpaj-stxa-is-not-held
  (implies (fn-stxa-p x) (not (fn-held-p x)))
  :hints (("Goal" :use fn-held-p-forward-natural-head
           :in-theory (enable fn-stxa-p fn-stxa-shapep fn-held-p fn-held-shapep)))))

(defthm fn-bpaj-record-for-msgid-is-cei-fold
  (equal (fn-bpaj-record-for-msgid msgid events)
         (fn-cei-article-records-for msgid events))
  :hints (("Goal" :induct (fn-bpaj-record-for-msgid msgid events)
           :in-theory (e/d (fn-bpaj-record-for-msgid
                            fn-cei-article-records-for
                            fn-bpr-event-article fn-cei-event-article
                            fn-replay-composite-held)
                           (fn-record-p fn-replay-composite-record
                            fn-stxa-p fn-held-p fn-hstxa-p)))))

; A row that stands for a WIRE record is a held row with its Message-ID.
(local
 (defthm fn-bpaj-standing-row-is-held-with-the-msgid
   (implies (fn-bpr-row-stands-for row record fn-arena)
            (and (fn-held-p row)
                 (equal (fn-record-msgid row) (fn-record-msgid record))))
   :rule-classes :forward-chaining
   :hints (("Goal" :use fn-bpr-row-stands-for-held-accessors
            :in-theory (disable fn-bpr-row-stands-for-held-accessors fn-held-p
                                fn-row-wire-of)))))

(local
 (defthm fn-bpaj-member-fold-is-member-article-records
   (implies (fn-record-p record)
            (iff (fn-bpr-rows-stand-for record
                                        (fn-bpaj-record-for-msgid
                                         (fn-record-msgid record) events)
                                        fn-arena)
                 (fn-bpr-rows-stand-for record (fn-bpr-article-records events) fn-arena)))
   :hints (("Goal" :induct (len events)
            :in-theory (e/d (fn-bpr-article-records fn-bpaj-record-for-msgid
                             fn-bpr-rows-stand-for)
                            (fn-bpaj-record-for-msgid-is-cei-fold fn-record-p
                             fn-bpr-event-article fn-held-p fn-row-wire-of
                             fn-bpr-row-stands-for))))))

(local
 (defthm fn-bpaj-record-msgid-is-a-string
   (implies (fn-record-p record) (stringp (fn-record-msgid record)))
   :hints (("Goal" :in-theory (enable fn-record-p fn-record-msgidp)))))

; The lookup reads the history stobj; under R it is the walk.
(defthm fn-bpaj-indexed-records-are-the-walk
  (implies (and (fn-hist-of-storep fn-hist store) (stringp msgid))
           (equal (fn-hist-msgid-records msgid fn-hist)
                  (fn-bpaj-record-for-msgid
                   msgid (fn-sf-records (fn-sn-files store)))))
  :hints (("Goal" :in-theory (e/d (fn-bpaj-record-for-msgid-is-cei-fold)
                                  (fn-bpaj-record-for-msgid
                                   fn-cei-article-records-for)))))

(local
 (defthm fn-bpaj-indexed-membership-is-history-membership
   (implies (and (fn-hist-of-storep fn-hist store) (fn-record-p record))
            (iff (fn-bpr-rows-stand-for record
                                        (fn-hist-msgid-records (fn-record-msgid record) fn-hist)
                                        fn-arena)
                 (fn-bpr-rows-stand-for record
                                        (fn-bpr-article-records
                                         (fn-sf-records (fn-sn-files store)))
                                        fn-arena)))
   :hints (("Goal" :use (fn-bpaj-record-msgid-is-a-string
                         (:instance fn-bpaj-indexed-records-are-the-walk
                                    (msgid (fn-record-msgid record)))
                         (:instance fn-bpaj-member-fold-is-member-article-records
                                    (events (fn-sf-records (fn-sn-files store)))))
            :in-theory (e/d ()
                            (fn-bpaj-indexed-records-are-the-walk
                             fn-bpaj-member-fold-is-member-article-records
                             fn-bpaj-record-msgid-is-a-string
                             fn-cei-msgid-records fn-bpaj-record-for-msgid
                             fn-record-p fn-bpr-rows-stand-for
                             fn-bpr-article-records ))))))

(in-theory (disable fn-bpaj-record-for-msgid-is-cei-fold))
; The stobj's Message-ID answer, as the receiver model's walk (no hypothesis:
; the stobj's logical value is a history list).
(defthm fn-bpaj-hist-msgid-records-is-record-for-msgid
  (equal (fn-hist-msgid-records msgid fn-hist)
         (fn-bpaj-record-for-msgid msgid fn-hist))
  :hints (("Goal" :in-theory (enable fn-bpaj-record-for-msgid-is-cei-fold))))
(in-theory (disable fn-bpaj-hist-msgid-records-is-record-for-msgid))


(defthm fn-bpaj-store-record-accepted-fast-is-checked
  (implies (and (fn-sn-statep store) (fn-hist-of-storep fn-hist store))
           (equal (fn-bpaj-store-record-accepted-fast store record fn-arena fn-hist)
                  (fn-bpr-store-record-acceptedp store record fn-arena)))
  :hints (("Goal" :in-theory
           (union-theories
            (theory 'minimal-theory)
            '(fn-bpaj-store-record-accepted-fast
              fn-bpr-store-record-acceptedp
              fn-bpaj-indexed-membership-is-history-membership
              fn-bpaj-sn-statep-carries-node-statep
              fn-bpaj-node-record-committed-carriedp-is-committedp)))))

(defthm fn-bpaj-request-acceptable-fast-is-checked
  (implies (and (fn-sn-statep store) (fn-hist-of-storep fn-hist store))
           (equal (fn-bpaj-request-acceptable-fast
                   store config record request policy-authorizedp fn-arena fn-hist)
                  (fn-bpr-request-acceptablep
                   store config record request policy-authorizedp fn-arena)))
  :hints (("Goal" :in-theory
           (union-theories
            (theory 'minimal-theory)
            '(fn-bpaj-request-acceptable-fast
              fn-bpr-request-acceptablep
              fn-bpaj-store-record-accepted-fast-is-checked)))))

(defthm fn-bpaj-bpr-accept-request-fast-is-checked
  (implies (and (fn-bpr-statep st) (fn-sn-statep store)
                (fn-hist-of-storep fn-hist store))
           (equal (fn-bpaj-bpr-accept-request-fast
                   st store record request policy-authorizedp fn-arena fn-hist)
                  (fn-bpr-accept-request
                   st store record request policy-authorizedp fn-arena)))
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
                (fn-hist-of-storep fn-hist store))
           (equal (fn-bpaj-bprr-apply-record-fast st store r fn-arena fn-hist)
                  (fn-bprr-apply-record st store r fn-arena)))
  :hints (("Goal" :in-theory
           (enable fn-bpaj-bprr-apply-record-fast fn-bprr-apply-record))))

(defthm fn-bpaj-projected-ref-acceptable-fast-is-checked
  (implies (and (fn-sn-statep store) (fn-hist-of-storep fn-hist store))
           (equal (fn-bpaj-projected-ref-acceptable-fast
                   store config record ref stored-length stored-digest
                   authorizedp fn-arena fn-hist)
                  (fn-bpr-projected-ref-acceptablep
                   store config record ref stored-length stored-digest
                   authorizedp fn-arena)))
  :hints (("Goal" :in-theory
           (enable fn-bpaj-projected-ref-acceptable-fast
                   fn-bpr-projected-ref-acceptablep
                   fn-bpaj-store-record-accepted-fast-is-checked))))

(defthm fn-bpaj-bpr-accept-projected-ref-fast-is-checked
  (implies (and (fn-bpr-statep st) (fn-sn-statep store)
                (fn-hist-of-storep fn-hist store))
           (equal (fn-bpaj-bpr-accept-projected-ref-fast
                   st store record ref stored-length stored-digest
                   authorizedp fn-arena fn-hist)
                  (fn-bpr-accept-projected-ref
                   st store record ref stored-length stored-digest
                   authorizedp fn-arena)))
  :hints (("Goal" :in-theory
           (enable fn-bpaj-bpr-accept-projected-ref-fast
                   fn-bpr-accept-projected-ref
                   fn-bpaj-projected-ref-acceptable-fast-is-checked))))

(defthm fn-bpaj-context-record-fast-is-checked
  (implies (fn-hist-of-storep fn-hist store)
           (equal (fn-bpaj-context-record-fast store r fn-arena fn-hist)
                  (fn-bpaj-context-record store r fn-arena)))
  :hints (("Goal" :in-theory
           (union-theories
            (theory 'minimal-theory)
            '(fn-bpaj-context-record-fast fn-bpaj-context-record
              fn-bpaj-indexed-records-are-the-walk)))))

(defthm fn-bpaj-transit-context-matches-intent-fast-is-checked
  (implies (and (fn-sn-statep store) (fn-hist-of-storep fn-hist store))
           (equal (fn-bpaj-transit-context-matches-intent-fastp
                   store context intent fn-arena fn-hist)
                  (fn-bpaj-transit-context-matches-intentp
                   store context intent fn-arena)))
  :hints (("Goal" :in-theory
           (e/d (fn-bpaj-transit-context-matches-intent-fastp
                 fn-bpaj-transit-context-matches-intentp
                 fn-bpaj-store-record-accepted-fast-is-checked
                 fn-bpaj-context-record-fast-is-checked)
                (fn-bpaj-transit-intentp fn-bpaj-transit-contextp
                 fn-bpaj-context-record fn-bpaj-context-record-fast
                 fn-bpaj-context-ref fn-bpaj-intent-ref
                 fn-bpr-store-record-acceptedp)))))

(defthm fn-bpaj-apply-record-fast-is-checked
  (implies (and (fn-bpaj-statep joined) (fn-sn-statep store)
                (fn-hist-of-storep fn-hist store))
           (equal (fn-bpaj-apply-record-fast joined store r fn-arena fn-hist)
                  (fn-bpaj-apply-record joined store r fn-arena)))
  :hints (("Goal"
           :use ((:instance fn-bpaj-bprr-apply-record-fast-is-checked
                            (st (fn-bpaj-receiver joined))
                            (r r))
                 (:instance fn-bpaj-context-record-fast-is-checked)
                 (:instance fn-bpaj-bpr-accept-projected-ref-fast-is-checked
                            (st (fn-bpaj-receiver joined))
                            (record (fn-bpaj-context-record store r fn-arena))
                            (ref (fn-bpaj-context-ref r))
                            (stored-length
                             (fn-bpaj-nth 11 (fn-bpaj-context-intent joined r)))
                            (stored-digest
                             (fn-bpaj-nth 12 (fn-bpaj-context-intent joined r)))
                            (authorizedp t))
                 (:instance fn-bpaj-transit-context-matches-intent-fast-is-checked
                            (context r)
                            (intent (fn-bpaj-context-intent joined r)))
                 (:instance fn-bpaj-statep-components))
           :cases ((equal (fn-bpaj-nth 0 r) :request-transit-intent)
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
  (implies (and (fn-sn-statep store) (fn-hist-of-storep fn-hist store))
           (equal (fn-bpaj-record-matches-request-fast store record request fn-arena fn-hist)
                  (fn-bpaj-record-matches-requestp store record request fn-arena)))
  :hints (("Goal" :in-theory
           (union-theories
            (theory 'minimal-theory)
            '(fn-bpaj-record-matches-request-fast
              fn-bpaj-record-matches-requestp
              fn-bpaj-store-record-accepted-fast-is-checked)))))

(defthm fn-bpaj-record-lookup-fast-is-checked
  (implies (and (fn-sn-statep store) (fn-hist-of-storep fn-hist store))
           (equal (fn-bpaj-record-lookup-fast store request fn-arena fn-hist)
                  (fn-bpaj-record-lookup store request fn-arena)))
  :hints (("Goal" :in-theory
           (union-theories
            (theory 'minimal-theory)
            '(fn-bpaj-record-lookup-fast fn-bpaj-record-lookup
              fn-bpaj-record-matches-request-fast-is-checked
              fn-bpaj-indexed-records-are-the-walk
              (:type-prescription fn-record-octets-string))))))

(defthm fn-bpaj-transit-record-lookup-fast-is-checked
  (implies (and (fn-sn-statep store) (fn-hist-of-storep fn-hist store))
           (equal (fn-bpaj-transit-record-lookup-fast store request intent fn-arena fn-hist)
                  (fn-bpaj-transit-record-lookup store request intent fn-arena)))
  :hints (("Goal" :in-theory
           (e/d (fn-bpaj-transit-record-lookup-fast
                 fn-bpaj-transit-record-lookup
                 fn-bpaj-transit-record-matchp
                 fn-bpaj-record-for-msgid-is-cei-fold)
                (fn-bpaj-transit-intentp fn-bpaj-transit-article-fields
                 fn-bpaj-record-for-msgid fn-bpr-store-record-acceptedp
                 fn-cei-article-records-for fn-record-octets-string)))))

(defthm fn-bpaj-dispatch-fast-is-checked
  (implies (and (fn-bpaj-statep joined) (fn-sn-statep store)
                (fn-hist-of-storep fn-hist store))
           (equal (fn-bpaj-dispatch-fast
                   joined store request-octets current-generation fn-arena fn-hist)
                  (fn-bpaj-dispatch
                   joined store request-octets current-generation fn-arena)))
  :hints (("Goal" :in-theory
           (union-theories
            (theory 'minimal-theory)
            '(fn-bpaj-dispatch-fast fn-bpaj-dispatch
              fn-bpaj-request-status-fast-is-checked
              fn-bpaj-transit-record-lookup-fast-is-checked)))))

(defthm fn-bpaj-apply-record-preserves-statep
  (implies (and (fn-bpaj-statep joined)
                (car (fn-bpaj-apply-record joined store r fn-arena)))
           (fn-bpaj-statep
            (fn-bpaj-nth 1 (fn-bpaj-apply-record joined store r fn-arena))))
  :hints (("Goal"
           :use ((:instance fn-bpaj-statep-components)
                 (:instance fn-bprr-apply-record-preserves-statep
                            (st (fn-bpaj-receiver joined))
                            (record r))
                 (:instance fn-bpr-accept-projected-ref-preserves-statep
                            (st (fn-bpaj-receiver joined))
                            (record (fn-bpaj-context-record store r fn-arena))
                            (ref (fn-bpaj-context-ref r))
                            (stored-length
                             (fn-bpaj-nth 11 (fn-bpaj-context-intent joined r)))
                            (stored-digest
                             (fn-bpaj-nth 12 (fn-bpaj-context-intent joined r)))
                            (policy-authorizedp t)))
           :cases ((equal (fn-bpaj-nth 0 r) :request-transit-intent)
                   (equal (fn-bpaj-nth 0 r) :request-transit-context)
                   (equal (fn-bpaj-nth 0 r) :request-context))
           :in-theory
           (union-theories
            (theory 'minimal-theory)
            '(car-cons cdr-cons fn-bpaj-nth-one-of-two-list
              fn-bpaj-bprr-nth-one-is-bpa-nth
              fn-bpaj-apply-record fn-bpaj-snoc
              fn-bpaj-statep-of-constructor
              fn-bpaj-intent-listp-append-one
              fn-bpaj-fact-listp-append-one
              fn-bpaj-transit-context-match-implies-contextp)))))

(defthm fn-bpaj-apply-record-fast-preserves-statep
  (implies (and (fn-bpaj-statep joined)
                (fn-sn-statep store)
                (fn-hist-of-storep fn-hist store)
                (car (fn-bpaj-apply-record-fast joined store r fn-arena fn-hist)))
           (fn-bpaj-statep
            (fn-bpaj-nth 1
                         (fn-bpaj-apply-record-fast joined store r fn-arena fn-hist))))
  :hints (("Goal"
           :use ((:instance fn-bpaj-apply-record-fast-is-checked)
                 (:instance fn-bpaj-apply-record-preserves-statep))
           :in-theory (theory 'minimal-theory))))

(defthm fn-bpaj-replay-rest-preserves-statep
  (implies (and (fn-bpaj-statep joined)
                (car (fn-bpaj-replay-rest joined store records fn-arena)))
           (fn-bpaj-statep
            (fn-bpaj-nth 1
                         (fn-bpaj-replay-rest joined store records fn-arena))))
  :hints (("Goal"
           :induct (fn-bpaj-replay-rest joined store records fn-arena)
           :in-theory (enable fn-bpaj-replay-rest))))

(defthm fn-bpaj-successful-replay-has-statep
  (implies (car (fn-bpaj-replay store records fn-arena))
           (fn-bpaj-statep
            (fn-bpaj-nth 1 (fn-bpaj-replay store records fn-arena))))
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
              fn-bpaj-intent-listp fn-bpaj-fact-listp
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
                    fn-bpaj-dispatch-fast-is-checked))

; KEYSTONE (PRF-220) for host/bp-receive-host.lisp fn-bpreq-existing-record
; and host/bp-receipt-host.lisp fn-bpr-host-accept, which retired their own
; walks of the history for this lookup: a record the indexed lookup finds is
; one the retired walk's predicate selects (the request's article and
; subject) and the receiver's checked Store predicate accepts.  The lookup
; is stricter than the walk in two cases only, both refusals: two records
; under the article's Message-ID (the host never picks a first), and a
; record whose Message-ID is not the article's own.
(defthm fn-bpaj-record-lookup-fast-found-is-an-accepted-match
  (implies (and (fn-sn-statep store) (fn-hist-of-storep fn-hist store)
                (equal (car (fn-bpaj-record-lookup-fast store request fn-arena fn-hist)) :found))
           (let ((record (cadr (fn-bpaj-record-lookup-fast store request fn-arena fn-hist))))
             (and (fn-record-p record)
                  (equal (fn-record-payload record)
                         (fn-bpa-request-article request))
                  (equal (fn-record-content-subject record)
                         (fn-bpa-request-subject request))
                  (fn-bpr-store-record-acceptedp store record fn-arena))))
  :hints (("Goal"
           :use ((:instance fn-bpaj-store-record-accepted-fast-is-checked
                            (record (fn-row-wire-of (car (fn-hist-msgid-records (fn-record-octets-string
                                           (cadr (fn-bpaj-article-fields request))) fn-hist)) fn-arena))))
           :in-theory (e/d (fn-bpaj-record-lookup-fast
                            fn-bpaj-record-matches-request-fast)
                           (fn-bpaj-store-record-accepted-fast
                            fn-bpr-store-record-acceptedp fn-record-p
                            fn-cei-msgid-records fn-bpaj-article-fields
                            fn-sn-statep fn-row-wire-of)))))
