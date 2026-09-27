; Native BP application join: intent-first FNRJ replay and exact Store binding.
(in-package "ACL2")
(include-book "bp-receipt-records")
(include-book "bp-request-ref")
; books/owner.lisp's own includes, not owner: this book names none of
; owner's definitions (audit 2026-09-25, packet 2), so a change to the owner
; no longer recertifies the BP application join and the 80 roots above it.
(include-book "store-observed")
(include-book "served")
(include-book "clock")
(include-book "owner-feed")
(include-book "msgid-index")
(include-book "provenance-codec")
(include-book "identity")
(set-verify-guards-eagerness 0)

(defun fn-bpaj-nth (n x)
  (declare (xargs :guard t :measure (nfix n)))
  (if (zp n) (if (consp x) (car x) nil)
    (fn-bpaj-nth (1- n) (if (consp x) (cdr x) nil))))

; Join state: (receiver-state request-intents bound-context-records strictp).
(defun fn-bpaj-make-state (receiver intents facts strictp)
  (declare (xargs :guard t))
  (list receiver intents facts (if strictp t nil)))
(defun fn-bpaj-receiver (x) (declare (xargs :guard t)) (fn-bpaj-nth 0 x))
(defun fn-bpaj-intents (x) (declare (xargs :guard t)) (fn-bpaj-nth 1 x))
(defun fn-bpaj-facts (x) (declare (xargs :guard t)) (fn-bpaj-nth 2 x))
(defun fn-bpaj-strictp (x) (declare (xargs :guard t)) (fn-bpaj-nth 3 x))
(defun fn-bpaj-request (octets)
  (declare (xargs :guard t))
  (let ((answer (fn-bpa-decode-exact octets)))
    (if (and (fn-bpa-result-okp answer)
             (fn-bpa-requestp (fn-bpa-result-message answer)))
        (fn-bpa-result-message answer)
      nil)))

(defun fn-bpaj-article-fields (request)
  (declare (xargs :guard t))
  (if (not (fn-bpa-requestp request)) (list :refused :request)
    (let ((parsed (fn-article-parse (fn-bpa-request-article request))))
      (if (not (fn-article-result-okp parsed)) (list :refused :article-syntax)
        (let ((checked (fn-af-proto-article-check
                        (fn-article-result-article parsed))))
          (if (not (equal (car checked) :ok))
              (list :refused (cadr checked))
            (let ((msgid (cadr checked)) (groups (caddr checked)))
              (if (or (not msgid) (not (consp groups)))
                  (list :refused :article-fields)
                (list :ok msgid groups)))))))))

;; A transit request's fields are the RELAYING agent's (RFC 5537 section 3.6
;; step 1, fn-af-relayed-article-check), exactly the check
;; fn-bpaj-transit-plan's Message-ID comes from (fn-bpaj-transit-msgid): a
;; relayed article carries the injecting node's Injection-Info (and may carry
;; its Xref), which the injecting agent's check fn-bpaj-article-fields
;; refuses.  Until mission-signed, the transit lookups below used that check,
;; so every transit request whose article had been injected (every
;; Store-rendered, hybrid-signed carrier) answered (:conflict) and was refused
;; as :intent before any Store attempt.
(defun fn-bpaj-transit-article-fields (request)
  (declare (xargs :guard t))
  (if (not (fn-bpa-requestp request)) (list :refused :request)
    (let ((parsed (fn-article-parse (fn-bpa-request-article request))))
      (if (not (fn-article-result-okp parsed)) (list :refused :article-syntax)
        (let ((checked (fn-af-relayed-article-check
                        (fn-article-result-article parsed))))
          (if (not (equal (car checked) :ok))
              (list :refused (cadr checked))
            (let ((msgid (cadr checked)) (groups (caddr checked)))
              (if (or (not msgid) (not (consp groups)))
                  (list :refused :article-fields)
                (list :ok msgid groups)))))))))

(defun fn-bpaj-request-subjectp (request)
  (declare (xargs :guard t))
  (and (fn-bpa-requestp request)
       (let* ((identity (fn-id-subject-of-payload
                         (fn-bpa-request-article request)))
              (text (fn-record-octets-string (fn-id-text identity))))
         (equal (fn-bpa-request-subject request) text))))


; The Store record a live transit REQUEST binds: its payload is the relay
; projection the intent pinned, by the projection's LENGTH and DIGEST (the
; intent holds no bytes), and its Message-ID is the request's.
(defun fn-bpaj-transit-record-matchp (store record request p-length p-digest)
  (declare (xargs :guard t))
  (and (fn-record-p record)
       (fn-bpa-requestp request)
       (fn-bpr-store-record-acceptedp store record)
       (equal (len (fn-record-payload record)) p-length)
       (equal (fn-frame-digest (fn-record-payload record)) p-digest)
       (let ((fields (fn-bpaj-transit-article-fields request)))
         (and (equal (car fields) :ok)
              (equal (fn-record-msgid record)
                     (fn-record-octets-string (cadr fields)))))))


; PKT-646 (D27): the transit intent and context carry the request by
; REFERENCE (books/bp-request-ref.lisp), never its bytes, and never the
; Store record or the relay projection.
;
; The intent is written before Store submission, while the request's bytes
; are the delivered bundle the BP node holds (the inbound identity):
; (kind inbound HEAD owner-generation planned-txid result peer
;  local-path peer-path A-LENGTH A-DIGEST P-LENGTH P-DIGEST)
; A-LENGTH and A-DIGEST are the article's; P-LENGTH and P-DIGEST the relay
; projection's (`fn-pu-relay-article' of the article under the pinned
; local and peer Path identities), the bytes the Store will hold.  An intent
; is never resolved to bytes: a live request is compared with it by
; reference (`fn-bpaj-intent-names-requestp'), and a Store record with it
; by the projection's length and digest.
(defun fn-bpaj-transit-intentp (r)
  (declare (xargs :guard t))
  (let* ((local (fn-record-string-octets (fn-bpaj-nth 7 r)))
         (expected (fn-record-string-octets (fn-bpaj-nth 8 r))))
    (and (true-listp r) (equal (len r) 13)
         (equal (fn-bpaj-nth 0 r) :request-transit-intent)
         (fn-bprr-textp (fn-bpaj-nth 1 r))
         (fn-bprr-octetsp (fn-bpaj-nth 2 r))
         (fn-bpaj-headp (fn-bpaj-nth 2 r))
         (fn-record-uint32p (fn-bpaj-nth 3 r))
         (fn-record-uint32p (fn-bpaj-nth 4 r))
         (member-equal (fn-bpaj-nth 5 r) '(:accepted :duplicate))
         (fn-bprr-textp (fn-bpaj-nth 6 r))
         (fn-bprr-textp (fn-bpaj-nth 7 r))
         (fn-bprr-textp (fn-bpaj-nth 8 r))
         (fn-path-identityp local) (fn-path-identityp expected)
         (natp (fn-bpaj-nth 9 r))
         (<= (fn-bpaj-nth 9 r) *fn-bpa-max-article*)
         (fn-frame-digestp (fn-bpaj-nth 10 r))
         (natp (fn-bpaj-nth 11 r))
         (fn-frame-digestp (fn-bpaj-nth 12 r)))))

; The intent's reference to its request.
(defun fn-bpaj-intent-ref (intent)
  (declare (xargs :guard t))
  (list (fn-bpaj-nth 2 intent) (fn-bpaj-nth 9 intent) (fn-bpaj-nth 10 intent)))

; The context binds the Store record the Store committed for a prior intent,
; by its identity (Message-ID, txid, generation), never a copy:
; (kind inbound HEAD store-msgid owner-generation store-txid
;  store-generation result A-LENGTH A-DIGEST)
(defun fn-bpaj-transit-contextp (r)
  (declare (xargs :guard t))
  (and (true-listp r) (equal (len r) 10)
       (equal (fn-bpaj-nth 0 r) :request-transit-context)
       (fn-bprr-textp (fn-bpaj-nth 1 r))
       (fn-bprr-octetsp (fn-bpaj-nth 2 r))
       (fn-bpaj-headp (fn-bpaj-nth 2 r))
       (fn-bprr-textp (fn-bpaj-nth 3 r))
       (fn-record-uint32p (fn-bpaj-nth 4 r))
       (fn-record-uint32p (fn-bpaj-nth 5 r))
       (fn-record-uint32p (fn-bpaj-nth 6 r))
       (member-equal (fn-bpaj-nth 7 r) '(:accepted :duplicate))
       (natp (fn-bpaj-nth 8 r))
       (<= (fn-bpaj-nth 8 r) *fn-bpa-max-article*)
       (fn-frame-digestp (fn-bpaj-nth 9 r))))

; The context's reference to its request.
(defun fn-bpaj-context-ref (context)
  (declare (xargs :guard t))
  (list (fn-bpaj-nth 2 context) (fn-bpaj-nth 8 context)
        (fn-bpaj-nth 9 context)))

; The article records of Store events RECORDS whose Message-ID is MSGID: a
; plain article record, or the article record a signed kind-4 composite
; carries (`fn-bpr-event-article'), so a signed article the Store committed
; binds as a plain one does (PKT-247).  Cost: every composite before the end
; of RECORDS is decoded once per lookup (its article record's octets); an
; index from Message-ID to event beside the Message-ID trie is owed (PKT-291).
(defun fn-bpaj-record-for-msgid (msgid records)
  (declare (xargs :guard t :measure (acl2-count records)))
  (if (consp records)
      (let ((rest (fn-bpaj-record-for-msgid msgid (cdr records)))
            (record (fn-bpr-event-article (car records))))
        (if (and (fn-record-p record)
                 (equal msgid (fn-record-msgid record)))
            (cons record rest)
          rest))
    nil))

; The Store record a context names: the one article record with its
; Message-ID, with its txid and generation; nil otherwise.  Every read of a
; context (recovery included) resolves it here.
(defun fn-bpaj-context-record-of (records r)
  (declare (xargs :guard t))
  (and (consp records) (not (consp (cdr records)))
       (fn-record-p (car records))
       (equal (fn-record-txid (car records)) (fn-bpaj-nth 5 r))
       (equal (fn-record-generation (car records)) (fn-bpaj-nth 6 r))
       (car records)))

(defun fn-bpaj-context-record (store r)
  (declare (xargs :guard t))
  (and (stringp (fn-bpaj-nth 3 r))
       (fn-bpaj-context-record-of
        (fn-bpaj-record-for-msgid (fn-bpaj-nth 3 r)
                                  (fn-sf-records (fn-sn-files store)))
        r)))

; The context the host publishes (host/bp-receipt-journal-host.lisp
; `fn-bprj-request-transit-context-record'), from the live request and the
; committed Store record: the request's reference and the record's
; identity, never either's bytes.
(defun fn-bpaj-transit-context-record
    (inbound-id request-octets store-record generation txid record-generation
                result)
  (declare (xargs :guard t))
  (let ((request (fn-bpaj-request request-octets))
        (record (fn-bprr-decode-value store-record :record)))
    (and request (fn-record-p record)
         (let* ((ref (fn-bpaj-request-ref request))
                (r (list :request-transit-context inbound-id (car ref)
                         (fn-record-msgid record) generation txid
                         record-generation result (cadr ref) (caddr ref))))
           (and (fn-bpaj-transit-contextp r) r)))))

; A context binds its intent exactly: the same inbound identity, reference,
; generation and result, the planned txid for a fresh acceptance, and a
; Store record (the one it names) whose payload is the intent's pinned
; projection by length and digest.
(defun fn-bpaj-transit-context-matches-intentp (store context intent)
  (declare (xargs :guard t))
  (let ((record (fn-bpaj-context-record store context)))
    (and (fn-bpaj-transit-contextp context)
         (fn-bpaj-transit-intentp intent)
         (equal (fn-bpaj-nth 1 context) (fn-bpaj-nth 1 intent))
         (equal (fn-bpaj-context-ref context) (fn-bpaj-intent-ref intent))
         (equal (fn-bpaj-nth 4 context) (fn-bpaj-nth 3 intent))
         (equal (fn-bpaj-nth 7 context) (fn-bpaj-nth 5 intent))
         (fn-record-p record)
         (fn-bpr-store-record-acceptedp store record)
         (equal (len (fn-record-payload record)) (fn-bpaj-nth 11 intent))
         (equal (fn-frame-digest (fn-record-payload record))
                (fn-bpaj-nth 12 intent))
         (or (equal (fn-bpaj-nth 5 intent) :duplicate)
             (equal (fn-record-txid record) (fn-bpaj-nth 4 intent))))))


; Whether INTENT names the live REQUEST (a decoded message): by reference.
(defun fn-bpaj-intent-names-requestp (intent request)
  (declare (xargs :guard t))
  (fn-bpaj-request-ref-matchesp request (fn-bpaj-nth 2 intent)
                                (fn-bpaj-nth 9 intent)
                                (fn-bpaj-nth 10 intent)))

(defun fn-bpaj-intent-listp (xs)
  (declare (xargs :guard t :measure (acl2-count xs)))
  (if (consp xs)
      (and (fn-bpaj-transit-intentp (car xs))
           (fn-bpaj-intent-listp (cdr xs)))
    (null xs)))

(defun fn-bpaj-fact-listp (xs)
  (declare (xargs :guard t :measure (acl2-count xs)))
  (if (consp xs)
      (and (fn-bpaj-transit-contextp (car xs))
           (fn-bpaj-fact-listp (cdr xs)))
    (null xs)))

(defun fn-bpaj-statep (x)
  (declare (xargs :guard t))
  (and (true-listp x) (equal (len x) 4)
       (fn-bpr-statep (fn-bpaj-receiver x))
       (fn-bpaj-intent-listp (fn-bpaj-intents x))
       (fn-bpaj-fact-listp (fn-bpaj-facts x))
       (booleanp (fn-bpaj-strictp x))))

(defthm fn-bpaj-statep-forward-shape
  (implies (fn-bpaj-statep x) (consp x))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable fn-bpaj-statep))))

; An intent's or context's work id is its reference's HEAD's.
(defun fn-bpaj-intent-work-id (intent)
  (declare (xargs :guard t))
  (fn-bpaj-head-work-id (fn-bpaj-nth 2 intent)))

(defun fn-bpaj-find-intent (work-id intents)
  (declare (xargs :guard t :measure (acl2-count intents)))
  (if (consp intents)
      (if (equal work-id (fn-bpaj-intent-work-id (car intents)))
          (car intents)
        (fn-bpaj-find-intent work-id (cdr intents)))
    nil))

(defun fn-bpaj-find-fact (work-id facts)
  (declare (xargs :guard t :measure (acl2-count facts)))
  (if (consp facts)
      (let ((fact-work-id (fn-bpaj-intent-work-id (car facts))))
        (if (and fact-work-id (equal work-id fact-work-id))
            (car facts)
          (fn-bpaj-find-fact work-id (cdr facts))))
    nil))

(defun fn-bpaj-context-intent (joined context)
  (declare (xargs :guard t))
  (let ((work-id (fn-bpaj-intent-work-id context)))
    (and work-id
         (fn-bpaj-find-intent work-id (fn-bpaj-intents joined)))))

; Result is (okp joined-state).  Legacy context-first records are accepted only
; before this journal has observed its first request intent.
(defun fn-bpaj-apply-record (joined store r)
  (declare (xargs :guard t))
  (if (not (fn-bpaj-statep joined)) (list nil joined)
    (let ((kind (fn-bpaj-nth 0 r)))
      (cond
       ((equal kind :request-transit-intent)
        (if (not (fn-bpaj-transit-intentp r)) (list nil joined)
          (let* ((work-id (fn-bpaj-intent-work-id r))
                 (prior (fn-bpaj-find-intent work-id (fn-bpaj-intents joined)))
                 (context (fn-bpr-find-context
                           work-id
                           (fn-bpr-state-contexts (fn-bpaj-receiver joined)))))
            (if (or prior context) (list nil joined)
              (list t (fn-bpaj-make-state
                       (fn-bpaj-receiver joined)
                       (append (fn-bpaj-intents joined) (list r))
                       (fn-bpaj-facts joined) t))))))
       ((equal kind :request-transit-context)
        (let ((intent (fn-bpaj-context-intent joined r)))
          (if (not (and intent
                        (fn-bpaj-transit-context-matches-intentp
                         store r intent)))
              (list nil joined)
            ; The receiver binds the request's REFERENCE to the Store
            ; record the context names, resolved here at every read
            ; (recovery included); no bytes of the request are read.
            (let* ((record (fn-bpaj-context-record store r))
                   (answer (fn-bpr-accept-projected-ref
                            (fn-bpaj-receiver joined) store record
                            (fn-bpaj-context-ref r)
                            (fn-bpaj-nth 11 intent) (fn-bpaj-nth 12 intent)
                            t)))
              (if (not (equal (car answer) :accepted)) (list nil joined)
                (list t (fn-bpaj-make-state
                         (fn-bprr-nth 1 answer)
                         (fn-bpaj-intents joined)
                         (append (fn-bpaj-facts joined) (list r)) t)))))))
       ((equal kind :request-context)
        (if (fn-bpaj-strictp joined) (list nil joined)
          (let ((answer (fn-bprr-apply-record
                         (fn-bpaj-receiver joined) store r)))
            (if (not (car answer)) (list nil joined)
              (list t (fn-bpaj-make-state (fn-bprr-nth 1 answer)
                                          (fn-bpaj-intents joined)
                                          (fn-bpaj-facts joined) nil))))))
       (t
        (let ((answer (fn-bprr-apply-record
                       (fn-bpaj-receiver joined) store r)))
          (if (not (car answer)) (list nil joined)
            (list t (fn-bpaj-make-state (fn-bprr-nth 1 answer)
                                        (fn-bpaj-intents joined)
                                        (fn-bpaj-facts joined)
                                        (fn-bpaj-strictp joined))))))))))

(defun fn-bpaj-replay-rest (joined store records)
  (declare (xargs :guard t :measure (acl2-count records)))
  (if (endp records) (list t joined)
    (let ((answer (fn-bpaj-apply-record joined store (car records))))
      (if (not (car answer)) (list nil joined)
        (fn-bpaj-replay-rest (fn-bpaj-nth 1 answer) store (cdr records))))))

(defun fn-bpaj-replay (store records)
  (declare (xargs :guard t))
  (if (or (endp records) (not (fn-bprr-configp (car records))))
      (list nil nil)
    (let ((receiver (fn-bpr-initial-state (fn-bprr-config (car records)))))
      (if (not (fn-bpr-statep receiver)) (list nil nil)
        (fn-bpaj-replay-rest (fn-bpaj-make-state receiver nil nil nil)
                             store (cdr records))))))

(defun fn-bpaj-request-status (joined request-octets)
  (declare (xargs :guard t))
  (let* ((request (fn-bpaj-request request-octets))
         (receiver (fn-bpaj-receiver joined)))
    (if (not (and (fn-bpaj-statep joined) request)) :malformed
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
               (intent (fn-bpaj-find-intent work-id
                                             (fn-bpaj-intents joined)))
               (pending (fn-bpr-state-pending receiver)))
          (cond ((and context
                      (not (equal (fn-bpaj-request-ref request)
                                  (fn-bpr-context-request-ref context))))
                 :conflict)
                ((and intent
                      (not (fn-bpaj-intent-names-requestp intent request)))
                 :conflict)
                ((and context (fn-bpr-receipt-adu receiver request)) :committed)
                ((consp pending)
                 (if (equal work-id
                            (fn-bpr-context-work-id
                             (fn-bpr-receipt-entry-context pending)))
                     :pending-receipt :blocked))
                (context :context)
                (intent :intent)
                (t :new)))))))

(defun fn-bpaj-pending-receipt-resolution (joined)
  (declare (xargs :guard t))
  (let* ((pending (and (fn-bpaj-statep joined)
                       (fn-bpr-state-pending (fn-bpaj-receiver joined))))
         (context (and (consp pending) (fn-bpr-receipt-entry-context pending)))
         (receipt (and (consp pending) (fn-bpr-receipt-entry-receipt pending))))
    (and context receipt
         (list :receipt-decision (fn-bpr-context-work-id context)
               (fn-bpa-receipt-id receipt) :absent))))

(defun fn-bpaj-request-intent (joined request-octets)
  (declare (xargs :guard t))
  (let ((request (fn-bpaj-request request-octets)))
    (and request
         (fn-bpaj-find-intent (fn-bpa-request-work-id request)
                              (fn-bpaj-intents joined)))))

(defun fn-bpaj-request-inbound-id (joined request-octets)
  (declare (xargs :guard t))
  (let ((intent (fn-bpaj-request-intent joined request-octets)))
    (and intent (fn-bpaj-nth 1 intent))))

(defun fn-bpaj-request-generation (joined request-octets)
  (declare (xargs :guard t))
  (let ((intent (fn-bpaj-request-intent joined request-octets)))
    (and intent (fn-bpaj-nth 3 intent))))

(defun fn-bpaj-request-planned-txid (joined request-octets)
  (declare (xargs :guard t))
  (let ((intent (fn-bpaj-request-intent joined request-octets)))
    (and intent (fn-bpaj-nth 4 intent))))

(defun fn-bpaj-request-planned-result (joined request-octets)
  (declare (xargs :guard t))
  (let ((intent (fn-bpaj-request-intent joined request-octets)))
    (and intent (fn-bpaj-nth 5 intent))))

(defun fn-bpaj-request-result (joined request-octets)
  (declare (xargs :guard t))
  (let* ((request (fn-bpaj-request request-octets))
         (fact (and request
                    (fn-bpaj-find-fact (fn-bpa-request-work-id request)
                                       (fn-bpaj-facts joined)))))
    (and fact (fn-bpaj-nth 7 fact))))

(defun fn-bpaj-bp-provenance-octets (node-id bundle-identity request)
  (declare (xargs :guard t))
  (if (not (and (stringp node-id) (fn-cbor-octet-listp bundle-identity)
                (fn-bpa-requestp request)))
      nil
    (let* ((bundle-text
            (fn-record-octets-string (fn-id-hex-octets bundle-identity)))
           (p (fn-prov-make-bp node-id bundle-text
                               (fn-bpa-request-policy-id request))))
      (and (fn-prov-durablep p)
           (fn-record-string-octets (fn-prov-wire p))))))

(defun fn-bpaj-eid-text (eid)
  (declare (xargs :guard t))
  (cond ((equal eid (list :dtn-none)) "dtn:none")
        ((and (consp eid) (equal (car eid) :dtn))
         (string-append "dtn:" (fn-record-octets-string (cdr eid))))
        ((and (true-listp eid) (equal (len eid) 3)
              (equal (car eid) :ipn) (natp (cadr eid)) (natp (caddr eid)))
         (string-append
          "ipn:" (string-append (fn-prov-nat-string (cadr eid))
                                 (string-append "."
                                                (fn-prov-nat-string
                                                 (caddr eid))))))
        (t "")))

(defun fn-bpaj-transit-record-lookup (store request intent)
  (declare (xargs :guard t))
  (let ((fields (fn-bpaj-transit-article-fields request)))
    (if (not (and (equal (car fields) :ok)
                  (fn-bpaj-transit-intentp intent)))
        (list :conflict)
      (let ((records (fn-bpaj-record-for-msgid
                      (fn-record-octets-string (cadr fields))
                      (fn-sf-records (fn-sn-files store)))))
        (cond ((endp records) (list :absent))
              ((consp (cdr records)) (list :conflict))
              ((fn-bpaj-transit-record-matchp
                store (car records) request (fn-bpaj-nth 11 intent)
                (fn-bpaj-nth 12 intent))
               (list :found (car records)))
              (t (list :conflict)))))))

; This is the dispatcher the native callback calls.  It is intentionally a
; projection over replayed FNRJ state plus the authoritative live Store.  In
; particular, an intent does not imply acceptance: it permits a Store attempt
; only while its pinned owner generation is still current and no committed
; record exists.  A unique exact record is bound; conflicting or multiple
; candidates are refused without choosing one.
(defun fn-bpaj-dispatch (joined store request-octets current-generation)
  (declare (xargs :guard t))
  (let* ((request (fn-bpaj-request request-octets))
         (status (fn-bpaj-request-status joined request-octets)))
    (case status
      (:new (list :persist-intent))
      (:intent
       (let* ((intent (fn-bpaj-request-intent joined request-octets))
              (lookup (fn-bpaj-transit-record-lookup store request intent)))
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

(defun fn-bpaj-receipt-id (request)
  (declare (xargs :guard t))
  (if (fn-bpa-requestp request)
      (string-append "receipt:" (fn-bpa-request-work-id request))
    ""))

; Local projection for the accepted transit-context branch: after its
; binding checks, the receiver component is the receiver's own acceptance of
; the context's REFERENCE bound to the Store record the context names
; (PKT-646).  This equation does not prove the composed replay invariant
; that connects every recovered context and receipt to the live owner's
; Store; that stronger trace result remains open.
(defthm fn-bpaj-transit-context-receiver-is-existing-transition
  (implies
   (and (fn-bpaj-statep joined)
        (equal (fn-bpaj-nth 0 context) :request-transit-context)
        (fn-bpaj-context-intent joined context)
        (fn-bpaj-transit-context-matches-intentp
         store context (fn-bpaj-context-intent joined context))
        (equal (car (fn-bpr-accept-projected-ref
                     (fn-bpaj-receiver joined) store
                     (fn-bpaj-context-record store context)
                     (fn-bpaj-context-ref context)
                     (fn-bpaj-nth 11 (fn-bpaj-context-intent joined context))
                     (fn-bpaj-nth 12 (fn-bpaj-context-intent joined context))
                     t))
               :accepted))
   (equal (fn-bpaj-receiver
           (fn-bpaj-nth 1 (fn-bpaj-apply-record joined store context)))
          (fn-bprr-nth 1
                      (fn-bpr-accept-projected-ref
                       (fn-bpaj-receiver joined) store
                       (fn-bpaj-context-record store context)
                       (fn-bpaj-context-ref context)
                       (fn-bpaj-nth 11 (fn-bpaj-context-intent joined context))
                       (fn-bpaj-nth 12 (fn-bpaj-context-intent joined context))
                       t))))
  :hints (("Goal" :in-theory
           (e/d (fn-bpaj-apply-record)
                (fn-bpaj-statep fn-bpaj-transit-contextp
                 fn-bpaj-context-intent fn-bpaj-transit-context-matches-intentp
                 fn-bpaj-context-record fn-bpaj-context-ref
                 fn-bpr-accept-projected-ref)))))

; Branch projection for the dispatch definition.  It records the exact facts
; under which this dispatcher returns :submit; it is not a replay theorem.
(defthm fn-bpaj-dispatch-transit-intent-absent-retries
  (implies
   (and (equal (fn-bpaj-request-status joined request-octets) :intent)
        (equal current-generation
               (fn-bpaj-request-generation joined request-octets))
        (equal (fn-bpaj-request-planned-result joined request-octets)
               :accepted)
        (equal (car (fn-bpaj-transit-record-lookup
                     store (fn-bpaj-request request-octets)
                     (fn-bpaj-request-intent joined request-octets)))
               :absent))
   (equal (fn-bpaj-dispatch joined store request-octets
                            current-generation)
          (list :submit)))
  :hints (("Goal" :in-theory
           (e/d (fn-bpaj-dispatch)
                (fn-bpaj-request-status fn-bpaj-request-generation
                 fn-bpaj-request-planned-result
                 fn-bpaj-transit-record-lookup fn-bpaj-request)))))

(defthm fn-bpaj-dispatch-committed-never-retries
  (implies (equal (fn-bpaj-request-status joined request-octets) :committed)
           (equal (fn-bpaj-dispatch joined store request-octets
                                    current-generation)
                  (list :return-receipt)))
  :hints (("Goal" :in-theory
           (e/d (fn-bpaj-dispatch)
                (fn-bpaj-request-status fn-bpaj-request-generation
                 fn-bpaj-request-planned-result fn-bpaj-transit-record-lookup
                 fn-bpaj-request)))))

(in-theory (disable fn-bpaj-statep fn-bpaj-intent-listp
                    fn-bpaj-apply-record fn-bpaj-replay-rest fn-bpaj-replay
                    fn-bpaj-request-status
                    fn-bpaj-dispatch))
