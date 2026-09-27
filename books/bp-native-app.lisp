; Native BP application join: intent-first FNRJ replay and exact Store binding.
(in-package "ACL2")
(include-book "bp-receipt-records")
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


(defun fn-bpaj-transit-record-matchp (store record request stored-octets)
  (declare (xargs :guard t))
  (and (fn-record-p record)
       (fn-bpa-requestp request)
       (fn-bpr-store-record-acceptedp store record)
       (equal (fn-record-payload record) stored-octets)
       (let ((fields (fn-bpaj-transit-article-fields request)))
         (and (equal (car fields) :ok)
              (equal (fn-record-msgid record)
                     (fn-record-octets-string (cadr fields)))))))


; The v3 intent is written before Store submission.  Its final three fields
; are the selected local Path identity, expected peer Path identity, and
; locally stored projection.  Replay verifies the projection against those
; pinned identities, without consulting a later owner configuration.
; (kind inbound raw-request generation planned-txid result peer
;       local-path peer-path stored-projection)
(defun fn-bpaj-transit-intentp (r)
  (declare (xargs :guard t))
  (let* ((request (fn-bpaj-request (fn-bpaj-nth 2 r)))
         (local (fn-record-string-octets (fn-bpaj-nth 7 r)))
         (expected (fn-record-string-octets (fn-bpaj-nth 8 r))))
    (and (true-listp r) (equal (len r) 10)
         (equal (fn-bpaj-nth 0 r) :request-transit-intent)
         (fn-bprr-textp (fn-bpaj-nth 1 r))
         (fn-bprr-octetsp (fn-bpaj-nth 2 r))
         request
         (fn-bpaj-request-subjectp request)
         (fn-record-uint32p (fn-bpaj-nth 3 r))
         (fn-record-uint32p (fn-bpaj-nth 4 r))
         (member-equal (fn-bpaj-nth 5 r) '(:accepted :duplicate))
         (fn-bprr-textp (fn-bpaj-nth 6 r))
         (fn-bprr-textp (fn-bpaj-nth 7 r))
         (fn-bprr-textp (fn-bpaj-nth 8 r))
         (fn-path-identityp local) (fn-path-identityp expected)
         (fn-bprr-octetsp (fn-bpaj-nth 9 r))
         (equal (fn-bpaj-nth 9 r)
                (fn-pu-relay-article (fn-bpa-request-article request)
                                     local expected)))))

; The context binds a recovered exact Store record to a prior validated v3
; intent.  The raw request stays in the context for receipt construction;
; the Store payload is compared with the independently pinned projection.
; (kind inbound raw-request store-record owner-generation store-txid
;       store-generation result)
(defun fn-bpaj-transit-contextp (r)
  (declare (xargs :guard t))
  (and (true-listp r) (equal (len r) 8)
       (equal (fn-bpaj-nth 0 r) :request-transit-context)
       (fn-bprr-textp (fn-bpaj-nth 1 r))
       (fn-bprr-octetsp (fn-bpaj-nth 2 r))
       (fn-bprr-octetsp (fn-bpaj-nth 3 r))
       (fn-record-uint32p (fn-bpaj-nth 4 r))
       (fn-record-uint32p (fn-bpaj-nth 5 r))
       (fn-record-uint32p (fn-bpaj-nth 6 r))
       (member-equal (fn-bpaj-nth 7 r) '(:accepted :duplicate))))

(defun fn-bpaj-transit-context-matches-intentp (store context intent)
  (declare (xargs :guard t))
  (let* ((request (fn-bpaj-request (fn-bpaj-nth 2 context)))
         (record (fn-bprr-decode-value (fn-bpaj-nth 3 context) :record)))
    (and (fn-bpaj-transit-contextp context)
         (fn-bpaj-transit-intentp intent)
         (equal (fn-bpaj-nth 1 context) (fn-bpaj-nth 1 intent))
         (equal (fn-bpaj-nth 2 context) (fn-bpaj-nth 2 intent))
         (equal (fn-bpaj-nth 4 context) (fn-bpaj-nth 3 intent))
         (equal (fn-bpaj-nth 7 context) (fn-bpaj-nth 5 intent))
         (fn-bpaj-transit-record-matchp
          store record request (fn-bpaj-nth 9 intent))
         (equal (fn-record-txid record) (fn-bpaj-nth 5 context))
         (equal (fn-record-generation record) (fn-bpaj-nth 6 context))
         (or (equal (fn-bpaj-nth 5 intent) :duplicate)
             (equal (fn-record-txid record) (fn-bpaj-nth 4 intent))))))


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

; ----------------------------------------------------------------------------
; PKT-646 (D27): a local request by REFERENCE, never by copy.
;
; A local FNRJ intent or context carries no copy of the request ADU.  It
; carries the request's REFERENCE (HEAD LENGTH DIGEST): HEAD the ADU's eight
; metadata items encoded exactly as the ADU encodes them
; (`fn-bpa-encode-fields'; at most 8 x 259 octets by the ADU grammar), LENGTH
; and DIGEST the article's length and `fn-frame-digest'.  The article's bytes
; are the held payload the delivery already made durable: the delivered
; bundle (the record's inbound identity) in the BP node's held journal while
; the delivery is held, and the Store record the context names (Message-ID,
; txid, generation) once the Store committed it.  Every read of a context
; resolves the reference against that Store record
; (`fn-bpaj-context-request'); `fn-bpaj-ref-request-resolves-exactly' is the
; exactness of the resolution, and a live request is compared with an
; intent through its reference (`fn-bpaj-intent-names-requestp').

; The eight metadata items of a request, as the ADU encodes them.
(defun fn-bpaj-head-fields (request)
  (declare (xargs :guard t))
  (list (fn-record-string-octets (fn-bpa-request-work-id request))
        (fn-record-string-octets (fn-bpa-request-subject request))
        (fn-record-string-octets (fn-bpa-request-source-eid request))
        (fn-record-string-octets (fn-bpa-request-destination-eid request))
        (fn-record-string-octets (fn-bpa-request-policy-id request))
        (fn-record-string-octets (fn-bpa-request-incarnation request))
        (fn-record-string-octets (fn-bpa-request-auth-context request))
        (fn-record-string-octets (fn-bpa-request-terms-id request))))

(defun fn-bpaj-head-octets (request)
  (declare (xargs :guard t))
  (fn-bpa-encode-fields (fn-bpaj-head-fields request)))

; The metadata items HEAD encodes, or nil.
(defun fn-bpaj-head-read (head)
  (declare (xargs :guard t))
  (let ((parsed (and (fn-cbor-octet-listp head)
                     (fn-bpa-read-fields 8 head))))
    (and (fn-record-parse-okp parsed)
         (null (fn-record-parse-rest parsed))
         (fn-record-parse-value parsed))))

(defun fn-bpaj-head-metadatap (fields)
  (declare (xargs :guard t))
  (if (consp fields)
      (and (fn-bpa-metadatap (fn-record-octets-string (car fields)))
           (fn-bpaj-head-metadatap (cdr fields)))
    (null fields)))

(defun fn-bpaj-headp (head)
  (declare (xargs :guard t))
  (let ((fields (fn-bpaj-head-read head)))
    (and (equal (len fields) 8) (fn-bpaj-head-metadatap fields))))

(defun fn-bpaj-head-work-id (head)
  (declare (xargs :guard t))
  (let ((fields (fn-bpaj-head-read head)))
    (and (consp fields) (fn-record-octets-string (car fields)))))

; The reference of a request message: (HEAD LENGTH DIGEST).
(defun fn-bpaj-request-ref (request)
  (declare (xargs :guard t))
  (list (fn-bpaj-head-octets request)
        (len (fn-bpa-request-article request))
        (fn-frame-digest (fn-bpa-request-article request))))

; RESOLUTION: the request message the reference names over ARTICLE, the
; held payload's bytes, or nil when ARTICLE is not the referenced one (its
; length or digest differs) or the whole is no request.
(defun fn-bpaj-ref-request (head length digest article)
  (declare (xargs :guard t))
  (let ((fields (fn-bpaj-head-read head)))
    (and fields
         (fn-cbor-octet-listp article)
         (equal (len article) length)
         (equal (fn-frame-digest article) digest)
         (let ((request (fn-bpa-request-from-fields
                         (append fields (list article)))))
           (and (fn-bpa-requestp request) request)))))

; A live request is the one an intent references: the same metadata, and an
; article of the same length and digest.
(defun fn-bpaj-request-ref-matchesp (request head length digest)
  (declare (xargs :guard t))
  (and (fn-bpa-requestp request)
       (equal (fn-bpaj-request-ref request) (list head length digest))))

; (kind inbound HEAD owner-generation planned-txid result LENGTH DIGEST)
(defun fn-bpaj-intentp (r)
  (declare (xargs :guard t))
  (and (true-listp r) (equal (len r) 8)
       (equal (fn-bpaj-nth 0 r) :request-intent)
       (fn-bprr-textp (fn-bpaj-nth 1 r))
       (fn-bprr-octetsp (fn-bpaj-nth 2 r))
       (fn-bpaj-headp (fn-bpaj-nth 2 r))
       (fn-record-uint32p (fn-bpaj-nth 3 r))
       (fn-record-uint32p (fn-bpaj-nth 4 r))
       (member-equal (fn-bpaj-nth 5 r) '(:accepted :duplicate))
       (natp (fn-bpaj-nth 6 r))
       (<= (fn-bpaj-nth 6 r) *fn-bpa-max-article*)
       (fn-frame-digestp (fn-bpaj-nth 7 r))))

; The intent the host publishes (host/bp-receipt-journal-host.lisp
; `fn-bprj-request-intent-record'): the request's reference, never its bytes.
(defun fn-bpaj-intent-record (inbound-id request-octets generation txid result)
  (declare (xargs :guard t))
  (let ((request (fn-bpaj-request request-octets)))
    (and request
         (let* ((ref (fn-bpaj-request-ref request))
                (r (list :request-intent inbound-id (car ref) generation txid
                         result (cadr ref) (caddr ref))))
           (and (fn-bpaj-intentp r) r)))))

; Whether INTENT names the live REQUEST (a decoded message): by reference for a
; local intent, by its carried bytes for a transit one.
(defun fn-bpaj-intent-names-requestp (intent request)
  (declare (xargs :guard t))
  (if (equal (fn-bpaj-nth 0 intent) :request-intent)
      (fn-bpaj-request-ref-matchesp request (fn-bpaj-nth 2 intent)
                                    (fn-bpaj-nth 6 intent)
                                    (fn-bpaj-nth 7 intent))
    (equal request (fn-bpaj-request (fn-bpaj-nth 2 intent)))))

(defun fn-bpaj-intent-listp (xs)
  (declare (xargs :guard t :measure (acl2-count xs)))
  (if (consp xs)
      (and (or (fn-bpaj-intentp (car xs))
               (fn-bpaj-transit-intentp (car xs)))
           (fn-bpaj-intent-listp (cdr xs)))
    (null xs)))

; (kind inbound HEAD store-msgid owner-generation store-txid store-generation
;       t result LENGTH DIGEST): the request's reference and the Store
; record's identity, never a copy of either.
(defun fn-bpaj-context-v2p (r)
  (declare (xargs :guard t))
  (and (true-listp r) (equal (len r) 11)
       (equal (fn-bpaj-nth 0 r) :request-context-v2)
       (fn-bprr-textp (fn-bpaj-nth 1 r))
       (fn-bprr-octetsp (fn-bpaj-nth 2 r))
       (fn-bpaj-headp (fn-bpaj-nth 2 r))
       (fn-bprr-textp (fn-bpaj-nth 3 r))
       (fn-record-uint32p (fn-bpaj-nth 4 r))
       (fn-record-uint32p (fn-bpaj-nth 5 r))
       (fn-record-uint32p (fn-bpaj-nth 6 r))
       (equal (fn-bpaj-nth 7 r) t)
       (member-equal (fn-bpaj-nth 8 r) '(:accepted :duplicate))
       (natp (fn-bpaj-nth 9 r))
       (<= (fn-bpaj-nth 9 r) *fn-bpa-max-article*)
       (fn-frame-digestp (fn-bpaj-nth 10 r))))

; The context the host publishes (`fn-bprj-request-context-v2-record'), from
; the live request and the committed Store record's octets.
(defun fn-bpaj-context-v2-record
    (inbound-id request-octets store-record generation txid record-generation
                result)
  (declare (xargs :guard t))
  (let ((request (fn-bpaj-request request-octets))
        (record (fn-bprr-decode-value store-record :record)))
    (and request (fn-record-p record)
         (let* ((ref (fn-bpaj-request-ref request))
                (r (list :request-context-v2 inbound-id (car ref)
                         (fn-record-msgid record) generation txid
                         record-generation t result (cadr ref) (caddr ref))))
           (and (fn-bpaj-context-v2p r) r)))))

; The Store record a context names: the one article record with its
; Message-ID, with its txid and generation; nil otherwise.
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

; The request a context's reference resolves to over the Store RECORD's
; payload: every read of the context (recovery included) goes through here.
(defun fn-bpaj-context-request (r record)
  (declare (xargs :guard t))
  (and (fn-record-p record)
       (fn-bpaj-ref-request (fn-bpaj-nth 2 r) (fn-bpaj-nth 9 r)
                            (fn-bpaj-nth 10 r) (fn-record-payload record))))

(defun fn-bpaj-context-v2-listp (xs)
  (declare (xargs :guard t :measure (acl2-count xs)))
  (if (consp xs)
      (and (or (fn-bpaj-context-v2p (car xs))
               (fn-bpaj-transit-contextp (car xs)))
           (fn-bpaj-context-v2-listp (cdr xs)))
    (null xs)))

(defun fn-bpaj-statep (x)
  (declare (xargs :guard t))
  (and (true-listp x) (equal (len x) 4)
       (fn-bpr-statep (fn-bpaj-receiver x))
       (fn-bpaj-intent-listp (fn-bpaj-intents x))
       (fn-bpaj-context-v2-listp (fn-bpaj-facts x))
       (booleanp (fn-bpaj-strictp x))))

(defthm fn-bpaj-statep-forward-shape
  (implies (fn-bpaj-statep x) (consp x))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable fn-bpaj-statep))))

(defthm fn-bpaj-context-v2p-forward-kind
  (implies (fn-bpaj-context-v2p x)
           (and (consp x)
                (equal (fn-bpaj-nth 0 x) :request-context-v2)))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable fn-bpaj-context-v2p))))

; A local intent's or context's work id is its reference's; a transit one's is
; its carried request's.
(defun fn-bpaj-intent-work-id (intent)
  (declare (xargs :guard t))
  (if (or (equal (fn-bpaj-nth 0 intent) :request-intent)
          (equal (fn-bpaj-nth 0 intent) :request-context-v2))
      (fn-bpaj-head-work-id (fn-bpaj-nth 2 intent))
    (let ((request (fn-bpaj-request (fn-bpaj-nth 2 intent))))
      (and request (fn-bpa-request-work-id request)))))

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

; A context binds its intent's reference exactly: the same inbound identity,
; HEAD, LENGTH and DIGEST, generation and result, and the planned txid for a
; fresh acceptance.  The Store record is checked where the context is read
; (`fn-bpaj-context-record').
(defun fn-bpaj-context-matches-intentp (context intent)
  (declare (xargs :guard t))
  (and (fn-bpaj-context-v2p context) (fn-bpaj-intentp intent)
       (equal (fn-bpaj-nth 1 context) (fn-bpaj-nth 1 intent))
       (equal (fn-bpaj-nth 2 context) (fn-bpaj-nth 2 intent))
       (equal (fn-bpaj-nth 9 context) (fn-bpaj-nth 6 intent))
       (equal (fn-bpaj-nth 10 context) (fn-bpaj-nth 7 intent))
       (equal (fn-bpaj-nth 4 context) (fn-bpaj-nth 3 intent))
       (equal (fn-bpaj-nth 8 context) (fn-bpaj-nth 5 intent))
       (or (equal (fn-bpaj-nth 5 intent) :duplicate)
           (equal (fn-bpaj-nth 5 context) (fn-bpaj-nth 4 intent)))))

; Result is (okp joined-state).  Legacy context-first records are accepted only
; before this journal has observed its first request intent.
(defun fn-bpaj-apply-record (joined store r)
  (declare (xargs :guard t))
  (if (not (fn-bpaj-statep joined)) (list nil joined)
    (let ((kind (fn-bpaj-nth 0 r)))
      (cond
       ((equal kind :request-intent)
        (if (not (fn-bpaj-intentp r)) (list nil joined)
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
       ((equal kind :request-context-v2)
        (let ((intent (fn-bpaj-context-intent joined r)))
          (if (not (and intent (fn-bpaj-context-matches-intentp r intent)))
              (list nil joined)
            ; The reference resolves against the Store record the context
            ; names; the receiver binds exactly that request and record.
            (let* ((record (fn-bpaj-context-record store r))
                   (answer (fn-bpr-accept-request
                            (fn-bpaj-receiver joined) store record
                            (fn-bpaj-context-request r record) t)))
              (if (not (equal (car answer) :accepted)) (list nil joined)
                (list t (fn-bpaj-make-state
                         (fn-bpa-nth 1 answer)
                         ; Retain the exact original inbound identity and
                         ; configuration generation after binding.  Receipt
                         ; retries may arrive in a different BP bundle, but
                         ; they never rewrite the acceptance evidence.
                         (fn-bpaj-intents joined)
                         (append (fn-bpaj-facts joined) (list r)) t)))))))
       ((equal kind :request-transit-context)
        (let ((intent (fn-bpaj-context-intent joined r)))
          (if (not (and intent
                        (fn-bpaj-transit-context-matches-intentp
                         store r intent)))
              (list nil joined)
            (let* ((request (fn-bpaj-request (fn-bpaj-nth 2 r)))
                   (record (fn-bprr-decode-value (fn-bpaj-nth 3 r) :record))
                   (answer (fn-bpr-accept-projected-request
                            (fn-bpaj-receiver joined) store record request
                            (fn-bpaj-nth 9 intent) t)))
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
                      (not (equal request (fn-bpr-context-request context))))
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
    (and fact (if (equal (fn-bpaj-nth 0 fact) :request-transit-context)
                  (fn-bpaj-nth 7 fact)
                (fn-bpaj-nth 8 fact)))))

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

(defun fn-bpaj-record-matches-requestp (store record request)
  (declare (xargs :guard t))
  (and (fn-record-p record) (fn-bpa-requestp request)
       (equal (fn-record-payload record) (fn-bpa-request-article request))
       (equal (fn-record-content-subject record)
              (fn-bpa-request-subject request))
       (fn-bpr-store-record-acceptedp store record)))

; (:found record), (:absent), or (:conflict).  Multiple same-Message-ID
; records are conflict even if byte-identical: the host never picks a first.
(defun fn-bpaj-record-lookup (store request)
  (declare (xargs :guard t))
  (let ((fields (fn-bpaj-article-fields request)))
    (if (not (equal (car fields) :ok)) (list :conflict)
      (let ((records (fn-bpaj-record-for-msgid
                      (fn-record-octets-string (cadr fields))
                      (fn-sf-records (fn-sn-files store)))))
        (cond ((endp records) (list :absent))
              ((consp (cdr records)) (list :conflict))
              ((fn-bpaj-record-matches-requestp store (car records) request)
               (list :found (car records)))
              (t (list :conflict)))))))

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
                store (car records) request (fn-bpaj-nth 9 intent))
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
                (lookup (if (equal (fn-bpaj-nth 0 intent)
                                   :request-transit-intent)
                            (fn-bpaj-transit-record-lookup store request intent)
                          (fn-bpaj-record-lookup store request))))
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

(defun fn-bpaj-receipt-id (request)
  (declare (xargs :guard t))
  (if (fn-bpa-requestp request)
      (string-append "receipt:" (fn-bpa-request-work-id request))
    ""))

; Local projection for the accepted strict-context branch: after its binding
; checks, the receiver component is the receiver's own acceptance of the
; request the context's reference resolves to over the Store record it names
; (PKT-646).  This equation does not prove the composed replay invariant that
; connects every recovered context and receipt to the live owner's Store;
; that stronger trace result remains open.
(defthm fn-bpaj-context-v2-receiver-is-existing-transition
  (implies
   (and (fn-bpaj-statep joined)
        (equal (fn-bpaj-nth 0 context) :request-context-v2)
        (fn-bpaj-context-intent joined context)
        (fn-bpaj-context-matches-intentp
         context (fn-bpaj-context-intent joined context))
        (equal (car (fn-bpr-accept-request
                     (fn-bpaj-receiver joined) store
                     (fn-bpaj-context-record store context)
                     (fn-bpaj-context-request
                      context (fn-bpaj-context-record store context))
                     t))
               :accepted))
   (equal (fn-bpaj-receiver
           (fn-bpaj-nth 1 (fn-bpaj-apply-record joined store context)))
          (fn-bpa-nth 1
                      (fn-bpr-accept-request
                       (fn-bpaj-receiver joined) store
                       (fn-bpaj-context-record store context)
                       (fn-bpaj-context-request
                        context (fn-bpaj-context-record store context))
                       t))))
  :hints (("Goal" :in-theory
           (e/d (fn-bpaj-apply-record)
                (fn-bpaj-statep fn-bpaj-context-v2p
                 fn-bpaj-context-intent fn-bpaj-context-matches-intentp
                 fn-bpaj-context-record fn-bpaj-context-request
                 fn-bpaj-request fn-bpr-accept-request)))))

; Branch projection for the dispatch definition.  It records the exact facts
; under which this dispatcher returns :submit; it is not a replay theorem.
(defthm fn-bpaj-dispatch-intent-absent-retries
  (implies (and (equal (fn-bpaj-request-status joined request-octets) :intent)
                (not (equal (fn-bpaj-nth 0
                             (fn-bpaj-request-intent joined request-octets))
                            :request-transit-intent))
                (equal current-generation
                       (fn-bpaj-request-generation joined request-octets))
                (equal (fn-bpaj-request-planned-result
                        joined request-octets) :accepted)
                (equal (car (fn-bpaj-record-lookup
                             store (fn-bpaj-request request-octets))) :absent))
           (equal (fn-bpaj-dispatch joined store request-octets
                                    current-generation)
                  (list :submit)))
  :hints (("Goal" :in-theory
           (e/d (fn-bpaj-dispatch)
                (fn-bpaj-request-status fn-bpaj-request-generation
                 fn-bpaj-request-planned-result fn-bpaj-record-lookup
                 fn-bpaj-request)))))

(defthm fn-bpaj-dispatch-transit-intent-absent-retries
  (implies
   (and (equal (fn-bpaj-request-status joined request-octets) :intent)
        (equal (fn-bpaj-nth 0
                (fn-bpaj-request-intent joined request-octets))
               :request-transit-intent)
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
                 fn-bpaj-request-planned-result fn-bpaj-record-lookup
                 fn-bpaj-request)))))

(in-theory (disable fn-bpaj-statep fn-bpaj-intentp fn-bpaj-intent-listp
                    fn-bpaj-context-v2p
                    fn-bpaj-apply-record fn-bpaj-replay-rest fn-bpaj-replay
                    fn-bpaj-request-status fn-bpaj-record-lookup
                    fn-bpaj-dispatch))
