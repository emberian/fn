; ACL2-owned durable composition for the selected hybrid signature profile.
; The three constructors that call the injecting agent (fn-inj-decide) are in
; books/hybrid-store-injected.lisp, so this book includes only the field
; checks of books/injection-shape.lisp (audit 2026-09-25, packet 1).

(in-package "ACL2")
(include-book "hybrid-signature")
(include-book "stx-accept-records")
(include-book "injection-shape")
(include-book "identity")
(include-book "records-stamp")
(include-book "hybrid-carrier")
(include-book "control-classify")

(defun fn-hsig-octet-fields-to-strings (fields)
  (declare (xargs :guard t))
  (if (consp fields)
      (cons (fn-record-octets-string (car fields))
            (fn-hsig-octet-fields-to-strings (cdr fields)))
    nil))

;; SPIKE: defers the dev binding that names the filing group (control C2/C3,
;; design 2026-09-25 section 2.1 rule 2); proof owner books/hybrid-store.lisp.
;; A signed control article's record groups are its filing group
;; (control.<verb> or control), never the groups its Newsgroups field names;
;; every other signed article keeps its Newsgroups.  The binding tests below
;; compare the record's groups with this list, so replay agrees with the
;; filing step (books/peer-authored-accept.lisp fn-pa-filing-plan).
(defun fn-hsig-filed-group-strings (article groups)
  (declare (xargs :guard t))
  (let ((classified (fn-ctl-classify article)))
    (if (and (consp classified) (eq (car classified) :control)
             (consp (cdr classified)))
        (list (fn-ctl-filing-group (cadr classified)))
      groups)))

(defun fn-hsig-authored-source-fields (source)
  "Return the supplied Message-ID and Newsgroups parsed from the exact source."
  (declare (xargs :guard t))
  (let ((parsed (fn-article-parse source)))
    (if (not (fn-article-result-okp parsed)) nil
      (let ((article (fn-article-result-article parsed)))
        (if (not (fn-article-syntax-p article)) nil
          (let ((check (fn-af-proto-article-check article)))
            (if (or (fn-inj-proto-reason check)
                    (fn-inj-mandatory-reason article)
                    (not (fn-inj-nth 1 check))
                    (not (consp (fn-inj-nth 2 check)))) nil
              (list (fn-record-octets-string (fn-inj-nth 1 check))
                    (fn-hsig-filed-group-strings
                     article
                     (fn-hsig-octet-fields-to-strings
                      (fn-inj-nth 2 check)))))))))))

; A keyring snapshot is deliberately narrow: one principal and the exact
; ordered public-key set used by the signed-preimage function.  Custody and
; succession policy are outside this representation.
(defun fn-hsig-keyring-snapshot (principal keys)
  (declare (xargs :guard t
                  :guard-hints
                  ; `fn-cbor-valuep-bounded' too: the item encoder checks
                  ; the bounded recognizer since the bounded codec landed,
                  ; and its definition is withdrawn on export (books/cbor).
                  (("Goal" :in-theory (enable fn-hsig-exact-octets-p
                                               fn-hsig-keyset-p
                                               fn-stmt-item-listp
                                               fn-cbor-valuep
                                               fn-cbor-valuep-bounded)))))
  (if (and (fn-hsig-exact-octets-p principal 32)
           (fn-hsig-keyset-p keys))
      (fn-stmt-encode-items
       (list (cons :bytes principal)
             (cons :uint *fn-hsig-ed25519-algorithm*)
             (cons :bytes (cdr (car keys)))
             (cons :uint *fn-hsig-ml-dsa-65-algorithm*)
             (cons :bytes (cdr (car (cdr keys))))))
    nil))

(defun fn-hsig-keyring-event (sequence txid generation keyring-generation
                                       principal keys)
  (declare (xargs :guard t))
  (let ((snapshot (fn-hsig-keyring-snapshot principal keys)))
    (if snapshot
        (let ((event (fn-stxk-make sequence txid generation keyring-generation
                                   *fn-hsig-profile-tag* snapshot)))
          (if (fn-stxk-p event) event nil))
      nil)))

; The guard hint carries the one fact the extraction below needs and the
; decoder cannot supply by induction on a literal fuel: a successful decode's
; value is an item sequence, so it is proper and each index lands on an item
; pair or off the end (books/statement-invariants).  The wrappers stay folded
; so the fact's subject is the term this guard conjecture holds.
(defun fn-hsig-keyring-snapshot-value (snapshot)
  "Return (principal keys) only for the exact canonical selected snapshot."
  (declare (xargs :guard t
                  :guard-hints
                  (("Goal"
                    :use ((:instance fn-stmt-decode-items-value-is-item-list
                                     (fuel 5)
                                     (octets (fn-stxk-snapshot snapshot))))
                    :in-theory
                    (e/d (fn-stmt-item-listp-implies-true-listp
                          fn-stmt-item-listp-nth-is-item-or-nil)
                         (fn-stmt-decode-items
                          fn-stmt-item-listp
                          nth))))))
  (if (not (fn-stxk-p snapshot)) nil
    (let ((decoded (fn-stmt-decode-items 5 (fn-stxk-snapshot snapshot))))
      (if (not (fn-stmt-okp decoded)) nil
        (let* ((items (fn-stmt-value decoded))
               (principal (and (consp items) (cdr (nth 0 items))))
               (keys (list (cons :ed25519 (cdr (nth 2 items)))
                           (cons :ml-dsa-65 (cdr (nth 4 items))))))
          (if (and (equal (fn-stxk-profile snapshot) *fn-hsig-profile-tag*)
                   (equal (fn-stxk-snapshot snapshot)
                          (fn-stxe-encode-items items))
                   (equal (len items) 5)
                   (fn-stmt-bytes-item-p (nth 0 items))
                   (fn-stmt-uint-item-p (nth 1 items))
                   (equal (cdr (nth 1 items)) *fn-hsig-ed25519-algorithm*)
                   (fn-stmt-bytes-item-p (nth 2 items))
                   (fn-stmt-uint-item-p (nth 3 items))
                   (equal (cdr (nth 3 items)) *fn-hsig-ml-dsa-65-algorithm*)
                   (fn-stmt-bytes-item-p (nth 4 items))
                   (fn-hsig-subject-p principal keys nil))
              (list principal keys) nil))))))

; The retained verdict detail contains both detached components in canonical
; algorithm order.  Replay can therefore preserve and independently inspect
; the evidence which produced :verified.
(defun fn-hsig-verdict-detail (principal keys signatures)
  (declare (xargs :guard t
                  :guard-hints
                  ; `fn-cbor-valuep-bounded' for the same reason as
                  ; `fn-hsig-keyring-snapshot' above: the item encoder checks
                  ; the bounded recognizer, whose definition is withdrawn.
                  (("Goal" :in-theory (enable fn-hsig-exact-octets-p
                                               fn-hsig-keyset-p
                                               fn-hsig-signatures-p
                                               fn-stmt-item-listp
                                               fn-cbor-valuep
                                               fn-cbor-valuep-bounded)))))
  (if (and (fn-hsig-exact-octets-p principal 32)
           (fn-hsig-keyset-p keys)
           (fn-hsig-signatures-p signatures))
      (fn-stmt-encode-items
       (list (cons :bytes principal)
             (cons :uint *fn-hsig-ed25519-algorithm*)
             (cons :bytes (cdr (car keys)))
             (cons :uint *fn-hsig-ml-dsa-65-algorithm*)
             (cons :bytes (cdr (car (cdr keys))))
             (cons :uint *fn-hsig-ed25519-algorithm*)
             (cons :bytes (cdr (car signatures)))
             (cons :uint *fn-hsig-ml-dsa-65-algorithm*)
             (cons :bytes (cdr (car (cdr signatures))))))
    nil))

; The evidence tag a verdict records: which carrier version, and so which
; preimage, the two primitive observations were made over.  The keyring
; snapshot and the kind-4 event keep `*fn-hsig-profile-tag*': the keys are
; the same D09 pair under either version.
(defun fn-hsig-evidence-tag (source)
  (declare (xargs :guard t))
  (if (equal (fn-hsig-source-version source) *fn-hsig-v2-version*)
      *fn-stxe-profile-hybrid-v2*
    *fn-hsig-profile-tag*))

(defthm fn-hsig-keyring-profile-of-evidence-tag
  (equal (fn-stxe-keyring-profile (fn-hsig-evidence-tag source))
         *fn-hsig-profile-tag*)
  :hints (("Goal" :in-theory (enable fn-stxe-keyring-profile))))

(defthm fn-hsig-evidence-tag-is-supported
  (fn-stxe-profile-supportedp (fn-hsig-evidence-tag source))
  :hints (("Goal" :in-theory (enable fn-stxe-profile-supportedp))))

; Schema-0 (legacy record) events stay carrier v1: replay's schema-0 binding
; admits only `fn-hybrid-v1'.  A v2 source is signed on the carried path.
(defun fn-hsig-authorized-article-event
    (sequence txid generation keyring-generation enrolled-snapshot
              msgid content-subject
              article-record principal keys source signatures observed-ml-key
              ed25519-observation ml-dsa-65-observation)
  (declare (xargs :guard t))
  (let ((decoded (fn-record-decode-exact article-record)))
    (if (and (equal enrolled-snapshot
                    (fn-hsig-keyring-snapshot principal keys))
             (fn-hsig-authorize principal keys source signatures
                                observed-ml-key ed25519-observation
                                ml-dsa-65-observation)
             (fn-record-result-okp decoded))
        (let* ((record (fn-record-result-record decoded))
               (detail (fn-hsig-verdict-detail principal keys signatures))
               (verdict (fn-stxe-make sequence txid generation msgid :verified
                                      detail keyring-generation
                                      *fn-hsig-profile-tag*))
               (event (fn-stxa-make sequence txid generation
                                    keyring-generation *fn-hsig-profile-tag*
                                    content-subject article-record
                                    (fn-stxe-encode verdict))))
          (if (and (fn-record-p record)
                   (equal (fn-record-sequence record) sequence)
                   (equal (fn-record-txid record) txid)
                   (equal (fn-record-generation record) generation)
                   (equal (fn-record-msgid record) msgid)
                   (equal (fn-record-payload record) source)
                   (equal (fn-record-string-octets
                           (fn-record-content-subject record))
                          content-subject)
                   (fn-stxa-bindsp event))
              event nil))
      nil)))

(defun fn-hsig-authorized-submission-event
    (sequence txid generation keyring-generation enrolled-snapshot
              msgid source groups obligation-id content-subject
              release-evidence charge principal keys signatures observed-ml-key
              ed25519-observation ml-dsa-65-observation observation)
  "Construct the legacy article record and atomic kind-4 event in ACL2."
  (declare (xargs :guard t))
  (let* ((fields (fn-hsig-authored-source-fields source))
         (stamp (fn-record-stamp-of-observation observation))
         (record
         (fn-record-make sequence txid generation msgid source groups
                         obligation-id content-subject release-evidence charge stamp)))
    (if (and (natp stamp) fields
             (equal msgid (car fields))
             (equal groups (cadr fields))
             (equal charge (fn-charge-for-payload (len source)))
             (fn-record-p record))
        (fn-hsig-authorized-article-event
         sequence txid generation keyring-generation enrolled-snapshot msgid
         (fn-record-string-octets content-subject) (fn-record-encode record)
         principal keys source signatures observed-ml-key
         ed25519-observation ml-dsa-65-observation)
      nil)))

(defun fn-hsig-authored-source-id (source)
  (declare (xargs :guard t))
  (if (and (fn-cbor-octet-listp source)
           (<= (len source) *fn-cbor-max-uint*))
      (fn-id-subject-of-payload source)
    nil))

; Replay must not let a structurally valid record relabel a signed article
; with another Message-ID, group set, or received-content identity.  These
; are the same ACL2 derivations the native metadata bridge calls before
; publication; the source identity above remains separate from this received
; article identity.
(defun fn-hsig-carried-record-metadatap (source received record)
  (declare (xargs :guard t
                  :guard-hints
                  (("Goal" :in-theory
                    (disable fn-hsig-authored-source-fields
                             fn-id-subject-of-payload
                             fn-id-obligation-of)))))
  (if (not (and (fn-record-p record)
                (fn-cbor-octet-listp received)
                (<= (len received) *fn-cbor-max-uint*)))
      nil
    (let* ((fields (fn-hsig-authored-source-fields source))
           (subject (fn-id-subject-of-payload received))
           (msgid (fn-record-msgid record))
           (msgid-octets (fn-record-string-octets msgid))
           (obligation (if (and (fn-cbor-octet-listp msgid-octets)
                                (<= (len msgid-octets) *fn-cbor-max-uint*)
                                (fn-cbor-octet-listp subject)
                                (<= (len subject) *fn-cbor-max-uint*))
                           (fn-id-obligation-of msgid-octets subject)
                         nil)))
      (and fields
           (fn-cbor-octet-listp subject)
           (fn-cbor-octet-listp obligation)
           (equal msgid (car fields))
           (equal (fn-record-groups record) (cadr fields))
           (equal (fn-record-payload record) received)
           (equal (fn-record-charge record)
                  (fn-charge-for-payload (len received)))
           (equal (fn-record-content-subject record)
                  (fn-record-octets-string (fn-id-text subject)))
           (equal (fn-record-obligation-id record)
                  (fn-record-octets-string
                   (fn-id-text obligation)))))))

; Native construction stores the received carrier article as the transport
; payload, while the version-1 parent separately retains the exact signed
; source and its ACL2-derived identity.  The Store content subject and charge
; supplied by the caller are over RECEIVED and are rederived here.
(defun fn-hsig-authorized-carried-submission-event-base
    (sequence txid generation keyring-generation enrolled-snapshot
              msgid source received groups obligation-id content-subject
              release-evidence charge principal keys signatures observed-ml-key
              ed25519-observation ml-dsa-65-observation observation
              projection-ok)
  (declare (xargs :guard t))
  (let* ((fields (fn-hsig-authored-source-fields source))
         (stamp (fn-record-stamp-of-observation observation))
         (record (fn-record-make sequence txid generation msgid received groups
                                 obligation-id content-subject release-evidence
                                 charge stamp))
         (source-id (fn-hsig-authored-source-id source)))
    (if (and (natp stamp) fields source-id projection-ok
             (equal msgid (car fields))
             (equal groups (cadr fields))
             (equal charge (fn-charge-for-payload (len received)))
             (fn-hsig-carried-record-metadatap source received record)
             (equal enrolled-snapshot
                    (fn-hsig-keyring-snapshot principal keys))
             (fn-hsig-authorize-at (fn-hsig-source-version source)
                                   principal keys source signatures
                                   observed-ml-key ed25519-observation
                                   ml-dsa-65-observation))
        (let* ((verdict (fn-stxe-make sequence txid generation msgid :verified
                                      principal keyring-generation
                                      (fn-hsig-evidence-tag source)))
               (event
                (fn-stxa-make-carried sequence txid generation
                                      keyring-generation
                                      (fn-hsig-evidence-tag source)
                                      (fn-record-string-octets content-subject)
                                      (fn-record-encode record)
                                      (fn-stxe-encode verdict)
                                      source source-id)))
          (if (fn-stxa-bindsp event) event nil))
      nil)))

; Historical constructor retained for old pathless schema-1 records and the
; existing exact-carrier test fixtures.  Recovery validates either profile by
; decoding the stored carrier and authored source; it never re-renders bytes.
(defun fn-hsig-authorized-carried-submission-event
    (sequence txid generation keyring-generation enrolled-snapshot
              msgid source received groups obligation-id content-subject
              release-evidence charge principal keys signatures observed-ml-key
              ed25519-observation ml-dsa-65-observation observation)
  (declare (xargs :guard t))
  (fn-hsig-authorized-carried-submission-event-base
   sequence txid generation keyring-generation enrolled-snapshot
   msgid source received groups obligation-id content-subject
   release-evidence charge principal keys signatures observed-ml-key
   ed25519-observation ml-dsa-65-observation observation
   (equal received
          (fn-hc-render-at-most *fn-article-max-octets*
                                source principal keys signatures))))

; Publication and recovery use the exact durable snapshot, not merely its
; generation number.  The construction-time authorization above also requires
; this same canonical snapshot, closing a valid-signature/wrong-enrollment
; substitution.
(defun fn-hsig-article-event-snapshot-bindsp-v0 (event snapshot)
  (declare (xargs :guard t))
  (and (fn-stxa-p event)
       (equal (fn-stxa-authored-source event) :legacy)
       (fn-stxk-p snapshot)
       (equal (fn-stxa-keyring-generation event)
              (fn-stxk-keyring-generation snapshot))
       (equal (fn-stxa-profile event) *fn-hsig-profile-tag*)
       (equal (fn-stxk-profile snapshot) *fn-hsig-profile-tag*)
       (let ((key-items (fn-stmt-decode-items 5 (fn-stxk-snapshot snapshot)))
             (verdict (fn-stxe-decode-exact (fn-stxa-verdict-event event))))
         (and (fn-stmt-okp key-items)
              (fn-stmt-okp verdict)
              (let* ((items (fn-stmt-value key-items))
                     (detail-items
                      (fn-stmt-decode-items
                       9 (fn-stxe-detail (fn-stmt-value verdict)))))
                (and (equal (fn-stxk-snapshot snapshot)
                            (fn-stxe-encode-items items))
                     (true-listp items) (equal (len items) 5)
                     (fn-stmt-bytes-item-p (nth 0 items))
                     (fn-hsig-exact-octets-p (cdr (nth 0 items)) 32)
                     (fn-stmt-uint-item-p (nth 1 items))
                     (equal (cdr (nth 1 items)) *fn-hsig-ed25519-algorithm*)
                     (fn-stmt-bytes-item-p (nth 2 items))
                     (fn-hsig-exact-octets-p
                      (cdr (nth 2 items)) *fn-hsig-ed25519-public-key-octets*)
                     (fn-stmt-uint-item-p (nth 3 items))
                     (equal (cdr (nth 3 items)) *fn-hsig-ml-dsa-65-algorithm*)
                     (fn-stmt-bytes-item-p (nth 4 items))
                     (fn-hsig-exact-octets-p
                      (cdr (nth 4 items)) *fn-hsig-ml-dsa-65-public-key-octets*)
                     (fn-stmt-okp detail-items)
                     (let ((details (fn-stmt-value detail-items)))
                       (and (equal (fn-stxe-detail (fn-stmt-value verdict))
                                   (fn-stxe-encode-items details))
                            (true-listp details) (equal (len details) 9)
                            (equal items (take 5 details))
                            (fn-stmt-uint-item-p (nth 5 details))
                            (equal (cdr (nth 5 details))
                                   *fn-hsig-ed25519-algorithm*)
                            (fn-stmt-bytes-item-p (nth 6 details))
                            (fn-hsig-exact-octets-p
                             (cdr (nth 6 details))
                             *fn-hsig-ed25519-signature-octets*)
                            (fn-stmt-uint-item-p (nth 7 details))
                            (equal (cdr (nth 7 details))
                                   *fn-hsig-ml-dsa-65-algorithm*)
                            (fn-stmt-bytes-item-p (nth 8 details))
                            (fn-hsig-exact-octets-p
                             (cdr (nth 8 details))
                             *fn-hsig-ml-dsa-65-signature-octets*)))))))))

(defun fn-hsig-article-event-snapshot-bindsp-v1 (event snapshot)
  (declare (xargs :guard t))
  (if (not (and (fn-stxa-p event)
                (fn-stxk-p snapshot)
                (equal (fn-stxa-schema event) *fn-stxa-carried-version*)
                (equal (fn-stxa-keyring-generation event)
                       (fn-stxk-keyring-generation snapshot))
                (equal (fn-stxa-profile event)
                       (fn-hsig-evidence-tag (fn-stxa-authored-source event)))
                (equal (fn-stxk-profile snapshot) *fn-hsig-profile-tag*)))
      nil
    (let* ((enrolled (fn-hsig-keyring-snapshot-value snapshot))
           (article (fn-record-decode-exact (fn-stxa-article-record event)))
           (verdict (fn-stxe-decode-exact (fn-stxa-verdict-event event)))
           (received (and (fn-record-result-okp article)
                          (fn-record-payload (fn-record-result-record article))))
           (plan (fn-hc-received-plan received)))
      (and (fn-stxa-bindsp event)
           (fn-record-result-okp article)
           (fn-hsig-carried-record-metadatap
            (fn-stxa-authored-source event) received
            (fn-record-result-record article))
           (true-listp enrolled) (equal (len enrolled) 2)
           (fn-hc-okp plan)
           (true-listp (fn-hc-value plan))
           (equal (len (fn-hc-value plan)) 2)
           (let ((carrier (cadr (fn-hc-value plan))))
             (and (true-listp carrier) (equal (len carrier) 3)
                  (equal (car (fn-hc-value plan))
                         (fn-stxa-authored-source event))
                  (equal (fn-stxa-authored-id event)
                         (fn-hsig-authored-source-id
                          (fn-stxa-authored-source event)))
                  (equal (first carrier) (first enrolled))
                  (equal (second carrier) (second enrolled))
                  (fn-hsig-signatures-p (third carrier))
                  (fn-stmt-okp verdict)
                  (equal (fn-stxe-token (fn-stmt-value verdict)) :verified)
                  (equal (fn-stxe-detail (fn-stmt-value verdict))
                         (first enrolled))))))))

(defun fn-hsig-article-event-snapshot-bindsp (event snapshot)
  (declare (xargs :guard t))
  (if (equal (fn-stxa-schema event) *fn-stxa-carried-version*)
      (fn-hsig-article-event-snapshot-bindsp-v1 event snapshot)
    (fn-hsig-article-event-snapshot-bindsp-v0 event snapshot)))

;; D23 (planning/decisions.md, 2026-09-24): a composite a node stores for a
;; neighbour whose boundary allowlists the author, when this node holds no
;; enrollment of the author.  It binds the article record, the authored source
;; and the carrier exactly as schema 1 does, names the carrier's principal in
;; its verdict, and carries the token :carried at keyring generation 0, which
;; no enrollment ever has (fn-hl-next-generationp starts at 1).  No signature
;; is checked here and none is claimed: replay admits it without a snapshot
;; (books/replay.lisp fn-replay-identity-step) and the reader renders it
;; `carried', never `verified' (books/stx-verify.lisp fn-stx-verified-item).
(defun fn-hsig-article-event-carried-bindsp (event)
  (declare (xargs :guard t))
  (if (not (and (fn-stxa-p event)
                (equal (fn-stxa-schema event) *fn-stxa-carried-version*)
                (equal (fn-stxa-keyring-generation event) 0)
                (equal (fn-stxa-profile event)
                       (fn-hsig-evidence-tag (fn-stxa-authored-source event)))))
      nil
    (let* ((article (fn-record-decode-exact (fn-stxa-article-record event)))
           (verdict (fn-stxe-decode-exact (fn-stxa-verdict-event event)))
           (received (and (fn-record-result-okp article)
                          (fn-record-payload (fn-record-result-record article))))
           (plan (fn-hc-received-plan received)))
      (and (fn-stxa-bindsp event)
           (fn-record-result-okp article)
           (fn-hsig-carried-record-metadatap
            (fn-stxa-authored-source event) received
            (fn-record-result-record article))
           (fn-hc-okp plan)
           (true-listp (fn-hc-value plan))
           (equal (len (fn-hc-value plan)) 2)
           (let ((carrier (cadr (fn-hc-value plan))))
             (and (true-listp carrier) (equal (len carrier) 3)
                  (equal (car (fn-hc-value plan))
                         (fn-stxa-authored-source event))
                  (equal (fn-stxa-authored-id event)
                         (fn-hsig-authored-source-id
                          (fn-stxa-authored-source event)))
                  (fn-hsig-exact-octets-p (first carrier) 32)
                  (fn-stmt-okp verdict)
                  (equal (fn-stxe-token (fn-stmt-value verdict)) :carried)
                  (equal (fn-stxe-detail (fn-stmt-value verdict))
                         (first carrier))))))))

(defthm fn-hsig-article-event-carried-bindsp-facts
  (implies (fn-hsig-article-event-carried-bindsp event)
           (and (fn-stxa-p event)
                (fn-stxa-bindsp event)
                (equal (fn-stxa-keyring-generation event) 0)
                (fn-stmt-okp (fn-stxe-decode-exact (fn-stxa-verdict-event event)))
                (equal (fn-stxe-token
                        (fn-stmt-value
                         (fn-stxe-decode-exact (fn-stxa-verdict-event event))))
                       :carried)))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (e/d (fn-hsig-article-event-carried-bindsp)
                                  (fn-stxa-bindsp fn-stxa-p
                                   fn-stxe-decode-exact
                                   fn-hc-received-plan
                                   fn-hsig-carried-record-metadatap
                                   fn-hsig-authored-source-id)))))

(in-theory (disable (:d fn-hsig-keyring-snapshot)
                    (:d fn-hsig-evidence-tag)
                    (:d fn-hsig-octet-fields-to-strings)
                    (:d fn-hsig-authored-source-fields)
                    (:d fn-hsig-keyring-event)
                    (:d fn-hsig-keyring-snapshot-value)
                    (:d fn-hsig-verdict-detail)
                    (:d fn-hsig-authorized-article-event)
                    (:d fn-hsig-authorized-submission-event)
                    (:d fn-hsig-authored-source-id)
                    (:d fn-hsig-carried-record-metadatap)
                    (:d fn-hsig-authorized-carried-submission-event-base)
                    (:d fn-hsig-authorized-carried-submission-event)
                    (:d fn-hsig-article-event-snapshot-bindsp-v0)
                    (:d fn-hsig-article-event-snapshot-bindsp-v1)
                    (:d fn-hsig-article-event-snapshot-bindsp)
                    (:d fn-hsig-article-event-carried-bindsp)))
