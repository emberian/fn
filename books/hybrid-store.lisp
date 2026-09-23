; ACL2-owned durable composition for the selected hybrid signature profile.

(in-package "ACL2")
(include-book "hybrid-signature")
(include-book "stx-accept-records")
(include-book "injection")
(include-book "identity")
(include-book "records-stamp")
(include-book "hybrid-carrier")

(defun fn-hsig-octet-fields-to-strings (fields)
  (declare (xargs :guard t))
  (if (consp fields)
      (cons (fn-record-octets-string (car fields))
            (fn-hsig-octet-fields-to-strings (cdr fields)))
    nil))

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
                    (fn-hsig-octet-fields-to-strings
                     (fn-inj-nth 2 check))))))))))

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

; Native construction stores the received carrier article as the transport
; payload, while the version-1 parent separately retains the exact signed
; source and its ACL2-derived identity.  The Store content subject and charge
; supplied by the caller are over RECEIVED; Store prepare rechecks them.
(defun fn-hsig-authorized-carried-submission-event
    (sequence txid generation keyring-generation enrolled-snapshot
              msgid source received groups obligation-id content-subject
              release-evidence charge principal keys signatures observed-ml-key
              ed25519-observation ml-dsa-65-observation observation)
  (declare (xargs :guard t))
  (let* ((fields (fn-hsig-authored-source-fields source))
         (stamp (fn-record-stamp-of-observation observation))
         (record (fn-record-make sequence txid generation msgid received groups
                                 obligation-id content-subject release-evidence
                                 charge stamp))
         (source-id (fn-hsig-authored-source-id source)))
    (if (and (natp stamp) fields source-id
             (equal received
                    (fn-hc-render-at-most *fn-article-max-octets*
                                          source principal keys signatures))
             (equal msgid (car fields))
             (equal groups (cadr fields))
             (equal charge (fn-charge-for-payload (len received)))
             (fn-record-p record)
             (equal enrolled-snapshot
                    (fn-hsig-keyring-snapshot principal keys))
             (fn-hsig-authorize principal keys source signatures
                                observed-ml-key ed25519-observation
                                ml-dsa-65-observation))
        (let* ((verdict (fn-stxe-make sequence txid generation msgid :verified
                                      principal keyring-generation
                                      *fn-hsig-profile-tag*))
               (event
                (fn-stxa-make-carried sequence txid generation
                                      keyring-generation *fn-hsig-profile-tag*
                                      (fn-record-string-octets content-subject)
                                      (fn-record-encode record)
                                      (fn-stxe-encode verdict)
                                      source source-id)))
          (if (fn-stxa-bindsp event) event nil))
      nil)))

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
                (equal (fn-stxa-profile event) *fn-hsig-profile-tag*)
                (equal (fn-stxk-profile snapshot) *fn-hsig-profile-tag*)))
      nil
    (let* ((enrolled (fn-hsig-keyring-snapshot-value snapshot))
           (article (fn-record-decode-exact (fn-stxa-article-record event)))
           (verdict (fn-stxe-decode-exact (fn-stxa-verdict-event event)))
           (received (and (fn-record-result-okp article)
                          (fn-record-payload (fn-record-result-record article))))
           (plan (fn-hc-received-plan received)))
      (and (fn-stxa-bindsp event)
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

(in-theory (disable (:d fn-hsig-keyring-snapshot)
                    (:d fn-hsig-octet-fields-to-strings)
                    (:d fn-hsig-authored-source-fields)
                    (:d fn-hsig-keyring-event)
                    (:d fn-hsig-keyring-snapshot-value)
                    (:d fn-hsig-verdict-detail)
                    (:d fn-hsig-authorized-article-event)
                    (:d fn-hsig-authorized-submission-event)
                    (:d fn-hsig-authored-source-id)
                    (:d fn-hsig-authorized-carried-submission-event)
                    (:d fn-hsig-article-event-snapshot-bindsp-v0)
                    (:d fn-hsig-article-event-snapshot-bindsp-v1)
                    (:d fn-hsig-article-event-snapshot-bindsp)))
