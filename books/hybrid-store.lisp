; ACL2-owned durable composition for the selected hybrid signature profile.

(in-package "ACL2")
(include-book "hybrid-signature")
(include-book "stx-accept-records")

; A keyring snapshot is deliberately narrow: one principal and the exact
; ordered public-key set used by the signed-preimage function.  Custody and
; succession policy are outside this representation.
(defun fn-hsig-keyring-snapshot (principal keys)
  (declare (xargs :guard t
                  :guard-hints
                  (("Goal" :in-theory (enable fn-hsig-exact-octets-p
                                               fn-hsig-keyset-p
                                               fn-stmt-item-listp
                                               fn-cbor-valuep)))))
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

(defun fn-hsig-keyring-snapshot-value (snapshot)
  "Return (principal keys) only for the exact canonical selected snapshot."
  (declare (xargs :guard t))
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
                  (("Goal" :in-theory (enable fn-hsig-exact-octets-p
                                               fn-hsig-keyset-p
                                               fn-hsig-signatures-p
                                               fn-stmt-item-listp
                                               fn-cbor-valuep)))))
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
              ed25519-observation ml-dsa-65-observation)
  "Construct the legacy article record and atomic kind-4 event in ACL2."
  (declare (xargs :guard t))
  (let ((record
         (fn-record-make sequence txid generation msgid source groups
                         obligation-id content-subject release-evidence charge)))
    (if (fn-record-p record)
        (fn-hsig-authorized-article-event
         sequence txid generation keyring-generation enrolled-snapshot msgid
         (fn-record-string-octets content-subject) (fn-record-encode record)
         principal keys source signatures observed-ml-key
         ed25519-observation ml-dsa-65-observation)
      nil)))

; Publication and recovery use the exact durable snapshot, not merely its
; generation number.  The construction-time authorization above also requires
; this same canonical snapshot, closing a valid-signature/wrong-enrollment
; substitution.
(defun fn-hsig-article-event-snapshot-bindsp (event snapshot)
  (declare (xargs :guard t))
  (and (fn-stxa-p event)
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

(in-theory (disable (:d fn-hsig-keyring-snapshot)
                    (:d fn-hsig-keyring-event)
                    (:d fn-hsig-keyring-snapshot-value)
                    (:d fn-hsig-verdict-detail)
                    (:d fn-hsig-authorized-article-event)
                    (:d fn-hsig-authorized-submission-event)
                    (:d fn-hsig-article-event-snapshot-bindsp)))
