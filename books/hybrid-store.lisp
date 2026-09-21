; ACL2-owned durable composition for the selected hybrid signature profile.

(in-package "ACL2")
(include-book "hybrid-signature")
(include-book "stx-accept-records")

; A keyring snapshot is deliberately narrow: one principal and the exact
; ordered public-key set used by the signed-preimage function.  Custody and
; succession policy are outside this representation.
(defun fn-hsig-keyring-snapshot (principal keys)
  (declare (xargs :guard t))
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

; The retained verdict detail contains both detached components in canonical
; algorithm order.  Replay can therefore preserve and independently inspect
; the evidence which produced :verified.
(defun fn-hsig-verdict-detail (signatures)
  (declare (xargs :guard t))
  (if (fn-hsig-signatures-p signatures)
      (fn-stmt-encode-items
       (list (cons :uint *fn-hsig-ed25519-algorithm*)
             (cons :bytes (cdr (car signatures)))
             (cons :uint *fn-hsig-ml-dsa-65-algorithm*)
             (cons :bytes (cdr (car (cdr signatures))))))
    nil))

(defun fn-hsig-authorized-article-event
    (sequence txid generation keyring-generation msgid content-subject
              article-record principal keys source signatures observed-ml-key
              ed25519-observation ml-dsa-65-observation)
  (declare (xargs :guard t))
  (let ((decoded (fn-record-decode-exact article-record)))
    (if (and (fn-hsig-authorize principal keys source signatures
                                observed-ml-key ed25519-observation
                                ml-dsa-65-observation)
             (fn-record-result-okp decoded))
        (let* ((record (fn-record-result-record decoded))
               (detail (fn-hsig-verdict-detail signatures))
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

(in-theory (disable (:d fn-hsig-keyring-snapshot)
                    (:d fn-hsig-keyring-event)
                    (:d fn-hsig-verdict-detail)
                    (:d fn-hsig-authorized-article-event)))
