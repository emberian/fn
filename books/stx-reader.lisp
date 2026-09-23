; Historical Store verdicts at the NNTP reader boundary.  The verdict list is
; pinned with the accepted archive; no current keyring enters this projection.
(in-package "ACL2")
(include-book "stx-verify")

(defun fn-stx-reader-lookup (msgid verdicts)
  (declare (xargs :guard t))
  (if (consp verdicts)
      (if (and (consp (car verdicts))
               (equal msgid (car (car verdicts))))
          (cdr (car verdicts))
        (fn-stx-reader-lookup msgid (cdr verdicts)))
    nil))

(defconst *fn-stx-token-legacy* '(108 101 103 97 99 121))
(defconst *fn-stx-token-no-record*
  '(110 111 45 114 101 99 111 114 100))

; Schema 1 writes exactly the 32-octet principal id as verified detail.
; Earlier Store records can contain a much larger key/signature blob.  Keep
; their historical :verified token, but never present that blob as a principal.
(defun fn-stx-reader-item (verdict)
  (declare (xargs :guard t))
  (let ((token (fn-stx-verdict-token verdict))
        (detail (fn-stx-verdict-detail verdict))
        (generation (fn-stx-verdict-generation verdict)))
    (cond ((not verdict)
           (append *fn-stx-token-absent*
                   (cons 32 *fn-stx-token-no-record*)))
          ((and (equal token :verified)
                (fn-cbor-octet-listp detail)
                (equal (len detail) 32))
           (fn-stx-verified-item verdict))
          ((equal token :verified)
           (append *fn-stx-token-verified*
                   (cons 32 (append *fn-stx-token-legacy*
                                    (fn-stx-keyring-suffix generation)))))
          (t (fn-stx-verified-item verdict)))))

(defun fn-stx-reader-verdict (msgid verdicts)
  (declare (xargs :guard t))
  (fn-stx-reader-item (fn-stx-reader-lookup msgid verdicts)))

(defthm fn-stx-reader-item-is-printable
  (fn-stx-printablep (fn-stx-reader-item verdict))
  :hints (("Goal" :in-theory (e/d (fn-stx-printablep)
                                  (fn-stx-verified-item
                                   fn-stx-keyring-suffix))
           :use ((:instance fn-stx-keyring-suffix-is-printable
                            (generation (fn-stx-verdict-generation verdict)))))))

(defthm fn-stx-reader-verdict-is-the-recorded-verdict
  (equal (fn-stx-reader-verdict msgid verdicts)
         (fn-stx-reader-item (fn-stx-reader-lookup msgid verdicts))))

(defthm fn-stx-reader-lookup-of-new-verdict
  (equal (fn-stx-reader-lookup msgid (cons (cons msgid verdict) old))
         verdict))

(defthm fn-stx-reader-lookup-ignores-other-message
  (implies (not (equal msgid other))
           (equal (fn-stx-reader-lookup msgid
                                        (cons (cons other verdict) old))
                  (fn-stx-reader-lookup msgid old))))
