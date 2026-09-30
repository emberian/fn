; PRF-1089: literal host-rewrite witness and hypothesis-removal tooth.
; Reclamation retains the typed commitment; no digest injectivity theorem.
(in-package "ACL2")
(include-book "../../books/store-reclaim-pack")
(include-book "../../books/crypto-attach")
(include-book "../../books/records-attach")
(include-book "article-subject-tests")

(defconst *ras-msgid* "<relay@article.invalid>")
(defconst *ras-record*
  (fn-record-make 0 0 0 *ras-msgid* *asjt-wire* '("g")
                  "pin" "original-bytes-commitment" "release" 1 100))
(defconst *ras-article*
  (fn-make-article *ras-msgid* 0 '("g") '(("g" . 1)) t 100))
(defconst *ras-ctx*
  (list '(:released-by-all-holders) 100 '(nil nil nil nil) nil
        (list *ras-article*) nil (fn-rclp-article-index (list *ras-article*))))
(defmacro ras-event () '(fn-record-encode *ras-record*))
(defmacro ras-new () '(fn-rclp-event (ras-event) *ras-ctx*))
(defmacro ras-decoded () '(fn-record-result-record (fn-record-decode-exact (ras-new))))
(defmacro ras-tomb () '(fn-record-payload (ras-decoded)))

; The entire antecedent and conclusion, through the actual event rewriter.
(assert-event
 (and (fn-record-p *ras-record*)
      (fn-rclp-rewrites-p (ras-event) *ras-ctx*)
      (equal (fn-rcl-tomb-article-subject
              (fn-record-payload (fn-record-result-record
                                 (fn-record-decode-exact
                                  (fn-rclp-event (ras-event) *ras-ctx*)))))
             (fn-asj-subject
              (fn-record-payload (fn-record-result-record
                                 (fn-record-decode-exact (ras-event))))))))
(assert-event
 (and (fn-rcl-tombstonep (ras-tomb))
      (equal (fn-record-content-subject (ras-decoded)) "original-bytes-commitment")
      (equal (fn-record-msgid (ras-decoded)) *ras-msgid*)
      (equal (fn-rcl-tomb-octets-digest (ras-tomb)) (fn-blake3 *asjt-wire*))
      (equal (fn-rcl-tomb-article-subject (ras-tomb)) (fn-asj-subject *asjt-other*))
      (not (equal (fn-rcl-tomb-article-subject (ras-tomb)) (fn-asj-subject *asjt-body-change*)))
      (equal (fn-rclp-event (ras-new) *ras-ctx*) (ras-new))))

; Only hypothesis removed: a keep-forever context does not rewrite, and the
; untouched article's bytes at the tombstone offset are not its commitment.
(defconst *ras-kept* (cons '(:keep-forever) (cdr *ras-ctx*)))
(assert-event
 (and (not (fn-rclp-rewrites-p (ras-event) *ras-kept*))
      (not (equal (fn-rcl-tomb-article-subject
                   (fn-record-payload (fn-record-result-record
                                      (fn-record-decode-exact
                                       (fn-rclp-event (ras-event) *ras-kept*)))))
                  (fn-asj-subject
                   (fn-record-payload (fn-record-result-record
                                      (fn-record-decode-exact (ras-event)))))))))

; Corrupted-state/format witnesses, not hypothesis-removal witnesses.
; There is exactly one recognizer. An old magic never invokes a reader.
(assert-event
 (and (not (fn-rcl-tombstonep (update-nth 7 49 (ras-tomb))))
      (not (fn-rcl-tombstonep (take 144 (ras-tomb))))
      (not (equal (fn-rcl-tomb-article-subject (update-nth 89 0 (ras-tomb)))
                  (fn-asj-subject *asjt-wire*)))))
