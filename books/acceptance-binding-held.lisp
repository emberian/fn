; Fixed-size binding gate and paired projection of one selected accepted row.
; The indexed first-acceptance locator and its operational carry are above
; this book.  This book never searches history, reads a payload, or decides
; authority from visibility, signature presence, or a native profile claim.
(in-package "ACL2")
(include-book "held-record")

(defun fn-ab-held-projections (held)
  (declare (xargs :guard t))
  (mv (fn-make-article (fn-record-msgid held)
                       (fn-record-payload held)
                       (fn-record-groups held)
                       (fn-held-numbers held) t (fn-record-stamp held))
      (fn-held-binding held)))

(defun fn-ab-held-binding-action (msgid incoming held)
  (declare (xargs :guard t))
  (cond ((not (fn-ab-p incoming)) :invalid-binding)
        ((null held) :absent)
        ((or (not (equal msgid (fn-record-msgid held)))
             (not (fn-ab-p (fn-held-binding held))))
         :recovery-required)
        ((equal incoming (fn-held-binding held)) :same-binding)
        (t :conflict)))

; The byte/group comparison may proceed only after this gate, and uses
; the article returned from the SAME held row by fn-ab-held-projections.
; These helpers do not assert that a row was selected by a valid index.
(defthm fn-ab-held-binding-action-same-unfolds
  (equal (equal (fn-ab-held-binding-action msgid incoming held) :same-binding)
         (and (fn-ab-p incoming)
              held
              (equal msgid (fn-record-msgid held))
              (fn-ab-p (fn-held-binding held))
              (equal incoming (fn-held-binding held))))
  :hints (("Goal" :in-theory (e/d (fn-ab-held-binding-action)
                                   (fn-ab-p fn-record-msgid fn-held-binding)))))

(defthm fn-ab-held-projections-by-definition
  (and (equal (mv-nth 0 (fn-ab-held-projections held))
              (fn-make-article (fn-record-msgid held)
                               (fn-record-payload held)
                               (fn-record-groups held)
                               (fn-held-numbers held) t (fn-record-stamp held)))
       (equal (mv-nth 1 (fn-ab-held-projections held))
              (fn-held-binding held)))
  :hints (("Goal" :in-theory (enable fn-ab-held-projections))))

(in-theory (disable fn-ab-held-projections fn-ab-held-binding-action))
