; Unchanged binding action over one captured held16 row. No codec ancestry.
(in-package "ACL2")
(include-book "held-record-shape")

(defun fn-ab-held-binding-action (msgid incoming held)
  (declare (xargs :guard t))
  (cond ((not (fn-ab-p incoming)) :invalid-binding)
        ((null held) :absent)
        ((or (not (equal msgid (fn-record-msgid held)))
             (not (fn-ab-p (fn-held-binding held))))
         :recovery-required)
        ((equal incoming (fn-held-binding held)) :same-binding)
        (t :conflict)))

(defthm fn-ab-held-binding-action-same-unfolds
  (equal (equal (fn-ab-held-binding-action msgid incoming held) :same-binding)
         (and (fn-ab-p incoming)
              held
              (equal msgid (fn-record-msgid held))
              (fn-ab-p (fn-held-binding held))
              (equal incoming (fn-held-binding held))))
  :hints (("Goal" :in-theory (e/d (fn-ab-held-binding-action)
                                   (fn-ab-p fn-record-msgid fn-held-binding)))))

(in-theory (disable fn-ab-held-binding-action))
