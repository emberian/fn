; Option 2': available news is distinct from retained acceptance evidence.
; Reuse the overview tombstone fact derived at intern.  Missing facts are
; undecided and unavailable; the recovery/reclaim loader completes them.
(in-package "ACL2")
(include-book "held-record")

(defun fn-cat-row-facts-decidedp (h)
  (declare (xargs :guard t))
  (fn-hnov-p (fn-hf-nov (fn-held-facts h))))

(defun fn-cat-row-availablep (h)
  (declare (xargs :guard t))
  (and (fn-cat-row-facts-decidedp h)
       (not (fn-hnov-tomb (fn-hf-nov (fn-held-facts h))))))

(defthm fn-cat-row-availablep-booleanp
  (booleanp (fn-cat-row-availablep h))
  :rule-classes :type-prescription)

(defthm fn-cat-row-availability-of-with-numbers
  (and (equal (fn-cat-row-facts-decidedp (fn-held-with-numbers h numbers))
              (fn-cat-row-facts-decidedp h))
       (equal (fn-cat-row-availablep (fn-held-with-numbers h numbers))
              (fn-cat-row-availablep h))))

(defthm fn-cat-row-availability-of-with-withdrawn
  (and (equal (fn-cat-row-facts-decidedp (fn-held-with-withdrawn h withdrawn))
              (fn-cat-row-facts-decidedp h))
       (equal (fn-cat-row-availablep (fn-held-with-withdrawn h withdrawn))
              (fn-cat-row-availablep h))))

(defthm fn-cat-row-availability-of-with-context
  (and (equal (fn-cat-row-facts-decidedp (fn-held-with-context h context))
              (fn-cat-row-facts-decidedp h))
       (equal (fn-cat-row-availablep (fn-held-with-context h context))
              (fn-cat-row-availablep h))))

; A derived-facts replacement never changes the retained wire identity,
; handle, memberships, context, or withdrawal history.
(defun fn-held-with-facts (h facts)
  (declare (xargs :guard t))
  (fn-held-make (fn-record-sequence h) (fn-record-txid h)
                (fn-record-generation h) (fn-record-msgid h)
                (fn-record-payload h) (fn-record-groups h)
                (fn-record-obligation-id h) (fn-record-content-subject h)
                (fn-record-release-evidence h) (fn-record-charge h)
                (fn-record-stamp h) facts (fn-held-context h)
                (fn-held-numbers h) (fn-held-withdrawn h)))

(defthm fn-held-with-facts-fields
  (let ((r (fn-held-with-facts h facts)))
    (and (equal (fn-record-sequence r) (fn-record-sequence h))
         (equal (fn-record-txid r) (fn-record-txid h))
         (equal (fn-record-generation r) (fn-record-generation h))
         (equal (fn-record-msgid r) (fn-record-msgid h))
         (equal (fn-record-payload r) (fn-record-payload h))
         (equal (fn-record-groups r) (fn-record-groups h))
         (equal (fn-record-obligation-id r) (fn-record-obligation-id h))
         (equal (fn-record-content-subject r) (fn-record-content-subject h))
         (equal (fn-record-release-evidence r) (fn-record-release-evidence h))
         (equal (fn-record-charge r) (fn-record-charge h))
         (equal (fn-record-stamp r) (fn-record-stamp h))
         (equal (fn-held-facts r) facts)
         (equal (fn-held-context r) (fn-held-context h))
         (equal (fn-held-numbers r) (fn-held-numbers h))
         (equal (fn-held-withdrawn r) (fn-held-withdrawn h)))))

(defthm fn-held-p-of-with-facts
  (implies (and (fn-held-p h) (fn-hf-p facts))
           (fn-held-p (fn-held-with-facts h facts)))
  :hints (("Goal" :in-theory (enable fn-held-p fn-held-with-facts
                                    fn-record-internals fn-held-internals))))

(in-theory (disable fn-held-with-facts fn-cat-row-facts-decidedp
                    fn-cat-row-availablep))
