; Availability completion at recovery/reclaim load, never a served read.
(in-package "ACL2")
(include-book "catalog-availability")
(include-book "catalog-record")
(include-book "article-arena-reads")

(defun fn-cat-complete-row-facts (h fn-arena)
  (declare (xargs :stobjs fn-arena :guard (fn-held-p h)
                  :guard-hints (("Goal" :in-theory
                    (e/d (fn-nntp-payload-bytes fn-arena-p-is-payload-listp
                          fn-arena-count-is-len fn-arena-payload-is-nth
                          fn-cbor-octet-listp-implies-true-listp
                          fn-arn-payload-listp-nth)
                         (fn-held-p))))))
  (if (fn-cat-row-facts-decidedp h) h
    (fn-held-with-facts h
      (fn-held-facts-of (fn-nntp-payload-bytes (fn-record-payload h) fn-arena)))))

(defthm fn-cat-complete-row-facts-decided
  (fn-cat-row-facts-decidedp (fn-cat-complete-row-facts h fn-arena))
  :hints (("Goal" :in-theory
           (e/d (fn-cat-complete-row-facts fn-cat-row-facts-decidedp)
                (fn-held-with-facts fn-held-facts-of fn-hf-nov fn-hnov-p fn-hnov-of)))))

(defthm fn-cat-complete-row-facts-keeps-held-p
  (implies (fn-held-p h)
           (fn-held-p (fn-cat-complete-row-facts h fn-arena)))
  :hints (("Goal" :in-theory
           (e/d (fn-cat-complete-row-facts)
                (fn-held-with-facts fn-held-p fn-held-facts-of)))))

(defthm fn-cat-complete-row-facts-keeps-wire
  (equal (fn-held-wire (fn-cat-complete-row-facts h fn-arena) bytes)
         (fn-held-wire h bytes))
  :hints (("Goal" :in-theory
           (e/d (fn-cat-complete-row-facts fn-held-wire)
                (fn-held-with-facts fn-held-facts-of)))))

(defthm fn-cat-complete-row-facts-keeps-read-identity
  (let ((r (fn-cat-complete-row-facts h fn-arena)))
    (and (equal (fn-record-msgid r) (fn-record-msgid h))
         (equal (fn-record-payload r) (fn-record-payload h))
         (equal (fn-record-groups r) (fn-record-groups h))
         (equal (fn-held-numbers r) (fn-held-numbers h))
         (equal (fn-held-context r) (fn-held-context h))
         (equal (fn-held-withdrawn r) (fn-held-withdrawn h))))
  :hints (("Goal" :in-theory
           (e/d (fn-cat-complete-row-facts)
                (fn-held-with-facts fn-held-facts-of)))))

(in-theory (disable fn-cat-complete-row-facts))
