; Derived constructor support; local algebra does not escape this book.
(in-package "ACL2")
(include-book "catalog-columns-indexed-row-store")

(local (defthm fn-lbnew-nth-of-cons
  (equal (nth i (cons value xs))
         (if (zp i) value (nth (- (nfix i) 1) xs)))
  :hints (("Goal" :in-theory (enable nth)))))

(defthm fn-lbc-handle-of-append-row-new
  (equal (fn-lbc-value (fn-lbc-count fn-lbc) :handle (fn-lbc-append-row row log fn-lbc))
         (fn-record-payload row))
  :hints (("Goal" :do-not '(preprocess) :do-not-induct t
   :in-theory (union-theories (theory 'minimal-theory)
    '(fn-lbc-append-row fn-lbc-value-of-escape-store-put
      fn-lbc-word-of-directory-store-update-by-definition
      fn-lbc-word-handle-of-store-append-at-index fn-lbnew-nth-of-cons
      fn-lbc-row-cell-decodes-handle
      fn-lbc-count-of-append-nov fn-lbc-count-of-append-memberships
      fn-lbc-count-of-msgid-pool-append fn-lbc-count-of-overview-pool-append
      fn-lbc-count-of-append-nov-texts car-cons cdr-cons
      (:executable-counterpart equal) (:executable-counterpart nfix)
      (:executable-counterpart zp) (:executable-counterpart binary-+))))))
