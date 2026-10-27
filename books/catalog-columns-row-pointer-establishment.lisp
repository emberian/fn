; Derived constructor support; local algebra does not escape this book.
(in-package "ACL2")
(include-book "catalog-columns-row-pointer-properties")

(local (defthm fn-lbppe-count-natural
 (natp (fn-lbc-count fn-lbc)) :rule-classes :type-prescription
 :hints (("Goal" :in-theory (union-theories (theory 'ground-zero)
  '(fn-lbc-count fn-lbc-row-store fn-lbc-rowwords-count-is-len))))))

(local (defthm fn-lbppe-new-last-row
 (implies (fn-lb-columns-directory-alignedp fn-lbc)
  (fn-lb-columns-row-pointersp (fn-lbc-count fn-lbc) (fn-lbc-append-row row log fn-lbc)))
 :hints (("Goal" :do-not-induct t
  :expand ((fn-lb-columns-row-pointersp (fn-lbc-count fn-lbc) (fn-lbc-append-row row log fn-lbc))
           (fn-lb-columns-row-pointersp (+ 1 (fn-lbc-count fn-lbc)) (fn-lbc-append-row row log fn-lbc)))
  :in-theory (union-theories (theory 'ground-zero)
   '(fn-lbc-count-of-append-row fn-lb-column-row-pointerp-of-append-row-new
     (:type-prescription fn-lbppe-count-natural)))))))

(defthm fn-lb-columns-row-pointersp-of-append-row
 (implies (and (natp i) (<= i (fn-lbc-count fn-lbc))
               (fn-lb-columns-directory-alignedp fn-lbc) (fn-lb-columns-row-pointersp i fn-lbc))
  (fn-lb-columns-row-pointersp i (fn-lbc-append-row row log fn-lbc)))
 :hints (("Goal" :induct (fn-lb-columns-row-pointersp i fn-lbc)
  :in-theory (set-difference-theories (union-theories (theory 'ground-zero)
   '(fn-lb-columns-row-pointersp fn-lbppe-new-last-row fn-lbc-count-of-append-row
     fn-lb-column-row-pointerp-of-append-row-old fn-lb-column-row-pointerp-of-append-row-new
     (:type-prescription fn-lbppe-count-natural))) '((tau-system))))))
