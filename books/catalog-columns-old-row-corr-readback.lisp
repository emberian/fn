; Derived constructor support; local algebra does not escape this book.
(in-package "ACL2")
(include-book "catalog-columns-slot-rows-corr-frames")

(defthm fn-lbc-loc0-of-append-row-old
 (implies (and (natp i) (< i (fn-lbc-count fn-lbc)))
  (equal (fn-lbc-loc0 i (fn-lbc-append-row row log fn-lbc)) (fn-lbc-loc0 i fn-lbc)))
 :hints (("Goal" :do-not-induct t :in-theory
  (union-theories (theory 'ground-zero)
   '(fn-lbc-loc0-is-word-by-definition fn-lbc-count-of-append-row fn-lbc-word-of-append-row-old
     (:type-prescription fn-lbc-count))))))

(defthm fn-lbc-loc1-of-append-row-old
 (implies (and (natp i) (< i (fn-lbc-count fn-lbc)))
  (equal (fn-lbc-loc1 i (fn-lbc-append-row row log fn-lbc)) (fn-lbc-loc1 i fn-lbc)))
 :hints (("Goal" :do-not-induct t :in-theory
  (union-theories (theory 'ground-zero)
   '(fn-lbc-loc1-is-word-by-definition fn-lbc-count-of-append-row fn-lbc-word-of-append-row-old
     (:type-prescription fn-lbc-count))))))

(defthm fn-lbc-home-entry-of-append-row-old
 (implies (and (natp i) (< i (fn-lbc-count fn-lbc)))
  (equal (fn-lbc-home-entry i (fn-lbc-append-row row log fn-lbc) log) (fn-lbc-home-entry i fn-lbc log)))
 :hints (("Goal" :do-not-induct t :in-theory
  (union-theories (theory 'minimal-theory)
   '(fn-lbc-home-entry fn-lbc-loc0-of-append-row-old fn-lbc-loc1-of-append-row-old)))))

(defthm fn-lbc-row-corr-of-append-row-old
 (implies (and (natp i) (< i (fn-lbc-count fn-lbc))
               (fn-lb-columns-directory-alignedp fn-lbc) (fn-lb-columns-pool-layoutp fn-lbc)
               (fn-lb-column-row-pointerp i fn-lbc))
  (equal (fn-lbc-row-corr i old-row pm (fn-lbc-append-row row log fn-lbc) log)
         (fn-lbc-row-corr i old-row pm fn-lbc log)))
 :hints (("Goal" :do-not-induct t :in-theory
  (union-theories (theory 'minimal-theory)
   '(fn-lbc-row-corr fn-lbc-home-entry-of-append-row-old
     fn-lbc-loc0-of-append-row-old fn-lbc-loc1-of-append-row-old
     fn-lbc-served-row-of-append-row-old fn-lbc-value-of-append-row-old
     fn-lbc-word-of-append-row-old fn-lbc-flag-of-append-row-old
     fn-lbc-xref-shift-prefix-of-append-row-old fn-lbc-directory-value-of-append-row-old
     fn-lbc-render-nov-of-append-row-old)))))
