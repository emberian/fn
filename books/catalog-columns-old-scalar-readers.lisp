; Derived constructor support; local algebra does not escape this book.
(in-package "ACL2")
(include-book "catalog-columns-row-pointer-layout")

(defthm fn-lbc-escape-of-append-row-old
 (implies (and (natp i) (< i (fn-lbc-count fn-lbc)) t)
  (equal (fn-lbc-escape i field (fn-lbc-append-row row log fn-lbc))
         (fn-lbc-escape i field fn-lbc)))
 :hints (("Goal" :do-not-induct t :in-theory
  (union-theories (theory 'ground-zero) '(fn-lbc-word-of-append-row-old fn-lbc-directory-field-of-append-row-old fn-lbc-escape-store-get-of-append-row-old fn-lbc-escape fn-lbc-value fn-lbc-directory-value fn-lbc-flag fn-lbc-withdrawn)))))

(defthm fn-lbc-value-of-append-row-old
 (implies (and (natp i) (< i (fn-lbc-count fn-lbc)) t)
  (equal (fn-lbc-value i field (fn-lbc-append-row row log fn-lbc))
         (fn-lbc-value i field fn-lbc)))
 :hints (("Goal" :do-not-induct t :in-theory
  (union-theories (theory 'ground-zero) '(fn-lbc-word-of-append-row-old fn-lbc-directory-field-of-append-row-old fn-lbc-escape-store-get-of-append-row-old fn-lbc-escape fn-lbc-value fn-lbc-directory-value fn-lbc-flag fn-lbc-withdrawn)))))

(defthm fn-lbc-directory-value-of-append-row-old
 (implies (and (natp i) (< i (fn-lbc-count fn-lbc)) (fn-lb-columns-directory-alignedp fn-lbc))
  (equal (fn-lbc-directory-value i field (fn-lbc-append-row row log fn-lbc))
         (fn-lbc-directory-value i field fn-lbc)))
 :hints (("Goal" :do-not-induct t :in-theory
  (union-theories (theory 'ground-zero) '(fn-lbc-word-of-append-row-old fn-lbc-directory-field-of-append-row-old fn-lbc-escape-store-get-of-append-row-old fn-lbc-escape fn-lbc-value fn-lbc-directory-value fn-lbc-flag fn-lbc-withdrawn)))))

(defthm fn-lbc-flag-of-append-row-old
 (implies (and (natp i) (< i (fn-lbc-count fn-lbc)) t)
  (equal (fn-lbc-flag i bit (fn-lbc-append-row row log fn-lbc))
         (fn-lbc-flag i bit fn-lbc)))
 :hints (("Goal" :do-not-induct t :in-theory
  (union-theories (theory 'ground-zero) '(fn-lbc-word-of-append-row-old fn-lbc-directory-field-of-append-row-old fn-lbc-escape-store-get-of-append-row-old fn-lbc-escape fn-lbc-value fn-lbc-directory-value fn-lbc-flag fn-lbc-withdrawn)))))

(defthm fn-lbc-withdrawn-of-append-row-old
 (implies (and (natp i) (< i (fn-lbc-count fn-lbc)) t)
  (equal (fn-lbc-withdrawn i (fn-lbc-append-row row log fn-lbc))
         (fn-lbc-withdrawn i fn-lbc)))
 :hints (("Goal" :do-not-induct t :in-theory
  (union-theories (theory 'ground-zero) '(fn-lbc-word-of-append-row-old fn-lbc-directory-field-of-append-row-old fn-lbc-escape-store-get-of-append-row-old fn-lbc-escape fn-lbc-value fn-lbc-directory-value fn-lbc-flag fn-lbc-withdrawn)))))

(defthm fn-lbc-xref-shift-prefix-of-append-row-old
 (implies (and (natp i) (< i (fn-lbc-count fn-lbc)) t)
  (equal (fn-lbc-xref-shift-prefix i (fn-lbc-append-row row log fn-lbc))
         (fn-lbc-xref-shift-prefix i fn-lbc)))
 :hints (("Goal" :do-not-induct t :in-theory
  (union-theories (theory 'ground-zero) '(fn-lbc-word-of-append-row-old fn-lbc-directory-field-of-append-row-old fn-lbc-escape-store-get-of-append-row-old fn-lbc-escape fn-lbc-value fn-lbc-directory-value fn-lbc-flag fn-lbc-withdrawn fn-lbc-xref-shift-prefix true-list-fix)))))
