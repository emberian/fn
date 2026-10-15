; Derived constructor support; local algebra does not escape this book.
(in-package "ACL2")
(include-book "catalog-columns-table-served-frames")

(local (defthm fn-lbrbf-count-natural
 (natp (fn-lbc-count fn-lbc)) :rule-classes :type-prescription
 :hints (("Goal" :in-theory (union-theories (theory 'ground-zero)
 '(fn-lbc-count fn-lbc-row-store fn-lbc-rowwords-count-is-len))))))

(defthm fn-lb-columns-directory-alignedp-of-rebuild-rows
 (implies (fn-lb-columns-directory-alignedp fn-lbc)
 (fn-lb-columns-directory-alignedp (fn-lbc-rebuild-rows rows log fn-lbc)))
 :hints (("Goal" :induct (fn-lbc-rebuild-rows rows log fn-lbc)
 :in-theory (union-theories (theory 'minimal-theory)
 '(fn-lbc-rebuild-rows fn-lb-columns-directory-alignedp-of-append-row
 fn-lb-columns-directory-alignedp-of-number-put-row)))))

(defthm fn-lb-column-row-pointerp-of-rebuild-rows-old
 (implies (and (natp i) (< i (fn-lbc-count fn-lbc)) (fn-lb-columns-directory-alignedp fn-lbc)
 (fn-lb-column-row-pointerp i fn-lbc))
 (fn-lb-column-row-pointerp i (fn-lbc-rebuild-rows rows log fn-lbc)))
 :hints (("Goal" :induct (fn-lbc-rebuild-rows rows log fn-lbc)
 :in-theory (union-theories (theory 'ground-zero)
 '(fn-lbc-rebuild-rows fn-lb-column-row-pointerp-of-append-row-old
 fn-lb-column-row-pointerp-of-number-put-row fn-lb-columns-directory-alignedp-of-append-row
 fn-lb-columns-directory-alignedp-of-number-put-row fn-lbc-count-of-append-row fn-lbc-count-of-number-put-row
 (:type-prescription fn-lbrbf-count-natural))))))

(defthm fn-lbc-row-corr-of-rebuild-rows-old
 (implies (and (natp i) (< i (fn-lbc-count fn-lbc))
 (fn-lb-columns-directory-alignedp fn-lbc) (fn-lb-columns-pool-layoutp fn-lbc)
 (fn-lb-column-row-pointerp i fn-lbc))
 (equal (fn-lbc-row-corr i old-row pm (fn-lbc-rebuild-rows rows log fn-lbc) log)
        (fn-lbc-row-corr i old-row pm fn-lbc log)))
 :hints (("Goal" :induct (fn-lbc-rebuild-rows rows log fn-lbc)
 :in-theory (union-theories (theory 'ground-zero)
 '(fn-lbc-rebuild-rows fn-lbc-row-corr-of-append-row-old fn-lbc-row-corr-of-number-put-row
 fn-lb-column-row-pointerp-of-append-row-old fn-lb-column-row-pointerp-of-number-put-row
 fn-lb-columns-directory-alignedp-of-append-row fn-lb-columns-directory-alignedp-of-number-put-row
 fn-lb-columns-pool-layoutp-of-append-row fn-lb-columns-pool-layoutp-of-number-put-row
 fn-lbc-count-of-append-row fn-lbc-count-of-number-put-row (:type-prescription fn-lbrbf-count-natural))))))

(defthm fn-lbc-rows-corr-of-rebuild-rows-old
 (implies (and (natp i) (<= (+ i (len old-rows)) (fn-lbc-count fn-lbc))
 (fn-lb-columns-directory-alignedp fn-lbc) (fn-lb-columns-pool-layoutp fn-lbc)
 (fn-lb-columns-row-pointersp i fn-lbc))
 (equal (fn-lbc-rows-corr i old-rows pm (fn-lbc-rebuild-rows rows log fn-lbc) log)
        (fn-lbc-rows-corr i old-rows pm fn-lbc log)))
 :hints (("Goal" :induct (fn-lbc-rebuild-rows rows log fn-lbc)
 :in-theory (union-theories (theory 'ground-zero)
 '(fn-lbc-rebuild-rows fn-lbc-rows-corr-of-append-row-old fn-lbc-rows-corr-of-number-put-row
 fn-lb-columns-row-pointersp-of-append-row fn-lb-columns-row-pointersp-of-number-put-row
 fn-lb-columns-directory-alignedp-of-append-row fn-lb-columns-directory-alignedp-of-number-put-row
 fn-lb-columns-pool-layoutp-of-append-row fn-lb-columns-pool-layoutp-of-number-put-row
 fn-lbc-count-of-append-row fn-lbc-count-of-number-put-row (:type-prescription fn-lbrbf-count-natural))))))
