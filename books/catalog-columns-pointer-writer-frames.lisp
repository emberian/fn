; Derived constructor support; local algebra does not escape this book.
(in-package "ACL2")
(include-book "catalog-columns-row-pointer-establishment")

(local (defthm fn-lbpwf-count-natural
 (natp (fn-lbc-count fn-lbc)) :rule-classes :type-prescription
 :hints (("Goal" :in-theory (union-theories (theory 'ground-zero)
  '(fn-lbc-count fn-lbc-row-store fn-lbc-rowwords-count-is-len))))))

(defthm fn-lb-column-row-pointerp-of-number-put-row
 (equal (fn-lb-column-row-pointerp i (fn-lbc-number-put-row numbers j fn-lbc)) (fn-lb-column-row-pointerp i fn-lbc))
 :hints (("Goal" :do-not-induct t :in-theory
  (union-theories (theory 'minimal-theory) '(fn-lb-column-row-pointerp fn-lbc-escape fn-lbc-count-of-number-put-row fn-lbc-word-of-number-put-row fn-lbc-directory-field-of-number-put-row fn-lbc-loc0-of-number-put-row fn-lbc-loc1-of-number-put-row fn-lbc-escape-store-get-of-number-put-row fn-lbc-escape-of-number-put-row fn-lbc-value-of-number-put-row fn-lbc-directory-value-of-number-put-row fn-lbc-flag-of-number-put-row fn-lbc-msgid-pool-count-frame-of-number-put-row fn-lbc-overview-pool-count-frame-of-number-put-row fn-lbc-nov-record-count-frame-of-number-put-row fn-lbc-membership-record-count-frame-of-number-put-row)))))

(defthm fn-lb-columns-row-pointersp-of-number-put-row
 (equal (fn-lb-columns-row-pointersp i (fn-lbc-number-put-row numbers j fn-lbc)) (fn-lb-columns-row-pointersp i fn-lbc))
 :hints (("Goal" :induct (fn-lb-columns-row-pointersp i fn-lbc) :in-theory
  (union-theories (theory 'minimal-theory)
   '(fn-lb-columns-row-pointersp fn-lb-column-row-pointerp-of-number-put-row fn-lbc-count-of-number-put-row)))))

(defthm fn-lb-column-row-pointerp-of-rebuild-summaries
 (equal (fn-lb-column-row-pointerp i (fn-lbc-rebuild-summaries groups rows fn-lbc)) (fn-lb-column-row-pointerp i fn-lbc))
 :hints (("Goal" :do-not-induct t :in-theory
  (union-theories (theory 'minimal-theory) '(fn-lb-column-row-pointerp fn-lbc-escape fn-lbc-count-of-rebuild-summaries fn-lbc-word-of-rebuild-summaries fn-lbc-directory-field-of-rebuild-summaries fn-lbc-loc0-of-rebuild-summaries fn-lbc-loc1-of-rebuild-summaries fn-lbc-escape-store-get-of-rebuild-summaries fn-lbc-escape-of-rebuild-summaries fn-lbc-value-of-rebuild-summaries fn-lbc-directory-value-of-rebuild-summaries fn-lbc-flag-of-rebuild-summaries fn-lbc-msgid-pool-count-frame-of-rebuild-summaries fn-lbc-overview-pool-count-frame-of-rebuild-summaries fn-lbc-nov-record-count-frame-of-rebuild-summaries fn-lbc-membership-record-count-frame-of-rebuild-summaries)))))

(defthm fn-lb-columns-row-pointersp-of-rebuild-summaries
 (equal (fn-lb-columns-row-pointersp i (fn-lbc-rebuild-summaries groups rows fn-lbc)) (fn-lb-columns-row-pointersp i fn-lbc))
 :hints (("Goal" :induct (fn-lb-columns-row-pointersp i fn-lbc) :in-theory
  (union-theories (theory 'minimal-theory)
   '(fn-lb-columns-row-pointersp fn-lb-column-row-pointerp-of-rebuild-summaries fn-lbc-count-of-rebuild-summaries)))))

(defthm fn-lb-column-row-pointerp-of-reserve-slots
 (equal (fn-lb-column-row-pointerp i (fn-lbc-reserve-slots n fn-lbc)) (fn-lb-column-row-pointerp i fn-lbc))
 :hints (("Goal" :do-not-induct t :in-theory
  (union-theories (theory 'minimal-theory) '(fn-lb-column-row-pointerp fn-lbc-escape fn-lbc-count-of-reserve-slots fn-lbc-word-of-reserve-slots fn-lbc-directory-field-of-reserve-slots fn-lbc-loc0-of-reserve-slots fn-lbc-loc1-of-reserve-slots fn-lbc-escape-store-get-of-reserve-slots fn-lbc-escape-of-reserve-slots fn-lbc-value-of-reserve-slots fn-lbc-directory-value-of-reserve-slots fn-lbc-flag-of-reserve-slots fn-lbc-msgid-pool-count-frame-of-reserve-slots fn-lbc-overview-pool-count-frame-of-reserve-slots fn-lbc-nov-record-count-frame-of-reserve-slots fn-lbc-membership-record-count-frame-of-reserve-slots)))))

(defthm fn-lb-columns-row-pointersp-of-reserve-slots
 (equal (fn-lb-columns-row-pointersp i (fn-lbc-reserve-slots n fn-lbc)) (fn-lb-columns-row-pointersp i fn-lbc))
 :hints (("Goal" :induct (fn-lb-columns-row-pointersp i fn-lbc) :in-theory
  (union-theories (theory 'minimal-theory)
   '(fn-lb-columns-row-pointersp fn-lb-column-row-pointerp-of-reserve-slots fn-lbc-count-of-reserve-slots)))))

(defthm fn-lb-columns-directory-alignedp-of-number-put-row
 (equal (fn-lb-columns-directory-alignedp (fn-lbc-number-put-row numbers j fn-lbc)) (fn-lb-columns-directory-alignedp fn-lbc))
 :hints (("Goal" :do-not-induct t :in-theory
  (union-theories (theory 'minimal-theory)
   '(fn-lb-columns-directory-alignedp fn-lbc-count-of-number-put-row fn-lbwf-number-put-row-field
     (:executable-counterpart natp) (:executable-counterpart member-equal) (:executable-counterpart equal))))))

(defthm fn-lb-columns-directory-alignedp-of-rebuild-summaries
 (equal (fn-lb-columns-directory-alignedp (fn-lbc-rebuild-summaries groups rows fn-lbc)) (fn-lb-columns-directory-alignedp fn-lbc))
 :hints (("Goal" :do-not-induct t :in-theory
  (union-theories (theory 'minimal-theory)
   '(fn-lb-columns-directory-alignedp fn-lbc-count-of-rebuild-summaries fn-lbwf-rebuild-summaries-field
     (:executable-counterpart natp) (:executable-counterpart member-equal) (:executable-counterpart equal))))))

(defthm fn-lb-columns-directory-alignedp-of-reserve-slots
 (equal (fn-lb-columns-directory-alignedp (fn-lbc-reserve-slots n fn-lbc)) (fn-lb-columns-directory-alignedp fn-lbc))
 :hints (("Goal" :do-not-induct t :in-theory
  (union-theories (theory 'minimal-theory)
   '(fn-lb-columns-directory-alignedp fn-lbc-count-of-reserve-slots fn-lbwf-reserve-slots-field
     (:executable-counterpart natp) (:executable-counterpart member-equal) (:executable-counterpart equal))))))

(defthm fn-lb-columns-row-pointersp-of-rebuild-rows
 (implies (and (fn-lb-columns-directory-alignedp fn-lbc) (fn-lb-columns-row-pointersp 0 fn-lbc))
  (fn-lb-columns-row-pointersp 0 (fn-lbc-rebuild-rows rows log fn-lbc)))
 :hints (("Goal" :induct (fn-lbc-rebuild-rows rows log fn-lbc) :in-theory
  (union-theories (theory 'ground-zero)
   '((:type-prescription fn-lbpwf-count-natural) fn-lbc-rebuild-rows fn-lb-columns-row-pointersp-of-append-row
     fn-lb-columns-row-pointersp-of-number-put-row fn-lb-columns-directory-alignedp-of-append-row
     fn-lb-columns-directory-alignedp-of-number-put-row)))))
