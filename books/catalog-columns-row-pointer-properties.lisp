; Derived constructor support; local algebra does not escape this book.
(in-package "ACL2")
(include-book "catalog-columns-old-row-readback")

(local (defthm fn-lbpp-nfix-natural
 (implies (natp x) (equal (nfix x) x))
 :hints (("Goal" :in-theory (enable nfix)))))

(defthm fn-lb-column-row-pointerp-of-append-row-new
 (implies (fn-lb-columns-directory-alignedp fn-lbc)
  (fn-lb-column-row-pointerp (fn-lbc-count fn-lbc) (fn-lbc-append-row row log fn-lbc)))
 :hints (("Goal" :do-not '(preprocess) :do-not-induct t
  :in-theory (set-difference-theories (union-theories (theory 'ground-zero)
   '(fn-lb-column-row-pointerp fn-lbc-escape fn-lbc-escape-store-get-of-append-row-new car-cons cdr-cons fn-lbpp-nfix-natural fn-lbc-row-cell-extra-nov fn-lbc-row-cell-extra-render-nov fn-lbc-row-cell-extra-groups fn-lbc-row-cell-extra-numbers fn-lbc-nov-start-of-append-row-new fn-lbc-nov-length-of-append-row-new fn-lbc-render-nov-start-of-append-row-new fn-lbc-groups-start-of-append-row-new fn-lbc-groups-count-of-append-row-new fn-lbc-numbers-start-of-append-row-new fn-lbc-numbers-count-of-append-row-new fn-lbc-msgid-offset-of-append-row-new fn-lbc-msgid-length-of-append-row-new fn-lbc-nov-record-count-of-append-row-allocation fn-lbc-membership-record-count-of-append-row-allocation fn-lbc-msgid-pool-count-of-append-row-allocation fn-lbc-nov-record-count-of-append-nov fn-lbc-membership-record-count-of-append-memberships fn-lbc-msgid-pool-count-of-append fn-lbc-overview-pool-count-frame-of-msgid-pool-append fn-lbc-nov-record-count-frame-of-msgid-pool-append fn-lbc-membership-record-count-frame-of-msgid-pool-append fn-lbc-msgid-pool-count-frame-of-overview-pool-append fn-lbc-nov-record-count-frame-of-overview-pool-append fn-lbc-membership-record-count-frame-of-overview-pool-append fn-lbc-msgid-pool-count-frame-of-append-nov-texts fn-lbc-nov-record-count-frame-of-append-nov-texts fn-lbc-membership-record-count-frame-of-append-nov-texts fn-lbc-msgid-pool-count-frame-of-append-nov fn-lbc-membership-record-count-frame-of-append-nov fn-lbc-msgid-pool-count-frame-of-append-memberships fn-lbc-nov-record-count-frame-of-append-memberships fn-lbc-msgid-pool-count-frame-of-escape-store-put fn-lbc-overview-pool-count-frame-of-escape-store-put fn-lbc-nov-record-count-frame-of-escape-store-put fn-lbc-membership-record-count-frame-of-escape-store-put fn-lbc-msgid-pool-count-frame-of-number-put-first fn-lbc-overview-pool-count-frame-of-number-put-first fn-lbc-nov-record-count-frame-of-number-put-first fn-lbc-membership-record-count-frame-of-number-put-first fn-lbc-msgid-pool-count-frame-of-number-put-row-seen fn-lbc-overview-pool-count-frame-of-number-put-row-seen fn-lbc-nov-record-count-frame-of-number-put-row-seen fn-lbc-membership-record-count-frame-of-number-put-row-seen fn-lbc-msgid-pool-count-frame-of-number-put-row fn-lbc-overview-pool-count-frame-of-number-put-row fn-lbc-nov-record-count-frame-of-number-put-row fn-lbc-membership-record-count-frame-of-number-put-row fn-lbc-msgid-pool-count-frame-of-summary-put fn-lbc-overview-pool-count-frame-of-summary-put fn-lbc-nov-record-count-frame-of-summary-put fn-lbc-membership-record-count-frame-of-summary-put fn-lbc-msgid-pool-count-frame-of-rebuild-summaries fn-lbc-overview-pool-count-frame-of-rebuild-summaries fn-lbc-nov-record-count-frame-of-rebuild-summaries fn-lbc-membership-record-count-frame-of-rebuild-summaries fn-lbc-msgid-pool-count-frame-of-reserve-slots fn-lbc-overview-pool-count-frame-of-reserve-slots fn-lbc-nov-record-count-frame-of-reserve-slots fn-lbc-membership-record-count-frame-of-reserve-slots fn-lbc-msgid-pool-count-frame-of-slot-drop-owner fn-lbc-overview-pool-count-frame-of-slot-drop-owner fn-lbc-nov-record-count-frame-of-slot-drop-owner fn-lbc-membership-record-count-frame-of-slot-drop-owner fn-lbc-msgid-pool-count-frame-of-slot-put fn-lbc-overview-pool-count-frame-of-slot-put fn-lbc-nov-record-count-frame-of-slot-put fn-lbc-membership-record-count-frame-of-slot-put fn-lbc-msgid-pool-count-frame-of-slot-insert fn-lbc-overview-pool-count-frame-of-slot-insert fn-lbc-nov-record-count-frame-of-slot-insert fn-lbc-membership-record-count-frame-of-slot-insert fn-lbc-msgid-pool-count-frame-of-index-slots fn-lbc-overview-pool-count-frame-of-index-slots fn-lbc-nov-record-count-frame-of-index-slots fn-lbc-membership-record-count-frame-of-index-slots (:type-prescription fn-lbc-nov-record-count-natural) (:type-prescription fn-lbc-membership-record-count-natural) (:type-prescription fn-lbc-msgid-pool-count-natural))) '((:definition nfix) (tau-system))))))

(local (defthm fn-lbpp-pointer-msgid
 (implies (fn-lb-column-row-pointerp i fn-lbc) (<= (+ (nfix (fn-lbc-value i :msgid-offset fn-lbc)) (nfix (fn-lbc-value i :msgid-length fn-lbc))) (fn-lbc-msgid-pool-count fn-lbc)))
 :rule-classes nil
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory) '(fn-lb-column-row-pointerp))))))

(local (defthm fn-lbpp-pointer-original-nov
 (implies (fn-lb-column-row-pointerp i fn-lbc) (implies (and (not (fn-lbc-escape i :nov fn-lbc)) (not (equal (fn-lbc-directory-value i :nov-length fn-lbc) 0))) (and (natp (fn-lbc-directory-value i :nov-start fn-lbc)) (< (fn-lbc-directory-value i :nov-start fn-lbc) (fn-lbc-nov-record-count fn-lbc)))))
 :rule-classes nil
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory) '(fn-lb-column-row-pointerp))))))

(local (defthm fn-lbpp-pointer-render-nov
 (implies (fn-lb-column-row-pointerp i fn-lbc) (implies (not (fn-lbc-escape i :render-nov fn-lbc)) (and (natp (fn-lbc-directory-value i :render-nov-start fn-lbc)) (< (fn-lbc-directory-value i :render-nov-start fn-lbc) (fn-lbc-nov-record-count fn-lbc)))))
 :rule-classes nil
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory) '(fn-lb-column-row-pointerp))))))

(local (defthm fn-lbpp-pointer-groups
 (implies (fn-lb-column-row-pointerp i fn-lbc) (implies (not (fn-lbc-escape i :groups fn-lbc)) (<= (+ (nfix (fn-lbc-directory-value i :groups-start fn-lbc)) (nfix (fn-lbc-directory-value i :groups-count fn-lbc))) (fn-lbc-membership-record-count fn-lbc))))
 :rule-classes nil
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory) '(fn-lb-column-row-pointerp))))))

(local (defthm fn-lbpp-pointer-numbers
 (implies (fn-lb-column-row-pointerp i fn-lbc) (implies (not (fn-lbc-escape i :numbers fn-lbc)) (<= (+ (nfix (fn-lbc-directory-value i :numbers-start fn-lbc)) (nfix (fn-lbc-directory-value i :numbers-count fn-lbc))) (fn-lbc-membership-record-count fn-lbc))))
 :rule-classes nil
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory) '(fn-lb-column-row-pointerp))))))

(defthm fn-lb-column-row-pointerp-of-append-row-old
 (implies (and (natp i) (< i (fn-lbc-count fn-lbc))
               (fn-lb-columns-directory-alignedp fn-lbc) (fn-lb-column-row-pointerp i fn-lbc))
  (fn-lb-column-row-pointerp i (fn-lbc-append-row row log fn-lbc)))
 :hints (("Goal" :do-not-induct t
  :expand ((fn-lb-column-row-pointerp i (fn-lbc-append-row row log fn-lbc)))
  :use ((:instance fn-lbpp-pointer-msgid) (:instance fn-lbpp-pointer-original-nov) (:instance fn-lbpp-pointer-render-nov) (:instance fn-lbpp-pointer-groups) (:instance fn-lbpp-pointer-numbers))
  :in-theory (union-theories (theory 'minimal-theory)
   '(fn-lbc-escape-of-append-row-old fn-lbc-value-of-append-row-old
     fn-lbc-directory-value-of-append-row-old
     fn-lbc-nov-record-count-of-append-row-nondecreasing
     fn-lbc-membership-record-count-of-append-row-nondecreasing
     fn-lbc-msgid-pool-count-of-append-row-nondecreasing)))))
