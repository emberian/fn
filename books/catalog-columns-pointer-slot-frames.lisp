; Derived constructor support; local algebra does not escape this book.
(in-package "ACL2")
(include-book "catalog-columns-slot-semantic-frames")

(defthm fn-lb-column-row-pointerp-of-slot-put
 (equal (fn-lb-column-row-pointerp i (fn-lbc-slot-put slot ordinal fn-lbc)) (fn-lb-column-row-pointerp i fn-lbc))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'minimal-theory) '(fn-lb-column-row-pointerp fn-lbc-escape-of-slot-put-other-key fn-lbc-value-of-slot-put-other-field fn-lbc-directory-value-of-slot-put-other-field (:executable-counterpart equal) fn-lbc-msgid-pool-count-frame-of-slot-put fn-lbc-overview-pool-count-frame-of-slot-put fn-lbc-nov-record-count-frame-of-slot-put fn-lbc-membership-record-count-frame-of-slot-put)))))

(defthm fn-lb-columns-row-pointersp-of-slot-put
 (equal (fn-lb-columns-row-pointersp i (fn-lbc-slot-put slot ordinal fn-lbc)) (fn-lb-columns-row-pointersp i fn-lbc))
 :hints (("Goal" :induct (fn-lb-columns-row-pointersp i fn-lbc) :in-theory
  (union-theories (theory 'minimal-theory)
   '(fn-lb-columns-row-pointersp fn-lb-column-row-pointerp-of-slot-put fn-lbc-count-of-slot-put)))))

(defthm fn-lb-columns-directory-alignedp-of-slot-put
 (equal (fn-lb-columns-directory-alignedp (fn-lbc-slot-put slot ordinal fn-lbc)) (fn-lb-columns-directory-alignedp fn-lbc))
 :hints (("Goal" :do-not-induct t :in-theory
  (union-theories (theory 'minimal-theory)
   '(fn-lb-columns-directory-alignedp fn-lbc-count-of-slot-put fn-lbwf-slot-put-field
     (:executable-counterpart natp) (:executable-counterpart member-equal) (:executable-counterpart equal))))))

(defthm fn-lb-columns-directory-alignedp-of-slot-insert
 (equal (fn-lb-columns-directory-alignedp (fn-lbc-slot-insert j slot fuel fn-lbc)) (fn-lb-columns-directory-alignedp fn-lbc))
 :hints (("Goal" :do-not-induct t :in-theory
  (union-theories (theory 'minimal-theory)
   '(fn-lb-columns-directory-alignedp fn-lbc-count-of-slot-insert fn-lbwf-slot-insert-field
     (:executable-counterpart natp) (:executable-counterpart member-equal) (:executable-counterpart equal))))))

(defthm fn-lb-columns-row-pointersp-of-slot-insert
 (equal (fn-lb-columns-row-pointersp i (fn-lbc-slot-insert j slot fuel fn-lbc)) (fn-lb-columns-row-pointersp i fn-lbc))
 :hints (("Goal" :induct (fn-lbc-slot-insert j slot fuel fn-lbc) :in-theory
  (union-theories (theory 'minimal-theory) '(fn-lbc-slot-insert fn-lb-columns-row-pointersp-of-slot-put)))))

(defthm fn-lb-columns-directory-alignedp-of-index-slots
 (equal (fn-lb-columns-directory-alignedp (fn-lbc-index-slots j n fn-lbc)) (fn-lb-columns-directory-alignedp fn-lbc))
 :hints (("Goal" :do-not-induct t :in-theory
  (union-theories (theory 'minimal-theory)
   '(fn-lb-columns-directory-alignedp fn-lbc-count-of-index-slots fn-lbwf-index-slots-field
     (:executable-counterpart natp) (:executable-counterpart member-equal) (:executable-counterpart equal))))))

(defthm fn-lb-columns-row-pointersp-of-index-slots
 (equal (fn-lb-columns-row-pointersp i (fn-lbc-index-slots j n fn-lbc)) (fn-lb-columns-row-pointersp i fn-lbc))
 :hints (("Goal" :induct (fn-lbc-index-slots j n fn-lbc) :in-theory
  (union-theories (theory 'minimal-theory) '(fn-lbc-index-slots fn-lb-columns-row-pointersp-of-slot-put fn-lb-columns-row-pointersp-of-slot-insert)))))

(local (defthm fn-lbpsf-row-pointer-frame-by-fields
 (implies (and (equal (nth 0 new) (nth 0 fn-lbc)) (equal (nth 1 new) (nth 1 fn-lbc)) (equal (nth 5 new) (nth 5 fn-lbc)) (equal (nth 6 new) (nth 6 fn-lbc)) (equal (nth 7 new) (nth 7 fn-lbc)) (equal (nth 9 new) (nth 9 fn-lbc)))
  (equal (fn-lb-column-row-pointerp i new) (fn-lb-column-row-pointerp i fn-lbc)))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t :in-theory
  (set-difference-theories (union-theories (theory 'ground-zero)
   '(fn-lb-column-row-pointerp fn-lbc-value fn-lbc-directory-value fn-lbc-escape fn-lbc-escape-store-get
     fn-lbc-word fn-lbc-directory-field fn-lbc-row-store fn-lbc-directory-store
     fn-lbc-msgid-pool-count fn-lbc-msgid-store fn-lbc-msgid-octets-count-is-len
     fn-lbc-nov-record-count fn-lbc-nov-store fn-lbc-nov-count-is-len
     fn-lbc-membership-record-count fn-lbc-membership-store fn-lbc-memberships-count-is-len))
   '((:definition nfix) (tau-system)))))))

(local (defthm fn-lbpsf-count-of-summary-groups-update
 (equal (fn-lbc-count (update-fn-lbc-summary-groups groups fn-lbc)) (fn-lbc-count fn-lbc))
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-lbc-count-frame-by-definition (new (update-fn-lbc-summary-groups groups fn-lbc))))
  :in-theory (union-theories (theory 'ground-zero) '(update-fn-lbc-summary-groups fn-dm-nth-update-nth))))))

(defthm fn-lb-column-row-pointerp-of-summary-groups-update
 (equal (fn-lb-column-row-pointerp i (update-fn-lbc-summary-groups groups fn-lbc)) (fn-lb-column-row-pointerp i fn-lbc))
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-lbpsf-row-pointer-frame-by-fields (new (update-fn-lbc-summary-groups groups fn-lbc))))
  :in-theory (union-theories (theory 'ground-zero) '(update-fn-lbc-summary-groups fn-dm-nth-update-nth)))))

(defthm fn-lb-columns-row-pointersp-of-summary-groups-update
 (equal (fn-lb-columns-row-pointersp i (update-fn-lbc-summary-groups groups fn-lbc)) (fn-lb-columns-row-pointersp i fn-lbc))
 :hints (("Goal" :induct (fn-lb-columns-row-pointersp i fn-lbc) :in-theory
  (union-theories (theory 'minimal-theory)
   '(fn-lb-columns-row-pointersp fn-lb-column-row-pointerp-of-summary-groups-update fn-lbpsf-count-of-summary-groups-update)))))

(defthm fn-lb-columns-row-pointersp-of-open-rebuild
 (fn-lb-columns-row-pointersp 0 (fn-lbc-open-rebuild rows log fn-lbc))
 :hints (("Goal" :do-not-induct t :in-theory
  (union-theories (theory 'minimal-theory)
   '(fn-lbc-open-rebuild fn-lb-columns-row-pointersp-of-clear-columns
     fn-lb-columns-directory-alignedp-of-clear-columns fn-lb-columns-row-pointersp-of-rebuild-rows
     fn-lb-columns-row-pointersp-of-rebuild-summaries fn-lb-columns-row-pointersp-of-reserve-slots
     fn-lb-columns-row-pointersp-of-summary-groups-update fn-lb-columns-row-pointersp-of-index-slots)))))
