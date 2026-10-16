; Derived constructor support; local algebra does not escape this book.
(in-package "ACL2")
(include-book "catalog-columns-slot-storage-frames")

(local (defthm fn-lbsem-slot-assoc-append
 (equal (assoc-eq :msgid-slot (append a b))
        (or (assoc-eq :msgid-slot a) (assoc-eq :msgid-slot b)))
 :hints (("Goal" :induct (len a) :in-theory (union-theories (theory 'ground-zero)
 '(len binary-append assoc-eq))))))

(defthm fn-lbc-row-escape-cell-has-no-slot-owner
 (equal (assoc-eq :msgid-slot (fn-lbc-row-escape-cell row payload render-nov head-length max-stamp msgid-offset msgid-length i nov-start render-start groups-start numbers-start raw-head-length nov-small render-small groups-small numbers-small)) nil)
 :hints (("Goal" :do-not '(preprocess) :do-not-induct t
 :in-theory (union-theories (theory 'minimal-theory)
 '(fn-lbc-row-escape-cell fn-lbc-sparse-u64-absent-key fn-lbsem-slot-assoc-append
 fn-lbc-assoc-eq-of-pair-cons (:executable-counterpart member-equal) (:executable-counterpart equal)
 (:executable-counterpart assoc-equal))))))

(local (defthm fn-lbsem-escape-of-update-fn-lbc-row-store
 (equal (fn-lbc-escape key :msgid-slot (update-fn-lbc-row-store value fn-lbc)) (fn-lbc-escape key :msgid-slot fn-lbc))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'minimal-theory)
 '(fn-lbc-escape fn-lbc-escape-store-get update-fn-lbc-row-store fn-dm-nth-update-nth
 (:executable-counterpart nfix) (:executable-counterpart equal)))))))

(local (defthm fn-lbsem-escape-of-update-fn-lbc-directory-store
 (equal (fn-lbc-escape key :msgid-slot (update-fn-lbc-directory-store value fn-lbc)) (fn-lbc-escape key :msgid-slot fn-lbc))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'minimal-theory)
 '(fn-lbc-escape fn-lbc-escape-store-get update-fn-lbc-directory-store fn-dm-nth-update-nth
 (:executable-counterpart nfix) (:executable-counterpart equal)))))))

(defthm fn-lbc-slot-escape-of-append-row
 (equal (fn-lbc-escape key :msgid-slot (fn-lbc-append-row row log fn-lbc))
        (if (equal key (fn-lbc-count fn-lbc)) nil (fn-lbc-escape key :msgid-slot fn-lbc)))
 :hints (("Goal" :do-not '(preprocess) :do-not-induct t
  :in-theory (union-theories (theory 'minimal-theory) '(fn-lbc-slot-escape-of-cell-put fn-lbc-row-escape-cell-has-no-slot-owner fn-lbsem-escape-of-update-fn-lbc-row-store fn-lbsem-escape-of-update-fn-lbc-directory-store fn-lbc-escape-of-msgid-pool-append fn-lbc-escape-of-overview-pool-append fn-lbc-escape-of-append-nov-texts fn-lbc-escape-of-append-nov fn-lbc-escape-of-append-memberships fn-lbc-append-row fn-lbc-escape-store-get-of-put car-cons cdr-cons fn-lbc-count-of-msgid-pool-append fn-lbc-count-of-overview-pool-append fn-lbc-count-of-append-nov-texts fn-lbc-count-of-append-nov fn-lbc-count-of-append-memberships fn-lbc-count-of-escape-store-put fn-lbc-count-of-number-put-first fn-lbc-count-of-number-put-row-seen fn-lbc-count-of-number-put-row fn-lbc-count-of-summary-put fn-lbc-count-of-rebuild-summaries fn-lbc-count-of-reserve-slots fn-lbc-count-of-slot-drop-owner fn-lbc-value-of-msgid-pool-append fn-lbc-value-of-overview-pool-append fn-lbc-value-of-append-nov-texts fn-lbc-value-of-append-nov fn-lbc-value-of-append-memberships fn-lbc-value-of-number-put-first fn-lbc-value-of-number-put-row-seen fn-lbc-value-of-number-put-row fn-lbc-value-of-summary-put fn-lbc-value-of-rebuild-summaries fn-lbc-value-of-reserve-slots fn-lbc-msgid-pool-count-frame-of-overview-pool-append fn-lbc-msgid-pool-count-frame-of-append-nov-texts fn-lbc-msgid-pool-count-frame-of-append-nov fn-lbc-msgid-pool-count-frame-of-append-memberships fn-lbc-msgid-pool-count-frame-of-escape-store-put fn-lbc-msgid-pool-count-frame-of-number-put-first fn-lbc-msgid-pool-count-frame-of-number-put-row-seen fn-lbc-msgid-pool-count-frame-of-number-put-row fn-lbc-msgid-pool-count-frame-of-summary-put fn-lbc-msgid-pool-count-frame-of-rebuild-summaries fn-lbc-msgid-pool-count-frame-of-reserve-slots fn-lbc-msgid-pool-count-frame-of-slot-drop-owner fn-lbc-msgid-pool-count-frame-of-slot-put fn-lbc-msgid-pool-count-frame-of-slot-insert fn-lbc-msgid-pool-count-frame-of-index-slots fn-lbc-nov-record-count-frame-of-msgid-pool-append fn-lbc-nov-record-count-frame-of-overview-pool-append fn-lbc-nov-record-count-frame-of-append-nov-texts fn-lbc-nov-record-count-frame-of-append-memberships fn-lbc-nov-record-count-frame-of-escape-store-put fn-lbc-nov-record-count-frame-of-number-put-first fn-lbc-nov-record-count-frame-of-number-put-row-seen fn-lbc-nov-record-count-frame-of-number-put-row fn-lbc-nov-record-count-frame-of-summary-put fn-lbc-nov-record-count-frame-of-rebuild-summaries fn-lbc-nov-record-count-frame-of-reserve-slots fn-lbc-nov-record-count-frame-of-slot-drop-owner fn-lbc-nov-record-count-frame-of-slot-put fn-lbc-nov-record-count-frame-of-slot-insert fn-lbc-nov-record-count-frame-of-index-slots fn-lbc-membership-record-count-frame-of-msgid-pool-append fn-lbc-membership-record-count-frame-of-overview-pool-append fn-lbc-membership-record-count-frame-of-append-nov-texts fn-lbc-membership-record-count-frame-of-append-nov fn-lbc-membership-record-count-frame-of-escape-store-put fn-lbc-membership-record-count-frame-of-number-put-first fn-lbc-membership-record-count-frame-of-number-put-row-seen fn-lbc-membership-record-count-frame-of-number-put-row fn-lbc-membership-record-count-frame-of-summary-put fn-lbc-membership-record-count-frame-of-rebuild-summaries fn-lbc-membership-record-count-frame-of-reserve-slots fn-lbc-membership-record-count-frame-of-slot-drop-owner fn-lbc-membership-record-count-frame-of-slot-put fn-lbc-membership-record-count-frame-of-slot-insert fn-lbc-membership-record-count-frame-of-index-slots (:executable-counterpart equal) (:executable-counterpart natp) (:executable-counterpart member-equal) (:executable-counterpart nfix) (:executable-counterpart zp) (:executable-counterpart binary-+))))))

(defthm fn-lbc-slot-escape-empty-of-rebuild-rows
 (implies (not (fn-lbc-escape key :msgid-slot fn-lbc))
 (not (fn-lbc-escape key :msgid-slot (fn-lbc-rebuild-rows rows log fn-lbc))))
 :hints (("Goal" :induct (fn-lbc-rebuild-rows rows log fn-lbc)
 :in-theory (union-theories (theory 'ground-zero)
 '(fn-lbc-rebuild-rows fn-lbc-slot-escape-of-append-row fn-lbc-escape-of-number-put-row)))))
