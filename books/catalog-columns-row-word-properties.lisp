; Derived constructor support; local algebra does not escape this book.
(in-package "ACL2")
(include-book "catalog-columns-directory-bool-properties")

(local (defthm fn-lbraw-nth-of-cons
 (equal (nth i (cons value xs)) (if (zp i) value (nth (- (nfix i) 1) xs)))
 :hints (("Goal" :in-theory (enable nth)))))

(local (defthm fn-lbraw-count-natural
 (natp (fn-lbc-count fn-lbc)) :rule-classes :type-prescription
 :hints (("Goal" :in-theory (union-theories (theory 'ground-zero)
  '(fn-lbc-count fn-lbc-row-store fn-lbc-rowwords-count-is-len))))))

(defthm fn-lbc-msgid-hash-word-of-append-row-new
 (equal (fn-lbc-word :msgid-hash (fn-lbc-count fn-lbc) (fn-lbc-append-row row log fn-lbc)) (fn-lbc-msgid-hash (fn-record-msgid row)))
 :hints (("Goal" :do-not '(preprocess) :do-not-induct t :in-theory
  (union-theories (theory 'minimal-theory) '(fn-lbc-append-row fn-lbc-word-of-escape-store-put fn-lbc-word-of-directory-store-update-by-definition fn-lbraw-nth-of-cons car-cons cdr-cons fn-lbc-count-of-append-nov fn-lbc-count-of-append-memberships fn-lbc-count-of-msgid-pool-append fn-lbc-count-of-overview-pool-append fn-lbc-count-of-append-nov-texts (:executable-counterpart equal) (:executable-counterpart nfix) (:executable-counterpart zp) (:executable-counterpart binary-+) fn-lbc-word-msgid-hash-of-store-append-at-index)))))

(defthm fn-lbc-loc0-word-of-append-row-new
 (equal (fn-lbc-word :loc0 (fn-lbc-count fn-lbc) (fn-lbc-append-row row log fn-lbc)) (mv-nth 0 (fn-loc-make (fn-lb-log-model-row-segment row log) (nth 3 (fn-lb-log-model-row-entry row log)) (nth 4 (fn-lb-log-model-row-entry row log)))))
 :hints (("Goal" :do-not '(preprocess) :do-not-induct t :in-theory
  (union-theories (theory 'minimal-theory) '(fn-lbc-append-row fn-lbc-word-of-escape-store-put fn-lbc-word-of-directory-store-update-by-definition fn-lbraw-nth-of-cons car-cons cdr-cons fn-lbc-count-of-append-nov fn-lbc-count-of-append-memberships fn-lbc-count-of-msgid-pool-append fn-lbc-count-of-overview-pool-append fn-lbc-count-of-append-nov-texts (:executable-counterpart equal) (:executable-counterpart nfix) (:executable-counterpart zp) (:executable-counterpart binary-+) fn-lbc-word-loc0-of-store-append-at-index mv-nth)))))

(defthm fn-lbc-loc1-word-of-append-row-new
 (equal (fn-lbc-word :loc1 (fn-lbc-count fn-lbc) (fn-lbc-append-row row log fn-lbc)) (mv-nth 1 (fn-loc-make (fn-lb-log-model-row-segment row log) (nth 3 (fn-lb-log-model-row-entry row log)) (nth 4 (fn-lb-log-model-row-entry row log)))))
 :hints (("Goal" :do-not '(preprocess) :do-not-induct t :in-theory
  (union-theories (theory 'minimal-theory) '(fn-lbc-append-row fn-lbc-word-of-escape-store-put fn-lbc-word-of-directory-store-update-by-definition fn-lbraw-nth-of-cons car-cons cdr-cons fn-lbc-count-of-append-nov fn-lbc-count-of-append-memberships fn-lbc-count-of-msgid-pool-append fn-lbc-count-of-overview-pool-append fn-lbc-count-of-append-nov-texts (:executable-counterpart equal) (:executable-counterpart nfix) (:executable-counterpart zp) (:executable-counterpart binary-+) fn-lbc-word-loc1-of-store-append-at-index mv-nth)))))

(defthm fn-lbc-loc0-of-append-row-new
 (equal (fn-lbc-loc0 (fn-lbc-count fn-lbc) (fn-lbc-append-row row log fn-lbc)) (mv-nth 0 (fn-loc-make (fn-lb-log-model-row-segment row log) (nth 3 (fn-lb-log-model-row-entry row log)) (nth 4 (fn-lb-log-model-row-entry row log)))))
 :hints (("Goal" :do-not-induct t :in-theory
  (union-theories (theory 'ground-zero)
   '(fn-lbc-loc0-is-word-by-definition fn-lbc-loc0-word-of-append-row-new
     fn-lbc-count-of-append-row (:type-prescription fn-lbraw-count-natural))))))

(defthm fn-lbc-loc1-of-append-row-new
 (equal (fn-lbc-loc1 (fn-lbc-count fn-lbc) (fn-lbc-append-row row log fn-lbc)) (mv-nth 1 (fn-loc-make (fn-lb-log-model-row-segment row log) (nth 3 (fn-lb-log-model-row-entry row log)) (nth 4 (fn-lb-log-model-row-entry row log)))))
 :hints (("Goal" :do-not-induct t :in-theory
  (union-theories (theory 'ground-zero)
   '(fn-lbc-loc1-is-word-by-definition fn-lbc-loc1-word-of-append-row-new
     fn-lbc-count-of-append-row (:type-prescription fn-lbraw-count-natural))))))

(defthm fn-lbc-nov-ok-flag-of-append-row-new
 (equal (fn-lbc-flag (fn-lbc-count fn-lbc) 0 (fn-lbc-append-row row log fn-lbc)) (if (and (fn-hnov-p (fn-hf-nov (fn-held-facts row))) (fn-hnov-ok (fn-hf-nov (fn-held-facts row)))) t nil))
 :hints (("Goal" :do-not '(preprocess) :do-not-induct t :in-theory
  (union-theories (theory 'minimal-theory) '(fn-lbc-append-row fn-lbc-word-of-escape-store-put fn-lbc-word-of-directory-store-update-by-definition fn-lbraw-nth-of-cons car-cons cdr-cons fn-lbc-count-of-append-nov fn-lbc-count-of-append-memberships fn-lbc-count-of-msgid-pool-append fn-lbc-count-of-overview-pool-append fn-lbc-count-of-append-nov-texts (:executable-counterpart equal) (:executable-counterpart nfix) (:executable-counterpart zp) (:executable-counterpart binary-+) fn-lbc-flag fn-lbc-word-flags-of-store-append-at-index fn-lbc-row-flags-nov-ok-bit fn-lbc-escape-store-get-of-put)))))

(defthm fn-lbc-nov-tomb-flag-of-append-row-new
 (equal (fn-lbc-flag (fn-lbc-count fn-lbc) 1 (fn-lbc-append-row row log fn-lbc)) (if (and (fn-hnov-p (fn-hf-nov (fn-held-facts row))) (fn-hnov-tomb (fn-hf-nov (fn-held-facts row)))) t nil))
 :hints (("Goal" :do-not '(preprocess) :do-not-induct t :in-theory
  (union-theories (theory 'minimal-theory) '(fn-lbc-append-row fn-lbc-word-of-escape-store-put fn-lbc-word-of-directory-store-update-by-definition fn-lbraw-nth-of-cons car-cons cdr-cons fn-lbc-count-of-append-nov fn-lbc-count-of-append-memberships fn-lbc-count-of-msgid-pool-append fn-lbc-count-of-overview-pool-append fn-lbc-count-of-append-nov-texts (:executable-counterpart equal) (:executable-counterpart nfix) (:executable-counterpart zp) (:executable-counterpart binary-+) fn-lbc-flag fn-lbc-word-flags-of-store-append-at-index fn-lbc-row-flags-nov-tomb-bit fn-lbc-escape-store-get-of-put)))))

(defthm fn-lbc-withdrawn-flag-of-append-row-new
 (equal (fn-lbc-flag (fn-lbc-count fn-lbc) 2 (fn-lbc-append-row row log fn-lbc)) (if (fn-held-withdrawn row) t nil))
 :hints (("Goal" :do-not '(preprocess) :do-not-induct t :in-theory
  (union-theories (theory 'minimal-theory) '(fn-lbc-append-row fn-lbc-word-of-escape-store-put fn-lbc-word-of-directory-store-update-by-definition fn-lbraw-nth-of-cons car-cons cdr-cons fn-lbc-count-of-append-nov fn-lbc-count-of-append-memberships fn-lbc-count-of-msgid-pool-append fn-lbc-count-of-overview-pool-append fn-lbc-count-of-append-nov-texts (:executable-counterpart equal) (:executable-counterpart nfix) (:executable-counterpart zp) (:executable-counterpart binary-+) fn-lbc-flag fn-lbc-word-flags-of-store-append-at-index fn-lbc-row-flags-withdrawn-bit fn-lbc-escape-store-get-of-put)))))

(defthm fn-lbc-escaped-flag-of-append-row-new
 (equal (fn-lbc-flag (fn-lbc-count fn-lbc) 3 (fn-lbc-append-row row log fn-lbc)) (if (fn-lbc-escape-store-get (fn-lbc-count fn-lbc) (fn-lbc-append-row row log fn-lbc)) t nil))
 :hints (("Goal" :do-not '(preprocess) :do-not-induct t :in-theory
  (union-theories (theory 'minimal-theory) '(fn-lbc-append-row fn-lbc-word-of-escape-store-put fn-lbc-word-of-directory-store-update-by-definition fn-lbraw-nth-of-cons car-cons cdr-cons fn-lbc-count-of-append-nov fn-lbc-count-of-append-memberships fn-lbc-count-of-msgid-pool-append fn-lbc-count-of-overview-pool-append fn-lbc-count-of-append-nov-texts (:executable-counterpart equal) (:executable-counterpart nfix) (:executable-counterpart zp) (:executable-counterpart binary-+) fn-lbc-flag fn-lbc-word-flags-of-store-append-at-index fn-lbc-row-flags-escaped-bit fn-lbc-escape-store-get-of-put)))))

(defthm fn-lbc-ingest-verified-flag-of-append-row-new
 (equal (fn-lbc-flag (fn-lbc-count fn-lbc) 4 (fn-lbc-append-row row log fn-lbc)) (if (fn-arx-entry-ok (fn-lb-entry-octets (fn-lb-log-model-row-segment row log) (nth 3 (fn-lb-log-model-row-entry row log)) log) (fn-lb-entry-protected-len (fn-lb-log-model-row-segment row log) (nth 3 (fn-lb-log-model-row-entry row log)) log)) t nil))
 :hints (("Goal" :do-not '(preprocess) :do-not-induct t :in-theory
  (union-theories (theory 'minimal-theory) '(fn-lbc-append-row fn-lbc-word-of-escape-store-put fn-lbc-word-of-directory-store-update-by-definition fn-lbraw-nth-of-cons car-cons cdr-cons fn-lbc-count-of-append-nov fn-lbc-count-of-append-memberships fn-lbc-count-of-msgid-pool-append fn-lbc-count-of-overview-pool-append fn-lbc-count-of-append-nov-texts (:executable-counterpart equal) (:executable-counterpart nfix) (:executable-counterpart zp) (:executable-counterpart binary-+) fn-lbc-flag fn-lbc-word-flags-of-store-append-at-index fn-lbc-row-flags-ingest-verified-bit fn-lbc-escape-store-get-of-put)))))

(defthm fn-lbc-reclaimed-flag-of-append-row-new
 (equal (fn-lbc-flag (fn-lbc-count fn-lbc) 5 (fn-lbc-append-row row log fn-lbc)) (if (fn-rcl-tombstonep (nth 6 (fn-lb-log-model-row-entry row log))) t nil))
 :hints (("Goal" :do-not '(preprocess) :do-not-induct t :in-theory
  (union-theories (theory 'minimal-theory) '(fn-lbc-append-row fn-lbc-word-of-escape-store-put fn-lbc-word-of-directory-store-update-by-definition fn-lbraw-nth-of-cons car-cons cdr-cons fn-lbc-count-of-append-nov fn-lbc-count-of-append-memberships fn-lbc-count-of-msgid-pool-append fn-lbc-count-of-overview-pool-append fn-lbc-count-of-append-nov-texts (:executable-counterpart equal) (:executable-counterpart nfix) (:executable-counterpart zp) (:executable-counterpart binary-+) fn-lbc-flag fn-lbc-word-flags-of-store-append-at-index fn-lbc-row-flags-reclaimed-bit fn-lbc-escape-store-get-of-put)))))
