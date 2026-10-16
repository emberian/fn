; Derived constructor support; local algebra does not escape this book.
(in-package "ACL2")
(include-book "catalog-columns-constructor-native-types")

(local (defthm fn-lbsgf-field
 (implies (natp k) (equal (nth k (update-fn-lbc-summary-groups groups fn-lbc)) (if (equal k 8) groups (nth k fn-lbc))))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'ground-zero)
 '(update-fn-lbc-summary-groups fn-dm-nth-update-nth))))))

(local (defthm fn-lbsgf-nfix-natural (natp (nfix x)) :hints (("Goal" :in-theory (enable nfix)))))

(defthm fn-lbc-count-of-summary-groups-update
 (equal (fn-lbc-count  (update-fn-lbc-summary-groups groups fn-lbc)) (fn-lbc-count  fn-lbc))
 :hints (("Goal" :do-not-induct t :use ((:instance fn-lbc-count-frame-by-definition (new (update-fn-lbc-summary-groups groups fn-lbc)) ))
 :in-theory (union-theories (theory 'minimal-theory)
 '(fn-lbsgf-field (:executable-counterpart natp) (:executable-counterpart equal))))))

(defthm fn-lbc-word-of-summary-groups-update
 (equal (fn-lbc-word read-field read-i (update-fn-lbc-summary-groups groups fn-lbc)) (fn-lbc-word read-field read-i fn-lbc))
 :hints (("Goal" :do-not-induct t :use ((:instance fn-lbc-word-frame-by-definition (new (update-fn-lbc-summary-groups groups fn-lbc)) (field read-field) (i read-i)))
 :in-theory (union-theories (theory 'minimal-theory)
 '(fn-lbsgf-field (:executable-counterpart natp) (:executable-counterpart equal))))))

(defthm fn-lbc-directory-field-of-summary-groups-update
 (equal (fn-lbc-directory-field read-field read-i (update-fn-lbc-summary-groups groups fn-lbc)) (fn-lbc-directory-field read-field read-i fn-lbc))
 :hints (("Goal" :do-not-induct t :use ((:instance fn-lbc-directory-field-frame-by-definition (new (update-fn-lbc-summary-groups groups fn-lbc)) (field read-field) (i read-i)))
 :in-theory (union-theories (theory 'minimal-theory)
 '(fn-lbsgf-field (:executable-counterpart natp) (:executable-counterpart equal))))))

(defthm fn-lbc-loc0-of-summary-groups-update
 (equal (fn-lbc-loc0 read-i (update-fn-lbc-summary-groups groups fn-lbc)) (fn-lbc-loc0 read-i fn-lbc))
 :hints (("Goal" :do-not-induct t :use ((:instance fn-lbc-loc0-frame-by-definition (new (update-fn-lbc-summary-groups groups fn-lbc)) (i read-i)))
 :in-theory (union-theories (theory 'minimal-theory)
 '(fn-lbsgf-field (:executable-counterpart natp) (:executable-counterpart equal))))))

(defthm fn-lbc-loc1-of-summary-groups-update
 (equal (fn-lbc-loc1 read-i (update-fn-lbc-summary-groups groups fn-lbc)) (fn-lbc-loc1 read-i fn-lbc))
 :hints (("Goal" :do-not-induct t :use ((:instance fn-lbc-loc1-frame-by-definition (new (update-fn-lbc-summary-groups groups fn-lbc)) (i read-i)))
 :in-theory (union-theories (theory 'minimal-theory)
 '(fn-lbsgf-field (:executable-counterpart natp) (:executable-counterpart equal))))))

(defthm fn-lbc-escape-store-get-of-summary-groups-update
 (equal (fn-lbc-escape-store-get read-i (update-fn-lbc-summary-groups groups fn-lbc)) (fn-lbc-escape-store-get read-i fn-lbc))
 :hints (("Goal" :do-not-induct t :use ((:instance fn-lbc-escape-store-get-frame-by-definition (new (update-fn-lbc-summary-groups groups fn-lbc)) (i read-i)))
 :in-theory (union-theories (theory 'minimal-theory)
 '(fn-lbsgf-field (:executable-counterpart natp) (:executable-counterpart equal))))))

(defthm fn-lbc-escape-of-summary-groups-update
 (equal (fn-lbc-escape read-i read-field (update-fn-lbc-summary-groups groups fn-lbc)) (fn-lbc-escape read-i read-field fn-lbc))
 :hints (("Goal" :do-not-induct t :use ((:instance fn-lbc-escape-frame-by-definition (new (update-fn-lbc-summary-groups groups fn-lbc)) (i read-i) (field read-field)))
 :in-theory (union-theories (theory 'minimal-theory)
 '(fn-lbsgf-field (:executable-counterpart natp) (:executable-counterpart equal))))))

(defthm fn-lbc-value-of-summary-groups-update
 (equal (fn-lbc-value read-i read-field (update-fn-lbc-summary-groups groups fn-lbc)) (fn-lbc-value read-i read-field fn-lbc))
 :hints (("Goal" :do-not-induct t :use ((:instance fn-lbc-value-frame-by-definition (new (update-fn-lbc-summary-groups groups fn-lbc)) (i read-i) (field read-field)))
 :in-theory (union-theories (theory 'minimal-theory)
 '(fn-lbsgf-field (:executable-counterpart natp) (:executable-counterpart equal))))))

(defthm fn-lbc-directory-value-of-summary-groups-update
 (equal (fn-lbc-directory-value read-i read-field (update-fn-lbc-summary-groups groups fn-lbc)) (fn-lbc-directory-value read-i read-field fn-lbc))
 :hints (("Goal" :do-not-induct t :use ((:instance fn-lbc-directory-value-frame-by-definition (new (update-fn-lbc-summary-groups groups fn-lbc)) (i read-i) (field read-field)))
 :in-theory (union-theories (theory 'minimal-theory)
 '(fn-lbsgf-field (:executable-counterpart natp) (:executable-counterpart equal))))))

(defthm fn-lbc-flag-of-summary-groups-update
 (equal (fn-lbc-flag read-i read-bit (update-fn-lbc-summary-groups groups fn-lbc)) (fn-lbc-flag read-i read-bit fn-lbc))
 :hints (("Goal" :do-not-induct t :use ((:instance fn-lbc-flag-frame-by-definition (new (update-fn-lbc-summary-groups groups fn-lbc)) (i read-i) (bit read-bit)))
 :in-theory (union-theories (theory 'minimal-theory)
 '(fn-lbsgf-field (:executable-counterpart natp) (:executable-counterpart equal))))))

(defthm fn-lbc-msgid-pool-model-frame-of-summary-groups-update
 (equal (fn-lbc-msgid-pool-model (update-fn-lbc-summary-groups groups fn-lbc)) (fn-lbc-msgid-pool-model fn-lbc))
 :hints (("Goal" :do-not-induct t :use ((:instance fn-lbc-msgid-pool-model-frame-by-definition (new (update-fn-lbc-summary-groups groups fn-lbc))))
 :in-theory (union-theories (theory 'minimal-theory)
 '(fn-lbsgf-field (:executable-counterpart natp) (:executable-counterpart equal))))))

(defthm fn-lbc-overview-pool-model-frame-of-summary-groups-update
 (equal (fn-lbc-overview-pool-model (update-fn-lbc-summary-groups groups fn-lbc)) (fn-lbc-overview-pool-model fn-lbc))
 :hints (("Goal" :do-not-induct t :use ((:instance fn-lbc-overview-pool-model-frame-by-definition (new (update-fn-lbc-summary-groups groups fn-lbc))))
 :in-theory (union-theories (theory 'minimal-theory)
 '(fn-lbsgf-field (:executable-counterpart natp) (:executable-counterpart equal))))))

(defthm fn-lbc-nov-at-of-summary-groups-update
 (equal (fn-lbc-nov-at read-j (update-fn-lbc-summary-groups groups fn-lbc)) (fn-lbc-nov-at read-j fn-lbc))
 :hints (("Goal" :do-not-induct t :use ((:instance fn-lbc-nov-at-frame-by-definition (new (update-fn-lbc-summary-groups groups fn-lbc)) (i read-j)))
 :in-theory (union-theories (theory 'minimal-theory)
 '(fn-lbsgf-field (:executable-counterpart natp) (:executable-counterpart equal))))))

(defthm fn-lbc-membership-run-of-summary-groups-update
 (equal (fn-lbc-membership-run start count numbersp (update-fn-lbc-summary-groups groups fn-lbc)) (fn-lbc-membership-run start count numbersp fn-lbc))
 :hints (("Goal" :do-not-induct t :use ((:instance fn-lbc-membership-run-frame-by-definition (new (update-fn-lbc-summary-groups groups fn-lbc)) ))
 :in-theory (union-theories (theory 'minimal-theory)
 '(fn-lbsgf-field (:executable-counterpart natp) (:executable-counterpart equal))))))

(defthm fn-lbc-msgid-pool-range-of-summary-groups-update
 (implies (and (natp off) (natp n)) (equal (fn-lbc-msgid-pool-range off n (update-fn-lbc-summary-groups groups fn-lbc)) (fn-lbc-msgid-pool-range off n fn-lbc)))
 :hints (("Goal" :do-not-induct t :use ((:instance fn-lbc-msgid-pool-range-of-same-model (new (update-fn-lbc-summary-groups groups fn-lbc))))
 :in-theory (union-theories (theory 'minimal-theory) '(fn-lbc-msgid-pool-model-frame-of-summary-groups-update)))))

(defthm fn-lbc-msgid-of-summary-groups-update
 (equal (fn-lbc-msgid i (update-fn-lbc-summary-groups groups fn-lbc)) (fn-lbc-msgid i fn-lbc))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'minimal-theory) '(fn-lbc-msgid fn-lbc-value-of-summary-groups-update fn-lbc-directory-value-of-summary-groups-update fn-lbc-escape-of-summary-groups-update fn-lbc-flag-of-summary-groups-update fn-lbc-nov-at-of-summary-groups-update fn-lbc-membership-run-of-summary-groups-update fn-lbc-msgid-pool-range-of-summary-groups-update fn-lbsgf-nfix-natural)))))

(defthm fn-lbc-original-nov-of-summary-groups-update
 (equal (fn-lbc-original-nov i (update-fn-lbc-summary-groups groups fn-lbc)) (fn-lbc-original-nov i fn-lbc))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'minimal-theory) '(fn-lbc-original-nov fn-lbc-value-of-summary-groups-update fn-lbc-directory-value-of-summary-groups-update fn-lbc-escape-of-summary-groups-update fn-lbc-flag-of-summary-groups-update fn-lbc-nov-at-of-summary-groups-update fn-lbc-membership-run-of-summary-groups-update fn-lbc-msgid-pool-range-of-summary-groups-update fn-lbsgf-nfix-natural)))))

(defthm fn-lbc-render-nov-of-summary-groups-update
 (equal (fn-lbc-render-nov i (update-fn-lbc-summary-groups groups fn-lbc)) (fn-lbc-render-nov i fn-lbc))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'minimal-theory) '(fn-lbc-render-nov fn-lbc-value-of-summary-groups-update fn-lbc-directory-value-of-summary-groups-update fn-lbc-escape-of-summary-groups-update fn-lbc-flag-of-summary-groups-update fn-lbc-nov-at-of-summary-groups-update fn-lbc-membership-run-of-summary-groups-update fn-lbc-msgid-pool-range-of-summary-groups-update fn-lbsgf-nfix-natural)))))

(defthm fn-lbc-groups-of-summary-groups-update
 (equal (fn-lbc-groups i (update-fn-lbc-summary-groups groups fn-lbc)) (fn-lbc-groups i fn-lbc))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'minimal-theory) '(fn-lbc-groups fn-lbc-value-of-summary-groups-update fn-lbc-directory-value-of-summary-groups-update fn-lbc-escape-of-summary-groups-update fn-lbc-flag-of-summary-groups-update fn-lbc-nov-at-of-summary-groups-update fn-lbc-membership-run-of-summary-groups-update fn-lbc-msgid-pool-range-of-summary-groups-update fn-lbsgf-nfix-natural)))))

(defthm fn-lbc-numbers-of-summary-groups-update
 (equal (fn-lbc-numbers i (update-fn-lbc-summary-groups groups fn-lbc)) (fn-lbc-numbers i fn-lbc))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'minimal-theory) '(fn-lbc-numbers fn-lbc-value-of-summary-groups-update fn-lbc-directory-value-of-summary-groups-update fn-lbc-escape-of-summary-groups-update fn-lbc-flag-of-summary-groups-update fn-lbc-nov-at-of-summary-groups-update fn-lbc-membership-run-of-summary-groups-update fn-lbc-msgid-pool-range-of-summary-groups-update fn-lbsgf-nfix-natural)))))

(defthm fn-lbc-xref-shift-prefix-of-summary-groups-update
 (equal (fn-lbc-xref-shift-prefix i (update-fn-lbc-summary-groups groups fn-lbc)) (fn-lbc-xref-shift-prefix i fn-lbc))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'minimal-theory) '(fn-lbc-xref-shift-prefix fn-lbc-value-of-summary-groups-update fn-lbc-directory-value-of-summary-groups-update fn-lbc-escape-of-summary-groups-update fn-lbc-flag-of-summary-groups-update fn-lbc-nov-at-of-summary-groups-update fn-lbc-membership-run-of-summary-groups-update fn-lbc-msgid-pool-range-of-summary-groups-update fn-lbsgf-nfix-natural)))))

(defthm fn-lbc-withdrawn-of-summary-groups-update
 (equal (fn-lbc-withdrawn i (update-fn-lbc-summary-groups groups fn-lbc)) (fn-lbc-withdrawn i fn-lbc))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'minimal-theory) '(fn-lbc-withdrawn fn-lbc-value-of-summary-groups-update fn-lbc-directory-value-of-summary-groups-update fn-lbc-escape-of-summary-groups-update fn-lbc-flag-of-summary-groups-update fn-lbc-nov-at-of-summary-groups-update fn-lbc-membership-run-of-summary-groups-update fn-lbc-msgid-pool-range-of-summary-groups-update fn-lbsgf-nfix-natural)))))

(defthm fn-lbc-served-row-of-summary-groups-update
 (equal (fn-lbc-served-row i (update-fn-lbc-summary-groups groups fn-lbc)) (fn-lbc-served-row i fn-lbc))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'minimal-theory) '(fn-lbc-served-row fn-lbc-value-of-summary-groups-update fn-lbc-directory-value-of-summary-groups-update fn-lbc-escape-of-summary-groups-update fn-lbc-flag-of-summary-groups-update fn-lbc-nov-at-of-summary-groups-update fn-lbc-membership-run-of-summary-groups-update fn-lbc-msgid-pool-range-of-summary-groups-update fn-lbsgf-nfix-natural fn-lbc-msgid-of-summary-groups-update fn-lbc-original-nov-of-summary-groups-update fn-lbc-render-nov-of-summary-groups-update fn-lbc-groups-of-summary-groups-update fn-lbc-numbers-of-summary-groups-update fn-lbc-xref-shift-prefix-of-summary-groups-update fn-lbc-withdrawn-of-summary-groups-update)))))

(defthm fn-lbc-home-entry-of-summary-groups-update
 (equal (fn-lbc-home-entry i (update-fn-lbc-summary-groups groups fn-lbc) log) (fn-lbc-home-entry i fn-lbc log))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'minimal-theory)
 '(fn-lbc-home-entry fn-lbc-loc0-of-summary-groups-update fn-lbc-loc1-of-summary-groups-update)))))

(defthm fn-lbc-row-corr-of-summary-groups-update
 (equal (fn-lbc-row-corr i row pm (update-fn-lbc-summary-groups groups fn-lbc) log) (fn-lbc-row-corr i row pm fn-lbc log))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'minimal-theory) '(fn-lbc-row-corr fn-lbc-loc0-of-summary-groups-update fn-lbc-loc1-of-summary-groups-update fn-lbc-home-entry-of-summary-groups-update fn-lbc-served-row-of-summary-groups-update fn-lbc-value-of-summary-groups-update fn-lbc-word-of-summary-groups-update fn-lbc-flag-of-summary-groups-update fn-lbc-xref-shift-prefix-of-summary-groups-update fn-lbc-directory-value-of-summary-groups-update fn-lbc-render-nov-of-summary-groups-update)))))

(defthm fn-lbc-rows-corr-of-summary-groups-update
 (equal (fn-lbc-rows-corr i rows pm (update-fn-lbc-summary-groups groups fn-lbc) log) (fn-lbc-rows-corr i rows pm fn-lbc log))
 :hints (("Goal" :induct (fn-lbc-rows-corr i rows pm fn-lbc log)
 :in-theory (union-theories (theory 'minimal-theory) '(fn-lbc-rows-corr fn-lbc-row-corr-of-summary-groups-update)))))
