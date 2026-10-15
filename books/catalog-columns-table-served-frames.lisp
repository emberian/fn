; Derived constructor support; local algebra does not escape this book.
(in-package "ACL2")
(include-book "catalog-columns-rows-corr-append")

(local (defthm fn-lbtsf-nfix-natural (natp (nfix x)) :hints (("Goal" :in-theory (enable nfix)))))

(defthm fn-lbc-nov-at-of-number-put-row
 (equal (fn-lbc-nov-at read-j (fn-lbc-number-put-row numbers j fn-lbc)) (fn-lbc-nov-at read-j fn-lbc))
 :hints (("Goal" :do-not-induct t
 :use ((:instance fn-lbc-nov-at-frame-by-definition (new (fn-lbc-number-put-row numbers j fn-lbc)) (i read-j)))
 :in-theory (union-theories (theory 'minimal-theory)
 '(fn-lbwf-number-put-row-field (:executable-counterpart natp) (:executable-counterpart equal) (:executable-counterpart member-equal))))))

(defthm fn-lbc-membership-run-of-number-put-row
 (equal (fn-lbc-membership-run start count numbersp (fn-lbc-number-put-row numbers j fn-lbc)) (fn-lbc-membership-run start count numbersp fn-lbc))
 :hints (("Goal" :do-not-induct t
 :use ((:instance fn-lbc-membership-run-frame-by-definition (new (fn-lbc-number-put-row numbers j fn-lbc)) ))
 :in-theory (union-theories (theory 'minimal-theory)
 '(fn-lbwf-number-put-row-field (:executable-counterpart natp) (:executable-counterpart equal) (:executable-counterpart member-equal))))))

(defthm fn-lbc-msgid-pool-range-of-number-put-row
 (implies (and (natp off) (natp n)) (equal (fn-lbc-msgid-pool-range off n (fn-lbc-number-put-row numbers j fn-lbc)) (fn-lbc-msgid-pool-range off n fn-lbc)))
 :hints (("Goal" :do-not-induct t
 :use ((:instance fn-lbc-msgid-pool-range-of-same-model (new (fn-lbc-number-put-row numbers j fn-lbc))))
 :in-theory (union-theories (theory 'minimal-theory) '(fn-lbc-msgid-pool-model-frame-of-number-put-row)))))

(defthm fn-lbc-msgid-of-number-put-row
 (equal (fn-lbc-msgid i (fn-lbc-number-put-row numbers j fn-lbc)) (fn-lbc-msgid i fn-lbc))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'minimal-theory) '(fn-lbc-msgid fn-lbc-value-of-number-put-row fn-lbc-directory-value-of-number-put-row fn-lbc-escape-of-number-put-row fn-lbc-flag-of-number-put-row fn-lbc-nov-at-of-number-put-row fn-lbc-membership-run-of-number-put-row fn-lbc-msgid-pool-range-of-number-put-row fn-lbtsf-nfix-natural)))))

(defthm fn-lbc-original-nov-of-number-put-row
 (equal (fn-lbc-original-nov i (fn-lbc-number-put-row numbers j fn-lbc)) (fn-lbc-original-nov i fn-lbc))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'minimal-theory) '(fn-lbc-original-nov fn-lbc-value-of-number-put-row fn-lbc-directory-value-of-number-put-row fn-lbc-escape-of-number-put-row fn-lbc-flag-of-number-put-row fn-lbc-nov-at-of-number-put-row fn-lbc-membership-run-of-number-put-row fn-lbc-msgid-pool-range-of-number-put-row fn-lbtsf-nfix-natural)))))

(defthm fn-lbc-render-nov-of-number-put-row
 (equal (fn-lbc-render-nov i (fn-lbc-number-put-row numbers j fn-lbc)) (fn-lbc-render-nov i fn-lbc))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'minimal-theory) '(fn-lbc-render-nov fn-lbc-value-of-number-put-row fn-lbc-directory-value-of-number-put-row fn-lbc-escape-of-number-put-row fn-lbc-flag-of-number-put-row fn-lbc-nov-at-of-number-put-row fn-lbc-membership-run-of-number-put-row fn-lbc-msgid-pool-range-of-number-put-row fn-lbtsf-nfix-natural)))))

(defthm fn-lbc-groups-of-number-put-row
 (equal (fn-lbc-groups i (fn-lbc-number-put-row numbers j fn-lbc)) (fn-lbc-groups i fn-lbc))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'minimal-theory) '(fn-lbc-groups fn-lbc-value-of-number-put-row fn-lbc-directory-value-of-number-put-row fn-lbc-escape-of-number-put-row fn-lbc-flag-of-number-put-row fn-lbc-nov-at-of-number-put-row fn-lbc-membership-run-of-number-put-row fn-lbc-msgid-pool-range-of-number-put-row fn-lbtsf-nfix-natural)))))

(defthm fn-lbc-numbers-of-number-put-row
 (equal (fn-lbc-numbers i (fn-lbc-number-put-row numbers j fn-lbc)) (fn-lbc-numbers i fn-lbc))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'minimal-theory) '(fn-lbc-numbers fn-lbc-value-of-number-put-row fn-lbc-directory-value-of-number-put-row fn-lbc-escape-of-number-put-row fn-lbc-flag-of-number-put-row fn-lbc-nov-at-of-number-put-row fn-lbc-membership-run-of-number-put-row fn-lbc-msgid-pool-range-of-number-put-row fn-lbtsf-nfix-natural)))))

(defthm fn-lbc-xref-shift-prefix-of-number-put-row
 (equal (fn-lbc-xref-shift-prefix i (fn-lbc-number-put-row numbers j fn-lbc)) (fn-lbc-xref-shift-prefix i fn-lbc))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'minimal-theory) '(fn-lbc-xref-shift-prefix fn-lbc-value-of-number-put-row fn-lbc-directory-value-of-number-put-row fn-lbc-escape-of-number-put-row fn-lbc-flag-of-number-put-row fn-lbc-nov-at-of-number-put-row fn-lbc-membership-run-of-number-put-row fn-lbc-msgid-pool-range-of-number-put-row fn-lbtsf-nfix-natural)))))

(defthm fn-lbc-withdrawn-of-number-put-row
 (equal (fn-lbc-withdrawn i (fn-lbc-number-put-row numbers j fn-lbc)) (fn-lbc-withdrawn i fn-lbc))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'minimal-theory) '(fn-lbc-withdrawn fn-lbc-value-of-number-put-row fn-lbc-directory-value-of-number-put-row fn-lbc-escape-of-number-put-row fn-lbc-flag-of-number-put-row fn-lbc-nov-at-of-number-put-row fn-lbc-membership-run-of-number-put-row fn-lbc-msgid-pool-range-of-number-put-row fn-lbtsf-nfix-natural)))))

(defthm fn-lbc-served-row-of-number-put-row
 (equal (fn-lbc-served-row i (fn-lbc-number-put-row numbers j fn-lbc)) (fn-lbc-served-row i fn-lbc))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'minimal-theory) '(fn-lbc-served-row fn-lbc-value-of-number-put-row fn-lbc-directory-value-of-number-put-row fn-lbc-escape-of-number-put-row fn-lbc-flag-of-number-put-row fn-lbc-nov-at-of-number-put-row fn-lbc-membership-run-of-number-put-row fn-lbc-msgid-pool-range-of-number-put-row fn-lbtsf-nfix-natural fn-lbc-msgid-of-number-put-row fn-lbc-original-nov-of-number-put-row fn-lbc-render-nov-of-number-put-row fn-lbc-groups-of-number-put-row fn-lbc-numbers-of-number-put-row fn-lbc-xref-shift-prefix-of-number-put-row fn-lbc-withdrawn-of-number-put-row)))))

(defthm fn-lbc-home-entry-of-number-put-row
 (equal (fn-lbc-home-entry i (fn-lbc-number-put-row numbers j fn-lbc) log) (fn-lbc-home-entry i fn-lbc log))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'minimal-theory)
 '(fn-lbc-home-entry fn-lbc-loc0-of-number-put-row fn-lbc-loc1-of-number-put-row)))))

(defthm fn-lbc-row-corr-of-number-put-row
 (equal (fn-lbc-row-corr i row pm (fn-lbc-number-put-row numbers j fn-lbc) log) (fn-lbc-row-corr i row pm fn-lbc log))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'minimal-theory) '(fn-lbc-row-corr fn-lbc-loc0-of-number-put-row fn-lbc-loc1-of-number-put-row fn-lbc-home-entry-of-number-put-row fn-lbc-served-row-of-number-put-row fn-lbc-value-of-number-put-row fn-lbc-word-of-number-put-row fn-lbc-flag-of-number-put-row fn-lbc-xref-shift-prefix-of-number-put-row fn-lbc-directory-value-of-number-put-row fn-lbc-render-nov-of-number-put-row)))))

(defthm fn-lbc-rows-corr-of-number-put-row
 (equal (fn-lbc-rows-corr i old-rows pm (fn-lbc-number-put-row numbers j fn-lbc) log) (fn-lbc-rows-corr i old-rows pm fn-lbc log))
 :hints (("Goal" :induct (fn-lbc-rows-corr i old-rows pm fn-lbc log)
 :in-theory (union-theories (theory 'minimal-theory) '(fn-lbc-rows-corr fn-lbc-row-corr-of-number-put-row)))))

(defthm fn-lbc-nov-at-of-rebuild-summaries
 (equal (fn-lbc-nov-at read-j (fn-lbc-rebuild-summaries groups rows fn-lbc)) (fn-lbc-nov-at read-j fn-lbc))
 :hints (("Goal" :do-not-induct t
 :use ((:instance fn-lbc-nov-at-frame-by-definition (new (fn-lbc-rebuild-summaries groups rows fn-lbc)) (i read-j)))
 :in-theory (union-theories (theory 'minimal-theory)
 '(fn-lbwf-rebuild-summaries-field (:executable-counterpart natp) (:executable-counterpart equal) (:executable-counterpart member-equal))))))

(defthm fn-lbc-membership-run-of-rebuild-summaries
 (equal (fn-lbc-membership-run start count numbersp (fn-lbc-rebuild-summaries groups rows fn-lbc)) (fn-lbc-membership-run start count numbersp fn-lbc))
 :hints (("Goal" :do-not-induct t
 :use ((:instance fn-lbc-membership-run-frame-by-definition (new (fn-lbc-rebuild-summaries groups rows fn-lbc)) ))
 :in-theory (union-theories (theory 'minimal-theory)
 '(fn-lbwf-rebuild-summaries-field (:executable-counterpart natp) (:executable-counterpart equal) (:executable-counterpart member-equal))))))

(defthm fn-lbc-msgid-pool-range-of-rebuild-summaries
 (implies (and (natp off) (natp n)) (equal (fn-lbc-msgid-pool-range off n (fn-lbc-rebuild-summaries groups rows fn-lbc)) (fn-lbc-msgid-pool-range off n fn-lbc)))
 :hints (("Goal" :do-not-induct t
 :use ((:instance fn-lbc-msgid-pool-range-of-same-model (new (fn-lbc-rebuild-summaries groups rows fn-lbc))))
 :in-theory (union-theories (theory 'minimal-theory) '(fn-lbc-msgid-pool-model-frame-of-rebuild-summaries)))))

(defthm fn-lbc-msgid-of-rebuild-summaries
 (equal (fn-lbc-msgid i (fn-lbc-rebuild-summaries groups rows fn-lbc)) (fn-lbc-msgid i fn-lbc))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'minimal-theory) '(fn-lbc-msgid fn-lbc-value-of-rebuild-summaries fn-lbc-directory-value-of-rebuild-summaries fn-lbc-escape-of-rebuild-summaries fn-lbc-flag-of-rebuild-summaries fn-lbc-nov-at-of-rebuild-summaries fn-lbc-membership-run-of-rebuild-summaries fn-lbc-msgid-pool-range-of-rebuild-summaries fn-lbtsf-nfix-natural)))))

(defthm fn-lbc-original-nov-of-rebuild-summaries
 (equal (fn-lbc-original-nov i (fn-lbc-rebuild-summaries groups rows fn-lbc)) (fn-lbc-original-nov i fn-lbc))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'minimal-theory) '(fn-lbc-original-nov fn-lbc-value-of-rebuild-summaries fn-lbc-directory-value-of-rebuild-summaries fn-lbc-escape-of-rebuild-summaries fn-lbc-flag-of-rebuild-summaries fn-lbc-nov-at-of-rebuild-summaries fn-lbc-membership-run-of-rebuild-summaries fn-lbc-msgid-pool-range-of-rebuild-summaries fn-lbtsf-nfix-natural)))))

(defthm fn-lbc-render-nov-of-rebuild-summaries
 (equal (fn-lbc-render-nov i (fn-lbc-rebuild-summaries groups rows fn-lbc)) (fn-lbc-render-nov i fn-lbc))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'minimal-theory) '(fn-lbc-render-nov fn-lbc-value-of-rebuild-summaries fn-lbc-directory-value-of-rebuild-summaries fn-lbc-escape-of-rebuild-summaries fn-lbc-flag-of-rebuild-summaries fn-lbc-nov-at-of-rebuild-summaries fn-lbc-membership-run-of-rebuild-summaries fn-lbc-msgid-pool-range-of-rebuild-summaries fn-lbtsf-nfix-natural)))))

(defthm fn-lbc-groups-of-rebuild-summaries
 (equal (fn-lbc-groups i (fn-lbc-rebuild-summaries groups rows fn-lbc)) (fn-lbc-groups i fn-lbc))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'minimal-theory) '(fn-lbc-groups fn-lbc-value-of-rebuild-summaries fn-lbc-directory-value-of-rebuild-summaries fn-lbc-escape-of-rebuild-summaries fn-lbc-flag-of-rebuild-summaries fn-lbc-nov-at-of-rebuild-summaries fn-lbc-membership-run-of-rebuild-summaries fn-lbc-msgid-pool-range-of-rebuild-summaries fn-lbtsf-nfix-natural)))))

(defthm fn-lbc-numbers-of-rebuild-summaries
 (equal (fn-lbc-numbers i (fn-lbc-rebuild-summaries groups rows fn-lbc)) (fn-lbc-numbers i fn-lbc))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'minimal-theory) '(fn-lbc-numbers fn-lbc-value-of-rebuild-summaries fn-lbc-directory-value-of-rebuild-summaries fn-lbc-escape-of-rebuild-summaries fn-lbc-flag-of-rebuild-summaries fn-lbc-nov-at-of-rebuild-summaries fn-lbc-membership-run-of-rebuild-summaries fn-lbc-msgid-pool-range-of-rebuild-summaries fn-lbtsf-nfix-natural)))))

(defthm fn-lbc-xref-shift-prefix-of-rebuild-summaries
 (equal (fn-lbc-xref-shift-prefix i (fn-lbc-rebuild-summaries groups rows fn-lbc)) (fn-lbc-xref-shift-prefix i fn-lbc))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'minimal-theory) '(fn-lbc-xref-shift-prefix fn-lbc-value-of-rebuild-summaries fn-lbc-directory-value-of-rebuild-summaries fn-lbc-escape-of-rebuild-summaries fn-lbc-flag-of-rebuild-summaries fn-lbc-nov-at-of-rebuild-summaries fn-lbc-membership-run-of-rebuild-summaries fn-lbc-msgid-pool-range-of-rebuild-summaries fn-lbtsf-nfix-natural)))))

(defthm fn-lbc-withdrawn-of-rebuild-summaries
 (equal (fn-lbc-withdrawn i (fn-lbc-rebuild-summaries groups rows fn-lbc)) (fn-lbc-withdrawn i fn-lbc))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'minimal-theory) '(fn-lbc-withdrawn fn-lbc-value-of-rebuild-summaries fn-lbc-directory-value-of-rebuild-summaries fn-lbc-escape-of-rebuild-summaries fn-lbc-flag-of-rebuild-summaries fn-lbc-nov-at-of-rebuild-summaries fn-lbc-membership-run-of-rebuild-summaries fn-lbc-msgid-pool-range-of-rebuild-summaries fn-lbtsf-nfix-natural)))))

(defthm fn-lbc-served-row-of-rebuild-summaries
 (equal (fn-lbc-served-row i (fn-lbc-rebuild-summaries groups rows fn-lbc)) (fn-lbc-served-row i fn-lbc))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'minimal-theory) '(fn-lbc-served-row fn-lbc-value-of-rebuild-summaries fn-lbc-directory-value-of-rebuild-summaries fn-lbc-escape-of-rebuild-summaries fn-lbc-flag-of-rebuild-summaries fn-lbc-nov-at-of-rebuild-summaries fn-lbc-membership-run-of-rebuild-summaries fn-lbc-msgid-pool-range-of-rebuild-summaries fn-lbtsf-nfix-natural fn-lbc-msgid-of-rebuild-summaries fn-lbc-original-nov-of-rebuild-summaries fn-lbc-render-nov-of-rebuild-summaries fn-lbc-groups-of-rebuild-summaries fn-lbc-numbers-of-rebuild-summaries fn-lbc-xref-shift-prefix-of-rebuild-summaries fn-lbc-withdrawn-of-rebuild-summaries)))))

(defthm fn-lbc-home-entry-of-rebuild-summaries
 (equal (fn-lbc-home-entry i (fn-lbc-rebuild-summaries groups rows fn-lbc) log) (fn-lbc-home-entry i fn-lbc log))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'minimal-theory)
 '(fn-lbc-home-entry fn-lbc-loc0-of-rebuild-summaries fn-lbc-loc1-of-rebuild-summaries)))))

(defthm fn-lbc-row-corr-of-rebuild-summaries
 (equal (fn-lbc-row-corr i row pm (fn-lbc-rebuild-summaries groups rows fn-lbc) log) (fn-lbc-row-corr i row pm fn-lbc log))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'minimal-theory) '(fn-lbc-row-corr fn-lbc-loc0-of-rebuild-summaries fn-lbc-loc1-of-rebuild-summaries fn-lbc-home-entry-of-rebuild-summaries fn-lbc-served-row-of-rebuild-summaries fn-lbc-value-of-rebuild-summaries fn-lbc-word-of-rebuild-summaries fn-lbc-flag-of-rebuild-summaries fn-lbc-xref-shift-prefix-of-rebuild-summaries fn-lbc-directory-value-of-rebuild-summaries fn-lbc-render-nov-of-rebuild-summaries)))))

(defthm fn-lbc-rows-corr-of-rebuild-summaries
 (equal (fn-lbc-rows-corr i old-rows pm (fn-lbc-rebuild-summaries groups rows fn-lbc) log) (fn-lbc-rows-corr i old-rows pm fn-lbc log))
 :hints (("Goal" :induct (fn-lbc-rows-corr i old-rows pm fn-lbc log)
 :in-theory (union-theories (theory 'minimal-theory) '(fn-lbc-rows-corr fn-lbc-row-corr-of-rebuild-summaries)))))

(defthm fn-lbc-nov-at-of-reserve-slots
 (equal (fn-lbc-nov-at read-j (fn-lbc-reserve-slots capacity fn-lbc)) (fn-lbc-nov-at read-j fn-lbc))
 :hints (("Goal" :do-not-induct t
 :use ((:instance fn-lbc-nov-at-frame-by-definition (new (fn-lbc-reserve-slots capacity fn-lbc)) (i read-j)))
 :in-theory (union-theories (theory 'minimal-theory)
 '(fn-lbwf-reserve-slots-field (:executable-counterpart natp) (:executable-counterpart equal) (:executable-counterpart member-equal))))))

(defthm fn-lbc-membership-run-of-reserve-slots
 (equal (fn-lbc-membership-run start count numbersp (fn-lbc-reserve-slots capacity fn-lbc)) (fn-lbc-membership-run start count numbersp fn-lbc))
 :hints (("Goal" :do-not-induct t
 :use ((:instance fn-lbc-membership-run-frame-by-definition (new (fn-lbc-reserve-slots capacity fn-lbc)) ))
 :in-theory (union-theories (theory 'minimal-theory)
 '(fn-lbwf-reserve-slots-field (:executable-counterpart natp) (:executable-counterpart equal) (:executable-counterpart member-equal))))))

(defthm fn-lbc-msgid-pool-range-of-reserve-slots
 (implies (and (natp off) (natp n)) (equal (fn-lbc-msgid-pool-range off n (fn-lbc-reserve-slots capacity fn-lbc)) (fn-lbc-msgid-pool-range off n fn-lbc)))
 :hints (("Goal" :do-not-induct t
 :use ((:instance fn-lbc-msgid-pool-range-of-same-model (new (fn-lbc-reserve-slots capacity fn-lbc))))
 :in-theory (union-theories (theory 'minimal-theory) '(fn-lbc-msgid-pool-model-frame-of-reserve-slots)))))

(defthm fn-lbc-msgid-of-reserve-slots
 (equal (fn-lbc-msgid i (fn-lbc-reserve-slots capacity fn-lbc)) (fn-lbc-msgid i fn-lbc))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'minimal-theory) '(fn-lbc-msgid fn-lbc-value-of-reserve-slots fn-lbc-directory-value-of-reserve-slots fn-lbc-escape-of-reserve-slots fn-lbc-flag-of-reserve-slots fn-lbc-nov-at-of-reserve-slots fn-lbc-membership-run-of-reserve-slots fn-lbc-msgid-pool-range-of-reserve-slots fn-lbtsf-nfix-natural)))))

(defthm fn-lbc-original-nov-of-reserve-slots
 (equal (fn-lbc-original-nov i (fn-lbc-reserve-slots capacity fn-lbc)) (fn-lbc-original-nov i fn-lbc))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'minimal-theory) '(fn-lbc-original-nov fn-lbc-value-of-reserve-slots fn-lbc-directory-value-of-reserve-slots fn-lbc-escape-of-reserve-slots fn-lbc-flag-of-reserve-slots fn-lbc-nov-at-of-reserve-slots fn-lbc-membership-run-of-reserve-slots fn-lbc-msgid-pool-range-of-reserve-slots fn-lbtsf-nfix-natural)))))

(defthm fn-lbc-render-nov-of-reserve-slots
 (equal (fn-lbc-render-nov i (fn-lbc-reserve-slots capacity fn-lbc)) (fn-lbc-render-nov i fn-lbc))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'minimal-theory) '(fn-lbc-render-nov fn-lbc-value-of-reserve-slots fn-lbc-directory-value-of-reserve-slots fn-lbc-escape-of-reserve-slots fn-lbc-flag-of-reserve-slots fn-lbc-nov-at-of-reserve-slots fn-lbc-membership-run-of-reserve-slots fn-lbc-msgid-pool-range-of-reserve-slots fn-lbtsf-nfix-natural)))))

(defthm fn-lbc-groups-of-reserve-slots
 (equal (fn-lbc-groups i (fn-lbc-reserve-slots capacity fn-lbc)) (fn-lbc-groups i fn-lbc))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'minimal-theory) '(fn-lbc-groups fn-lbc-value-of-reserve-slots fn-lbc-directory-value-of-reserve-slots fn-lbc-escape-of-reserve-slots fn-lbc-flag-of-reserve-slots fn-lbc-nov-at-of-reserve-slots fn-lbc-membership-run-of-reserve-slots fn-lbc-msgid-pool-range-of-reserve-slots fn-lbtsf-nfix-natural)))))

(defthm fn-lbc-numbers-of-reserve-slots
 (equal (fn-lbc-numbers i (fn-lbc-reserve-slots capacity fn-lbc)) (fn-lbc-numbers i fn-lbc))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'minimal-theory) '(fn-lbc-numbers fn-lbc-value-of-reserve-slots fn-lbc-directory-value-of-reserve-slots fn-lbc-escape-of-reserve-slots fn-lbc-flag-of-reserve-slots fn-lbc-nov-at-of-reserve-slots fn-lbc-membership-run-of-reserve-slots fn-lbc-msgid-pool-range-of-reserve-slots fn-lbtsf-nfix-natural)))))

(defthm fn-lbc-xref-shift-prefix-of-reserve-slots
 (equal (fn-lbc-xref-shift-prefix i (fn-lbc-reserve-slots capacity fn-lbc)) (fn-lbc-xref-shift-prefix i fn-lbc))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'minimal-theory) '(fn-lbc-xref-shift-prefix fn-lbc-value-of-reserve-slots fn-lbc-directory-value-of-reserve-slots fn-lbc-escape-of-reserve-slots fn-lbc-flag-of-reserve-slots fn-lbc-nov-at-of-reserve-slots fn-lbc-membership-run-of-reserve-slots fn-lbc-msgid-pool-range-of-reserve-slots fn-lbtsf-nfix-natural)))))

(defthm fn-lbc-withdrawn-of-reserve-slots
 (equal (fn-lbc-withdrawn i (fn-lbc-reserve-slots capacity fn-lbc)) (fn-lbc-withdrawn i fn-lbc))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'minimal-theory) '(fn-lbc-withdrawn fn-lbc-value-of-reserve-slots fn-lbc-directory-value-of-reserve-slots fn-lbc-escape-of-reserve-slots fn-lbc-flag-of-reserve-slots fn-lbc-nov-at-of-reserve-slots fn-lbc-membership-run-of-reserve-slots fn-lbc-msgid-pool-range-of-reserve-slots fn-lbtsf-nfix-natural)))))

(defthm fn-lbc-served-row-of-reserve-slots
 (equal (fn-lbc-served-row i (fn-lbc-reserve-slots capacity fn-lbc)) (fn-lbc-served-row i fn-lbc))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'minimal-theory) '(fn-lbc-served-row fn-lbc-value-of-reserve-slots fn-lbc-directory-value-of-reserve-slots fn-lbc-escape-of-reserve-slots fn-lbc-flag-of-reserve-slots fn-lbc-nov-at-of-reserve-slots fn-lbc-membership-run-of-reserve-slots fn-lbc-msgid-pool-range-of-reserve-slots fn-lbtsf-nfix-natural fn-lbc-msgid-of-reserve-slots fn-lbc-original-nov-of-reserve-slots fn-lbc-render-nov-of-reserve-slots fn-lbc-groups-of-reserve-slots fn-lbc-numbers-of-reserve-slots fn-lbc-xref-shift-prefix-of-reserve-slots fn-lbc-withdrawn-of-reserve-slots)))))

(defthm fn-lbc-home-entry-of-reserve-slots
 (equal (fn-lbc-home-entry i (fn-lbc-reserve-slots capacity fn-lbc) log) (fn-lbc-home-entry i fn-lbc log))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'minimal-theory)
 '(fn-lbc-home-entry fn-lbc-loc0-of-reserve-slots fn-lbc-loc1-of-reserve-slots)))))

(defthm fn-lbc-row-corr-of-reserve-slots
 (equal (fn-lbc-row-corr i row pm (fn-lbc-reserve-slots capacity fn-lbc) log) (fn-lbc-row-corr i row pm fn-lbc log))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'minimal-theory) '(fn-lbc-row-corr fn-lbc-loc0-of-reserve-slots fn-lbc-loc1-of-reserve-slots fn-lbc-home-entry-of-reserve-slots fn-lbc-served-row-of-reserve-slots fn-lbc-value-of-reserve-slots fn-lbc-word-of-reserve-slots fn-lbc-flag-of-reserve-slots fn-lbc-xref-shift-prefix-of-reserve-slots fn-lbc-directory-value-of-reserve-slots fn-lbc-render-nov-of-reserve-slots)))))

(defthm fn-lbc-rows-corr-of-reserve-slots
 (equal (fn-lbc-rows-corr i old-rows pm (fn-lbc-reserve-slots capacity fn-lbc) log) (fn-lbc-rows-corr i old-rows pm fn-lbc log))
 :hints (("Goal" :induct (fn-lbc-rows-corr i old-rows pm fn-lbc log)
 :in-theory (union-theories (theory 'minimal-theory) '(fn-lbc-rows-corr fn-lbc-row-corr-of-reserve-slots)))))
