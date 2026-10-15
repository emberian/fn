; Derived constructor support; local algebra does not escape this book.
(in-package "ACL2")
(include-book "catalog-columns-open-slot-correspondence")

(defthm fn-lbc-count-of-open-rebuild
 (equal (fn-lbc-count (fn-lbc-open-rebuild rows log fn-lbc)) (len rows))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'ground-zero)
 '(fn-lbc-open-rebuild fn-lbc-count-of-index-slots fn-lbc-count-of-reserve-slots
 fn-lbc-count-of-summary-groups-update fn-lbc-count-of-rebuild-summaries
 fn-lbc-count-of-rebuild-rows fn-lbc-count-of-clear-columns)))))

(local (defthm fn-lbocc-summary-groups-of-reserve-slots
 (equal (fn-lbc-summary-groups (fn-lbc-reserve-slots n fn-lbc)) (fn-lbc-summary-groups fn-lbc))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'minimal-theory)
 '(fn-lbc-summary-groups fn-lbwf-reserve-slots-field (:executable-counterpart natp)
 (:executable-counterpart equal) (:executable-counterpart member-equal)))))))

(local (defthm fn-lbocc-summary-groups-of-index-slots
 (equal (fn-lbc-summary-groups (fn-lbc-index-slots i n fn-lbc)) (fn-lbc-summary-groups fn-lbc))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'minimal-theory)
 '(fn-lbc-summary-groups fn-lbwf-index-slots-field (:executable-counterpart natp)
 (:executable-counterpart equal) (:executable-counterpart member-equal)))))))

(local (defthm fn-lbocc-summary-groups-update
 (equal (fn-lbc-summary-groups (update-fn-lbc-summary-groups groups fn-lbc)) groups)
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
 '(fn-lbc-summary-groups update-fn-lbc-summary-groups fn-dm-nth-update-nth
 (:executable-counterpart nfix) (:executable-counterpart equal)))))))

(defthm fn-lbc-summary-groups-of-open-rebuild
 (equal (fn-lbc-summary-groups (fn-lbc-open-rebuild rows log fn-lbc)) (fn-lbc-row-group-keys rows))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'ground-zero)
 '(fn-lbc-open-rebuild fn-lbocc-summary-groups-of-index-slots
 fn-lbocc-summary-groups-of-reserve-slots fn-lbocc-summary-groups-update)))))

(local (defthm fn-lbr13-directory-alignedp-of-summary-groups-update
 (equal (fn-lb-columns-directory-alignedp (update-fn-lbc-summary-groups groups fn-lbc))
        (fn-lb-columns-directory-alignedp fn-lbc))
 :hints (("Goal" :do-not-induct t
 :use ((:instance fn-lbc-count-of-summary-groups-update))
 :in-theory (union-theories (theory 'ground-zero)
 '(fn-lb-columns-directory-alignedp update-fn-lbc-summary-groups fn-dm-nth-update-nth))))))

(defthm fn-lb-columns-directory-alignedp-of-open-rebuild
 (fn-lb-columns-directory-alignedp (fn-lbc-open-rebuild rows log fn-lbc))
 :hints (("Goal" :do-not-induct t
 :in-theory (union-theories (theory 'ground-zero)
 '(fn-lbc-open-rebuild fn-lb-columns-directory-alignedp-of-index-slots
 fn-lb-columns-directory-alignedp-of-reserve-slots
 fn-lb-columns-directory-alignedp-of-rebuild-summaries
 fn-lb-columns-directory-alignedp-of-rebuild-rows
 fn-lb-columns-directory-alignedp-of-clear-columns
 fn-lbr13-directory-alignedp-of-summary-groups-update)))))

(defthm fn-lbc-corr-of-open-rebuild
 (implies (and (fn-lbc-p fn-lbc) (fn-cat-rowsp rows) (fn-lbc-rows-log-guardp rows log)
 (fn-lb-log-layoutp log) (fn-lb-log-model-segsp log) (fn-lb-log-rows-sourcep rows log))
 (fn-lbc-corr (fn-lbc-open-rebuild rows log fn-lbc) rows log))
 :hints (("Goal" :do-not-induct t
 :use ((:instance fn-lb-columns-directory-alignedp-of-open-rebuild)
       (:instance fn-lbc-open-rebuild-establishes-rows-corr)
 (:instance fn-lbc-tables-corr-of-open-rebuild)
 (:instance fn-lbc-number-rows-covered-of-open-rebuild (rest rows))
 (:instance fn-lbc-slots-corr-of-open-rebuild)
 (:instance fn-lbc-summaries-corr-of-open-rebuild))
 :in-theory (union-theories (theory 'ground-zero)
 '(fn-lbc-corr fn-lbc-directory-count-is-len fn-lb-columns-directory-alignedp fn-lbc-count-of-open-rebuild fn-lbc-summary-groups-of-open-rebuild)))))
