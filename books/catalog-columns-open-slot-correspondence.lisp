; Derived constructor support; local algebra does not escape this book.
(in-package "ACL2")
(include-book "catalog-columns-slot-build-start")

(defthm fn-lb-slot-build-start-rows-corr
 (implies (and (fn-lbc-p fn-lbc) (fn-cat-rowsp rows) (fn-lbc-rows-log-guardp rows log)
 (fn-lb-log-layoutp log) (fn-lb-log-model-segsp log) (fn-lb-log-rows-sourcep rows log))
 (fn-lbc-rows-corr 0 rows 0 (fn-lb-slot-build-start rows log fn-lbc) log))
 :hints (("Goal" :do-not-induct t
 :use ((:instance fn-lbc-rebuild-rows-establishes-rows-corr (fn-lbc (fn-lbc-clear-columns fn-lbc))))
 :in-theory (union-theories (theory 'ground-zero)
 '(fn-lb-slot-build-start fn-lbc-rows-corr-of-index-slots fn-lbc-rows-corr-of-reserve-slots
 fn-lbc-rows-corr-of-summary-groups-update fn-lbc-rows-corr-of-rebuild-summaries
 fn-lbc-p-of-clear-columns fn-lbc-p-of-rebuild-rows fn-lbc-p-of-rebuild-summaries
 fn-lbc-p-of-update-summary-groups fn-lbc-p-of-reserve-slots
 fn-lbc-count-of-clear-columns fn-lbc-count-of-rebuild-rows fn-lbc-count-of-rebuild-summaries
 fn-lbc-count-of-summary-groups-update fn-lbc-count-of-reserve-slots
 fn-lb-columns-pool-layoutp-of-clear-columns fn-lb-columns-directory-alignedp-of-clear-columns)))))

(defthm fn-lb-slot-build-start-row-hashes
 (implies (and (fn-lbc-p fn-lbc) (fn-cat-rowsp rows) (fn-lbc-rows-log-guardp rows log)
 (fn-lb-log-layoutp log) (fn-lb-log-model-segsp log) (fn-lb-log-rows-sourcep rows log)) (fn-lb-slot-row-hashesp rows 0 (fn-lb-slot-build-start rows log fn-lbc)))
 :hints (("Goal" :do-not-induct t
 :use ((:instance fn-lb-slot-build-start-rows-corr)
 (:instance fn-lb-slot-row-hashesp-from-rows-corr
 (start 0) (pm 0) (fn-lbc (fn-lb-slot-build-start rows log fn-lbc))))
 :in-theory (theory 'ground-zero))))

(defthm fn-lbc-slots-corr-of-open-rebuild
 (implies (and (fn-lbc-p fn-lbc) (fn-cat-rowsp rows) (fn-lbc-rows-log-guardp rows log)
 (fn-lb-log-layoutp log) (fn-lb-log-model-segsp log) (fn-lb-log-rows-sourcep rows log)) (fn-lbc-slots-corr (fn-lbc-open-rebuild rows log fn-lbc) rows))
 :hints (("Goal" :do-not-induct t
 :use ((:instance fn-lbc-index-slots-refines-canonical (i 0)
 (table (make-list (+ 1 (* 2 (len rows))) :initial-element 0))
 (fn-lbc (fn-lb-slot-build-start rows log fn-lbc)))
 (:instance fn-lb-slot-zero-table-shape (n (+ 1 (* 2 (len rows))))))
 :in-theory (union-theories (theory 'ground-zero)
 '(fn-lbc-slots-corr fn-lbc-open-rebuild-by-slot-start-definition
 fn-lbc-slot-count-of-index-slots fn-lb-slot-build-start-capacity
 fn-lb-slot-build-start-row-hashes fn-lb-slot-build-start-zero-cells
 fn-lb-slot-build-start-owner-keys fn-lb-slot-owner-keys-below fn-lb-slot-build-start-unindexed posp natp)))))
