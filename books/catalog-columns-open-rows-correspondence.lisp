; Derived constructor support; local algebra does not escape this book.
(in-package "ACL2")
(include-book "catalog-columns-summary-group-frames")

(defthm fn-lbc-open-rebuild-establishes-rows-corr
 (implies (and (fn-lbc-p fn-lbc) (fn-cat-rowsp rows) (fn-lbc-rows-log-guardp rows log)
 (fn-lb-log-layoutp log) (fn-lb-log-model-segsp log) (fn-lb-log-rows-sourcep rows log))
 (fn-lbc-rows-corr 0 rows 0 (fn-lbc-open-rebuild rows log fn-lbc) log))
 :hints (("Goal" :do-not-induct t
 :use ((:instance fn-lbc-rebuild-rows-establishes-rows-corr (fn-lbc (fn-lbc-clear-columns fn-lbc))))
 :in-theory (union-theories (theory 'ground-zero)
 '(fn-lbc-open-rebuild fn-lbc-rows-corr-of-index-slots fn-lbc-rows-corr-of-reserve-slots
 fn-lbc-rows-corr-of-summary-groups-update fn-lbc-rows-corr-of-rebuild-summaries
 fn-lbc-p-of-clear-columns fn-lbc-p-of-rebuild-rows fn-lbc-p-of-rebuild-summaries
 fn-lbc-p-of-update-summary-groups fn-lbc-p-of-reserve-slots
 fn-lbc-count-of-clear-columns fn-lbc-count-of-rebuild-rows fn-lbc-count-of-rebuild-summaries
 fn-lbc-count-of-summary-groups-update fn-lbc-count-of-reserve-slots
 fn-lb-columns-pool-layoutp-of-clear-columns fn-lb-columns-directory-alignedp-of-clear-columns)))))
