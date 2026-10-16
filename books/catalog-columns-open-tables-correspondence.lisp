; Derived constructor support; local algebra does not escape this book.
(in-package "ACL2")
(include-book "catalog-columns-summary-cell-correspondence")

(defthm fn-lbc-tables-corr-of-open-rebuild
  (implies (fn-cat-rowsp rows) (fn-lbc-tables-corr (fn-lbc-open-rebuild rows log fn-lbc) rows))
  :hints (("Goal" :do-not-induct t
   :use ((:instance fn-lbc-number-cells-corr-of-open-rebuild)
         (:instance fn-lbc-summary-cells-corr-of-open-rebuild))
   :in-theory (union-theories (theory 'ground-zero)
    '(fn-lbc-tables-corr fn-lb-number-table fn-lb-summary-table)))))
