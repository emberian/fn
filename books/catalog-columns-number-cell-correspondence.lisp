; Derived constructor support; local algebra does not escape this book.
(in-package "ACL2")
(include-book "catalog-columns-number-key-layout")

(local (defthm fn-lbncc-hons-assoc-cons-key
 (equal (cdr (hons-assoc-equal (cons group number) table))
        (cdr (assoc-equal (cons group number) table)))
 :hints (("Goal" :induct (len table) :in-theory (union-theories (theory 'ground-zero)
 '(len hons-assoc-equal assoc-equal))))))

(defthm fn-lbc-number-get-by-table
 (equal (fn-lbc-number-get group number fn-lbc)
        (cdr (assoc-equal (cons group number) (fn-lb-number-table fn-lbc))))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'ground-zero)
 '(fn-lbc-number-get fn-lbc-number-store fn-dmap-get fn-dmap$a-get fn-lb-number-table fn-lbncc-hons-assoc-cons-key)))))

(defthm fn-lbc-number-cell-of-open-rebuild
 (implies (and (fn-cat-rowsp rows) (consp key))
 (equal (cdr (assoc-equal key (fn-lb-number-table (fn-lbc-open-rebuild rows log fn-lbc))))
        (fn-cat-number-seq (car key) (cdr key) rows 0)))
 :hints (("Goal" :do-not-induct t
 :use ((:instance fn-lbc-number-get-of-open-rebuild (group (car key)) (number (cdr key)))
       (:instance fn-lbc-number-get-by-table (group (car key)) (number (cdr key))
        (fn-lbc (fn-lbc-open-rebuild rows log fn-lbc))))
 :in-theory (theory 'ground-zero))))

(defthm fn-lbc-number-cells-corr-for-open-rebuild
 (implies (and (fn-cat-rowsp rows) (fn-lb-number-keysp keys))
 (fn-lbc-number-cells-corr keys (fn-lb-number-table (fn-lbc-open-rebuild rows log fn-lbc)) rows))
 :hints (("Goal" :induct (len keys) :in-theory (union-theories (theory 'ground-zero)
 '(len fn-lb-number-keysp fn-lbc-number-cells-corr fn-lbc-number-cell-of-open-rebuild)))))

(defthm fn-lbc-number-cells-corr-of-open-rebuild
 (implies (fn-cat-rowsp rows)
 (fn-lbc-number-cells-corr (fn-lb-number-table (fn-lbc-open-rebuild rows log fn-lbc))
                         (fn-lb-number-table (fn-lbc-open-rebuild rows log fn-lbc)) rows))
 :hints (("Goal" :do-not-induct t
 :use ((:instance fn-lbc-number-cells-corr-for-open-rebuild
        (keys (fn-lb-number-table (fn-lbc-open-rebuild rows log fn-lbc)))))
 :in-theory (union-theories (theory 'minimal-theory) '(fn-lb-number-keysp-of-open-rebuild)))))
