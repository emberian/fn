; Resident number bindings; independent of command and cursor adapters.
(in-package "ACL2")
(include-book "catalog-columns-row-correspondence")

(local (defthm fn-lbr11-number-cells-lookup
 (implies (and (fn-lbc-number-cells-corr keys table rows)
               (assoc-equal (cons group number) keys))
  (equal (cdr (assoc-equal (cons group number) table))
         (fn-cat-number-seq group number rows 0)))
 :hints (("Goal" :induct (fn-lbc-number-cells-corr keys table rows)
 :in-theory (union-theories (theory 'ground-zero) '(fn-lbc-number-cells-corr assoc-equal))))))

(local (defthm fn-lbr11-hons-assoc-is-assoc-for-cons-key
 (implies (consp key) (equal (hons-assoc-equal key table) (assoc-equal key table)))
 :hints (("Goal" :induct (hons-assoc-equal key table)
 :in-theory (union-theories (theory 'ground-zero) '(hons-assoc-equal assoc-equal))))))

(local (defthm fn-lbr11-number-get-at-present-key
 (implies (and (fn-lbc-tables-corr fn-lbc rows)
  (assoc-equal (cons group number) (nth 0 (nth *fn-lbc-number-store* fn-lbc))))
 (equal (fn-lbc-number-get group number fn-lbc) (fn-cat-number-seq group number rows 0)))
 :hints (("Goal" :use ((:instance fn-lbr11-number-cells-lookup
  (keys (nth 0 (nth *fn-lbc-number-store* fn-lbc)))
  (table (nth 0 (nth *fn-lbc-number-store* fn-lbc)))))
 :in-theory (union-theories (theory 'ground-zero)
  '(fn-lbc-tables-corr fn-lbc-number-get fn-lbc-number-store fn-dmap-get fn-dmap$a-get
    fn-lbr11-hons-assoc-is-assoc-for-cons-key))))))

(local (defthm fn-lbr11-number-get-at-absent-key
 (implies (not (assoc-equal (cons group number) (nth 0 (nth *fn-lbc-number-store* fn-lbc))))
  (equal (fn-lbc-number-get group number fn-lbc) nil))
 :hints (("Goal" :in-theory (union-theories (theory 'ground-zero)
  '(fn-lbc-number-get fn-lbc-number-store fn-dmap-get fn-dmap$a-get fn-lbr11-hons-assoc-is-assoc-for-cons-key))))))

(local (defthm fn-lbr11-covered-number-key-lookup
 (implies (and (fn-lbc-number-keys-covered numbers rows fn-lbc)
               (fn-cat-assoc group numbers))
  (equal (fn-lbc-number-get group (cdr (fn-cat-assoc group numbers)) fn-lbc)
         (fn-cat-number-seq group (cdr (fn-cat-assoc group numbers)) rows 0)))
 :hints (("Goal" :induct (fn-lbc-number-keys-covered numbers rows fn-lbc)
 :in-theory (union-theories (theory 'ground-zero) '(fn-lbc-number-keys-covered fn-cat-assoc))))))

(local (defthm fn-lbr11-covered-row-number-lookup
 (implies (and (fn-lbc-number-rows-covered rest rows fn-lbc)
               (fn-cat-number-seq group number rest base))
  (equal (fn-lbc-number-get group number fn-lbc)
         (fn-cat-number-seq group number rows 0)))
 :hints (("Goal" :induct (fn-cat-number-seq group number rest base)
 :in-theory (union-theories (theory 'ground-zero)
  '(fn-lbc-number-rows-covered fn-cat-number-seq fn-held-number-in
    fn-lbr11-covered-number-key-lookup))))))

(defthm fn-lbc-number-get-is-abstract
 (implies (and (fn-lbc-p fn-lbc) (fn-cat$ap rows) (fn-lbc-corr fn-lbc rows log))
  (equal (fn-lbc-number-get group number fn-lbc)
         (fn-cat-number-seq group number rows 0)))
 :hints (("Goal" :do-not-induct t
 :cases ((fn-cat-number-seq group number rows 0)
         (and (not (fn-cat-number-seq group number rows 0))
              (assoc-equal (cons group number) (nth 0 (nth *fn-lbc-number-store* fn-lbc)))))
 :use ((:instance fn-lbr11-covered-row-number-lookup (rest rows) (base 0)))
 :in-theory (union-theories (theory 'ground-zero)
  '(fn-lbc-corr fn-lbr11-number-get-at-present-key fn-lbr11-number-get-at-absent-key)))))
