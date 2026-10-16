; Derived constructor support; local algebra does not escape this book.
(in-package "ACL2")
(include-book "catalog-columns-number-row-readback")

(local (defthm fn-lbnrb-count-natural
 (natp (fn-lbc-count fn-lbc)) :rule-classes :type-prescription
 :hints (("Goal" :in-theory (union-theories (theory 'ground-zero)
 '(fn-lbc-count fn-lbc-row-store fn-lbc-rowwords-count-is-len))))))

(local (defthm fn-lbnrb-cat-assoc-number-positive
 (implies (and (fn-held-numbersp numbers) (fn-cat-assoc group numbers))
 (and (consp (fn-cat-assoc group numbers)) (posp (cdr (fn-cat-assoc group numbers)))))
 :hints (("Goal" :induct (fn-cat-assoc group numbers)
 :in-theory (union-theories (theory 'ground-zero) '(fn-held-numbersp fn-cat-assoc))))))

(local (defthm fn-lbnrb-row-number-shape
 (implies (fn-cat-rowp row) (fn-held-numbersp (fn-held-numbers row)))
 :hints (("Goal" :in-theory (enable fn-cat-rowp)))))

(defthm fn-lbc-number-get-of-number-put-row
 (implies (fn-held-numbersp numbers)
 (equal (fn-lbc-number-get group number (fn-lbc-number-put-row numbers i fn-lbc))
  (let ((old (fn-lbc-number-get group number fn-lbc)) (pair (fn-cat-assoc group numbers)))
   (if (natp old) old (if (and (consp pair) (equal number (cdr pair))) i old)))))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'ground-zero)
 '(fn-lbc-number-put-row fn-lbc-number-get-of-number-put-row-seen)))))

(defthm fn-lbc-number-get-of-row-numbers
 (implies (fn-cat-rowp row)
 (equal (fn-lbc-number-get group number (fn-lbc-number-put-row (fn-held-numbers row) i fn-lbc))
  (let ((old (fn-lbc-number-get group number fn-lbc)) (b (fn-held-number-in group row)))
   (if (natp old) old (if (and b (equal b number)) i old)))))
 :hints (("Goal" :do-not-induct t
 :use ((:instance fn-lbnrb-cat-assoc-number-positive (numbers (fn-held-numbers row))))
 :in-theory (union-theories (theory 'ground-zero)
 '(fn-held-number-in fn-lbc-number-get-of-number-put-row fn-lbnrb-row-number-shape posp)))))

(local (defthm fn-lbnrb-reference-index-type
 (implies (natp i) (or (null (fn-cat-number-seq group number rows i))
                       (natp (fn-cat-number-seq group number rows i))))
 :hints (("Goal" :induct (fn-cat-number-seq group number rows i)
 :in-theory (union-theories (theory 'ground-zero) '(fn-cat-number-seq))))))

(defthm fn-lbc-number-get-of-rebuild-rows
 (implies (fn-cat-rowsp rows)
 (equal (fn-lbc-number-get group number (fn-lbc-rebuild-rows rows log fn-lbc))
  (let ((old (fn-lbc-number-get group number fn-lbc))
        (q (fn-cat-number-seq group number rows (fn-lbc-count fn-lbc))))
   (if (natp old) old (if q q old)))))
 :hints (("Goal" :induct (fn-lbc-rebuild-rows rows log fn-lbc)
 :in-theory (union-theories (theory 'ground-zero)
 '(fn-lbc-rebuild-rows fn-cat-rowsp fn-cat-number-seq fn-lbc-number-get-of-row-numbers
 fn-lbc-number-get-of-append-row fn-lbc-count-of-number-put-row fn-lbc-count-of-append-row
 (:type-prescription fn-lbnrb-count-natural))))))
