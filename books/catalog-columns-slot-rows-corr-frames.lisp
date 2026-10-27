; Derived constructor support; local algebra does not escape this book.
(in-package "ACL2")
(include-book "catalog-columns-slot-corr-frames")

(defthm fn-lbc-rows-corr-of-slot-put
 (implies (and (fn-lbc-p fn-lbc) (natp base) (<= (+ base (len rows)) (fn-lbc-count fn-lbc)))
  (equal (fn-lbc-rows-corr base rows pm (fn-lbc-slot-put slot ordinal fn-lbc) log)
         (fn-lbc-rows-corr base rows pm fn-lbc log)))
 :hints (("Goal" :induct (fn-lbc-rows-corr base rows pm fn-lbc log)
  :in-theory (set-difference-theories (union-theories (theory 'ground-zero)
   '(fn-lbc-rows-corr fn-lbc-row-corr-of-slot-put fn-lbc-count-of-slot-put
     len nfix (:type-prescription fn-lbc-count))) '((tau-system))))))

(defthm fn-lbc-rows-corr-of-slot-insert
 (implies (and (fn-lbc-p fn-lbc) (natp base) (<= (+ base (len rows)) (fn-lbc-count fn-lbc)))
  (equal (fn-lbc-rows-corr base rows pm (fn-lbc-slot-insert j slot fuel fn-lbc) log)
         (fn-lbc-rows-corr base rows pm fn-lbc log)))
 :hints (("Goal" :induct (fn-lbc-rows-corr base rows pm fn-lbc log)
  :in-theory (set-difference-theories (union-theories (theory 'ground-zero)
   '(fn-lbc-rows-corr fn-lbc-row-corr-of-slot-insert fn-lbc-count-of-slot-insert
     len nfix (:type-prescription fn-lbc-count))) '((tau-system))))))

(defthm fn-lbc-rows-corr-of-index-slots
 (implies (and (fn-lbc-p fn-lbc) (natp base) (<= (+ base (len rows)) (fn-lbc-count fn-lbc)))
  (equal (fn-lbc-rows-corr base rows pm (fn-lbc-index-slots j end fn-lbc) log)
         (fn-lbc-rows-corr base rows pm fn-lbc log)))
 :hints (("Goal" :induct (fn-lbc-rows-corr base rows pm fn-lbc log)
  :in-theory (set-difference-theories (union-theories (theory 'ground-zero)
   '(fn-lbc-rows-corr fn-lbc-row-corr-of-index-slots fn-lbc-count-of-index-slots
     len nfix (:type-prescription fn-lbc-count))) '((tau-system))))))
