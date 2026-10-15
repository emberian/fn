; Derived constructor support; local algebra does not escape this book.
(in-package "ACL2")
(include-book "catalog-columns-slot-put-storage")

(local (defun-nx fn-lbscu-index-induct (table base j)
 (declare (xargs :measure (nfix j)))
 (if (and (consp table) (not (zp j)))
 (fn-lbscu-index-induct (cdr table) (+ 1 (nfix base)) (- j 1)) (list table base))))

(defthm fn-lbc-slot-cells-corr-nth
 (implies (and (fn-lbc-slot-cells-corr table base fn-lbc) (natp base) (natp j) (< j (len table)))
 (equal (fn-lbc-slot-word (+ base j) fn-lbc) (nth j table)))
 :hints (("Goal" :induct (fn-lbscu-index-induct table base j)
 :in-theory (union-theories (theory 'ground-zero)
 '(fn-lbscu-index-induct fn-lbc-slot-cells-corr nth natp nfix zp len)))))

(local (defun-nx fn-lbscu-overwrite (table base slot ordinal)
 (if (consp table)
 (cons (if (equal (nfix base) slot) ordinal (car table))
       (fn-lbscu-overwrite (cdr table) (+ 1 (nfix base)) slot ordinal)) nil)))

(local (defthm fn-lbscu-cells-corr-overwrite
 (implies (and (fn-lbc-slot-cells-corr table base fn-lbc) (natp base)
 (<= (+ base (len table)) (fn-lbc-slot-count fn-lbc))
 (posp ordinal) (natp slot) (< slot (fn-lbc-slot-count fn-lbc))
 (not (member-equal (- ordinal 1) (fn-lbc-slot-escape-keys fn-lbc)))
 (not (fn-lbc-escape (- ordinal 1) :msgid-slot fn-lbc)))
 (fn-lbc-slot-cells-corr (fn-lbscu-overwrite table base slot ordinal) base
                       (fn-lbc-slot-put slot ordinal fn-lbc)))
 :hints (("Goal" :induct (fn-lbscu-overwrite table base slot ordinal)
 :in-theory (union-theories (theory 'ground-zero)
 '(fn-lbscu-overwrite fn-lbc-slot-cells-corr fn-lbc-slot-word-of-fresh-slot-put
 len natp nfix posp))))))

(local (defthm fn-lbscu-overwrite-before-base
 (implies (and (natp base) (< slot base) (true-listp table))
 (equal (fn-lbscu-overwrite table base slot ordinal) table))
 :hints (("Goal" :induct (fn-lbscu-overwrite table base slot ordinal)
 :in-theory (union-theories (theory 'ground-zero)
 '(fn-lbscu-overwrite true-listp natp nfix))))))

(local (defthm fn-lbscu-overwrite-is-update
 (implies (and (natp base) (natp j) (< j (len table)) (true-listp table))
 (equal (fn-lbscu-overwrite table base (+ base j) ordinal) (update-nth j ordinal table)))
 :hints (("Goal" :induct (fn-lbscu-index-induct table base j)
 :in-theory (union-theories (theory 'ground-zero)
 '(fn-lbscu-index-induct fn-lbscu-overwrite fn-lbscu-overwrite-before-base update-nth len natp nfix zp true-listp))))))

(defthm fn-lbc-slot-cells-corr-of-fresh-slot-put
 (implies (and (fn-lbc-slot-cells-corr table 0 fn-lbc)
 (true-listp table) (equal (len table) (fn-lbc-slot-count fn-lbc))
 (posp ordinal) (natp slot) (< slot (len table))
 (not (member-equal (- ordinal 1) (fn-lbc-slot-escape-keys fn-lbc)))
 (not (fn-lbc-escape (- ordinal 1) :msgid-slot fn-lbc)))
 (fn-lbc-slot-cells-corr (update-nth slot ordinal table) 0 (fn-lbc-slot-put slot ordinal fn-lbc)))
 :hints (("Goal" :do-not-induct t
 :use ((:instance fn-lbscu-cells-corr-overwrite (base 0))
       (:instance fn-lbscu-overwrite-is-update (base 0) (j slot)))
 :in-theory (theory 'ground-zero))))

(defthm fn-lbc-slot-count-of-slot-insert
 (equal (fn-lbc-slot-count (fn-lbc-slot-insert i slot fuel fn-lbc)) (fn-lbc-slot-count fn-lbc))
 :hints (("Goal" :induct (fn-lbc-slot-insert i slot fuel fn-lbc)
 :in-theory (union-theories (theory 'ground-zero) '(fn-lbc-slot-insert fn-lbc-slot-count-of-slot-put)))))

(defthm fn-lbc-slot-count-of-index-slots
 (equal (fn-lbc-slot-count (fn-lbc-index-slots i n fn-lbc)) (fn-lbc-slot-count fn-lbc))
 :hints (("Goal" :induct (fn-lbc-index-slots i n fn-lbc)
 :in-theory (union-theories (theory 'ground-zero) '(fn-lbc-index-slots fn-lbc-slot-count-of-slot-insert)))))
