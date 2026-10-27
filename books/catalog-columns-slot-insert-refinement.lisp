; Derived constructor support; local algebra does not escape this book.
(in-package "ACL2")
(include-book "catalog-columns-slot-cells-update")
(local (include-book "arithmetic-5/top" :dir :system))

(local (defthm fn-lbsin-next-slot-natural
 (natp (mod (+ 1 (nfix slot)) (max 1 (len table))))))

(local (defthm fn-lbsin-next-slot-below
 (< (mod (+ 1 (nfix slot)) (max 1 (len table))) (max 1 (len table)))
 :rule-classes :linear))

(local (defthm fn-lbsin-table-read
 (implies (and (fn-lbc-slot-cells-corr table 0 fn-lbc) (natp slot) (< slot (len table)))
 (equal (fn-lbc-slot-word slot fn-lbc) (nth slot table)))
 :hints (("Goal" :do-not-induct t
 :use ((:instance fn-lbc-slot-cells-corr-nth (base 0) (j slot)))
 :in-theory (theory 'ground-zero)))))

(local (defthm fn-lbsin-count-natural
 (natp (fn-lbc-slot-count fn-lbc)) :rule-classes :type-prescription
 :hints (("Goal" :in-theory (union-theories (theory 'ground-zero) '(fn-lbc-slot-count-by-store natp))))))

(local (defthm fn-lbsin-mod-natural
 (implies (and (natp x) (posp y)) (natp (mod x y))) :rule-classes :type-prescription))

(local (defthm fn-lbsin-mod-below
 (implies (and (natp x) (posp y)) (< (mod x y) y)) :rule-classes :linear))

(defthm fn-lbc-slot-insert-refines-canonical
 (implies (and (natp i) (natp slot) (< slot (len table)) (natp fuel) (true-listp table)
 (equal (len table) (fn-lbc-slot-count fn-lbc)) (fn-lbc-slot-cells-corr table 0 fn-lbc)
 (not (member-equal i (fn-lbc-slot-escape-keys fn-lbc)))
 (not (fn-lbc-escape i :msgid-slot fn-lbc)))
 (fn-lbc-slot-cells-corr (fn-lbc-canonical-slot-insert (+ 1 i) slot fuel table) 0
                       (fn-lbc-slot-insert i slot fuel fn-lbc)))
 :hints (("Goal" :induct (fn-lbc-slot-insert i slot fuel fn-lbc)
 :in-theory (set-difference-theories (union-theories (theory 'ground-zero)
 '(fn-lbc-slot-insert fn-lbc-canonical-slot-insert fn-lbsin-table-read
 fn-lbc-slot-cells-corr-of-fresh-slot-put fn-lbsin-next-slot-natural fn-lbsin-next-slot-below
 fn-lbsin-count-natural fn-lbsin-mod-natural fn-lbsin-mod-below natp posp nfix zp)) '(mod floor)))))
