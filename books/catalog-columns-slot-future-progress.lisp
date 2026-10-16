; Derived constructor support; local algebra does not escape this book.
(in-package "ACL2")
(include-book "catalog-columns-slot-owner-progress")

(defun-nx fn-lb-unindexed-slotsp (start n fn-lbc)
 (declare (xargs :measure (nfix (- (nfix n) (nfix start)))))
 (if (and (natp start) (natp n) (< start n))
 (and (not (fn-lbc-escape start :msgid-slot fn-lbc))
      (fn-lb-unindexed-slotsp (+ 1 start) n fn-lbc)) t))

(defthm fn-lb-unindexed-slotsp-head
 (implies (and (fn-lb-unindexed-slotsp start n fn-lbc) (natp start) (natp n) (< start n))
 (not (fn-lbc-escape start :msgid-slot fn-lbc)))
 :hints (("Goal" :in-theory (union-theories (theory 'ground-zero) '(fn-lb-unindexed-slotsp)))))

(defthm fn-lb-unindexed-slotsp-tail
 (implies (and (fn-lb-unindexed-slotsp start n fn-lbc) (natp start) (natp n) (< start n))
 (fn-lb-unindexed-slotsp (+ 1 start) n fn-lbc))
 :hints (("Goal" :in-theory (union-theories (theory 'ground-zero) '(fn-lb-unindexed-slotsp)))))

(defthm fn-lb-unindexed-slotsp-of-prior-slot-insert
 (implies (and (natp i) (natp start) (< i start)
 (fn-lb-slot-owner-keys-below (fn-lbc-slot-escape-keys fn-lbc) i)
 (fn-lb-unindexed-slotsp start n fn-lbc))
 (fn-lb-unindexed-slotsp start n (fn-lbc-slot-insert i slot fuel fn-lbc)))
 :hints (("Goal" :induct (fn-lb-unindexed-slotsp start n fn-lbc)
 :in-theory (union-theories (theory 'ground-zero)
 '(fn-lb-unindexed-slotsp fn-lbc-slot-escape-of-slot-insert-future natp)))))

(defthm fn-lb-unindexed-slotsp-of-next-slot-insert
 (implies (and (natp i) (natp n) (< i n)
 (fn-lb-slot-owner-keys-below (fn-lbc-slot-escape-keys fn-lbc) i)
 (fn-lb-unindexed-slotsp i n fn-lbc))
 (fn-lb-unindexed-slotsp (+ 1 i) n (fn-lbc-slot-insert i slot fuel fn-lbc)))
 :hints (("Goal" :do-not-induct t
 :use ((:instance fn-lb-unindexed-slotsp-tail (start i))
       (:instance fn-lb-unindexed-slotsp-of-prior-slot-insert (start (+ 1 i))))
 :in-theory (theory 'ground-zero))))
