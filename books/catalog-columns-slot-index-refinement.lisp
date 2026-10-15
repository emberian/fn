; Derived constructor support; local algebra does not escape this book.
(in-package "ACL2")
(include-book "catalog-columns-slot-canonical-storage")
(local (include-book "arithmetic-5/top" :dir :system))

(local (defthm fn-lbsix-mod-natural
 (implies (and (natp x) (posp y)) (natp (mod x y))) :rule-classes :type-prescription))

(local (defthm fn-lbsix-mod-below
 (implies (and (natp x) (posp y)) (< (mod x y) y)) :rule-classes :linear))

(local (defthm fn-lbsix-row-hashes-head
 (implies (and (consp rows) (natp start) (fn-lb-slot-row-hashesp rows start fn-lbc))
 (equal (fn-lbc-word :msgid-hash start fn-lbc) (fn-lbc-msgid-hash (fn-record-msgid (car rows)))))
 :hints (("Goal" :in-theory (union-theories (theory 'ground-zero) '(fn-lb-slot-row-hashesp natp nfix))))))

(local (defthm fn-lbsix-row-hashes-tail
 (implies (and (consp rows) (natp start) (fn-lb-slot-row-hashesp rows start fn-lbc))
 (fn-lb-slot-row-hashesp (cdr rows) (+ 1 start) fn-lbc))
 :hints (("Goal" :in-theory (union-theories (theory 'ground-zero) '(fn-lb-slot-row-hashesp natp nfix))))))

(local (defun-nx fn-lbsix-build-induct (rows i table fn-lbc)
 (if (consp rows)
 (let* ((capacity (fn-lbc-slot-count fn-lbc))
        (slot (mod (nfix (fn-lbc-word :msgid-hash i fn-lbc)) (max 1 capacity)))
        (next (fn-lbc-slot-insert i slot capacity fn-lbc))
        (table (fn-lbc-canonical-slot-insert (+ 1 (nfix i))
          (mod (fn-lbc-msgid-hash (fn-record-msgid (car rows))) (max 1 (len table))) (len table) table)))
 (fn-lbsix-build-induct (cdr rows) (+ 1 (nfix i)) table next)) (list i table fn-lbc))))

(local (defthm fn-lbsix-consp-positive-length
 (implies (consp xs) (< 0 (len xs))) :rule-classes (:rewrite :linear)
 :hints (("Goal" :in-theory (enable len)))))

(local (defthm fn-lbsix-canonical-insert-nonempty
 (implies (and (natp slot) (< slot (len table)))
 (consp (fn-lbc-canonical-slot-insert ordinal slot fuel table)))
 :hints (("Goal" :do-not-induct t
 :use ((:instance fn-lbc-canonical-slot-insert-length))
 :in-theory (union-theories (theory 'ground-zero) '(len natp))))))

(local (defthm fn-lbsix-count-natural
 (natp (fn-lbc-slot-count fn-lbc)) :rule-classes :type-prescription
 :hints (("Goal" :in-theory (union-theories (theory 'ground-zero) '(fn-lbc-slot-count-by-store natp))))))

(defthm fn-lbc-index-slots-refines-canonical
 (implies (and (natp i) (consp table) (true-listp table)
 (equal (len table) (fn-lbc-slot-count fn-lbc)) (fn-lbc-slot-cells-corr table 0 fn-lbc)
 (fn-lb-slot-row-hashesp rows i fn-lbc)
 (fn-lb-slot-owner-keys-below (fn-lbc-slot-escape-keys fn-lbc) i)
 (fn-lb-unindexed-slotsp i (+ i (len rows)) fn-lbc))
 (fn-lbc-slot-cells-corr (fn-lbc-canonical-slots-from rows i table) 0
                       (fn-lbc-index-slots i (+ i (len rows)) fn-lbc)))
 :hints (("Goal" :induct (fn-lbsix-build-induct rows i table fn-lbc)
 :expand ((:free (n) (fn-lbc-index-slots i n fn-lbc)))
 :in-theory (set-difference-theories (union-theories (theory 'ground-zero)
 '(fn-lbsix-build-induct fn-lbc-index-slots fn-lbc-canonical-slots-from len
 fn-lbc-slot-insert-refines-canonical fn-lbc-canonical-slot-insert-length
 fn-lbc-canonical-slot-insert-proper fn-lbsix-consp-positive-length fn-lbsix-canonical-insert-nonempty fn-lbsix-count-natural fn-lbc-slot-count-of-slot-insert
 fn-lb-slot-owner-keys-below-of-slot-insert fn-lb-unindexed-slotsp-of-next-slot-insert
 fn-lb-slot-row-hashesp-of-slot-insert fn-lbsix-row-hashes-head fn-lbsix-row-hashes-tail
 fn-lb-slot-owner-keys-below-nonmember fn-lb-unindexed-slotsp-head
 fn-lbc-msgid-hash-natural fn-lbsix-mod-natural fn-lbsix-mod-below natp posp nfix zp))
 '(mod floor)))))
