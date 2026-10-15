; Derived constructor support; local algebra does not escape this book.
(in-package "ACL2")
(include-book "catalog-columns-slot-future-progress")
(local (include-book "arithmetic-5/top" :dir :system))

(local (defthm fn-lbscs-len-update
 (implies (and (natp i) (< i (len xs))) (equal (len (update-nth i value xs)) (len xs)))
 :hints (("Goal" :induct (update-nth i value xs) :in-theory (enable update-nth len)))))

(local (defthm fn-lbscs-proper-update
 (implies (true-listp xs) (true-listp (update-nth i value xs)))
 :hints (("Goal" :induct (update-nth i value xs) :in-theory (enable update-nth true-listp)))))

(local (defthm fn-lbscs-mod-natural
 (implies (and (natp x) (posp y)) (natp (mod x y))) :rule-classes :type-prescription))

(local (defthm fn-lbscs-mod-below
 (implies (and (natp x) (posp y)) (< (mod x y) y)) :rule-classes :linear))

(defthm fn-lbc-canonical-slot-insert-length
 (implies (and (natp slot) (< slot (len table)))
 (equal (len (fn-lbc-canonical-slot-insert ordinal slot fuel table)) (len table)))
 :hints (("Goal" :induct (fn-lbc-canonical-slot-insert ordinal slot fuel table)
 :in-theory (set-difference-theories (union-theories (theory 'ground-zero)
 '(fn-lbc-canonical-slot-insert fn-lbscs-len-update fn-lbscs-mod-natural fn-lbscs-mod-below natp posp nfix zp))
 '(mod floor)))))

(defthm fn-lbc-canonical-slot-insert-proper
 (implies (true-listp table) (true-listp (fn-lbc-canonical-slot-insert ordinal slot fuel table)))
 :hints (("Goal" :induct (fn-lbc-canonical-slot-insert ordinal slot fuel table)
 :in-theory (union-theories (theory 'ground-zero)
 '(fn-lbc-canonical-slot-insert fn-lbscs-proper-update)))))

(local (defthm fn-lbscs-hash-octets-natural
 (natp (fn-lbc-msgid-hash-octets bytes hash)) :rule-classes :type-prescription
 :hints (("Goal" :induct (fn-lbc-msgid-hash-octets bytes hash)
 :in-theory (set-difference-theories (union-theories (theory 'ground-zero)
 '(fn-lbc-msgid-hash-octets nfix natp)) '(mod floor))))))

(defthm fn-lbc-msgid-hash-natural
 (natp (fn-lbc-msgid-hash msgid)) :rule-classes :type-prescription
 :hints (("Goal" :in-theory (union-theories (theory 'ground-zero)
 '(fn-lbc-msgid-hash fn-lbscs-hash-octets-natural)))))

(defun-nx fn-lb-slot-row-hashesp (rows start fn-lbc)
 (if (consp rows)
 (and (equal (fn-lbc-word :msgid-hash (nfix start) fn-lbc) (fn-lbc-msgid-hash (fn-record-msgid (car rows))))
 (fn-lb-slot-row-hashesp (cdr rows) (+ 1 (nfix start)) fn-lbc)) t))

(local (defthm fn-lbscs-row-corr-hash
 (implies (fn-lbc-row-corr i row pm fn-lbc log)
 (equal (fn-lbc-word :msgid-hash i fn-lbc) (fn-lbc-msgid-hash (fn-record-msgid row))))
 :hints (("Goal" :in-theory (union-theories (theory 'ground-zero) '(fn-lbc-row-corr))))))

(defthm fn-lb-slot-row-hashesp-from-rows-corr
 (implies (and (natp start) (fn-lbc-rows-corr start rows pm fn-lbc log))
 (fn-lb-slot-row-hashesp rows start fn-lbc))
 :hints (("Goal" :induct (fn-lbc-rows-corr start rows pm fn-lbc log)
 :in-theory (union-theories (theory 'ground-zero)
 '(fn-lbc-rows-corr fn-lb-slot-row-hashesp fn-lbscs-row-corr-hash natp nfix)))))

(defthm fn-lb-slot-row-hashesp-of-slot-insert
 (equal (fn-lb-slot-row-hashesp rows start (fn-lbc-slot-insert i slot fuel fn-lbc))
        (fn-lb-slot-row-hashesp rows start fn-lbc))
 :hints (("Goal" :induct (fn-lb-slot-row-hashesp rows start fn-lbc)
 :in-theory (union-theories (theory 'ground-zero)
 '(fn-lb-slot-row-hashesp fn-lbc-word-of-slot-insert-other-field)))))
