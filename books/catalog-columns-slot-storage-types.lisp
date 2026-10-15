; Derived constructor support; local algebra does not escape this book.
(in-package "ACL2")
(include-book "catalog-columns-slot-flag-frames")

(local (defthm fn-lbstp-true-listp-update
 (implies (true-listp xs) (true-listp (update-nth i value xs)))
 :hints (("Goal" :induct (update-nth i value xs) :in-theory (enable update-nth true-listp)))))

(defthm fn-lbc-p-of-update-row-store
 (implies (and (fn-lbc-p fn-lbc) (fn-lbc-rowwordsp value)) (fn-lbc-p (update-fn-lbc-row-store value fn-lbc)))
 :hints (("Goal" :do-not-induct t :in-theory
  (union-theories (theory 'ground-zero)
   '(fn-lbc-p update-fn-lbc-row-store fn-lbc-row-storep fn-dm-nth-update-nth
     fn-dm-len-update-nth fn-lbstp-true-listp-update length)))))

(defthm fn-lbc-p-of-update-slot-store
 (implies (and (fn-lbc-p fn-lbc) (fn-lbc-msgid-slotsp value)) (fn-lbc-p (update-fn-lbc-slot-store value fn-lbc)))
 :hints (("Goal" :do-not-induct t :in-theory
  (union-theories (theory 'ground-zero)
   '(fn-lbc-p update-fn-lbc-slot-store fn-lbc-slot-storep fn-dm-nth-update-nth
     fn-dm-len-update-nth fn-lbstp-true-listp-update length)))))

(defthm fn-lbc-p-of-update-slot-escape-keys
 (implies (and (fn-lbc-p fn-lbc) t) (fn-lbc-p (update-fn-lbc-slot-escape-keys value fn-lbc)))
 :hints (("Goal" :do-not-induct t :in-theory
  (union-theories (theory 'ground-zero)
   '(fn-lbc-p update-fn-lbc-slot-escape-keys fn-lbc-slot-escape-keysp fn-dm-nth-update-nth
     fn-dm-len-update-nth fn-lbstp-true-listp-update length)))))

(defthm fn-lbc-p-of-escape-store-put
 (implies (fn-lbc-p fn-lbc) (fn-lbc-p (fn-lbc-escape-store-put key cell fn-lbc)))
 :hints (("Goal" :do-not-induct t :in-theory
  (union-theories (theory 'ground-zero)
   '(fn-lbc-p fn-lbc-escape-store-put fn-lbc-escape-storep fn-dm-nth-update-nth
     fn-dm-len-update-nth fn-lbstp-true-listp-update length)))))

(defthm fn-lbc-rowwordsp-of-set-flags
 (implies (and (fn-lbc-rowwordsp rows) (natp j) (< j (len rows)) (unsigned-byte-p 64 value))
  (fn-lbc-rowwordsp (fn-lbc-rowwords-set-flags j value rows)))
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-lbc-rowwords-set-flags{preserved} (fn-lbc-rowwords rows) (i j) (v value)))
  :in-theory (union-theories (theory 'ground-zero)
   '(fn-lbc-rowwordsp fn-lbc-rowwords-set-flags fn-lbc-rowwords$a-count adt-val-okp)))))

(defthm fn-lbc-p-of-in-bounds-flags-set
 (implies (and (fn-lbc-p fn-lbc) (natp j) (< j (fn-lbc-count fn-lbc)) (unsigned-byte-p 64 value))
  (fn-lbc-p (update-fn-lbc-row-store (fn-lbc-rowwords-set-flags j value (fn-lbc-row-store fn-lbc)) fn-lbc)))
 :hints (("Goal" :do-not-induct t :in-theory
  (union-theories (theory 'ground-zero)
   '(fn-lbc-p-of-update-row-store fn-lbc-rowwordsp-of-set-flags
     fn-lbc-p fn-lbc-row-storep fn-lbc-count fn-lbc-row-store fn-lbc-rowwords-count-is-len)))))

(defthm fn-lbc-msgid-slotsp-of-set-word
 (implies (and (fn-lbc-msgid-slotsp rows) (natp j) (< j (len rows)) (unsigned-byte-p 64 value))
  (fn-lbc-msgid-slotsp (fn-lbc-msgid-slots-set-word j value rows)))
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-lbc-msgid-slots-set-word{preserved} (fn-lbc-msgid-slots rows) (i j) (v value)))
  :in-theory (union-theories (theory 'ground-zero)
   '(fn-lbc-msgid-slotsp fn-lbc-msgid-slots-set-word fn-lbc-msgid-slots$a-count adt-val-okp)))))

(defthm fn-lbc-p-of-in-bounds-word-set
 (implies (and (fn-lbc-p fn-lbc) (natp j) (< j (fn-lbc-slot-count fn-lbc)) (unsigned-byte-p 64 value))
  (fn-lbc-p (update-fn-lbc-slot-store (fn-lbc-msgid-slots-set-word j value (fn-lbc-slot-store fn-lbc)) fn-lbc)))
 :hints (("Goal" :do-not-induct t :in-theory
  (union-theories (theory 'ground-zero)
   '(fn-lbc-p-of-update-slot-store fn-lbc-msgid-slotsp-of-set-word
     fn-lbc-p fn-lbc-slot-storep fn-lbc-slot-count fn-lbc-slot-store fn-lbc-msgid-slots-count-is-len)))))

(defthm fn-lbc-p-of-slot-drop-owner
 (implies (fn-lbc-p fn-lbc) (fn-lbc-p (mv-nth 1 (fn-lbc-slot-drop-owner slot keys fn-lbc))))
 :hints (("Goal" :induct (fn-lbc-slot-drop-owner slot keys fn-lbc) :in-theory
  (union-theories (theory 'ground-zero)
   '(fn-lbc-slot-drop-owner fn-lbc-p-of-escape-store-put mv-nth
     (:type-prescription fn-lbc-slot-drop-owner))))))
