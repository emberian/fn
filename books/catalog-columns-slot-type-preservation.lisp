; Derived constructor support; local algebra does not escape this book.
(in-package "ACL2")
(include-book "catalog-columns-slot-storage-types")
(local (include-book "ihs/logops-lemmas" :dir :system))

(local (defthm fn-lbsty-slot-count-frame
 (implies (equal (nth 4 new) (nth 4 fn-lbc))
  (equal (fn-lbc-slot-count new) (fn-lbc-slot-count fn-lbc)))
 :rule-classes nil
 :hints (("Goal" :in-theory (union-theories (theory 'ground-zero) '(fn-lbc-slot-count fn-lbc-slot-store))))))

(local (defthm fn-lbsty-slot-count-of-escape-put
 (equal (fn-lbc-slot-count (fn-lbc-escape-store-put key cell fn-lbc)) (fn-lbc-slot-count fn-lbc))
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-lbsty-slot-count-frame (new (fn-lbc-escape-store-put key cell fn-lbc))))
  :in-theory (union-theories (theory 'ground-zero) '(fn-lbwf-escape-store-put-field))))))

(local (defthm fn-lbsty-slot-count-of-slot-drop-owner
 (equal (fn-lbc-slot-count (mv-nth 1 (fn-lbc-slot-drop-owner slot keys fn-lbc))) (fn-lbc-slot-count fn-lbc))
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-lbsty-slot-count-frame (new (mv-nth 1 (fn-lbc-slot-drop-owner slot keys fn-lbc)))))
  :in-theory (union-theories (theory 'ground-zero) '(fn-lbwf-slot-drop-owner-field fn-lbwf-slot-drop-owner-field-car))))))

(local (defthm fn-lbsty-slot-count-of-key-update
 (equal (fn-lbc-slot-count (update-fn-lbc-slot-escape-keys keys fn-lbc)) (fn-lbc-slot-count fn-lbc))
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-lbsty-slot-count-frame (new (update-fn-lbc-slot-escape-keys keys fn-lbc))))
  :in-theory (union-theories (theory 'ground-zero) '(update-fn-lbc-slot-escape-keys fn-dm-nth-update-nth))))))

(local (defthm fn-lbsty-slot-count-of-row-update
 (equal (fn-lbc-slot-count (update-fn-lbc-row-store rows fn-lbc)) (fn-lbc-slot-count fn-lbc))
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-lbsty-slot-count-frame (new (update-fn-lbc-row-store rows fn-lbc))))
  :in-theory (union-theories (theory 'ground-zero) '(update-fn-lbc-row-store fn-dm-nth-update-nth))))))

(local (defthm fn-lbsty-flags-getter-native-type
 (implies (and (fn-lbc-p fn-lbc) (natp j) (< j (fn-lbc-count fn-lbc)))
  (unsigned-byte-p 64 (fn-lbc-rowwords-get-flags j (fn-lbc-row-store fn-lbc))))
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-lbc-flags-word-has-native-type (i j)))
  :in-theory (union-theories (theory 'ground-zero)
   '(fn-lbc-word-flags-by-definition fn-lbc-count fn-lbc-row-store fn-lbc-rowwords-count-is-len
     fn-lbc-rowwords-get-flags fn-lbc-rowwords$a-get-flags))))))

(local (defthm fn-lbsty-or-eight-native-type
 (implies (unsigned-byte-p 64 flags) (unsigned-byte-p 64 (logior flags 8)))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'minimal-theory)
  '(unsigned-byte-p-logior (:executable-counterpart unsigned-byte-p) (:executable-counterpart integerp)))))))

(defthm fn-lbc-p-of-slot-put
 (implies (fn-lbc-p fn-lbc) (fn-lbc-p (fn-lbc-slot-put slot ordinal fn-lbc)))
 :hints (("Goal" :do-not-induct t :in-theory
  (set-difference-theories (union-theories (theory 'ground-zero)
   '(fn-lbc-slot-put fn-lbc-p-of-update-slot-escape-keys fn-lbc-p-of-escape-store-put
     fn-lbc-p-of-in-bounds-flags-set fn-lbc-p-of-in-bounds-word-set fn-lbc-p-of-slot-drop-owner
     fn-lbsty-slot-count-of-escape-put fn-lbsty-slot-count-of-slot-drop-owner
     fn-lbsty-slot-count-of-key-update fn-lbsty-slot-count-of-row-update
     fn-lbsty-flags-getter-native-type fn-lbsty-or-eight-native-type
     unsigned-byte-p integer-range-p nfix (:type-prescription fn-lbc-slot-drop-owner)))
   '((:definition binary-logior) (tau-system))))))

(defthm fn-lbc-p-of-slot-insert
 (implies (fn-lbc-p fn-lbc) (fn-lbc-p (fn-lbc-slot-insert i slot fuel fn-lbc)))
 :hints (("Goal" :induct (fn-lbc-slot-insert i slot fuel fn-lbc) :in-theory
  (union-theories (theory 'minimal-theory) '(fn-lbc-slot-insert fn-lbc-p-of-slot-put)))))

(defthm fn-lbc-p-of-index-slots
 (implies (fn-lbc-p fn-lbc) (fn-lbc-p (fn-lbc-index-slots i n fn-lbc)))
 :hints (("Goal" :induct (fn-lbc-index-slots i n fn-lbc) :in-theory
  (union-theories (theory 'minimal-theory) '(fn-lbc-index-slots fn-lbc-p-of-slot-insert)))))
