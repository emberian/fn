; Derived constructor support; local algebra does not escape this book.
(in-package "ACL2")
(include-book "catalog-columns-flags-native-type")

(local (defthm fn-lbsff-count-of-update-slot-store
 (equal (fn-lbc-count  (update-fn-lbc-slot-store value fn-lbc))
        (fn-lbc-count  fn-lbc))
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-lbc-count-frame-by-definition (new (update-fn-lbc-slot-store value fn-lbc)) ))
  :in-theory (union-theories (theory 'ground-zero) '(update-fn-lbc-slot-store fn-dm-nth-update-nth))))))

(local (defthm fn-lbsff-count-of-update-slot-escape-keys
 (equal (fn-lbc-count  (update-fn-lbc-slot-escape-keys value fn-lbc))
        (fn-lbc-count  fn-lbc))
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-lbc-count-frame-by-definition (new (update-fn-lbc-slot-escape-keys value fn-lbc)) ))
  :in-theory (union-theories (theory 'ground-zero) '(update-fn-lbc-slot-escape-keys fn-dm-nth-update-nth))))))

(local (defthm fn-lbsff-word-of-update-slot-store
 (equal (fn-lbc-word field i (update-fn-lbc-slot-store value fn-lbc))
        (fn-lbc-word field i fn-lbc))
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-lbc-word-frame-by-definition (new (update-fn-lbc-slot-store value fn-lbc)) (field field) (i i)))
  :in-theory (union-theories (theory 'ground-zero) '(update-fn-lbc-slot-store fn-dm-nth-update-nth))))))

(local (defthm fn-lbsff-word-of-update-slot-escape-keys
 (equal (fn-lbc-word field i (update-fn-lbc-slot-escape-keys value fn-lbc))
        (fn-lbc-word field i fn-lbc))
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-lbc-word-frame-by-definition (new (update-fn-lbc-slot-escape-keys value fn-lbc)) (field field) (i i)))
  :in-theory (union-theories (theory 'ground-zero) '(update-fn-lbc-slot-escape-keys fn-dm-nth-update-nth))))))

(local (defthm fn-lbsff-flag-of-update-slot-store
 (equal (fn-lbc-flag i bit (update-fn-lbc-slot-store value fn-lbc))
        (fn-lbc-flag i bit fn-lbc))
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-lbc-flag-frame-by-definition (new (update-fn-lbc-slot-store value fn-lbc)) (i i) (bit bit)))
  :in-theory (union-theories (theory 'ground-zero) '(update-fn-lbc-slot-store fn-dm-nth-update-nth))))))

(local (defthm fn-lbsff-flag-of-update-slot-escape-keys
 (equal (fn-lbc-flag i bit (update-fn-lbc-slot-escape-keys value fn-lbc))
        (fn-lbc-flag i bit fn-lbc))
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-lbc-flag-frame-by-definition (new (update-fn-lbc-slot-escape-keys value fn-lbc)) (i i) (bit bit)))
  :in-theory (union-theories (theory 'ground-zero) '(update-fn-lbc-slot-escape-keys fn-dm-nth-update-nth))))))

(defthm fn-lbc-bit-0-of-slot-put
 (implies (fn-lbc-p fn-lbc)
  (equal (fn-lbc-flag i 0 (fn-lbc-slot-put slot ordinal fn-lbc)) (fn-lbc-flag i 0 fn-lbc)))
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-lbc-flag-of-slot-drop-owner (read-i i) (read-bit 0) (keys (fn-lbc-slot-escape-keys fn-lbc))))
  :in-theory (set-difference-theories (union-theories (theory 'ground-zero) '(fn-lbc-slot-put fn-lbc-count-of-slot-drop-owner fn-lbc-count-of-escape-store-put fn-lbc-word-of-slot-drop-owner fn-lbc-word-of-escape-store-put fn-lbc-flag-of-escape-store-put fn-lbc-flags-word-has-native-type fn-lbc-bit-0-of-in-bounds-slot-flag-set nfix (:type-prescription fn-lbc-slot-drop-owner) fn-lbsff-count-of-update-slot-store fn-lbsff-count-of-update-slot-escape-keys fn-lbsff-word-of-update-slot-store fn-lbsff-word-of-update-slot-escape-keys fn-lbsff-flag-of-update-slot-store fn-lbsff-flag-of-update-slot-escape-keys))
   '((:definition binary-logior) (:definition logbitp) (tau-system))))))

(defthm fn-lbc-bit-1-of-slot-put
 (implies (fn-lbc-p fn-lbc)
  (equal (fn-lbc-flag i 1 (fn-lbc-slot-put slot ordinal fn-lbc)) (fn-lbc-flag i 1 fn-lbc)))
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-lbc-flag-of-slot-drop-owner (read-i i) (read-bit 1) (keys (fn-lbc-slot-escape-keys fn-lbc))))
  :in-theory (set-difference-theories (union-theories (theory 'ground-zero) '(fn-lbc-slot-put fn-lbc-count-of-slot-drop-owner fn-lbc-count-of-escape-store-put fn-lbc-word-of-slot-drop-owner fn-lbc-word-of-escape-store-put fn-lbc-flag-of-escape-store-put fn-lbc-flags-word-has-native-type fn-lbc-bit-1-of-in-bounds-slot-flag-set nfix (:type-prescription fn-lbc-slot-drop-owner) fn-lbsff-count-of-update-slot-store fn-lbsff-count-of-update-slot-escape-keys fn-lbsff-word-of-update-slot-store fn-lbsff-word-of-update-slot-escape-keys fn-lbsff-flag-of-update-slot-store fn-lbsff-flag-of-update-slot-escape-keys))
   '((:definition binary-logior) (:definition logbitp) (tau-system))))))

(defthm fn-lbc-bit-2-of-slot-put
 (implies (fn-lbc-p fn-lbc)
  (equal (fn-lbc-flag i 2 (fn-lbc-slot-put slot ordinal fn-lbc)) (fn-lbc-flag i 2 fn-lbc)))
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-lbc-flag-of-slot-drop-owner (read-i i) (read-bit 2) (keys (fn-lbc-slot-escape-keys fn-lbc))))
  :in-theory (set-difference-theories (union-theories (theory 'ground-zero) '(fn-lbc-slot-put fn-lbc-count-of-slot-drop-owner fn-lbc-count-of-escape-store-put fn-lbc-word-of-slot-drop-owner fn-lbc-word-of-escape-store-put fn-lbc-flag-of-escape-store-put fn-lbc-flags-word-has-native-type fn-lbc-bit-2-of-in-bounds-slot-flag-set nfix (:type-prescription fn-lbc-slot-drop-owner) fn-lbsff-count-of-update-slot-store fn-lbsff-count-of-update-slot-escape-keys fn-lbsff-word-of-update-slot-store fn-lbsff-word-of-update-slot-escape-keys fn-lbsff-flag-of-update-slot-store fn-lbsff-flag-of-update-slot-escape-keys))
   '((:definition binary-logior) (:definition logbitp) (tau-system))))))

(defthm fn-lbc-bit-4-of-slot-put
 (implies (fn-lbc-p fn-lbc)
  (equal (fn-lbc-flag i 4 (fn-lbc-slot-put slot ordinal fn-lbc)) (fn-lbc-flag i 4 fn-lbc)))
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-lbc-flag-of-slot-drop-owner (read-i i) (read-bit 4) (keys (fn-lbc-slot-escape-keys fn-lbc))))
  :in-theory (set-difference-theories (union-theories (theory 'ground-zero) '(fn-lbc-slot-put fn-lbc-count-of-slot-drop-owner fn-lbc-count-of-escape-store-put fn-lbc-word-of-slot-drop-owner fn-lbc-word-of-escape-store-put fn-lbc-flag-of-escape-store-put fn-lbc-flags-word-has-native-type fn-lbc-bit-4-of-in-bounds-slot-flag-set nfix (:type-prescription fn-lbc-slot-drop-owner) fn-lbsff-count-of-update-slot-store fn-lbsff-count-of-update-slot-escape-keys fn-lbsff-word-of-update-slot-store fn-lbsff-word-of-update-slot-escape-keys fn-lbsff-flag-of-update-slot-store fn-lbsff-flag-of-update-slot-escape-keys))
   '((:definition binary-logior) (:definition logbitp) (tau-system))))))

(defthm fn-lbc-bit-5-of-slot-put
 (implies (fn-lbc-p fn-lbc)
  (equal (fn-lbc-flag i 5 (fn-lbc-slot-put slot ordinal fn-lbc)) (fn-lbc-flag i 5 fn-lbc)))
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-lbc-flag-of-slot-drop-owner (read-i i) (read-bit 5) (keys (fn-lbc-slot-escape-keys fn-lbc))))
  :in-theory (set-difference-theories (union-theories (theory 'ground-zero) '(fn-lbc-slot-put fn-lbc-count-of-slot-drop-owner fn-lbc-count-of-escape-store-put fn-lbc-word-of-slot-drop-owner fn-lbc-word-of-escape-store-put fn-lbc-flag-of-escape-store-put fn-lbc-flags-word-has-native-type fn-lbc-bit-5-of-in-bounds-slot-flag-set nfix (:type-prescription fn-lbc-slot-drop-owner) fn-lbsff-count-of-update-slot-store fn-lbsff-count-of-update-slot-escape-keys fn-lbsff-word-of-update-slot-store fn-lbsff-word-of-update-slot-escape-keys fn-lbsff-flag-of-update-slot-store fn-lbsff-flag-of-update-slot-escape-keys))
   '((:definition binary-logior) (:definition logbitp) (tau-system))))))
