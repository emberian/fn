; Derived constructor support; local algebra does not escape this book.
(in-package "ACL2")
(include-book "catalog-columns-slot-native-readback")

(defthm fn-lbc-slot-count-of-slot-put
 (equal (fn-lbc-slot-count (fn-lbc-slot-put slot ordinal fn-lbc)) (fn-lbc-slot-count fn-lbc))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'ground-zero) '(fn-lbc-slot-put fn-lbc-slot-count-of-native-word-set fn-lb-slot-raw-word-of-native-set
 fn-lb-slot-raw-word-of-drop-owner fn-lbc-slot-count-of-drop-owner
 fn-lb-slot-raw-word-of-escape-store-put fn-lb-slot-raw-word-of-update-fn-lbc-row-store
 fn-lb-slot-raw-word-of-update-fn-lbc-slot-escape-keys fn-lbc-slot-count-of-escape-store-put
 fn-lbc-slot-count-of-update-fn-lbc-row-store fn-lbc-slot-count-of-update-fn-lbc-slot-escape-keys
 (:type-prescription fn-lbc-slot-drop-owner))))))

(defthm fn-lb-slot-raw-word-of-slot-put
 (implies (and (natp slot) (< slot (fn-lbc-slot-count fn-lbc))
               (natp query) (< query (fn-lbc-slot-count fn-lbc)))
 (equal (fn-lb-slot-raw-word query (fn-lbc-slot-put slot ordinal fn-lbc))
        (if (equal query slot)
            (if (<= *fn-lbc-slot-escape-word* (nfix ordinal)) *fn-lbc-slot-escape-word* (nfix ordinal))
          (fn-lb-slot-raw-word query fn-lbc))))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'ground-zero) '(fn-lbc-slot-put fn-lbc-slot-count-of-native-word-set fn-lb-slot-raw-word-of-native-set
 fn-lb-slot-raw-word-of-drop-owner fn-lbc-slot-count-of-drop-owner
 fn-lb-slot-raw-word-of-escape-store-put fn-lb-slot-raw-word-of-update-fn-lbc-row-store
 fn-lb-slot-raw-word-of-update-fn-lbc-slot-escape-keys fn-lbc-slot-count-of-escape-store-put
 fn-lbc-slot-count-of-update-fn-lbc-row-store fn-lbc-slot-count-of-update-fn-lbc-slot-escape-keys
 (:type-prescription fn-lbc-slot-drop-owner))))))

(local (defthm fn-lbsps-escape-of-update-fn-lbc-slot-store
 (equal (fn-lbc-escape key :msgid-slot (update-fn-lbc-slot-store value fn-lbc)) (fn-lbc-escape key :msgid-slot fn-lbc))
 :hints (("Goal" :in-theory (union-theories (theory 'ground-zero)
 '(fn-lbc-escape fn-lbc-escape-store-get update-fn-lbc-slot-store fn-dm-nth-update-nth))))))

(local (defthm fn-lbsps-escape-of-update-fn-lbc-row-store
 (equal (fn-lbc-escape key :msgid-slot (update-fn-lbc-row-store value fn-lbc)) (fn-lbc-escape key :msgid-slot fn-lbc))
 :hints (("Goal" :in-theory (union-theories (theory 'ground-zero)
 '(fn-lbc-escape fn-lbc-escape-store-get update-fn-lbc-row-store fn-dm-nth-update-nth))))))

(local (defthm fn-lbsps-escape-of-update-fn-lbc-slot-escape-keys
 (equal (fn-lbc-escape key :msgid-slot (update-fn-lbc-slot-escape-keys value fn-lbc)) (fn-lbc-escape key :msgid-slot fn-lbc))
 :hints (("Goal" :in-theory (union-theories (theory 'ground-zero)
 '(fn-lbc-escape fn-lbc-escape-store-get update-fn-lbc-slot-escape-keys fn-dm-nth-update-nth))))))

(local (defthm fn-lbsps-slot-keys-of-update-fn-lbc-slot-store
 (equal (fn-lbc-slot-escape-keys (update-fn-lbc-slot-store value fn-lbc)) (fn-lbc-slot-escape-keys fn-lbc))
 :hints (("Goal" :in-theory (union-theories (theory 'ground-zero)
 '(fn-lbc-slot-escape-keys update-fn-lbc-slot-store fn-dm-nth-update-nth))))))

(local (defthm fn-lbsps-slot-keys-of-update-fn-lbc-row-store
 (equal (fn-lbc-slot-escape-keys (update-fn-lbc-row-store value fn-lbc)) (fn-lbc-slot-escape-keys fn-lbc))
 :hints (("Goal" :in-theory (union-theories (theory 'ground-zero)
 '(fn-lbc-slot-escape-keys update-fn-lbc-row-store fn-dm-nth-update-nth))))))

(local (defthm fn-lbsps-slot-keys-of-fn-lbc-escape-store-put
 (equal (fn-lbc-slot-escape-keys (fn-lbc-escape-store-put at cell fn-lbc)) (fn-lbc-slot-escape-keys fn-lbc))
 :hints (("Goal" :in-theory (union-theories (theory 'ground-zero)
 '(fn-lbc-slot-escape-keys fn-lbc-escape-store-put fn-dm-nth-update-nth))))))

(defthm fn-lbc-escape-of-drop-unlisted-key
 (implies (not (member-equal key keys))
 (equal (fn-lbc-escape key field (mv-nth 1 (fn-lbc-slot-drop-owner slot keys fn-lbc)))
        (fn-lbc-escape key field fn-lbc)))
 :hints (("Goal" :in-theory (union-theories (theory 'ground-zero)
 '(fn-lbc-escape fn-lbc-escape-cell-after-drop-unlisted-key)))))

(defthm fn-lbc-slot-escape-of-cell-put
 (equal (fn-lbc-escape key :msgid-slot (fn-lbc-escape-store-put at cell fn-lbc))
 (if (equal key at) (assoc-eq :msgid-slot cell) (fn-lbc-escape key :msgid-slot fn-lbc)))
 :hints (("Goal" :in-theory (union-theories (theory 'ground-zero)
 '(fn-lbc-escape fn-lbc-escape-store-get-of-put)))))

(local (defthm fn-lbsps-slot-position-put
 (equal (assoc-eq :msgid-slot (put-assoc-eq :msgid-slot value cell)) (cons :msgid-slot value))
 :hints (("Goal" :induct (put-assoc-eq :msgid-slot value cell) :in-theory (enable put-assoc-eq assoc-eq)))))

(local (defthm fn-lbsps-keys-of-update-keys
 (equal (fn-lbc-slot-escape-keys (update-fn-lbc-slot-escape-keys value fn-lbc)) value)
 :hints (("Goal" :in-theory (union-theories (theory 'ground-zero)
 '(fn-lbc-slot-escape-keys update-fn-lbc-slot-escape-keys fn-dm-nth-update-nth))))))

(defthm fn-lbc-slot-escape-keys-of-slot-put
 (equal (fn-lbc-slot-escape-keys (fn-lbc-slot-put slot ordinal fn-lbc))
 (if (not (and (natp slot) (< slot (fn-lbc-slot-count fn-lbc)))) (fn-lbc-slot-escape-keys fn-lbc)
 (let* ((keys (mv-nth 0 (fn-lbc-slot-drop-owner slot (fn-lbc-slot-escape-keys fn-lbc) fn-lbc)))
        (seq (if (zp (nfix ordinal)) 0 (- (nfix ordinal) 1))))
 (if (<= *fn-lbc-slot-escape-word* (nfix ordinal))
     (if (member-equal seq keys) keys (cons seq keys)) keys))))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'ground-zero)
 '(fn-lbc-slot-put fn-lbsps-keys-of-update-keys
 fn-lbsps-slot-keys-of-update-fn-lbc-slot-store fn-lbsps-slot-keys-of-update-fn-lbc-row-store
 fn-lbsps-slot-keys-of-fn-lbc-escape-store-put fn-dm-nth-update-nth
 (:type-prescription fn-lbc-slot-drop-owner))))))

(local (defthm fn-lbsps-slot-position-by-definition
 (equal (assoc-eq :msgid-slot (fn-lbc-escape-store-get key fn-lbc))
        (fn-lbc-escape key :msgid-slot fn-lbc))
 :hints (("Goal" :in-theory (enable fn-lbc-escape)))))

(local (defthm fn-lbsps-escaped-after-drop-car
 (equal (fn-lbc-escaped-slot-word query
        (car (fn-lbc-slot-drop-owner slot keys fn-lbc))
        (mv-nth 1 (fn-lbc-slot-drop-owner slot keys fn-lbc)))
 (if (equal query slot) 0 (fn-lbc-escaped-slot-word query keys fn-lbc)))
 :hints (("Goal" :do-not-induct t :use ((:instance fn-lbc-escaped-word-after-drop))
 :in-theory (theory 'ground-zero)))))

(local (defthm fn-lbsps-drop-nonmember-car
 (implies (not (member-equal key keys))
 (not (member-equal key (car (fn-lbc-slot-drop-owner slot keys fn-lbc)))))
 :hints (("Goal" :do-not-induct t :use ((:instance fn-lbc-slot-drop-keys-preserve-nonmember))
 :in-theory (theory 'ground-zero)))))

(defthm fn-lbc-escaped-word-of-fresh-slot-put
 (implies (and (posp ordinal) (natp slot) (< slot (fn-lbc-slot-count fn-lbc))
 (not (member-equal (- ordinal 1) (fn-lbc-slot-escape-keys fn-lbc)))
 (not (fn-lbc-escape (- ordinal 1) :msgid-slot fn-lbc)))
 (equal (fn-lbc-escaped-slot-word query
         (fn-lbc-slot-escape-keys (fn-lbc-slot-put slot ordinal fn-lbc))
         (fn-lbc-slot-put slot ordinal fn-lbc))
        (if (equal query slot)
            (if (<= *fn-lbc-slot-escape-word* ordinal) ordinal 0)
          (fn-lbc-escaped-slot-word query (fn-lbc-slot-escape-keys fn-lbc) fn-lbc))))
 :hints (("Goal" :do-not-induct t
 :in-theory (union-theories (theory 'ground-zero)
 '(fn-lbc-slot-put posp nfix fn-lbsps-escaped-after-drop-car fn-lbsps-drop-nonmember-car
 fn-lbc-escape-of-drop-unlisted-key fn-lbc-slot-drop-keys-preserve-nonmember
 fn-lbc-escaped-word-of-fresh-owner-insertion fn-lbsps-slot-position-by-definition fn-lbsps-escape-of-update-fn-lbc-slot-escape-keys fn-lbsps-escape-of-update-fn-lbc-row-store fn-lbsps-escape-of-update-fn-lbc-slot-store
 fn-lbc-escaped-slot-word-of-update-fn-lbc-slot-store
 fn-lbc-escaped-slot-word-of-update-fn-lbc-row-store
 fn-lbc-escaped-slot-word-of-update-fn-lbc-slot-escape-keys
 fn-lbsps-slot-keys-of-update-fn-lbc-slot-store fn-lbsps-slot-keys-of-update-fn-lbc-row-store
 fn-lbsps-slot-keys-of-fn-lbc-escape-store-put fn-lbsps-keys-of-update-keys
 (:type-prescription fn-lbc-slot-drop-owner))))))

(defthm fn-lbc-slot-word-of-fresh-slot-put
 (implies (and (posp ordinal) (natp slot) (< slot (fn-lbc-slot-count fn-lbc))
 (natp query) (< query (fn-lbc-slot-count fn-lbc))
 (not (member-equal (- ordinal 1) (fn-lbc-slot-escape-keys fn-lbc)))
 (not (fn-lbc-escape (- ordinal 1) :msgid-slot fn-lbc)))
 (equal (fn-lbc-slot-word query (fn-lbc-slot-put slot ordinal fn-lbc))
        (if (equal query slot) ordinal (fn-lbc-slot-word query fn-lbc))))
 :hints (("Goal" :do-not-induct t
 :in-theory (union-theories (theory 'ground-zero)
 '(fn-lbc-slot-word-by-raw-word fn-lb-slot-raw-word-of-slot-put
 fn-lbc-escaped-word-of-fresh-slot-put posp nfix)))))
