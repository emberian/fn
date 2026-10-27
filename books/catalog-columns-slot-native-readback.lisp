; Derived constructor support; local algebra does not escape this book.
(in-package "ACL2")
(include-book "catalog-columns-slot-drop-readback")

(defun-nx fn-lb-slot-raw-word (slot fn-lbc)
 (if (and (natp slot) (< slot (len (nth 4 fn-lbc)))) (nth 0 (nth slot (nth 4 fn-lbc))) 0))

(defthm fn-lbc-slot-count-by-store
 (equal (fn-lbc-slot-count fn-lbc) (len (nth 4 fn-lbc)))
 :hints (("Goal" :in-theory (union-theories (theory 'ground-zero)
 '(fn-lbc-slot-count fn-lbc-slot-store fn-lbc-msgid-slots-count-is-len)))))

(defthm fn-lbc-slot-word-by-raw-word
 (equal (fn-lbc-slot-word slot fn-lbc)
 (let ((word (fn-lb-slot-raw-word slot fn-lbc)))
 (if (equal word *fn-lbc-slot-escape-word*)
 (fn-lbc-escaped-slot-word slot (fn-lbc-slot-escape-keys fn-lbc) fn-lbc) word)))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'ground-zero)
 '(fn-lbc-slot-word fn-lb-slot-raw-word fn-lbc-slot-store fn-lbc-msgid-slots-count-is-len
 fn-lbc-msgid-slots-get-word fn-lbc-msgid-slots$a-get-word)))))

(local (defthm fn-lbsnr-raw-word-frame
 (implies (equal (nth 4 new) (nth 4 fn-lbc))
 (equal (fn-lb-slot-raw-word query new) (fn-lb-slot-raw-word query fn-lbc)))
 :hints (("Goal" :in-theory (union-theories (theory 'ground-zero) '(fn-lb-slot-raw-word))))))

(local (defthm fn-lbsnr-count-frame
 (implies (equal (nth 4 new) (nth 4 fn-lbc))
 (equal (fn-lbc-slot-count new) (fn-lbc-slot-count fn-lbc)))
 :hints (("Goal" :in-theory (union-theories (theory 'ground-zero) '(fn-lbc-slot-count-by-store))))))

(local (defthm fn-lbsnr-escaped-frame
 (implies (equal (nth 9 new) (nth 9 fn-lbc))
 (equal (fn-lbc-escaped-slot-word query keys new) (fn-lbc-escaped-slot-word query keys fn-lbc)))
 :hints (("Goal" :induct (len keys) :in-theory (union-theories (theory 'ground-zero)
 '(len fn-lbc-escaped-slot-word fn-lbc-escape fn-lbc-escape-store-get))))))

(defthm fn-lb-slot-raw-word-of-escape-store-put
 (equal (fn-lb-slot-raw-word query (fn-lbc-escape-store-put at cell fn-lbc)) (fn-lb-slot-raw-word query fn-lbc))
 :hints (("Goal" :do-not-induct t :use ((:instance fn-lbsnr-raw-word-frame (new (fn-lbc-escape-store-put at cell fn-lbc))))
 :in-theory (union-theories (theory 'ground-zero) '(fn-lbc-escape-store-put fn-dm-nth-update-nth)))))

(defthm fn-lb-slot-raw-word-of-update-fn-lbc-row-store
 (equal (fn-lb-slot-raw-word query (update-fn-lbc-row-store value fn-lbc)) (fn-lb-slot-raw-word query fn-lbc))
 :hints (("Goal" :do-not-induct t :use ((:instance fn-lbsnr-raw-word-frame (new (update-fn-lbc-row-store value fn-lbc))))
 :in-theory (union-theories (theory 'ground-zero) '(update-fn-lbc-row-store fn-dm-nth-update-nth)))))

(defthm fn-lb-slot-raw-word-of-update-fn-lbc-slot-escape-keys
 (equal (fn-lb-slot-raw-word query (update-fn-lbc-slot-escape-keys value fn-lbc)) (fn-lb-slot-raw-word query fn-lbc))
 :hints (("Goal" :do-not-induct t :use ((:instance fn-lbsnr-raw-word-frame (new (update-fn-lbc-slot-escape-keys value fn-lbc))))
 :in-theory (union-theories (theory 'ground-zero) '(update-fn-lbc-slot-escape-keys fn-dm-nth-update-nth)))))

(defthm fn-lbc-slot-count-of-escape-store-put
 (equal (fn-lbc-slot-count (fn-lbc-escape-store-put at cell fn-lbc)) (fn-lbc-slot-count fn-lbc))
 :hints (("Goal" :do-not-induct t :use ((:instance fn-lbsnr-count-frame (new (fn-lbc-escape-store-put at cell fn-lbc))))
 :in-theory (union-theories (theory 'ground-zero) '(fn-lbc-escape-store-put fn-dm-nth-update-nth)))))

(defthm fn-lbc-slot-count-of-update-fn-lbc-row-store
 (equal (fn-lbc-slot-count (update-fn-lbc-row-store value fn-lbc)) (fn-lbc-slot-count fn-lbc))
 :hints (("Goal" :do-not-induct t :use ((:instance fn-lbsnr-count-frame (new (update-fn-lbc-row-store value fn-lbc))))
 :in-theory (union-theories (theory 'ground-zero) '(update-fn-lbc-row-store fn-dm-nth-update-nth)))))

(defthm fn-lbc-slot-count-of-update-fn-lbc-slot-escape-keys
 (equal (fn-lbc-slot-count (update-fn-lbc-slot-escape-keys value fn-lbc)) (fn-lbc-slot-count fn-lbc))
 :hints (("Goal" :do-not-induct t :use ((:instance fn-lbsnr-count-frame (new (update-fn-lbc-slot-escape-keys value fn-lbc))))
 :in-theory (union-theories (theory 'ground-zero) '(update-fn-lbc-slot-escape-keys fn-dm-nth-update-nth)))))

(defthm fn-lbc-escaped-slot-word-of-update-fn-lbc-slot-store
 (equal (fn-lbc-escaped-slot-word query keys (update-fn-lbc-slot-store value fn-lbc)) (fn-lbc-escaped-slot-word query keys fn-lbc))
 :hints (("Goal" :do-not-induct t :use ((:instance fn-lbsnr-escaped-frame (new (update-fn-lbc-slot-store value fn-lbc))))
 :in-theory (union-theories (theory 'ground-zero) '(update-fn-lbc-slot-store fn-dm-nth-update-nth)))))

(defthm fn-lbc-escaped-slot-word-of-update-fn-lbc-row-store
 (equal (fn-lbc-escaped-slot-word query keys (update-fn-lbc-row-store value fn-lbc)) (fn-lbc-escaped-slot-word query keys fn-lbc))
 :hints (("Goal" :do-not-induct t :use ((:instance fn-lbsnr-escaped-frame (new (update-fn-lbc-row-store value fn-lbc))))
 :in-theory (union-theories (theory 'ground-zero) '(update-fn-lbc-row-store fn-dm-nth-update-nth)))))

(defthm fn-lbc-escaped-slot-word-of-update-fn-lbc-slot-escape-keys
 (equal (fn-lbc-escaped-slot-word query keys (update-fn-lbc-slot-escape-keys value fn-lbc)) (fn-lbc-escaped-slot-word query keys fn-lbc))
 :hints (("Goal" :do-not-induct t :use ((:instance fn-lbsnr-escaped-frame (new (update-fn-lbc-slot-escape-keys value fn-lbc))))
 :in-theory (union-theories (theory 'ground-zero) '(update-fn-lbc-slot-escape-keys fn-dm-nth-update-nth)))))

(defthm fn-lb-slot-raw-word-of-drop-owner
 (equal (fn-lb-slot-raw-word query (mv-nth 1 (fn-lbc-slot-drop-owner slot keys fn-lbc)))
        (fn-lb-slot-raw-word query fn-lbc))
 :hints (("Goal" :do-not-induct t
 :use ((:instance fn-lbsnr-raw-word-frame (new (mv-nth 1 (fn-lbc-slot-drop-owner slot keys fn-lbc)))))
 :in-theory (union-theories (theory 'ground-zero)
 '(fn-lbwf-slot-drop-owner-field (:executable-counterpart natp) (:executable-counterpart member-equal) (:executable-counterpart equal))))))

(defthm fn-lbc-slot-count-of-drop-owner
 (equal (fn-lbc-slot-count (mv-nth 1 (fn-lbc-slot-drop-owner slot keys fn-lbc))) (fn-lbc-slot-count fn-lbc))
 :hints (("Goal" :do-not-induct t
 :use ((:instance fn-lbsnr-count-frame (new (mv-nth 1 (fn-lbc-slot-drop-owner slot keys fn-lbc)))))
 :in-theory (union-theories (theory 'ground-zero)
 '(fn-lbwf-slot-drop-owner-field (:executable-counterpart natp) (:executable-counterpart member-equal) (:executable-counterpart equal))))))

(local (defthm fn-lbsnr-len-in-bounds-update
 (implies (and (natp i) (< i (len xs))) (equal (len (update-nth i value xs)) (len xs)))
 :hints (("Goal" :induct (update-nth i value xs) :in-theory (enable update-nth len)))))

(defthm fn-lbc-slot-count-of-native-word-set
 (implies (and (natp slot) (< slot (fn-lbc-slot-count fn-lbc)))
 (equal (fn-lbc-slot-count (update-fn-lbc-slot-store
          (fn-lbc-msgid-slots-set-word slot value (fn-lbc-slot-store fn-lbc)) fn-lbc))
        (fn-lbc-slot-count fn-lbc)))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'ground-zero)
 '(fn-lbc-slot-count-by-store update-fn-lbc-slot-store fn-lbc-slot-store fn-dm-nth-update-nth
 fn-lbc-msgid-slots-set-word fn-lbc-msgid-slots$a-set-word adt-set-a fn-lbsnr-len-in-bounds-update)))))

(defthm fn-lb-slot-raw-word-of-native-set
 (implies (and (natp slot) (< slot (fn-lbc-slot-count fn-lbc)) (natp query) (< query (fn-lbc-slot-count fn-lbc)))
 (equal (fn-lb-slot-raw-word query (update-fn-lbc-slot-store
          (fn-lbc-msgid-slots-set-word slot value (fn-lbc-slot-store fn-lbc)) fn-lbc))
        (if (equal query slot) value (fn-lb-slot-raw-word query fn-lbc))))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'ground-zero)
 '(fn-lb-slot-raw-word fn-lbc-slot-count-by-store update-fn-lbc-slot-store fn-lbc-slot-store
 fn-dm-nth-update-nth fn-lbc-msgid-slots-set-word fn-lbc-msgid-slots$a-set-word adt-set-a
 fn-lbsnr-len-in-bounds-update nth)))))
