; Derived constructor support; local algebra does not escape this book.
(in-package "ACL2")
(include-book "catalog-columns-slot-word-frames")

(local (defthm fn-lbss-assoc-of-put-other
 (implies (not (equal field key))
  (equal (assoc-eq field (put-assoc-eq key value cell)) (assoc-eq field cell)))
 :hints (("Goal" :induct (put-assoc-eq key value cell)
  :in-theory (union-theories (theory 'ground-zero) '(put-assoc-eq assoc-eq))))))

(local (defthm fn-lbss-escape-of-update-slot-store
 (equal (fn-lbc-escape i field (update-fn-lbc-slot-store value fn-lbc))
        (fn-lbc-escape i field fn-lbc))
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-lbc-escape-frame-by-definition (new (update-fn-lbc-slot-store value fn-lbc))))
  :in-theory (union-theories (theory 'ground-zero)
   '(update-fn-lbc-slot-store fn-dm-nth-update-nth))))))

(local (defthm fn-lbss-escape-of-update-slot-escape-keys
 (equal (fn-lbc-escape i field (update-fn-lbc-slot-escape-keys value fn-lbc))
        (fn-lbc-escape i field fn-lbc))
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-lbc-escape-frame-by-definition (new (update-fn-lbc-slot-escape-keys value fn-lbc))))
  :in-theory (union-theories (theory 'ground-zero)
   '(update-fn-lbc-slot-escape-keys fn-dm-nth-update-nth))))))

(local (defthm fn-lbss-escape-of-update-row-store
 (equal (fn-lbc-escape i field (update-fn-lbc-row-store value fn-lbc))
        (fn-lbc-escape i field fn-lbc))
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-lbc-escape-frame-by-definition (new (update-fn-lbc-row-store value fn-lbc))))
  :in-theory (union-theories (theory 'ground-zero)
   '(update-fn-lbc-row-store fn-dm-nth-update-nth))))))

(local (defthm fn-lbss-word-of-update-slot-store
 (equal (fn-lbc-word field i (update-fn-lbc-slot-store value fn-lbc))
        (fn-lbc-word field i fn-lbc))
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-lbc-word-frame-by-definition (new (update-fn-lbc-slot-store value fn-lbc))))
  :in-theory (union-theories (theory 'ground-zero)
   '(update-fn-lbc-slot-store fn-dm-nth-update-nth))))))

(local (defthm fn-lbss-word-of-update-slot-escape-keys
 (equal (fn-lbc-word field i (update-fn-lbc-slot-escape-keys value fn-lbc))
        (fn-lbc-word field i fn-lbc))
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-lbc-word-frame-by-definition (new (update-fn-lbc-slot-escape-keys value fn-lbc))))
  :in-theory (union-theories (theory 'ground-zero)
   '(update-fn-lbc-slot-escape-keys fn-dm-nth-update-nth))))))

(local (defthm fn-lbss-escape-of-put-slot-metadata
 (implies (not (equal field :msgid-slot))
  (equal (fn-lbc-escape i field (fn-lbc-escape-store-put key
           (put-assoc-eq :msgid-slot value (fn-lbc-escape-store-get key fn-lbc)) fn-lbc))
         (fn-lbc-escape i field fn-lbc)))
 :hints (("Goal" :do-not-induct t :in-theory
  (union-theories (theory 'ground-zero)
   '(fn-lbc-escape fn-lbc-escape-store-get-of-put fn-lbss-assoc-of-put-other))))))

(defthm fn-lbc-escape-of-slot-put-other-key
 (implies (not (equal field :msgid-slot))
  (equal (fn-lbc-escape i field (fn-lbc-slot-put slot ordinal fn-lbc))
         (fn-lbc-escape i field fn-lbc)))
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-lbc-escape-of-slot-drop-owner-other-key (keys (fn-lbc-slot-escape-keys fn-lbc))))
  :in-theory (set-difference-theories (union-theories (theory 'ground-zero)
   '(fn-lbc-slot-put fn-lbss-escape-of-update-slot-store fn-lbss-escape-of-update-slot-escape-keys
     fn-lbss-escape-of-update-row-store fn-lbss-escape-of-put-slot-metadata (:type-prescription fn-lbc-slot-drop-owner))) '((tau-system))))))

(defthm fn-lbc-word-of-slot-put-other-field
 (implies (not (equal field :flags))
  (equal (fn-lbc-word field i (fn-lbc-slot-put slot ordinal fn-lbc))
         (fn-lbc-word field i fn-lbc)))
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-lbc-word-of-slot-drop-owner (read-field field) (read-i i) (keys (fn-lbc-slot-escape-keys fn-lbc))))
  :in-theory (set-difference-theories (union-theories (theory 'ground-zero)
   '(fn-lbc-slot-put fn-lbss-word-of-update-slot-store fn-lbss-word-of-update-slot-escape-keys
     fn-lbc-word-of-escape-store-put fn-lbc-word-of-in-bounds-set-flags-other-field
     nfix (:type-prescription fn-lbc-slot-drop-owner))) '((tau-system))))))

(defthm fn-lbc-value-of-slot-put-other-field
 (implies (and (not (equal field :msgid-slot)) (not (equal field :flags)))
  (equal (fn-lbc-value i field (fn-lbc-slot-put slot ordinal fn-lbc))
         (fn-lbc-value i field fn-lbc)))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'minimal-theory)
  '(fn-lbc-value fn-lbc-escape-of-slot-put-other-key fn-lbc-word-of-slot-put-other-field)))))

(defthm fn-lbc-directory-value-of-slot-put-other-field
 (implies (not (equal field :msgid-slot))
  (equal (fn-lbc-directory-value i field (fn-lbc-slot-put slot ordinal fn-lbc))
         (fn-lbc-directory-value i field fn-lbc)))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'minimal-theory)
  '(fn-lbc-directory-value fn-lbc-escape-of-slot-put-other-key fn-lbc-directory-field-of-slot-put)))))
