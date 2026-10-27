; Derived constructor support; local algebra does not escape this book.
(in-package "ACL2")
(include-book "catalog-columns-slot-insert-refinement")

(defun-nx fn-lb-slot-owner-keys-below (keys upper)
 (if (consp keys) (and (natp (car keys)) (< (car keys) upper)
 (fn-lb-slot-owner-keys-below (cdr keys) upper)) (null keys)))

(defthm fn-lb-slot-owner-keys-below-nonmember
 (implies (and (fn-lb-slot-owner-keys-below keys upper) (natp key) (<= upper key))
 (not (member-equal key keys)))
 :hints (("Goal" :induct (len keys) :in-theory (union-theories (theory 'ground-zero)
 '(len fn-lb-slot-owner-keys-below member-equal natp)))))

(defthm fn-lb-slot-owner-keys-below-widen
 (implies (and (fn-lb-slot-owner-keys-below keys lower) (<= lower upper))
 (fn-lb-slot-owner-keys-below keys upper))
 :hints (("Goal" :induct (len keys) :in-theory (union-theories (theory 'ground-zero)
 '(len fn-lb-slot-owner-keys-below)))))

(defthm fn-lb-slot-owner-keys-below-of-drop-owner
 (implies (fn-lb-slot-owner-keys-below keys upper)
 (fn-lb-slot-owner-keys-below (mv-nth 0 (fn-lbc-slot-drop-owner slot keys fn-lbc)) upper))
 :hints (("Goal" :induct (fn-lbc-slot-drop-owner slot keys fn-lbc)
 :in-theory (union-theories (theory 'ground-zero)
 '(fn-lbc-slot-drop-owner fn-lb-slot-owner-keys-below mv-nth (:type-prescription fn-lbc-slot-drop-owner))))))

(local (defthm fn-lbsop-key-bound-of-car-drop
 (implies (fn-lb-slot-owner-keys-below keys upper)
 (fn-lb-slot-owner-keys-below (car (fn-lbc-slot-drop-owner slot keys fn-lbc)) upper))
 :hints (("Goal" :do-not-induct t :use ((:instance fn-lb-slot-owner-keys-below-of-drop-owner))
 :in-theory (theory 'ground-zero)))))

(defthm fn-lb-slot-owner-keys-below-of-slot-put
 (implies (and (natp i) (fn-lb-slot-owner-keys-below (fn-lbc-slot-escape-keys fn-lbc) i))
 (fn-lb-slot-owner-keys-below (fn-lbc-slot-escape-keys (fn-lbc-slot-put slot (+ 1 i) fn-lbc)) (+ 1 i)))
 :hints (("Goal" :do-not-induct t
 :use ((:instance fn-lbc-slot-escape-keys-of-slot-put (ordinal (+ 1 i)))
 (:instance fn-lb-slot-owner-keys-below-widen (keys (fn-lbc-slot-escape-keys fn-lbc)) (lower i) (upper (+ 1 i)))
 (:instance fn-lb-slot-owner-keys-below-of-drop-owner (keys (fn-lbc-slot-escape-keys fn-lbc)) (upper i)))
 :in-theory (union-theories (theory 'ground-zero)
 '(fn-lb-slot-owner-keys-below fn-lbsop-key-bound-of-car-drop natp nfix zp)))))

(local (defthm fn-lbsop-escape-of-update-fn-lbc-slot-store
 (equal (fn-lbc-escape key :msgid-slot (update-fn-lbc-slot-store value fn-lbc)) (fn-lbc-escape key :msgid-slot fn-lbc))
 :hints (("Goal" :in-theory (union-theories (theory 'ground-zero)
 '(fn-lbc-escape fn-lbc-escape-store-get update-fn-lbc-slot-store fn-dm-nth-update-nth))))))

(local (defthm fn-lbsop-escape-of-update-fn-lbc-row-store
 (equal (fn-lbc-escape key :msgid-slot (update-fn-lbc-row-store value fn-lbc)) (fn-lbc-escape key :msgid-slot fn-lbc))
 :hints (("Goal" :in-theory (union-theories (theory 'ground-zero)
 '(fn-lbc-escape fn-lbc-escape-store-get update-fn-lbc-row-store fn-dm-nth-update-nth))))))

(local (defthm fn-lbsop-escape-of-update-fn-lbc-slot-escape-keys
 (equal (fn-lbc-escape key :msgid-slot (update-fn-lbc-slot-escape-keys value fn-lbc)) (fn-lbc-escape key :msgid-slot fn-lbc))
 :hints (("Goal" :in-theory (union-theories (theory 'ground-zero)
 '(fn-lbc-escape fn-lbc-escape-store-get update-fn-lbc-slot-escape-keys fn-dm-nth-update-nth))))))

(defthm fn-lbc-slot-escape-of-slot-put-unlisted-other
 (implies (and (not (member-equal key (fn-lbc-slot-escape-keys fn-lbc)))
              (not (equal key (if (zp (nfix ordinal)) 0 (- (nfix ordinal) 1)))))
 (equal (fn-lbc-escape key :msgid-slot (fn-lbc-slot-put slot ordinal fn-lbc))
        (fn-lbc-escape key :msgid-slot fn-lbc)))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'ground-zero)
 '(fn-lbc-slot-put fn-lbc-escape-of-drop-unlisted-key fn-lbc-slot-escape-of-cell-put
 fn-lbsop-escape-of-update-fn-lbc-slot-store fn-lbsop-escape-of-update-fn-lbc-row-store
 fn-lbsop-escape-of-update-fn-lbc-slot-escape-keys (:type-prescription fn-lbc-slot-drop-owner))))))

(defthm fn-lbc-slot-escape-of-slot-put-future
 (implies (and (natp i) (natp key) (< i key)
 (fn-lb-slot-owner-keys-below (fn-lbc-slot-escape-keys fn-lbc) i))
 (equal (fn-lbc-escape key :msgid-slot (fn-lbc-slot-put slot (+ 1 i) fn-lbc))
        (fn-lbc-escape key :msgid-slot fn-lbc)))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'ground-zero)
 '(fn-lbc-slot-escape-of-slot-put-unlisted-other fn-lb-slot-owner-keys-below-nonmember natp nfix zp)))))

(defthm fn-lb-slot-owner-keys-below-of-slot-insert
 (implies (and (natp i) (fn-lb-slot-owner-keys-below (fn-lbc-slot-escape-keys fn-lbc) i))
 (fn-lb-slot-owner-keys-below (fn-lbc-slot-escape-keys (fn-lbc-slot-insert i slot fuel fn-lbc)) (+ 1 i)))
 :hints (("Goal" :induct (fn-lbc-slot-insert i slot fuel fn-lbc)
 :in-theory (union-theories (theory 'ground-zero)
 '(fn-lbc-slot-insert fn-lb-slot-owner-keys-below-of-slot-put fn-lb-slot-owner-keys-below-widen natp)))))

(defthm fn-lbc-slot-escape-of-slot-insert-future
 (implies (and (natp i) (natp key) (< i key)
 (fn-lb-slot-owner-keys-below (fn-lbc-slot-escape-keys fn-lbc) i))
 (equal (fn-lbc-escape key :msgid-slot (fn-lbc-slot-insert i slot fuel fn-lbc))
        (fn-lbc-escape key :msgid-slot fn-lbc)))
 :hints (("Goal" :induct (fn-lbc-slot-insert i slot fuel fn-lbc)
 :in-theory (union-theories (theory 'ground-zero)
 '(fn-lbc-slot-insert fn-lbc-slot-escape-of-slot-put-future)))))
