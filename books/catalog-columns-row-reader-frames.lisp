; Derived constructor support; local algebra does not escape this book.
(in-package "ACL2")
(include-book "catalog-columns-row-projections")

(defthm fn-lbc-count-frame-by-definition
 (implies (and (equal (nth 0 new) (nth 0 fn-lbc)))
  (equal (fn-lbc-count  new) (fn-lbc-count  fn-lbc)))
 :hints (("Goal" :do-not-induct t :in-theory
  (union-theories (theory 'ground-zero) '(fn-lbc-count fn-lbc-row-store)))))

(defthm fn-lbc-word-frame-by-definition
 (implies (and (equal (nth 0 new) (nth 0 fn-lbc)))
  (equal (fn-lbc-word field i new) (fn-lbc-word field i fn-lbc)))
 :hints (("Goal" :do-not-induct t :in-theory
  (union-theories (theory 'ground-zero) '(fn-lbc-word fn-lbc-row-store)))))

(defthm fn-lbc-directory-field-frame-by-definition
 (implies (and (equal (nth 5 new) (nth 5 fn-lbc)))
  (equal (fn-lbc-directory-field field i new) (fn-lbc-directory-field field i fn-lbc)))
 :hints (("Goal" :do-not-induct t :in-theory
  (union-theories (theory 'ground-zero) '(fn-lbc-directory-field fn-lbc-directory-store)))))

(defthm fn-lbc-loc0-frame-by-definition
 (implies (and (equal (nth 0 new) (nth 0 fn-lbc)))
  (equal (fn-lbc-loc0 i new) (fn-lbc-loc0 i fn-lbc)))
 :hints (("Goal" :do-not-induct t :in-theory
  (union-theories (theory 'ground-zero) '(fn-lbc-loc0 fn-lbc-row-store)))))

(defthm fn-lbc-loc1-frame-by-definition
 (implies (and (equal (nth 0 new) (nth 0 fn-lbc)))
  (equal (fn-lbc-loc1 i new) (fn-lbc-loc1 i fn-lbc)))
 :hints (("Goal" :do-not-induct t :in-theory
  (union-theories (theory 'ground-zero) '(fn-lbc-loc1 fn-lbc-row-store)))))

(defthm fn-lbc-escape-store-get-frame-by-definition
 (implies (and (equal (nth 9 new) (nth 9 fn-lbc)))
  (equal (fn-lbc-escape-store-get i new) (fn-lbc-escape-store-get i fn-lbc)))
 :hints (("Goal" :do-not-induct t :in-theory
  (union-theories (theory 'ground-zero) '(fn-lbc-escape-store-get)))))

(defthm fn-lbc-escape-frame-by-definition
 (implies (and (equal (nth 9 new) (nth 9 fn-lbc)))
  (equal (fn-lbc-escape i field new) (fn-lbc-escape i field fn-lbc)))
 :hints (("Goal" :do-not-induct t :in-theory
  (union-theories (theory 'ground-zero) '(fn-lbc-escape fn-lbc-escape-store-get)))))

(defthm fn-lbc-value-frame-by-definition
 (implies (and (equal (nth 0 new) (nth 0 fn-lbc)) (equal (nth 9 new) (nth 9 fn-lbc)))
  (equal (fn-lbc-value i field new) (fn-lbc-value i field fn-lbc)))
 :hints (("Goal" :do-not-induct t :in-theory
  (union-theories (theory 'ground-zero) '(fn-lbc-value fn-lbc-escape fn-lbc-escape-store-get fn-lbc-word fn-lbc-row-store)))))

(defthm fn-lbc-directory-value-frame-by-definition
 (implies (and (equal (nth 5 new) (nth 5 fn-lbc)) (equal (nth 9 new) (nth 9 fn-lbc)))
  (equal (fn-lbc-directory-value i field new) (fn-lbc-directory-value i field fn-lbc)))
 :hints (("Goal" :do-not-induct t :in-theory
  (union-theories (theory 'ground-zero) '(fn-lbc-directory-value fn-lbc-escape fn-lbc-escape-store-get fn-lbc-directory-field fn-lbc-directory-store)))))

(defthm fn-lbc-flag-frame-by-definition
 (implies (and (equal (nth 0 new) (nth 0 fn-lbc)))
  (equal (fn-lbc-flag i bit new) (fn-lbc-flag i bit fn-lbc)))
 :hints (("Goal" :do-not-induct t :in-theory
  (union-theories (theory 'ground-zero) '(fn-lbc-flag fn-lbc-word fn-lbc-row-store)))))

(defthm fn-lbc-escape-store-get-of-put
 (equal (fn-lbc-escape-store-get key (fn-lbc-escape-store-put at cell fn-lbc))
        (if (equal key at) cell (fn-lbc-escape-store-get key fn-lbc)))
 :hints (("Goal" :in-theory (e/d (fn-lbc-escape-store-get fn-lbc-escape-store-put) (fn-lbc-p)))))
