; Derived constructor support; local algebra does not escape this book.
(in-package "ACL2")
(include-book "catalog-columns-reader-writer-frames")

(defthm fn-lbc-value-of-escape-store-put
 (equal (fn-lbc-value i field (fn-lbc-escape-store-put key cell fn-lbc))
  (let ((escape (assoc-eq field (if (equal i key) cell (fn-lbc-escape-store-get i fn-lbc)))))
   (if escape (cdr escape) (fn-lbc-word field i fn-lbc))))
 :hints (("Goal" :do-not-induct t :in-theory
  (union-theories (theory 'minimal-theory)
   '(fn-lbc-value fn-lbc-escape fn-lbc-escape-store-get-of-put fn-lbc-word-of-escape-store-put)))))

(defthm fn-lbc-directory-value-of-escape-store-put
 (equal (fn-lbc-directory-value i field (fn-lbc-escape-store-put key cell fn-lbc))
  (let ((escape (assoc-eq field (if (equal i key) cell (fn-lbc-escape-store-get i fn-lbc)))))
   (if escape (cdr escape) (fn-lbc-directory-field field i fn-lbc))))
 :hints (("Goal" :do-not-induct t :in-theory
  (union-theories (theory 'minimal-theory)
   '(fn-lbc-directory-value fn-lbc-escape fn-lbc-escape-store-get-of-put
     fn-lbc-directory-field-of-escape-store-put)))))

(defthm fn-lbc-word-of-directory-store-update-by-definition
 (equal (fn-lbc-word field i (update-fn-lbc-directory-store directory fn-lbc))
        (fn-lbc-word field i fn-lbc))
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-lbc-word-frame-by-definition (new (update-fn-lbc-directory-store directory fn-lbc))))
  :in-theory (union-theories (theory 'ground-zero)
   '(update-fn-lbc-directory-store fn-dm-nth-update-nth nth)))))

(defthm fn-lbc-directory-field-of-row-store-update-by-definition
 (equal (fn-lbc-directory-field field i (update-fn-lbc-row-store rows fn-lbc))
        (fn-lbc-directory-field field i fn-lbc))
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-lbc-directory-field-frame-by-definition (new (update-fn-lbc-row-store rows fn-lbc))))
  :in-theory (union-theories (theory 'ground-zero)
   '(update-fn-lbc-row-store fn-dm-nth-update-nth nth)))))
