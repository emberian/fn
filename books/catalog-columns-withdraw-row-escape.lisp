; Escaped withdrawal values replace only their two keys.
(in-package "ACL2")
(include-book "catalog-columns-withdraw-row-frames")
(include-book "catalog-columns-row-reader-frames")

(local (defthm fn-lbcwde-assoc-remove-other
 (implies (not (equal field key))
  (equal (assoc-eq field (remove-assoc-equal key cell)) (assoc-eq field cell)))
 :hints (("Goal" :induct (remove-assoc-equal key cell)
  :in-theory (union-theories (theory 'ground-zero) '(remove-assoc-equal assoc-eq))))))

(defthm fn-lbc-withdrawal-escape-cell-other-by-definition
 (implies (and (not (equal field :withdrawal-at)) (not (equal field :withdrawal-by)))
  (equal (assoc-eq field (fn-lbc-withdrawal-escape-cell version by cell))
         (assoc-eq field cell)))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'ground-zero)
  '(fn-lbc-withdrawal-escape-cell fn-lbc-sparse-u64 fn-lbcwde-assoc-remove-other assoc-eq binary-append)))))

(local (defthm fn-lbcwde-get-of-put
 (equal (fn-lbc-escape-store-get key (fn-lbc-escape-store-put at cell fn-lbc-v))
  (if (equal key at) cell (fn-lbc-escape-store-get key fn-lbc-v)))
 :hints (("Goal" :in-theory (e/d (fn-lbc-escape-store-get fn-lbc-escape-store-put) (fn-lbc-p))))))
(local (defthm fn-lbcwde-get-of-row-update
 (equal (fn-lbc-escape-store-get key (update-fn-lbc-row-store rows fn-lbc-v))
  (fn-lbc-escape-store-get key fn-lbc-v))
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-lbc-escape-store-get-frame-by-definition
   (i key) (fn-lbc fn-lbc-v) (new (update-fn-lbc-row-store rows fn-lbc-v))))
  :in-theory (union-theories (theory 'ground-zero)
   '(update-fn-lbc-row-store fn-dm-nth-update-nth))))))

(defthm fn-lbc-escape-store-get-of-set-withdrawal-by-definition
 (equal (fn-lbc-escape-store-get j (fn-lbc-set-withdrawal i version by fn-lbc-v))
  (if (equal i j)
   (fn-lbc-withdrawal-escape-cell version by (fn-lbc-escape-store-get i fn-lbc-v))
   (fn-lbc-escape-store-get j fn-lbc-v)))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'ground-zero)
  '(fn-lbc-set-withdrawal fn-lbcwde-get-of-put fn-lbcwde-get-of-row-update)))))

(defthm fn-lbc-escape-other-of-set-withdrawal-by-definition
 (implies (and (not (equal field :withdrawal-at)) (not (equal field :withdrawal-by)))
  (equal (fn-lbc-escape j field (fn-lbc-set-withdrawal i version by fn-lbc-v))
         (fn-lbc-escape j field fn-lbc-v)))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'ground-zero)
  '(fn-lbc-escape fn-lbc-escape-store-get-of-set-withdrawal-by-definition
    fn-lbc-withdrawal-escape-cell-other-by-definition)))))

(local (defthm fn-lbcwde-assoc-remove-same
 (equal (assoc-eq key (remove-assoc-equal key cell)) nil)
 :hints (("Goal" :induct (remove-assoc-equal key cell)
  :in-theory (union-theories (theory 'ground-zero) '(remove-assoc-equal assoc-eq))))))

(defthm fn-lbc-withdrawal-escape-cell-withdrawal-at-by-definition
 (equal (assoc-eq :withdrawal-at (fn-lbc-withdrawal-escape-cell version by cell))
  (if (unsigned-byte-p 64 version) nil (cons :withdrawal-at version)))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'ground-zero)
  '(fn-lbc-withdrawal-escape-cell fn-lbc-sparse-u64 fn-lbcwde-assoc-remove-same
    fn-lbcwde-assoc-remove-other assoc-eq binary-append)))))

(defthm fn-lbc-withdrawal-escape-cell-withdrawal-by-by-definition
 (equal (assoc-eq :withdrawal-by (fn-lbc-withdrawal-escape-cell version by cell))
  (if (unsigned-byte-p 64 by) nil (cons :withdrawal-by by)))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'ground-zero)
  '(fn-lbc-withdrawal-escape-cell fn-lbc-sparse-u64 fn-lbcwde-assoc-remove-same
    fn-lbcwde-assoc-remove-other assoc-eq binary-append)))))
