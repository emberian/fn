; Resident row correspondence; independent of NNTP command execution.
(in-package "ACL2")
(include-book "catalog-columns-guards")
(local (include-book "arithmetic-5/top" :dir :system))

(local (defthm fn-lbp-row-corr-served-projection
 (implies (fn-lbc-row-corr i row pm fn-lbc log)
  (equal (fn-lbc-served-row i fn-lbc) (fn-cat-served-projection row)))
 :hints (("Goal" :in-theory '(fn-lbc-row-corr)))))

(defun fn-lbp-rows-corr-induction (base j rows pm)
  (declare (xargs :measure (nfix j) :verify-guards nil))
  (if (and (consp rows) (not (zp j)))
      (fn-lbp-rows-corr-induction (+ 1 (nfix base)) (- j 1) (cdr rows)
                                 (max (nfix pm) (nfix (fn-record-stamp (car rows)))))
    (list base pm)))

(local (defthm fn-lbp-rows-corr-served-nth
  (implies (and (fn-lbc-rows-corr base rows pm fn-lbc log)
                (natp base) (natp j) (< j (len rows)))
           (equal (fn-lbc-served-row (+ base j) fn-lbc)
                  (fn-cat-served-projection (nth j rows))))
  :hints (("Goal" :induct (fn-lbp-rows-corr-induction base j rows pm)
 :in-theory (union-theories (theory 'ground-zero)
 '(fn-lbp-rows-corr-induction fn-lbc-rows-corr nth natp nfix zp max fn-lbp-row-corr-served-projection))))))

(defthm fn-lbc-served-row-is-abstract
  (implies (and (fn-lbc-p fn-lbc) (fn-cat$ap rows) (fn-lbc-corr fn-lbc rows log)
                (natp i) (< i (len rows)))
           (equal (fn-lbc-served-row i fn-lbc)
                  (fn-cat-served-projection (nth i rows))))
  :hints (("Goal" :use ((:instance fn-lbp-rows-corr-served-nth (base 0) (j i) (pm 0)))
           :in-theory (e/d (fn-lbc-corr) (fn-lbc-p fn-cat$ap fn-lbc-rows-corr
                            fn-lbc-served-row fn-cat-served-projection)))))

(local (defthm fn-lbp-restore-control-of-homes
 (implies (true-listp control)
  (equal (fn-lbc-restore-control
          (list (len control) (take (min 3 (len control)) control) (nthcdr 4 control))
          (nth 3 control))
         control))
 :hints (("Goal" :in-theory (enable fn-lbc-restore-control take nthcdr nth len)
          :expand ((len control) (len (cdr control)) (len (cddr control))
                   (len (cdddr control)))))))

(local (defthm fn-lbp-row-reconstruction-shapes
 (implies (fn-cat-rowp row)
  (and (fn-held-shapep row) (fn-hf-shapep (fn-held-facts row))
       (true-listp (fn-hf-control (fn-held-facts row)))))
 :rule-classes nil
 :hints (("Goal" :in-theory '(fn-cat-rowp fn-hf-p)))))

(local (defthm fn-lbp-row-corr-homes
 (implies (fn-lbc-row-corr i row pm fn-lbc log)
  (equal (nth 7 (fn-lbc-home-entry i fn-lbc log)) (fn-lb-log-model-homes row)))
 :hints (("Goal" :in-theory '(fn-lbc-row-corr)))))

(local (defthm fn-lbp-true-list-fix-identity
 (implies (true-listp x) (equal (true-list-fix x) x))
 :hints (("Goal" :induct (true-list-fix x) :in-theory (enable true-list-fix true-listp)))))

(local (defthm fn-lbp-restore-control-canonical
 (implies (true-listp control)
  (equal (fn-lbc-restore-control
          (list (len control) (take (min 3 (len control)) control) (nthcdr 4 control))
          (cadddr control))
         control))
 :hints (("Goal" :use fn-lbp-restore-control-of-homes
          :in-theory (e/d (nth) (fn-lbc-restore-control len take min nthcdr
                                fn-lbp-restore-control-of-homes))))))

(local (defthm fn-lbp-at-of-row-corr
 (implies (and (fn-cat-rowp row) (fn-lbc-row-corr i row pm fn-lbc log))
          (equal (fn-lbc-at i fn-lbc log) row))
 :hints (("Goal" :use ((:instance fn-lbp-row-reconstruction-shapes)
                      (:instance fn-held-make-of-accessors (x row))
                      (:instance fn-hf-make-of-accessors (x (fn-held-facts row))))
 :in-theory (union-theories (set-difference-theories (theory 'ground-zero) '(true-listp len min nfix take nthcdr true-list-fix))
 '(fn-lbc-at fn-lbp-row-corr-served-projection fn-lbp-row-corr-homes fn-cat-served-projection fn-lb-log-model-homes fn-hf-nov
   fn-held-accessors-are-the-wire-accessors fn-cbor-ag-car fn-cbor-ag-cdr
   fn-lbp-restore-control-canonical nth fn-lbp-true-list-fix-identity
   ))))))

(local (defthm fn-lbp-rows-corr-full-nth
  (implies (and (fn-lbc-rows-corr base rows pm fn-lbc log) (fn-cat-rowsp rows)
                (natp base) (natp j) (< j (len rows)))
           (equal (fn-lbc-at (+ base j) fn-lbc log) (nth j rows)))
 :hints (("Goal" :induct (fn-lbp-rows-corr-induction base j rows pm)
 :in-theory (union-theories (theory 'ground-zero)
  '(fn-lbp-rows-corr-induction fn-lbc-rows-corr fn-cat-rowsp nth natp nfix zp max
    fn-lbp-at-of-row-corr))))))

(defthm fn-lbc-row-is-abstract
  (implies (and (fn-lbc-p fn-lbc) (fn-cat$ap rows) (fn-lbc-corr fn-lbc rows log)
                (natp i) (< i (len rows)))
           (equal (fn-lbc-at i fn-lbc log) (nth i rows)))
 :hints (("Goal" :use ((:instance fn-lbp-rows-corr-full-nth (base 0) (j i) (pm 0)))
 :in-theory (union-theories (theory 'ground-zero) '(fn-lbc-corr fn-cat$ap natp)))))

(local (defthm fn-lbr10-served-projection-fields
 (implies (equal (fn-lbc-served-row i fn-lbc) (fn-cat-served-projection row))
  (and (equal (fn-lbc-msgid i fn-lbc) (fn-record-msgid row))
       (equal (fn-lbc-value i :handle fn-lbc) (fn-record-payload row))
       (equal (fn-lbc-groups i fn-lbc) (fn-record-groups row))
       (equal (fn-lbc-numbers i fn-lbc) (fn-held-numbers row))
       (equal (fn-lbc-value i :stamp fn-lbc) (fn-record-stamp row))
       (equal (fn-lbc-withdrawn i fn-lbc) (fn-held-withdrawn row))))
 :hints (("Goal" :in-theory (union-theories (theory 'ground-zero)
  '(fn-lbc-served-row fn-cat-served-projection))))))

(defthm fn-lbc-served-fields-are-abstract
 (implies (and (fn-lbc-p fn-lbc) (fn-cat$ap rows) (fn-lbc-corr fn-lbc rows log)
               (natp i) (< i (len rows)))
  (and (equal (fn-lbc-msgid i fn-lbc) (fn-record-msgid (nth i rows)))
       (equal (fn-lbc-value i :handle fn-lbc) (fn-record-payload (nth i rows)))
       (equal (fn-lbc-groups i fn-lbc) (fn-record-groups (nth i rows)))
       (equal (fn-lbc-numbers i fn-lbc) (fn-held-numbers (nth i rows)))
       (equal (fn-lbc-value i :stamp fn-lbc) (fn-record-stamp (nth i rows)))
       (equal (fn-lbc-withdrawn i fn-lbc) (fn-held-withdrawn (nth i rows)))) )
 :hints (("Goal" :use ((:instance fn-lbc-served-row-is-abstract)
                       (:instance fn-lbr10-served-projection-fields (row (nth i rows))))
 :in-theory (union-theories (theory 'ground-zero) '(natp)))))

(defthm fn-lbc-corr-count-is-length
 (implies (fn-lbc-corr fn-lbc rows log) (equal (fn-lbc-count fn-lbc) (len rows)))
 :hints (("Goal" :in-theory '(fn-lbc-corr))))

(defthm fn-lbc-original-nov-is-abstract
 (implies (and (fn-lbc-p fn-lbc) (fn-cat$ap rows) (fn-lbc-corr fn-lbc rows log)
               (natp i) (< i (len rows)))
  (equal (fn-lbc-original-nov i fn-lbc) (fn-hf-nov (fn-held-facts (nth i rows)))))
 :hints (("Goal" :use fn-lbc-served-row-is-abstract
  :in-theory (union-theories (theory 'ground-zero) '(fn-lbc-served-row fn-cat-served-projection)))))
