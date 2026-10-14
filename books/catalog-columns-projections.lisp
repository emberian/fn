; LB row/column refinements; local proof cuts have real book scope.
(in-package "ACL2")
(include-book "catalog-columns-properties")

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

(defthm fn-lbc-article-is-row-article
 (implies (and (fn-lbc-p fn-lbc) (fn-cat$ap rows) (fn-lbc-corr fn-lbc rows log)
               (natp i) (< i (len rows)))
  (equal (fn-lbc-article i fn-lbc) (fn-cat-row-article i fn-arena rows)))
 :hints (("Goal" :use fn-lbc-served-fields-are-abstract
 :in-theory (e/d (fn-lbc-article fn-cat-row-article fn-cat$a-at)
 (fn-lbc-p fn-cat$ap fn-lbc-corr fn-lbc-msgid fn-lbc-value fn-lbc-groups fn-lbc-numbers
  fn-make-article fn-lbc-served-fields-are-abstract)))))

(defthm fn-lb-arena-is-log-binds-nth
 (implies (and (fn-lb-arena-is-log fn-arena rows log) (natp i) (< i (len rows)))
  (equal (fn-nntp-payload-bytes (fn-record-payload (nth i rows)) fn-arena)
         (fn-lb-log-payload (nth i rows) log)))
 :hints (("Goal" :induct (nth i rows)
 :in-theory (e/d (fn-lb-arena-is-log nth)
 (fn-nntp-payload-bytes fn-record-payload fn-lb-log-payload)))))

(local (defthm fn-lbr10-row-stamp-natural
 (implies (fn-cat-rowp row) (natp (fn-record-stamp row)))
 :hints (("Goal" :in-theory (union-theories (theory 'ground-zero)
  '(fn-cat-rowp fn-record-stampp fn-record-uint64p fn-held-accessors-are-the-wire-accessors))))))

(local (defthm fn-lbr10-row-withdrawal-typed
 (implies (and (fn-cat$ap rows) (natp i) (< i (len rows)))
  (fn-held-withdrawnp (fn-held-withdrawn (nth i rows))))
 :hints (("Goal" :use ((:instance fn-cat-rowp-of-nth-of-rowsp (xs rows))
  (:instance fn-cat-rowp-fields (h (nth i rows))))
 :in-theory (union-theories (theory 'ground-zero) '(fn-cat$ap))))))

(defthm fn-lbc-abstract-row-stamp-natural
 (implies (and (fn-cat$ap rows) (natp i) (< i (len rows)))
  (natp (fn-record-stamp (nth i rows))))
 :hints (("Goal" :use ((:instance fn-cat-rowp-of-nth-of-rowsp (xs rows))
  (:instance fn-lbr10-row-stamp-natural (row (nth i rows))))
 :in-theory (union-theories (theory 'ground-zero) '(fn-cat$ap)))))

(defthm fn-lbc-corr-count-is-length
 (implies (fn-lbc-corr fn-lbc rows log) (equal (fn-lbc-count fn-lbc) (len rows)))
 :hints (("Goal" :in-theory '(fn-lbc-corr))))

(defthm fn-lbc-visible-is-row-visible
 (implies (and (fn-lbc-p fn-lbc) (fn-cat$ap rows) (fn-lbc-corr fn-lbc rows log)
  (natp i) (< i (len rows)) (natp v))
 (equal (fn-lbc-visiblep i v fn-lbc) (fn-cat-visiblep i v rows)))
 :hints (("Goal" :do-not-induct t
 :use fn-lbr10-row-withdrawal-typed
 :in-theory (union-theories (theory 'ground-zero)
  '(fn-lbc-visiblep fn-cat-visiblep fn-held-withdrawnp fn-lbc-corr-count-is-length
    fn-lbc-served-fields-are-abstract natp nfix rfix)))))

(local (defthm fn-lbr10-row-corr-metadata-by-definition
 (implies (fn-lbc-row-corr i row pm fn-lbc log)
  (and (equal (fn-lbc-value i :prefix-max fn-lbc) pm)
       (equal (fn-lbc-flag i *fn-lbc-reclaimed-bit* fn-lbc)
              (fn-rcl-tombstonep (fn-lb-log-payload row log)))
       (fn-arx-entry-ok (fn-lb-entry-octets
          (fn-loc-segment (fn-lbc-loc0 i fn-lbc) (fn-lbc-loc1 i fn-lbc))
          (fn-loc-offset (fn-lbc-loc0 i fn-lbc) (fn-lbc-loc1 i fn-lbc)) log)
        (fn-lb-entry-protected-len
          (fn-loc-segment (fn-lbc-loc0 i fn-lbc) (fn-lbc-loc1 i fn-lbc))
          (fn-loc-offset (fn-lbc-loc0 i fn-lbc) (fn-lbc-loc1 i fn-lbc)) log))))
 :hints (("Goal" :in-theory '(fn-lbc-row-corr)))))

(local (defun fn-lbr10-row-metadata-induct (base j rows pm)
 (declare (xargs :measure (nfix j) :verify-guards nil))
 (if (and (consp rows) (not (zp j)))
  (fn-lbr10-row-metadata-induct (+ 1 (nfix base)) (- j 1) (cdr rows)
   (max (nfix pm) (nfix (fn-record-stamp (car rows)))))
  (list base pm))))

(local (defthm fn-lbr10-rows-corr-reclaimed-nth
 (implies (and (fn-lbc-rows-corr base rows pm fn-lbc log)
  (natp base) (natp j) (< j (len rows)))
 (equal (fn-lbc-flag (+ base j) *fn-lbc-reclaimed-bit* fn-lbc)
        (fn-rcl-tombstonep (fn-lb-log-payload (nth j rows) log))))
 :hints (("Goal" :induct (fn-lbr10-row-metadata-induct base j rows pm)
 :in-theory (union-theories (theory 'ground-zero)
  '(fn-lbr10-row-metadata-induct fn-lbc-rows-corr fn-lbr10-row-corr-metadata-by-definition nth natp nfix zp max))))))

(local (defthm fn-lbr10-rows-corr-prefix-bound
 (implies (and (fn-lbc-rows-corr base rows pm fn-lbc log)
  (natp base) (natp j) (< j (len rows)))
 (and (natp (fn-lbc-value (+ base j) :prefix-max fn-lbc))
      (<= (nfix pm) (fn-lbc-value (+ base j) :prefix-max fn-lbc))
      (<= (nfix (fn-record-stamp (nth j rows))) (fn-lbc-value (+ base j) :prefix-max fn-lbc))))
 :hints (("Goal" :induct (fn-lbr10-row-metadata-induct base j rows pm)
 :in-theory (union-theories (theory 'ground-zero)
  '(fn-lbr10-row-metadata-induct fn-lbc-rows-corr fn-lbr10-row-corr-metadata-by-definition nth natp nfix zp max))))))

(defthm fn-lbc-reclaimed-is-log-tombstone
 (implies (and (fn-lbc-corr fn-lbc rows log) (natp i) (< i (len rows)))
 (equal (fn-lbc-flag i *fn-lbc-reclaimed-bit* fn-lbc)
        (fn-rcl-tombstonep (fn-lb-log-payload (nth i rows) log))))
 :hints (("Goal" :use ((:instance fn-lbr10-rows-corr-reclaimed-nth (base 0) (j i) (pm 0)))
 :in-theory (union-theories (theory 'ground-zero) '(fn-lbc-corr natp)))))

(defthm fn-lbc-prefix-dominates-row-stamp
 (implies (and (fn-lbc-corr fn-lbc rows log) (natp i) (< i (len rows)))
 (and (natp (fn-lbc-value i :prefix-max fn-lbc))
      (<= (nfix (fn-record-stamp (nth i rows))) (fn-lbc-value i :prefix-max fn-lbc))))
 :hints (("Goal" :use ((:instance fn-lbr10-rows-corr-prefix-bound (base 0) (j i) (pm 0)))
 :in-theory (union-theories (theory 'ground-zero) '(fn-lbc-corr natp)))))

(defthm fn-lbc-row-article-fields
 (and (equal (fn-article-msgid (fn-cat-row-article i fn-arena rows)) (fn-record-msgid (nth i rows)))
      (equal (fn-article-payload (fn-cat-row-article i fn-arena rows)) (fn-record-payload (nth i rows)))
      (equal (fn-article-stamp (fn-cat-row-article i fn-arena rows)) (fn-record-stamp (nth i rows)))
      (equal (fn-article-memberships (fn-cat-row-article i fn-arena rows)) (fn-held-numbers (nth i rows)))
      (equal (fn-nntp-article-idp (fn-cat-row-article i fn-arena rows))
             (fn-nntp-article-idp (fn-make-article (fn-record-msgid (nth i rows)) 0 nil nil t 0))))
 :hints (("Goal" :in-theory (union-theories (theory 'ground-zero)
  '(fn-cat-row-article fn-cat-at-is-nth fn-cat$a-at fn-nntp-article-idp
    fn-article-msgid-of-fn-make-article fn-article-payload-of-fn-make-article
    fn-article-stamp-of-fn-make-article fn-article-memberships-of-fn-make-article)))))

(defthm fn-lbc-row-article-bytes-are-log-payload
 (implies (and (fn-lb-arena-is-log fn-arena rows log) (natp i) (< i (len rows)))
 (equal (fn-nntp-article-bytes (fn-cat-row-article i fn-arena rows) fn-arena)
        (fn-lb-log-payload (nth i rows) log)))
 :hints (("Goal" :use fn-lb-arena-is-log-binds-nth
 :in-theory (union-theories (theory 'ground-zero)
  '(fn-nntp-article-bytes fn-lbc-row-article-fields)))))

(defthm fn-lbc-reclaimed-is-row-tombstone
 (implies (and (fn-lbc-corr fn-lbc rows log) (fn-lb-arena-is-log fn-arena rows log)
  (natp i) (< i (len rows)))
 (equal (fn-lbc-flag i *fn-lbc-reclaimed-bit* fn-lbc)
        (fn-nntp-article-tombstonep (fn-cat-row-article i fn-arena rows) fn-arena)))
 :hints (("Goal" :in-theory (union-theories (theory 'ground-zero)
  '(fn-nntp-article-tombstonep fn-lbc-reclaimed-is-log-tombstone fn-lbc-row-article-bytes-are-log-payload)))))

(local (defun fn-lbr10-two-prefix-induct (base i j rows pm)
 (declare (xargs :measure (nfix i) :verify-guards nil))
 (if (and (consp rows) (not (zp i)))
  (fn-lbr10-two-prefix-induct (+ 1 (nfix base)) (- i 1) (- j 1) (cdr rows)
   (max (nfix pm) (nfix (fn-record-stamp (car rows)))))
  (list base j pm))))

(local (defthm fn-lbr10-prefix-first-lower
 (implies (and (fn-lbc-rows-corr base rows pm fn-lbc log)
  (natp base) (natp j) (< j (len rows)))
 (<= (fn-lbc-value base :prefix-max fn-lbc)
     (fn-lbc-value (+ base j) :prefix-max fn-lbc)))
 :hints (("Goal" :cases ((zp j)) :do-not-induct t
 :use ((:instance fn-lbr10-rows-corr-prefix-bound
  (base (+ 1 base)) (rows (cdr rows)) (j (- j 1))
  (pm (max (nfix pm) (nfix (fn-record-stamp (car rows)))))))
 :in-theory (union-theories (theory 'ground-zero)
  '(fn-lbc-rows-corr fn-lbr10-row-corr-metadata-by-definition natp nfix zp max len))))))

(local (defthm fn-lbr10-rows-corr-prefix-ordered
 (implies (and (fn-lbc-rows-corr base rows pm fn-lbc log)
  (natp base) (natp i) (natp j) (<= i j) (< j (len rows)))
 (<= (fn-lbc-value (+ base i) :prefix-max fn-lbc)
     (fn-lbc-value (+ base j) :prefix-max fn-lbc)))
 :hints (("Goal" :induct (fn-lbr10-two-prefix-induct base i j rows pm)
 :in-theory (union-theories (theory 'ground-zero)
  '(fn-lbr10-two-prefix-induct fn-lbc-rows-corr fn-lbr10-row-corr-metadata-by-definition
    fn-lbr10-prefix-first-lower fn-lbr10-rows-corr-prefix-bound natp nfix zp max))))))

(defthm fn-lbc-prefix-ordered
 (implies (and (fn-lbc-corr fn-lbc rows log)
  (natp i) (natp j) (<= i j) (< j (len rows)))
 (<= (fn-lbc-value i :prefix-max fn-lbc) (fn-lbc-value j :prefix-max fn-lbc)))
 :hints (("Goal" :use ((:instance fn-lbr10-rows-corr-prefix-ordered (base 0) (pm 0)))
 :in-theory (union-theories (theory 'ground-zero) '(fn-lbc-corr natp)))))
