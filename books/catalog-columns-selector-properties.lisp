; Total-domain served selector refinement.
(in-package "ACL2")
(include-book "catalog-columns-msgid-properties")

(local (defthm fn-lbr11-visible-is-bounded-row-visible
 (implies (and (fn-lbc-p fn-lbc) (fn-cat$ap rows) (fn-lbc-corr fn-lbc rows log))
 (equal (fn-lbc-visiblep i v fn-lbc)
 (and (natp i) (< i (len rows)) (fn-cat-visible-at i v rows))))
 :hints (("Goal" :do-not-induct t :cases ((and (natp i) (< i (len rows))))
 :use (fn-lbc-visible-implies-index-bounds fn-lbc-corr-count-is-length)
 :in-theory (union-theories (theory 'ground-zero)
 '(fn-lbc-visible-is-row-visible-total-version fn-cat-visible-at-is-visiblep natp))))))

(local (defthm fn-lbr11-msgid-visible-last-is-catalog-last
 (implies (and (fn-lbc-p fn-lbc) (fn-cat$ap rows) (fn-lbc-corr fn-lbc rows log))
 (equal (fn-lbc-msgid-visible-last seqs v fn-lbc) (fn-cat-view-last-visible seqs v rows)))
 :hints (("Goal" :induct (fn-lbc-msgid-visible-last seqs v fn-lbc)
 :in-theory (union-theories (theory 'ground-zero)
 '(fn-lbc-msgid-visible-last fn-cat-view-last-visible fn-lbr11-visible-is-bounded-row-visible fn-cat-count-is-len))))))

(defthm fn-lbc-msgid-visible-is-walk
 (implies (and (fn-lbc-p fn-lbc) (fn-cat$ap rows) (fn-lbc-corr fn-lbc rows log))
 (equal (fn-lbc-msgid-visible-last (fn-lbc-msgid-seqs msgid fn-lbc) v fn-lbc)
        (fn-cat-view-find msgid (len rows) v rows)))
 :hints (("Goal" :do-not-induct t
 :use ((:instance fn-cat-view-find-is-msgid-column (fn-cat rows)))
 :in-theory (union-theories (theory 'ground-zero)
 '(fn-lbr11-msgid-visible-last-is-catalog-last fn-lbc-msgid-seqs-is-abstract fn-cat-msgid-seqs-is-seqs-for fn-cat-count-is-len)))))

(defthm fn-lbc-msgid-visible-index-in-range
 (implies (fn-lbc-msgid-visible-last seqs v fn-lbc)
 (and (natp (fn-lbc-msgid-visible-last seqs v fn-lbc))
      (< (fn-lbc-msgid-visible-last seqs v fn-lbc) (fn-lbc-count fn-lbc))
      (fn-lbc-visiblep (fn-lbc-msgid-visible-last seqs v fn-lbc) v fn-lbc)))
 :hints (("Goal" :induct (fn-lbc-msgid-visible-last seqs v fn-lbc)
 :in-theory (union-theories (theory 'ground-zero) '(fn-lbc-msgid-visible-last fn-lbc-visible-implies-index-bounds natp)))))

(local (defthm fn-lbr11-membership-number-is-held-number
 (implies (and group (posp number))
 (equal (equal (fn-nntp-membership-number group memberships) number)
        (equal (cdr (fn-cat-assoc group memberships)) number)))
 :hints (("Goal" :induct (fn-nntp-membership-number group memberships)
 :in-theory (union-theories (theory 'ground-zero) '(fn-nntp-membership-number fn-cat-assoc fn-ag-car fn-ag-cdr posp natp))))))

(local (defthm fn-lbr11-row-membership-number-binding
 (implies (and group (posp number))
 (equal (equal (fn-nntp-membership-number group (fn-article-memberships (fn-cat-row-article i fn-arena rows))) number)
        (equal (fn-held-number-in group (fn-cat-at i rows)) number)))
 :hints (("Goal" :in-theory (union-theories (theory 'ground-zero)
 '(fn-cat-row-article-memberships fn-held-number-in fn-lbr11-membership-number-is-held-number))))))

(local (defthm fn-lbr11-view-number-find-bounds
 (implies (and (natp i) (fn-cat-view-number-find group number i v rows))
 (and (natp (fn-cat-view-number-find group number i v rows))
      (< (fn-cat-view-number-find group number i v rows) i)))
 :hints (("Goal" :induct (fn-cat-view-number-find group number i v rows)
 :in-theory (union-theories (theory 'ground-zero) '(fn-cat-view-number-find natp zp))))))

(local (defthm fn-lbr11-number-article-is-view-walk
 (implies (and group (posp number))
 (equal (fn-nntp-find-group-number group number (fn-cat-view-below i v fn-arena rows))
        (let ((seq (fn-cat-view-number-find group number i v rows)))
          (if seq (fn-cat-row-article seq fn-arena rows) nil))))
 :hints (("Goal" :induct (fn-cat-view-below i v fn-arena rows)
 :in-theory (union-theories (theory 'ground-zero)
 '(fn-cat-view-below fn-nntp-find-group-number fn-cat-view-number-find fn-lbr11-row-membership-number-binding))))))

(local (defthm fn-lbr11-row-article-is-cons
 (consp (fn-cat-row-article i fn-arena rows))
 :hints (("Goal" :in-theory (union-theories (theory 'ground-zero) '(fn-cat-row-article fn-make-article))))))

(local (defthm fn-lbr11-number-seq-characteristics
 (implies (and (natp base) (fn-cat-number-seq group number rows base))
 (and (natp (fn-cat-number-seq group number rows base))
 (<= base (fn-cat-number-seq group number rows base))
 (< (fn-cat-number-seq group number rows base) (+ base (len rows)))
 (equal (fn-held-number-in group (nth (- (fn-cat-number-seq group number rows base) base) rows)) number)))
 :hints (("Goal" :induct (fn-cat-number-seq group number rows base)
 :in-theory (union-theories (theory 'ground-zero) '(fn-cat-number-seq nth natp zp len))))))

(local (defthm fn-lbr11-row-article-number-matches
 (implies (and group (posp number) (<= number *fn-nntp-max-article-number*))
 (equal (equal (fn-nntp-article-number group (fn-cat-row-article i fn-arena rows)) number)
        (and (equal (fn-held-number-in group (fn-cat-at i rows)) number)
             (fn-nntp-article-idp (fn-cat-row-article i fn-arena rows)))))
 :hints (("Goal" :do-not-induct t :use fn-lbr11-row-membership-number-binding :in-theory (union-theories (theory 'ground-zero)
 '(fn-nntp-article-number posp natp))))))

(local (defthm fn-lbr11-available-number-out-of-domain
 (implies (or (not (posp number)) (< *fn-nntp-max-article-number* number))
 (equal (fn-nntp-available-article group number articles) nil))
 :hints (("Goal" :induct (fn-nntp-available-article group number articles)
 :in-theory (union-theories (theory 'ground-zero) '(fn-nntp-available-article fn-nntp-article-number-bounded posp natp))))))

(local (defthm fn-lbr11-id-article-idp-is-row-idp
 (implies (and (fn-lbc-p fn-lbc) (fn-cat$ap rows) (fn-lbc-corr fn-lbc rows log) (natp i) (< i (len rows)))
 (equal (fn-nntp-article-idp (fn-lbc-id-article i fn-lbc))
        (fn-nntp-article-idp (fn-cat-row-article i fn-arena rows))))
 :hints (("Goal" :use (fn-lbc-row-article-fields fn-lbc-served-fields-are-abstract)
 :in-theory (union-theories (theory 'ground-zero) '(fn-lbc-id-article))))))

(local (defthm fn-lbr11-number-column-type
 (or (null (fn-cat-number-seq group number rows 0)) (natp (fn-cat-number-seq group number rows 0)))
 :rule-classes :type-prescription
 :hints (("Goal" :use ((:instance fn-lbr11-number-seq-characteristics (base 0))) :in-theory (union-theories (theory 'ground-zero) '(natp))))))

(local (defthm fn-lbr11-number-column-binds
 (implies (fn-cat-number-seq group number rows 0)
 (equal (fn-held-number-in group (nth (fn-cat-number-seq group number rows 0) rows)) number))
 :hints (("Goal" :use ((:instance fn-lbr11-number-seq-characteristics (base 0))) :in-theory (theory 'ground-zero)))))

(local (defthm fn-lbr11-available-view-is-number-column
 (implies (and group (posp number) (<= number *fn-nntp-max-article-number*)
 (fn-cnx-freshp rows) (natp i) (<= i (len rows)))
 (equal (fn-nntp-available-article group number (fn-cat-view-below i v fn-arena rows))
 (let ((s (fn-cat-number-seq group number rows 0)))
 (if (and s (< s i) (fn-cat-visible-at s v rows)
          (fn-nntp-article-idp (fn-cat-row-article s fn-arena rows)))
 (fn-cat-row-article s fn-arena rows) nil))))
 :hints (("Goal" :induct (fn-cat-view-below i v fn-arena rows)
 :in-theory (union-theories (theory 'ground-zero)
 '(fn-cat-view-below fn-nntp-available-article fn-lbr11-row-article-number-matches
 fn-lbr11-row-article-is-cons fn-lbr11-number-column-type fn-lbr11-number-column-binds fn-cat-at-is-nth natp posp zp)))
 ("Subgoal *1/2" :use (fn-lbr11-number-column-binds (:instance fn-cnx-number-seq-unique (c rows) (g group) (n number) (j (- i 1))))))))

(local (defthm fn-lbr11-number-selection-article-is-reference
 (implies (and (fn-lbc-p fn-lbc) (fn-cat$ap rows) (fn-lbc-corr fn-lbc rows log)
 (fn-cnx-freshp rows) group (posp number))
 (equal (fn-nntp-find-group-number group number (fn-cat-view-articles v fn-arena rows))
 (let ((i (fn-lbc-number-get group number fn-lbc)))
  (if (and (natp i) (fn-lbc-visiblep i v fn-lbc)) (fn-lbc-article i fn-lbc) nil))))
 :hints (("Goal" :do-not-induct t
 :use (fn-lbc-number-visible-is-walk
 (:instance fn-lbr11-number-article-is-view-walk (i (len rows)))
 (:instance fn-lbc-visible-implies-index-bounds (i (fn-lbc-number-get group number fn-lbc))))
 :in-theory (union-theories (theory 'ground-zero)
 '(fn-cat-view-articles fn-cat-count-is-len fn-lbc-corr-count-is-length fn-lbc-article-is-row-article posp natp))))))

(local (defthm fn-lbr11-msgid-selection-article-is-reference
 (implies (and (fn-lbc-p fn-lbc) (fn-cat$ap rows) (fn-lbc-corr fn-lbc rows log))
 (equal (fn-find-article msgid (fn-cat-view-articles v fn-arena rows))
 (let ((i (fn-lbc-msgid-visible-last (fn-lbc-msgid-seqs msgid fn-lbc) v fn-lbc)))
  (if (natp i) (fn-lbc-article i fn-lbc) nil))))
 :hints (("Goal" :do-not-induct t
 :use ((:instance fn-cat-view-find-article-is-walk (i (len rows)) (fn-cat rows))
 (:instance fn-lbc-msgid-visible-index-in-range (seqs (fn-lbc-msgid-seqs msgid fn-lbc)))
 fn-lbc-msgid-visible-is-walk)
 :in-theory (union-theories (theory 'ground-zero)
 '(fn-cat-view-articles fn-cat-count-is-len fn-lbc-corr-count-is-length fn-lbc-article-is-row-article natp))))))

(local (defthm fn-lbr11-current-selection-article-is-reference
 (implies (and (fn-lbc-p fn-lbc) (fn-cat$ap rows) (fn-lbc-corr fn-lbc rows log)
 (fn-cnx-freshp rows) group)
 (equal (fn-nntp-available-article group number (fn-cat-view-articles v fn-arena rows))
 (let ((i (fn-lbc-number-get group number fn-lbc)))
  (if (and (natp i) (fn-lbc-visiblep i v fn-lbc) (posp number)
           (<= number *fn-nntp-max-article-number*) (fn-nntp-article-idp (fn-lbc-id-article i fn-lbc)))
   (fn-lbc-article i fn-lbc) nil))))
 :hints (("Goal" :do-not-induct t
 :cases ((and (posp number) (<= number *fn-nntp-max-article-number*)))
 :use ((:instance fn-lbr11-available-view-is-number-column (i (len rows)))
 (:instance fn-lbr11-number-seq-characteristics (base 0))
 (:instance fn-lbc-visible-implies-index-bounds (i (fn-lbc-number-get group number fn-lbc))))
 :in-theory (union-theories (theory 'ground-zero)
 '(fn-cat-view-articles fn-cat-count-is-len fn-lbc-corr-count-is-length fn-lbc-number-get-is-abstract
 fn-lbr11-available-number-out-of-domain fn-lbr11-id-article-idp-is-row-idp
 fn-lbc-visible-is-row-visible-total-version fn-cat-visible-at-is-visiblep fn-lbc-article-is-row-article posp natp))))))

(local (defthm fn-lbr11-native-article-consp
 (consp (fn-lbc-article i fn-lbc))
 :hints (("Goal" :in-theory (union-theories (theory 'ground-zero) '(fn-lbc-article fn-make-article))))))

(defthm fn-lbc-select-row-is-in-range
 (implies (equal (car (fn-lbc-select session kind args v fn-lbc)) :row)
 (let ((i (cadr (fn-lbc-select session kind args v fn-lbc))))
 (and (natp i) (< i (fn-lbc-count fn-lbc)) (fn-lbc-visiblep i v fn-lbc))))
 :hints (("Goal" :do-not-induct t
 :in-theory (union-theories (theory 'ground-zero)
 '(fn-lbc-select fn-lbc-visible-implies-index-bounds fn-lbc-msgid-visible-index-in-range natp)))))

(defthm fn-lbc-selector-reference-dispatch
 (implies (and (fn-lbc-p fn-lbc) (fn-cat$ap rows) (fn-lbc-corr fn-lbc rows log)
               (fn-cnx-freshp rows) (equal arts (fn-state-articles archive))
               (equal arts (fn-cat-view-articles v fn-arena rows)))
 (equal
 (let ((selected (fn-lbc-select session kind args v fn-lbc)))
 (if (equal (car selected) :refusal) (fn-nntp-single session (cadr selected))
 (fn-rcompat-article-reply session (fn-lbc-article (nth 1 selected) fn-lbc)
  (nth 2 selected) kind (nth 3 selected) (nth 4 selected) server fn-arena)))
 (fn-rcompat-retrieval session archive arts kind args server fn-arena)))
 :hints (("Goal" :do-not-induct t
 :in-theory (union-theories (theory 'ground-zero)
 '(fn-lbc-select fn-rcompat-retrieval fn-lbr11-number-selection-article-is-reference
 fn-lbr11-msgid-selection-article-is-reference fn-lbr11-current-selection-article-is-reference
 fn-lbr11-native-article-consp fn-lbc-msgid-visible-index-in-range
 fn-nntp-number-token-value-positive natp posp nth)))))
