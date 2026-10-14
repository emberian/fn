; LB row/column refinements; local proof cuts have real book scope.
(in-package "ACL2")
(include-book "catalog-columns-projections")

(local (include-book "arithmetic-5/top" :dir :system))

(local (defthm fn-lbr10-newnews-candidate-from-memberships
 (equal (fn-nntp-newnews-candidatep groups article)
  (and (fn-nntp-article-idp article)
       (fn-lbc-newnews-candidatep groups (fn-article-memberships article))))
 :hints (("Goal" :induct (fn-nntp-newnews-candidatep groups article)
 :in-theory (union-theories (theory 'ground-zero)
  '(fn-nntp-newnews-candidatep fn-lbc-newnews-candidatep fn-nntp-article-number
    fn-ag-car fn-ag-cdr posp natp))))))

(local (defun fn-lbr10-stamped-articlesp (articles)
 (declare (xargs :guard t))
 (if (consp articles)
  (and (natp (fn-article-stamp (car articles))) (fn-lbr10-stamped-articlesp (cdr articles)))
  t)))

(local (defun fn-lbr10-newnews-stamped-filter (groups threshold articles fn-arena)
 (declare (xargs :stobjs fn-arena :guard t :verify-guards nil))
 (if (consp articles)
  (let ((article (car articles))
        (rest (fn-lbr10-newnews-stamped-filter groups threshold (cdr articles) fn-arena)))
   (if (and (fn-nntp-newnews-candidatep groups article)
            (not (fn-nntp-article-tombstonep article fn-arena))
            (fn-ng-less-equal threshold (* 1000 (fn-article-stamp article))))
    (cons (fn-nntp-string-octets (fn-article-msgid article)) rest) rest))
  nil)))

(local (defthm fn-lbr10-accepted-since-is-stamped-filter
 (implies (fn-lbr10-stamped-articlesp articles)
  (equal (fn-nntp-newnews-accepted-since groups threshold articles newer horizon fn-arena)
         (fn-lbr10-newnews-stamped-filter groups threshold articles fn-arena)))
 :hints (("Goal" :induct (fn-nntp-newnews-accepted-since groups threshold articles newer horizon fn-arena)
 :in-theory (union-theories (theory 'ground-zero)
  '(fn-nntp-newnews-accepted-since fn-lbr10-newnews-stamped-filter fn-lbr10-stamped-articlesp
    fn-nntp-newnews-newp))))))

(local (defthm fn-lbr10-view-below-stamped
 (implies (and (fn-cat$ap rows) (natp i) (<= i (len rows)))
  (fn-lbr10-stamped-articlesp (fn-cat-view-below i v fn-arena rows)))
 :hints (("Goal" :induct (fn-cat-view-below i v fn-arena rows)
 :in-theory (union-theories (theory 'ground-zero)
  '(fn-cat-view-below fn-lbr10-stamped-articlesp fn-lbc-row-article-fields
    fn-lbc-abstract-row-stamp-natural natp zp))))))

(local (defthm fn-lbr10-newnews-row-qualifies
 (implies (and (fn-lbc-p fn-lbc) (fn-cat$ap rows) (fn-lbc-corr fn-lbc rows log)
  (fn-lb-arena-is-log fn-arena rows log) (natp i) (< i (len rows)))
 (equal
  (and (fn-nntp-newnews-candidatep groups (fn-cat-row-article i fn-arena rows))
       (not (fn-nntp-article-tombstonep (fn-cat-row-article i fn-arena rows) fn-arena))
       (fn-ng-less-equal threshold (* 1000 (fn-article-stamp (fn-cat-row-article i fn-arena rows)))))
  (and (not (fn-lbc-flag i *fn-lbc-reclaimed-bit* fn-lbc))
       (fn-nntp-article-idp (fn-make-article (fn-lbc-msgid i fn-lbc) 0 nil nil t 0))
       (fn-lbc-newnews-candidatep groups (fn-lbc-numbers i fn-lbc))
       (fn-ng-less-equal threshold (* 1000 (fn-lbc-value i :stamp fn-lbc))))))
 :hints (("Goal" :in-theory (union-theories (theory 'ground-zero)
  '(fn-lbr10-newnews-candidate-from-memberships fn-lbc-row-article-fields
    fn-lbc-reclaimed-is-row-tombstone fn-lbc-served-fields-are-abstract))))))

(local (defthm fn-lbc-newnews-tail-zero-is-view-filter
 (implies (and (fn-lbc-p fn-lbc) (fn-cat$ap rows) (fn-lbc-corr fn-lbc rows log)
  (fn-lb-arena-is-log fn-arena rows log) (natp i) (<= i (len rows)) (natp v))
 (equal (fn-lbc-newnews-tail groups threshold v 0 i fn-lbc)
        (fn-lbr10-newnews-stamped-filter groups threshold (fn-cat-view-below i v fn-arena rows) fn-arena)))
 :hints (("Goal" :induct (fn-lbc-newnews-tail groups threshold v 0 i fn-lbc)
 :in-theory (union-theories (theory 'ground-zero)
  '(fn-lbc-newnews-tail fn-lbr10-newnews-stamped-filter fn-cat-view-below
    fn-cat-visible-at-is-visiblep fn-lbc-visible-is-row-visible fn-lbr10-newnews-row-qualifies
    fn-lbc-row-article-fields fn-lbc-served-fields-are-abstract
    fn-lbc-reclaimed-is-row-tombstone fn-lbr10-newnews-candidate-from-memberships natp zp))))))

(defthm
    fn-lbc-midpoint-bounds
    (implies
      (and (natp lo) (natp hi) (< lo hi))
      (and
        (natp (+ lo (floor (- hi lo) 2)))
        (<= lo (+ lo (floor (- hi lo) 2)))
        (< (+ lo (floor (- hi lo) 2)) hi)))
    :hints
    (("Goal" :in-theory (disable floor mod |(floor x 2)|)))
    :rule-classes
    nil)

(defthm
    fn-lbc-first-reaching-bounds
    (implies
      (and (natp lo) (natp hi) (<= lo hi))
      (and
        (natp (fn-lbc-first-reaching threshold lo hi fn-lbc))
        (<= lo (fn-lbc-first-reaching threshold lo hi fn-lbc))
        (<= (fn-lbc-first-reaching threshold lo hi fn-lbc) hi)))
    :hints
    (("Goal"
       :induct
       (fn-lbc-first-reaching threshold lo hi fn-lbc)
       :expand
       ((fn-lbc-first-reaching threshold lo hi fn-lbc))
       :in-theory
       (set-difference-theories (union-theories (theory 'ground-zero) '((:induction fn-lbc-first-reaching) natp nfix)) '(floor mod |(floor x 2)|)))
      ("Subgoal *1/1" :use fn-lbc-midpoint-bounds)
      ("Subgoal *1/3" :use fn-lbc-midpoint-bounds)
      ("Subgoal *1/2" :use fn-lbc-midpoint-bounds))
    :rule-classes
    nil)

(defthm fn-lbc-first-reaching-skips-only-below
 (implies (and (fn-lbc-corr fn-lbc rows log) (natp lo) (natp hi) (<= lo hi)
  (<= hi (len rows)) (natp j) (<= lo j)
  (< j (fn-lbc-first-reaching threshold lo hi fn-lbc)))
  (< (* 1000 (nfix (fn-lbc-value j :prefix-max fn-lbc))) threshold))
 :hints (("Goal" :induct (fn-lbc-first-reaching threshold lo hi fn-lbc)
 :expand ((fn-lbc-first-reaching threshold lo hi fn-lbc))
 :in-theory (set-difference-theories
  (union-theories (theory 'ground-zero) '((:induction fn-lbc-first-reaching) natp nfix))
  '(floor mod)))
 ("Subgoal *1/1" :use (fn-lbc-midpoint-bounds
  (:instance fn-lbc-first-reaching-bounds (lo (+ 1 lo (floor (- hi lo) 2))))
  (:instance fn-lbc-first-reaching-bounds (hi (+ lo (floor (- hi lo) 2))))
  (:instance fn-lbc-prefix-ordered (i j) (j (+ lo (floor (- hi lo) 2))))
  (:instance fn-lbc-prefix-dominates-row-stamp (i (+ lo (floor (- hi lo) 2))))
  (:instance fn-lbc-prefix-dominates-row-stamp (i j)))
  :cases ((< j (+ 1 lo (floor (- hi lo) 2)))))
 ("Subgoal *1/2" :use (fn-lbc-midpoint-bounds
  (:instance fn-lbc-first-reaching-bounds (lo (+ 1 lo (floor (- hi lo) 2))))
  (:instance fn-lbc-first-reaching-bounds (hi (+ lo (floor (- hi lo) 2))))
  (:instance fn-lbc-prefix-ordered (i j) (j (+ lo (floor (- hi lo) 2))))
  (:instance fn-lbc-prefix-dominates-row-stamp (i (+ lo (floor (- hi lo) 2))))
  (:instance fn-lbc-prefix-dominates-row-stamp (i j)))
  :cases ((< j (+ 1 lo (floor (- hi lo) 2)))))
 ("Subgoal *1/3" :use (fn-lbc-midpoint-bounds
  (:instance fn-lbc-first-reaching-bounds (lo (+ 1 lo (floor (- hi lo) 2))))
  (:instance fn-lbc-first-reaching-bounds (hi (+ lo (floor (- hi lo) 2))))
  (:instance fn-lbc-prefix-ordered (i j) (j (+ lo (floor (- hi lo) 2))))
  (:instance fn-lbc-prefix-dominates-row-stamp (i (+ lo (floor (- hi lo) 2))))
  (:instance fn-lbc-prefix-dominates-row-stamp (i j)))
  :cases ((< j (+ 1 lo (floor (- hi lo) 2)))))
))

(local (defthm fn-lbr10-newnews-tail-partition
 (implies (and (natp lo) (natp mid) (natp hi) (<= lo mid) (<= mid hi))
 (equal (fn-lbc-newnews-tail groups threshold v lo hi fn-lbc)
  (append (fn-lbc-newnews-tail groups threshold v mid hi fn-lbc)
          (fn-lbc-newnews-tail groups threshold v lo mid fn-lbc))))
 :hints (("Goal" :induct (fn-lbc-newnews-tail groups threshold v mid hi fn-lbc)
 :in-theory (union-theories (theory 'ground-zero) '(fn-lbc-newnews-tail natp append))))))

(local (defthm fn-lbr10-newnews-skipped-row-is-below
 (implies (and (fn-lbc-p fn-lbc) (fn-cat$ap rows) (fn-lbc-corr fn-lbc rows log)
  (natp bound) (<= bound (len rows)) (natp i)
  (< i (fn-lbc-first-reaching threshold 0 bound fn-lbc)))
  (not (fn-ng-less-equal threshold (* 1000 (fn-lbc-value i :stamp fn-lbc)))))
 :hints (("Goal" :do-not-induct t
 :use ((:instance fn-lbc-first-reaching-bounds (lo 0) (hi bound))
       (:instance fn-lbc-first-reaching-skips-only-below (lo 0) (hi bound) (j i))
       (:instance fn-lbc-prefix-dominates-row-stamp)
       (:instance fn-lbc-abstract-row-stamp-natural))
 :in-theory (union-theories (theory 'ground-zero)
  '(fn-lbc-served-fields-are-abstract fn-ng-less-equal-is-less-equal natp nfix))))))

(local (defthm fn-lbr10-newnews-tail-below-search-is-empty
 (implies (and (fn-lbc-p fn-lbc) (fn-cat$ap rows) (fn-lbc-corr fn-lbc rows log)
  (natp bound) (<= bound (len rows)) (natp lo) (natp hi) (<= lo hi)
  (<= hi (fn-lbc-first-reaching threshold 0 bound fn-lbc)))
 (equal (fn-lbc-newnews-tail groups threshold v lo hi fn-lbc) nil))
 :hints (("Goal" :induct (fn-lbc-newnews-tail groups threshold v lo hi fn-lbc)
 :in-theory (union-theories (theory 'ground-zero)
  '(fn-lbc-newnews-tail fn-lbr10-newnews-skipped-row-is-below natp))))))

(local (defthm fn-lbr10-newnews-tail-proper
 (true-listp (fn-lbc-newnews-tail groups threshold v lo hi fn-lbc))
 :hints (("Goal" :induct (fn-lbc-newnews-tail groups threshold v lo hi fn-lbc)
 :in-theory (union-theories (theory 'ground-zero) '(fn-lbc-newnews-tail))))))

(local (defthm fn-lbr10-append-nil-when-proper
 (implies (true-listp xs) (equal (append xs nil) xs))
 :hints (("Goal" :in-theory (union-theories (theory 'ground-zero) '(append))))))

(local (defthm fn-lbc-newnews-search-is-tail-zero
 (implies (and (fn-lbc-p fn-lbc) (fn-cat$ap rows) (fn-lbc-corr fn-lbc rows log)
  (natp v) (<= v (len rows)))
 (equal (fn-lbc-newnews-range groups threshold v horizon fn-lbc)
        (fn-lbc-newnews-tail groups threshold v 0 v fn-lbc)))
 :hints (("Goal" :do-not-induct t
 :use ((:instance fn-lbc-first-reaching-bounds (lo 0) (hi v))
  (:instance fn-lbr10-newnews-tail-partition (lo 0) (hi v)
   (mid (fn-lbc-first-reaching threshold 0 v fn-lbc)))
  (:instance fn-lbr10-newnews-tail-below-search-is-empty (bound v) (lo 0)
   (hi (fn-lbc-first-reaching threshold 0 v fn-lbc))))
 :in-theory (union-theories (theory 'ground-zero)
  '(fn-lbc-newnews-range fn-lbr10-append-nil-when-proper fn-lbr10-newnews-tail-proper natp))))))

(local (defun fn-lbr10-above-pin-induct (i v)
 (declare (xargs :measure (nfix i) :verify-guards nil))
 (if (and (natp i) (natp v) (< v i)) (fn-lbr10-above-pin-induct (- i 1) v) nil)))

(local (defthm fn-lbr10-view-below-at-pin
 (implies (and (natp i) (natp v) (<= v i))
 (equal (fn-cat-view-below i v fn-arena rows) (fn-cat-view-below v v fn-arena rows)))
 :rule-classes nil
 :hints (("Goal" :induct (fn-lbr10-above-pin-induct i v)
 :in-theory (union-theories (theory 'ground-zero)
  '(fn-lbr10-above-pin-induct fn-cat-visible-at-is-visiblep fn-cat-visiblep natp zp)))
 ("Subgoal *1/1" :expand ((fn-cat-view-below i v fn-arena rows))))))

(defthm fn-lbc-newnews-range-is-accepted-since
  (implies (and (fn-lbc-p fn-lbc) (fn-cat$ap rows) (fn-lbc-corr fn-lbc rows log)
                (fn-arena-p fn-arena) (fn-scol-okp fn-arena rows)
                (fn-lb-arena-is-log fn-arena rows log)
                (natp v) (<= v (len rows)) (natp threshold))
           (equal (fn-lbc-newnews-range groups threshold v horizon fn-lbc)
                  (fn-nntp-newnews-accepted-since groups threshold
                    (fn-cat-view-articles v fn-arena rows) nil horizon fn-arena)))
 :hints (("Goal" :do-not-induct t
 :use ((:instance fn-lbc-newnews-tail-zero-is-view-filter (i v))
       (:instance fn-lbr10-accepted-since-is-stamped-filter
        (articles (fn-cat-view-below v v fn-arena rows)) (newer nil))
       (:instance fn-lbr10-view-below-at-pin (i (len rows))))
 :in-theory (union-theories (theory 'ground-zero)
  '(fn-lbc-newnews-search-is-tail-zero fn-cat-view-articles fn-cat-count-is-len
    fn-lbr10-view-below-stamped natp)))))
