; Logical dirt is covered by column changes and the directory/control regions.
(in-package "ACL2")
(include-book "log-checkpoint-values")
(include-book "log-checkpoint-delta")
(include-book "pagestore-keystones")
(include-book "defkeystone")
(local (include-book "std/lists/nth" :dir :system))
(local (include-book "std/lists/append" :dir :system))
(defthm fn-lc-column-page-outside-directory
 (implies (and (natp i)
               (not (and (<= (len (true-list-fix columns)) i)
                         (< i (+ (len (true-list-fix columns))
                                 (len (fn-lc-directory-pages columns header)))))))
          (equal (fn-lc-page-at (+ 1 i) (fn-lc-pages columns header))
                 (fn-lc-page-at i (fn-lc-column-pages columns))))
 :hints (("Goal" :in-theory (enable fn-lc-page-at fn-lc-pages fn-lc-column-pages))))
(defun fn-lc-uncovered-pagep (i old old-header new header)
 (declare (xargs :guard t :verify-guards nil))
 (let* ((o (+ 1 (len (true-list-fix old))))
        (n (+ 1 (len (true-list-fix new))))
        (od (len (true-list-fix (mbe :logic (nth 4 old-header) :exec (fn-lc-at 4 old-header)))))
        (nd (len (true-list-fix (mbe :logic (nth 4 header) :exec (fn-lc-at 4 header)))))
        (oc (len (true-list-fix (mbe :logic (nth 5 old-header) :exec (fn-lc-at 5 old-header)))))
        (nc (len (true-list-fix (mbe :logic (nth 5 header) :exec (fn-lc-at 5 header))))))
  (and (< 0 (nfix i))
       (not (fn-lc-in-either-range i o (+ o od) n (+ n nd)))
       (not (fn-lc-in-either-range i (+ o od) (+ o od oc)
                                   (+ n nd) (+ n nd nc))))))
(defun fn-lc-uncovered-dirty (dirty old old-header new header)
 (declare (xargs :guard t :verify-guards nil))
 (if (consp dirty)
  (let ((rest (fn-lc-uncovered-dirty (mbe :logic (cdr dirty) :exec (fn-lc-rest dirty)) old old-header new header)))
   (if (fn-lc-uncovered-pagep (mbe :logic (caar dirty) :exec (fn-lc-head (fn-lc-head dirty))) old old-header new header)
    (cons (mbe :logic (car dirty) :exec (fn-lc-head dirty)) rest) rest)) nil))
(defun fn-lc-shift-dirty-column (dirty)
 (declare (xargs :guard t :verify-guards nil))
 (if (consp dirty)
  (cons (cons (+ 1 (nfix (mbe :logic (caar dirty) :exec (fn-lc-head (fn-lc-head dirty))))) (mbe :logic (cdar dirty) :exec (fn-lc-rest (fn-lc-head dirty))))
        (fn-lc-shift-dirty-column (mbe :logic (cdr dirty) :exec (fn-lc-rest dirty)))) nil))
(defthm fn-lc-len-shift-dirty-column
 (equal (len (fn-lc-shift-dirty-column dirty)) (len dirty)))
(defthm fn-lc-uncovered-old-page-is-column
 (implies (and (natp i) (fn-lc-uncovered-pagep (+ 1 i) old old-header new header))
          (equal (fn-lc-page-at (+ 1 i) (fn-lc-pages old old-header))
                 (fn-lc-page-at i (fn-lc-column-pages old))))
 :hints (("Goal" :use ((:instance fn-lc-column-page-outside-directory
                                      (columns old) (header old-header)))
  :in-theory (e/d (fn-lc-uncovered-pagep fn-lc-in-either-range fn-lc-directory-pages)
                 (fn-lc-column-page-outside-directory fn-lc-page-at fn-lc-pages)))))
(defthm fn-lc-uncovered-new-page-is-column
 (implies (and (natp i) (fn-lc-uncovered-pagep (+ 1 i) old old-header new header))
          (equal (fn-lc-page-at (+ 1 i) (fn-lc-pages new header))
                 (fn-lc-page-at i (fn-lc-column-pages new))))
 :hints (("Goal" :use ((:instance fn-lc-column-page-outside-directory (columns new)))
  :in-theory (e/d (fn-lc-uncovered-pagep fn-lc-in-either-range fn-lc-directory-pages)
                 (fn-lc-column-page-outside-directory fn-lc-page-at fn-lc-pages)))))
(defthm fn-lc-uncovered-growth-is-column-growth
 (implies (and (natp i) (fn-lc-uncovered-pagep (+ 1 i) old old-header new header)
               (<= (len (fn-lc-pages old old-header)) (+ 1 i))
               (< (+ 1 i) (len (fn-lc-pages new header))))
          (and (<= (len (fn-lc-column-pages old)) i)
               (< i (len (fn-lc-column-pages new)))))
 :hints (("Goal" :in-theory (enable fn-lc-uncovered-pagep fn-lc-in-either-range
                           fn-lc-pages fn-lc-column-pages fn-lc-directory-pages))))
(defun fn-lc-budget-induction (i count)
 (declare (xargs :guard t :measure (nfix count) :verify-guards nil))
 (if (mbe :logic (zp count) :exec (not (posp count))) i (fn-lc-budget-induction (+ 1 (nfix i)) (1- count))))
(local (defthm fn-lc-subset-cons-super
 (implies (subsetp-equal x y) (subsetp-equal x (cons a y)))
 :hints (("Goal" :induct (subsetp-equal x y)
  :in-theory (union-theories (theory 'minimal-theory)
   '(subsetp-equal member-equal (:induction subsetp-equal) car-cons cdr-cons))))))
(defthm fn-lc-uncovered-delta-is-column-subset
 (implies (natp i)
  (subsetp-equal
   (fn-lc-uncovered-dirty
    (fn-lc-value-dirty-from (fn-lc-pages old old-header) (fn-lc-pages new header)
                            (+ 1 i) count) old old-header new header)
   (fn-lc-shift-dirty-column
    (fn-lc-value-dirty-from (fn-lc-column-pages old) (fn-lc-column-pages new) i count))))
 :hints (("Goal" :induct (fn-lc-budget-induction i count)
  :in-theory (union-theories (theory 'minimal-theory) '((:COMPOUND-RECOGNIZER NATP-COMPOUND-RECOGNIZER)
(:COMPOUND-RECOGNIZER ZP-COMPOUND-RECOGNIZER)

(:DEFINITION FN-LC-SHIFT-DIRTY-COLUMN)
(:DEFINITION FN-LC-UNCOVERED-DIRTY)
(:DEFINITION FN-LC-VALUE-DIRTY-FROM)
(:DEFINITION MEMBER-EQUAL)
(:DEFINITION NATP)
(:DEFINITION NOT)
(:DEFINITION SUBSETP-EQUAL)
(:DEFINITION SYNP) (:DEFINITION NFIX)
(:EXECUTABLE-COUNTERPART BINARY-+)
(:EXECUTABLE-COUNTERPART CONSP)
(:EXECUTABLE-COUNTERPART FN-LC-SHIFT-DIRTY-COLUMN)
(:EXECUTABLE-COUNTERPART NOT)
(:EXECUTABLE-COUNTERPART SUBSETP-EQUAL)
(:INDUCTION FN-LC-BUDGET-INDUCTION)
(:REWRITE CAR-CONS)
(:REWRITE CDR-CONS)
(:REWRITE FN-LC-COLUMN-PAGE-OUTSIDE-DIRECTORY)
(:REWRITE FN-LC-COLUMN-PAGES-PRESERVES-LENGTH)
(:REWRITE FN-LC-UNCOVERED-NEW-PAGE-IS-COLUMN)
(:REWRITE FN-LC-UNCOVERED-OLD-PAGE-IS-COLUMN)


(:REWRITE FOLD-CONSTS-IN-+)
(:REWRITE FN-LC-SUBSET-CONS-SUPER)


(:TYPE-PRESCRIPTION FN-LC-SHIFT-DIRTY-COLUMN)
(:TYPE-PRESCRIPTION FN-LC-UNCOVERED-DIRTY)
(:TYPE-PRESCRIPTION FN-LC-UNCOVERED-PAGEP)
(:TYPE-PRESCRIPTION FN-LC-VALUE-DIRTY-FROM)
(:TYPE-PRESCRIPTION LEN)
(:TYPE-PRESCRIPTION SUBSETP-EQUAL)))) ("Subgoal *1/2" :use ((:instance fn-lc-uncovered-growth-is-column-growth)))))

(defun fn-lc-fuel-cut-induction (i small large)
 (declare (xargs :guard (acl2-numberp large) :measure (nfix small) :verify-guards nil))
 (if (mbe :logic (zp small) :exec (not (posp small))) i
  (fn-lc-fuel-cut-induction (+ 1 (nfix i)) (1- small) (1- large))))
(defthm fn-lc-delta-fuel-cut
 (implies (and (natp i) (natp small) (natp large) (<= small large)
               (<= (len old) (+ i small)) (<= (len new) (+ i small)))
  (equal (fn-lc-value-dirty-from old new i large)
         (fn-lc-value-dirty-from old new i small)))
 :rule-classes nil
 :hints (("Goal" :induct (fn-lc-fuel-cut-induction i small large)
  :in-theory (e/d (fn-lc-value-dirty-from) (fn-lc-page-at fn-lc-zero-page)))))
(defthm fn-lc-pages-length
 (equal (len (fn-lc-pages columns header))
        (+ 1 (len (fn-lc-column-pages columns))
             (len (fn-lc-directory-pages columns header))))
 :hints (("Goal" :in-theory (enable fn-lc-pages))))
(defthm fn-lc-pages-nonempty
 (< 0 (len (fn-lc-pages columns header)))
 :rule-classes :linear
 :hints (("Goal" :in-theory (enable fn-lc-pages))))
(defthm fn-lc-column-fuel-fits
 (<= (max (len (fn-lc-column-pages old)) (len (fn-lc-column-pages new)))
     (- (max (len (fn-lc-pages old old-header)) (len (fn-lc-pages new header))) 1))
 :hints (("Goal" :in-theory (disable fn-lc-pages fn-lc-column-pages fn-lc-directory-pages))))
(defthm fn-lc-column-fuel-is-exact
 (equal (fn-lc-value-dirty-from (fn-lc-column-pages old) (fn-lc-column-pages new) 0
          (- (max (len (fn-lc-pages old old-header)) (len (fn-lc-pages new header))) 1))
        (fn-lc-dirty-column-pages old new))
 :hints (("Goal" :use ((:instance fn-lc-delta-fuel-cut
   (old (fn-lc-column-pages old)) (new (fn-lc-column-pages new)) (i 0)
   (small (max (len (fn-lc-column-pages old)) (len (fn-lc-column-pages new))))
   (large (- (max (len (fn-lc-pages old old-header)) (len (fn-lc-pages new header))) 1))))
  :in-theory (e/d (fn-lc-dirty-column-pages fn-lc-column-pages)
    (fn-lc-value-dirty-from fn-lc-pages fn-lc-directory-pages)))))
(defthm fn-lc-uncovered-header-is-omitted
 (implies (posp count)
  (equal (fn-lc-uncovered-dirty
          (fn-lc-value-dirty-from (fn-lc-pages old old-header)
                                  (fn-lc-pages new header) 0 count)
          old old-header new header)
         (fn-lc-uncovered-dirty
          (fn-lc-value-dirty-from (fn-lc-pages old old-header)
                                  (fn-lc-pages new header) 1 (1- count))
          old old-header new header)))
 :hints (("Goal" :expand ((fn-lc-value-dirty-from (fn-lc-pages old old-header)
                           (fn-lc-pages new header) 0 count))
  :in-theory (e/d (fn-lc-uncovered-dirty fn-lc-uncovered-pagep)
   (fn-lc-value-dirty-from fn-lc-pages fn-lc-column-pages fn-lc-directory-pages
    fn-lc-page-at)))))
(defthm fn-lc-uncovered-whole-delta-is-column-subset
 (subsetp-equal (fn-lc-uncovered-dirty (fn-lc-dirty old old-header new header)
                                      old old-header new header)
                (fn-lc-shift-dirty-column (fn-lc-dirty-column-pages old new)))
 :hints (("Goal" :use ((:instance fn-lc-uncovered-delta-is-column-subset
   (i 0) (count (- (max (len (fn-lc-pages old old-header))
                        (len (fn-lc-pages new header))) 1))))
  :in-theory (e/d (fn-lc-dirty fn-lc-uncovered-dirty fn-lc-uncovered-pagep)
   (fn-lc-uncovered-delta-is-column-subset fn-lc-value-dirty-from
    fn-lc-dirty-column-pages fn-lc-pages fn-lc-column-pages fn-lc-directory-pages
    fn-lc-shift-dirty-column fn-lc-page-at)))))
(defun fn-lc-dirty-keys-above (dirty low)
 (declare (xargs :guard t :verify-guards nil))
 (if (consp dirty)
  (and (natp (mbe :logic (caar dirty) :exec (fn-lc-head (fn-lc-head dirty)))) (<= (nfix low) (mbe :logic (caar dirty) :exec (fn-lc-head (fn-lc-head dirty))))
       (fn-lc-dirty-keys-above (mbe :logic (cdr dirty) :exec (fn-lc-rest dirty)) low)) t))
(defthm fn-lc-delta-keys-above
 (implies (and (natp i) (<= (nfix low) i))
  (fn-lc-dirty-keys-above (fn-lc-value-dirty-from old new i count) low))
 :hints (("Goal" :induct (fn-lc-value-dirty-from old new i count)
  :in-theory (e/d (fn-lc-value-dirty-from fn-lc-dirty-keys-above)
                 (fn-lc-page-at fn-lc-zero-page)))))
(defthm fn-lc-key-below-not-member
 (implies (and (fn-lc-dirty-keys-above dirty low) (consp entry)
               (natp (car entry)) (< (car entry) (nfix low)))
          (not (member-equal entry dirty)))
 :hints (("Goal" :induct (fn-lc-dirty-keys-above dirty low)
  :in-theory (enable fn-lc-dirty-keys-above))))
(defthm fn-lc-delta-next-cannot-contain-this-key
 (implies (natp i)
  (not (member-equal (cons i page) (fn-lc-value-dirty-from old new (+ 1 i) count))))
 :hints (("Goal" :use
  ((:instance fn-lc-key-below-not-member
    (dirty (fn-lc-value-dirty-from old new (+ 1 i) count))
    (entry (cons i page)) (low (+ 1 i)))
   (:instance fn-lc-delta-keys-above (i (+ 1 i)) (low (+ 1 i))))
  :in-theory (disable fn-lc-key-below-not-member fn-lc-delta-keys-above
                      fn-lc-value-dirty-from fn-lc-dirty-keys-above))))
(defthm fn-lc-delta-has-distinct-entries
 (implies (natp i) (no-duplicatesp-equal (fn-lc-value-dirty-from old new i count)))
 :hints (("Goal" :induct (fn-lc-value-dirty-from old new i count)
  :in-theory (e/d (fn-lc-value-dirty-from no-duplicatesp-equal)
                  (fn-lc-page-at fn-lc-zero-page fn-lc-dirty-keys-above)))))
(defthm fn-lc-uncovered-members
 (iff (member-equal entry (fn-lc-uncovered-dirty dirty old old-header new header))
      (and (member-equal entry dirty)
           (fn-lc-uncovered-pagep (car entry) old old-header new header)))
 :hints (("Goal" :induct (fn-lc-uncovered-dirty dirty old old-header new header)
  :in-theory (disable fn-lc-uncovered-pagep))))
(defthm fn-lc-uncovered-has-distinct-entries
 (implies (no-duplicatesp-equal dirty)
          (no-duplicatesp-equal (fn-lc-uncovered-dirty dirty old old-header new header)))
 :hints (("Goal" :induct (fn-lc-uncovered-dirty dirty old old-header new header)
  :in-theory (e/d (no-duplicatesp-equal) (fn-lc-uncovered-pagep)))))

; General finite-set cardinality; the induction removes an occupied slot.
(defun fn-lc-subset-length-induct (xs ys)
  (declare (xargs :guard (true-listp ys)))
  (if (consp xs)
      (fn-lc-subset-length-induct (mbe :logic (cdr xs) :exec (fn-lc-rest xs)) (remove-equal (mbe :logic (car xs) :exec (fn-lc-head xs)) ys))
    ys))

(defthm fn-lc-member-remove
 (iff (member-equal x (remove-equal a ys))
      (and (not (equal x a)) (member-equal x ys)))
 :hints (("Goal" :induct (remove-equal a ys) :in-theory (enable remove-equal))))

(defthm fn-lc-subset-remove
 (implies (and (subsetp-equal xs ys) (not (member-equal a xs)))
          (subsetp-equal xs (remove-equal a ys)))
 :hints (("Goal" :induct (subsetp-equal xs ys) :in-theory (enable subsetp-equal))))

(defthm fn-lc-remove-length-at-most
 (<= (len (remove-equal a ys)) (len ys))
 :rule-classes :linear
 :hints (("Goal" :induct (remove-equal a ys) :in-theory (enable remove-equal))))

(defthm fn-lc-remove-member-shortens
 (implies (member-equal a ys) (< (len (remove-equal a ys)) (len ys)))
 :rule-classes :linear
 :hints (("Goal" :induct (remove-equal a ys) :in-theory (enable remove-equal))))

(defthm fn-lc-distinct-subset-length
 (implies (and (no-duplicatesp-equal xs) (subsetp-equal xs ys))
          (<= (len xs) (len ys)))
 :rule-classes nil
 :hints (("Goal" :induct (fn-lc-subset-length-induct xs ys)
          :in-theory (enable no-duplicatesp-equal subsetp-equal))))
(defthm fn-lc-dirty-has-distinct-entries
 (no-duplicatesp-equal (fn-lc-dirty old old-header new header))
 :hints (("Goal" :in-theory (e/d (fn-lc-dirty)
                 (fn-lc-value-dirty-from fn-lc-pages)))))
(defthm fn-lc-uncovered-length-bounded-by-columns
 (<= (len (fn-lc-uncovered-dirty (fn-lc-dirty old old-header new header)
                                 old old-header new header))
     (len (fn-lc-dirty-column-pages old new)))
 :rule-classes nil
 :hints (("Goal" :use
  (fn-lc-uncovered-whole-delta-is-column-subset
   (:instance fn-lc-distinct-subset-length
    (xs (fn-lc-uncovered-dirty (fn-lc-dirty old old-header new header)
                              old old-header new header))
    (ys (fn-lc-shift-dirty-column (fn-lc-dirty-column-pages old new)))))
  :in-theory (disable fn-lc-dirty fn-lc-uncovered-dirty fn-lc-value-dirty-from
                     fn-lc-pages fn-lc-dirty-column-pages fn-lc-shift-dirty-column
                     fn-lc-uncovered-whole-delta-is-column-subset))))

(defthm fn-lc-dirty-filter-cover-length
 (let* ((o (+ 1 (len (true-list-fix old))))
        (n (+ 1 (len (true-list-fix new))))
        (od (len (true-list-fix (nth 4 old-header))))
        (nd (len (true-list-fix (nth 4 header))))
        (oc (len (true-list-fix (nth 5 old-header))))
        (nc (len (true-list-fix (nth 5 header)))))
  (<= (len dirty)
      (+ (len (fn-lc-uncovered-dirty dirty old old-header new header))
         (len (fn-lc-changed-part dirty 0 1))
         (len (fn-lc-changed-in-either-range dirty o (+ o od) n (+ n nd)))
         (len (fn-lc-changed-in-either-range dirty (+ o od) (+ o od oc)
                                             (+ n nd) (+ n nd nc))))))
 :rule-classes nil
 :hints (("Goal" :induct (fn-lc-uncovered-dirty dirty old old-header new header)
  :in-theory (e/d (fn-lc-uncovered-dirty fn-lc-uncovered-pagep fn-lc-changed-part
                  fn-lc-changed-in-either-range)
                 (fn-lc-in-either-range nfix)))))
(defthm fn-lc-dirty-bound
 (<= (len (fn-lc-dirty old old-header new header))
      (+ (len (fn-lc-dirty-column-pages old new))
         (len (fn-lc-dirty-directory-structure-pages old old-header new header))
         (len (fn-lc-dirty-control-pages old old-header new header))))
 :rule-classes nil
 :hints (("Goal" :use
  ((:instance fn-lc-dirty-filter-cover-length (dirty (fn-lc-dirty old old-header new header)))
   fn-lc-uncovered-length-bounded-by-columns)
  :in-theory (e/d (fn-lc-dirty-directory-structure-pages fn-lc-dirty-control-pages)
   (fn-lc-dirty fn-lc-dirty-column-pages fn-lc-uncovered-dirty fn-lc-changed-part
    fn-lc-changed-in-either-range fn-lc-table-dirty-keys fn-lc-directory-run-keys
    pgs-touched pgs-dirty-lpages pgs-dir-run-pages fn-lc-pages)))))
(defteeth fn-lc-dirty-bound
 :claim (nil (<= (len (fn-lc-dirty old old-header new header))
     (+ (len (fn-lc-dirty-column-pages old new))
        (len (fn-lc-dirty-directory-structure-pages old old-header new header))
        (len (fn-lc-dirty-control-pages old old-header new header)))))
 :subject fn-lc-dirty
 :witness ((old '((1))) (new '((2)))
   (old-header '(:lc-header (0 0 0 0 nil) 1 nil nil nil))
   (header '(:lc-header (0 0 0 0 nil) 1 nil nil nil)))
 :breaks nil
 :mutations ((drops-writes (:conclusion (<= (len (fn-lc-dirty old old-header new header)) 0))
   nil :fault "a dirty column write is omitted from the admitted work")))
(defteeth-check (fn-lc-dirty-bound))

(defun fn-lc-covered-dirty (dirty old old-header new header)
 (declare (xargs :guard t :verify-guards nil))
 (if (consp dirty)
  (let ((rest (fn-lc-covered-dirty (mbe :logic (cdr dirty) :exec (fn-lc-rest dirty)) old old-header new header)))
   (if (fn-lc-uncovered-pagep (mbe :logic (caar dirty) :exec (fn-lc-head (fn-lc-head dirty))) old old-header new header)
    rest (cons (mbe :logic (car dirty) :exec (fn-lc-head dirty)) rest))) nil))
(defthm fn-lc-covered-and-uncovered-partition-length
 (equal (+ (len (fn-lc-covered-dirty dirty old old-header new header))
           (len (fn-lc-uncovered-dirty dirty old old-header new header)))
        (len dirty))
 :hints (("Goal" :induct (fn-lc-uncovered-dirty dirty old old-header new header)
  :in-theory (e/d (fn-lc-covered-dirty fn-lc-uncovered-dirty)
                 (fn-lc-uncovered-pagep)))))
(defthm fn-lc-covered-members
 (iff (member-equal entry (fn-lc-covered-dirty dirty old old-header new header))
      (and (member-equal entry dirty)
           (not (fn-lc-uncovered-pagep (car entry) old old-header new header))))
 :hints (("Goal" :induct (fn-lc-covered-dirty dirty old old-header new header)
  :in-theory (disable fn-lc-uncovered-pagep))))
(defthm fn-lc-covered-distinct
 (implies (no-duplicatesp-equal dirty)
          (no-duplicatesp-equal (fn-lc-covered-dirty dirty old old-header new header)))
 :hints (("Goal" :induct (fn-lc-covered-dirty dirty old old-header new header)
  :in-theory (e/d (no-duplicatesp-equal) (fn-lc-uncovered-pagep)))))
(defthm fn-lc-covered-keys-above
 (implies (fn-lc-dirty-keys-above dirty low)
          (fn-lc-dirty-keys-above (fn-lc-covered-dirty dirty old old-header new header) low))
 :hints (("Goal" :induct (fn-lc-covered-dirty dirty old old-header new header)
  :in-theory (e/d (fn-lc-dirty-keys-above) (fn-lc-uncovered-pagep)))))
(defthm fn-lc-table-keys-length
 (equal (len (fn-lc-table-dirty-keys tables)) (len tables)))
(defthm fn-lc-directory-keys-length
 (equal (len (fn-lc-directory-run-keys n)) (nfix n)))
(defthm fn-lc-table-key-member
 (iff (member-equal (list :pgs-table i) (fn-lc-table-dirty-keys tables))
      (member-equal i tables)))
(defthm fn-lc-table-keys-distinct
 (implies (no-duplicatesp-equal tables)
          (no-duplicatesp-equal (fn-lc-table-dirty-keys tables))))
(defthm fn-lc-directory-key-too-high
 (implies (and (natp n) (natp i) (<= n i))
          (not (member-equal (list :pgs-directory i) (fn-lc-directory-run-keys n))))
 :hints (("Goal" :induct (fn-lc-directory-run-keys n))))
(defthm fn-lc-directory-keys-distinct
 (implies (natp n) (no-duplicatesp-equal (fn-lc-directory-run-keys n)))
 :hints (("Goal" :induct (fn-lc-directory-run-keys n)
  :in-theory (enable no-duplicatesp-equal))))
(defthm fn-lc-directory-key-not-table-key
 (not (member-equal (list :pgs-directory i) (fn-lc-table-dirty-keys tables))))
(defthm fn-lc-table-key-not-directory-key
 (not (member-equal (list :pgs-table i) (fn-lc-directory-run-keys n))))
(defthm fn-lc-nat-key-not-table-key
 (implies (natp (car entry))
          (not (member-equal entry (fn-lc-table-dirty-keys tables)))))
(defthm fn-lc-nat-key-not-directory-key
 (implies (natp (car entry))
          (not (member-equal entry (fn-lc-directory-run-keys n)))))
(defthm fn-lc-ascending-member-above
 (implies (and (pgs-asc-above xs prev) (natp prev) (member-equal x xs))
          (< prev x))
 :hints (("Goal" :induct (pgs-asc-above xs prev)
                 :in-theory (enable pgs-asc-above))))
(defthm fn-lc-ascending-does-not-contain-prev
 (implies (and (pgs-asc-above xs prev) (natp prev))
          (not (member-equal prev xs)))
 :hints (("Goal" :use ((:instance fn-lc-ascending-member-above (x prev)))
  :in-theory (disable pgs-asc-above fn-lc-ascending-member-above))))
(defthm fn-lc-ascending-distinct
 (implies (pgs-asc-above xs prev) (no-duplicatesp-equal xs))
 :hints (("Goal" :induct (pgs-asc-above xs prev)
  :in-theory (enable pgs-asc-above no-duplicatesp-equal))))
(defun fn-lc-publication-metadata-keys (old old-header new header)
 (declare (xargs :guard t :verify-guards nil))
 (mbe :logic (append (fn-lc-table-dirty-keys
          (pgs-touched (pgs-dirty-lpages (fn-lc-dirty old old-header new header)) nil))
         (fn-lc-directory-run-keys (pgs-dir-run-pages (len (fn-lc-pages new header))))) :exec (fn-lc-join (fn-lc-table-dirty-keys (pgs-touched (pgs-dirty-lpages (fn-lc-dirty old old-header new header)) nil)) (fn-lc-directory-run-keys (pgs-dir-run-pages (len (fn-lc-pages new header)))))))
(defthm fn-lc-touched-tables-distinct
 (no-duplicatesp-equal
  (pgs-touched (pgs-dirty-lpages (fn-lc-dirty old old-header new header)) nil))
 :hints (("Goal" :use
  ((:instance pgs-touched-ascending
    (ls (pgs-dirty-lpages (fn-lc-dirty old old-header new header)))
    (n (len (fn-lc-pages old old-header))) (lo 0) (prev nil))
   (:instance fn-lc-ascending-distinct
    (xs (pgs-touched (pgs-dirty-lpages (fn-lc-dirty old old-header new header)) nil))
    (prev nil)))
  :in-theory (disable pgs-touched pgs-dirty-lpages fn-lc-dirty fn-lc-pages
                      pgs-asc-above fn-lc-ascending-distinct pgs-touched-ascending))))

(defun fn-lc-non-nat-key-listp (xs)
 (declare (xargs :guard t :verify-guards nil))
 (if (consp xs) (and (not (natp (mbe :logic (caar xs) :exec (fn-lc-head (fn-lc-head xs))))) (fn-lc-non-nat-key-listp (mbe :logic (cdr xs) :exec (fn-lc-rest xs)))) t))
(defthm fn-lc-table-markers-non-nat
 (fn-lc-non-nat-key-listp (fn-lc-table-dirty-keys tables)))
(defthm fn-lc-directory-markers-non-nat
 (fn-lc-non-nat-key-listp (fn-lc-directory-run-keys n)))
(defthm fn-lc-non-nat-keys-of-append
 (equal (fn-lc-non-nat-key-listp (append x y))
        (and (fn-lc-non-nat-key-listp x) (fn-lc-non-nat-key-listp y))))
(defthm fn-lc-non-nat-keys-do-not-contain-nat-key
 (implies (and (fn-lc-non-nat-key-listp xs) (natp (car entry)))
          (not (member-equal entry xs))))
(defthm fn-lc-member-append
 (iff (member-equal entry (append x y))
      (or (member-equal entry x) (member-equal entry y))))
(defthm fn-lc-nat-and-non-nat-distinct-append
 (implies (and (no-duplicatesp-equal x) (no-duplicatesp-equal y)
               (fn-lc-dirty-keys-above x 0) (fn-lc-non-nat-key-listp y))
          (no-duplicatesp-equal (append x y)))
 :hints (("Goal" :induct (len x)
  :in-theory (enable no-duplicatesp-equal fn-lc-dirty-keys-above))))
(defthm fn-lc-table-and-directory-markers-distinct
 (implies (and (no-duplicatesp-equal tables) (natp n))
  (no-duplicatesp-equal
   (append (fn-lc-table-dirty-keys tables) (fn-lc-directory-run-keys n))))
 :hints (("Goal" :induct (len tables) :in-theory (enable no-duplicatesp-equal))))
(defthm fn-lc-directory-run-pages-natp
 (natp (pgs-dir-run-pages n))
 :rule-classes :type-prescription
 :hints (("Goal" :in-theory (enable pgs-dir-run-pages pgs-ptab-run-pages pgs-ntables))))
(defthm fn-lc-metadata-keys-distinct
 (no-duplicatesp-equal (fn-lc-publication-metadata-keys old old-header new header))
 :hints (("Goal" :in-theory (e/d (fn-lc-publication-metadata-keys)
  (fn-lc-table-dirty-keys fn-lc-directory-run-keys pgs-touched pgs-dirty-lpages
   fn-lc-dirty pgs-dir-run-pages fn-lc-pages)))))
(defthm fn-lc-metadata-keys-non-nat
 (fn-lc-non-nat-key-listp (fn-lc-publication-metadata-keys old old-header new header))
 :hints (("Goal" :in-theory (e/d (fn-lc-publication-metadata-keys)
  (fn-lc-table-dirty-keys fn-lc-directory-run-keys pgs-touched pgs-dirty-lpages
   fn-lc-dirty pgs-dir-run-pages fn-lc-pages)))))
(defthm fn-lc-covered-and-metadata-distinct
 (no-duplicatesp-equal
  (append (fn-lc-covered-dirty (fn-lc-dirty old old-header new header)
                               old old-header new header)
          (fn-lc-publication-metadata-keys old old-header new header)))
 :hints (("Goal" :use
  ((:instance fn-lc-nat-and-non-nat-distinct-append
    (x (fn-lc-covered-dirty (fn-lc-dirty old old-header new header)
                             old old-header new header))
    (y (fn-lc-publication-metadata-keys old old-header new header))))
  :in-theory (e/d (fn-lc-dirty)
   (fn-lc-value-dirty-from fn-lc-pages fn-lc-covered-dirty
    fn-lc-publication-metadata-keys fn-lc-dirty-keys-above
    fn-lc-non-nat-key-listp fn-lc-nat-and-non-nat-distinct-append)))))

(defthm fn-lc-changed-part-member
 (iff (member-equal entry (fn-lc-changed-part dirty lo hi))
      (and (member-equal entry dirty) (<= (nfix lo) (nfix (car entry)))
           (< (nfix (car entry)) (nfix hi)))))
(defthm fn-lc-changed-either-member
 (iff (member-equal entry (fn-lc-changed-in-either-range dirty lo0 hi0 lo1 hi1))
      (and (member-equal entry dirty)
           (fn-lc-in-either-range (car entry) lo0 hi0 lo1 hi1)))
 :hints (("Goal" :induct (fn-lc-changed-in-either-range dirty lo0 hi0 lo1 hi1)
  :in-theory (disable fn-lc-in-either-range))))
(defthm fn-lc-member-union
 (iff (member-equal entry (union-equal x y))
      (or (member-equal entry x) (member-equal entry y))))
(defthm fn-lc-covered-entry-in-directory
 (implies (and (member-equal entry (fn-lc-dirty old old-header new header))
               (not (fn-lc-uncovered-pagep (car entry) old old-header new header)))
  (member-equal entry (fn-lc-dirty-directory-pages old old-header new header)))
 :hints (("Goal" :in-theory (e/d
  (fn-lc-dirty-directory-pages fn-lc-dirty-directory-structure-pages
   fn-lc-dirty-control-pages fn-lc-uncovered-pagep)
  (fn-lc-dirty fn-lc-changed-part fn-lc-changed-in-either-range fn-lc-in-either-range
   fn-lc-table-dirty-keys fn-lc-directory-run-keys pgs-touched pgs-dirty-lpages
   pgs-dir-run-pages fn-lc-pages union-equal)))))
(defthm fn-lc-covered-subset-directory
 (implies (subsetp-equal dirty (fn-lc-dirty old old-header new header))
  (subsetp-equal (fn-lc-covered-dirty dirty old old-header new header)
                (fn-lc-dirty-directory-pages old old-header new header)))
 :hints (("Goal" :induct (fn-lc-covered-dirty dirty old old-header new header)
  :in-theory (e/d (subsetp-equal) (fn-lc-uncovered-pagep fn-lc-dirty-directory-pages fn-lc-dirty)))))
(defthm fn-lc-subset-of-union-left
 (implies (subsetp-equal x left) (subsetp-equal x (union-equal left right))))
(defthm fn-lc-subset-append
 (iff (subsetp-equal (append x y) z) (and (subsetp-equal x z) (subsetp-equal y z))))

(defthm fn-lc-subset-self (subsetp-equal x x))
(defthm fn-lc-subset-append-right
 (implies (subsetp-equal x y) (subsetp-equal x (append prefix y))))
(defthm fn-lc-subset-append-left
 (implies (subsetp-equal x y) (subsetp-equal x (append y suffix))))
(defthm fn-lc-metadata-subset-directory
 (subsetp-equal (fn-lc-publication-metadata-keys old old-header new header)
                (fn-lc-dirty-directory-pages old old-header new header))
 :hints (("Goal" :in-theory (e/d (fn-lc-publication-metadata-keys
                 fn-lc-dirty-directory-pages fn-lc-dirty-directory-structure-pages)
  (fn-lc-table-dirty-keys fn-lc-directory-run-keys fn-lc-changed-part
   fn-lc-changed-in-either-range fn-lc-dirty-control-pages fn-lc-dirty fn-lc-pages
   pgs-touched pgs-dirty-lpages pgs-dir-run-pages union-equal)))))
(defthm fn-lc-covered-plus-metadata-length
 (<= (+ (len (fn-lc-covered-dirty (fn-lc-dirty old old-header new header)
                                  old old-header new header))
         (len (fn-lc-publication-metadata-keys old old-header new header)))
     (len (fn-lc-dirty-directory-pages old old-header new header)))
 :rule-classes nil
 :hints (("Goal" :use
  ((:instance fn-lc-distinct-subset-length
    (xs (append (fn-lc-covered-dirty (fn-lc-dirty old old-header new header)
                                     old old-header new header)
                (fn-lc-publication-metadata-keys old old-header new header)))
    (ys (fn-lc-dirty-directory-pages old old-header new header))))
  :in-theory (disable fn-lc-dirty fn-lc-covered-dirty fn-lc-publication-metadata-keys
                     fn-lc-dirty-directory-pages union-equal subsetp-equal))))
(defthm fn-lc-dirty-plus-physical-metadata-bound
 (<= (+ (len (fn-lc-dirty old old-header new header))
         (len (pgs-touched (pgs-dirty-lpages (fn-lc-dirty old old-header new header)) nil))
         (pgs-dir-run-pages (len (fn-lc-pages new header))))
     (+ (len (fn-lc-dirty-column-pages old new))
         (len (fn-lc-dirty-directory-pages old old-header new header))))
 :rule-classes nil
 :hints (("Goal" :use
  (fn-lc-uncovered-length-bounded-by-columns fn-lc-covered-plus-metadata-length
   (:instance fn-lc-covered-and-uncovered-partition-length
    (dirty (fn-lc-dirty old old-header new header))))
  :in-theory (e/d (fn-lc-publication-metadata-keys)
   (fn-lc-covered-dirty fn-lc-uncovered-dirty fn-lc-dirty fn-lc-dirty-column-pages
    fn-lc-dirty-directory-pages fn-lc-table-dirty-keys fn-lc-directory-run-keys
    fn-lc-pages pgs-touched pgs-dirty-lpages pgs-dir-run-pages
    fn-lc-covered-and-uncovered-partition-length)))))
