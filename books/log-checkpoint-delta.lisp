; Page delta refinement, including allocation of a new all-zero page.
(in-package "ACL2")
(include-book "log-checkpoint-values")
(include-book "defkeystone")
(local (include-book "std/lists/append" :dir :system))
(local (include-book "std/lists/update-nth" :dir :system))

(defthm fn-lc-update-after-prefix
  (equal (update-nth (len prefix) value (append prefix (cons old tail)))
         (append prefix (cons value tail)))
  :hints (("Goal" :induct (len prefix) :in-theory (enable update-nth))))
(defun fn-lc-delta-induction (old new i count prefix)
  (declare (xargs :guard t :measure (nfix count) :verify-guards nil) (irrelevant old))
  (if (mbe :logic (zp count) :exec (not (posp count))) prefix
    (fn-lc-delta-induction old new (+ 1 (nfix i)) (1- count)
      (mbe :logic (append prefix (list (fn-lc-page-at (nfix i) new))) :exec (fn-lc-join prefix (list (fn-lc-page-at (nfix i) new)))))))
(defthm fn-lc-delta-applies-to-observed-region
  (implies (and (natp i) (natp count) (equal (len prefix) i))
           (equal (pgs-apply-dirty
                   (append prefix (fn-lc-observe-from i count old))
                   (fn-lc-value-dirty-from old new i count))
                  (append prefix (fn-lc-observe-from i count new))))
  :hints (("Goal" :induct (fn-lc-delta-induction old new i count prefix)
           :in-theory (e/d (fn-lc-value-dirty-from fn-lc-observe-from pgs-apply-dirty)
                           (fn-lc-page-at fn-lc-zero-page)))))

(defthm fn-lc-len-observe-from
 (equal (len (fn-lc-observe-from i count pages)) (nfix count)))

(defthm fn-lc-nthcdr-at-end
 (implies (true-listp pages) (equal (nthcdr (len pages) pages) nil)))
(defthm fn-lc-nthcdr-cons
 (implies (and (natp i) (< i (len pages)))
  (equal (cons (nth i pages) (nthcdr (+ 1 i) pages)) (nthcdr i pages)))
 :hints (("Goal" :induct (nthcdr i pages))))
(defthm fn-lc-observe-existing-region
 (implies (and (natp i) (natp count) (true-listp pages)
               (equal (len pages) (+ i count)))
          (equal (fn-lc-observe-from i count pages) (nthcdr i pages)))
 :hints (("Goal" :induct (fn-lc-observe-from i count pages)
          :in-theory (e/d (fn-lc-page-at) (nth nthcdr)))))
; Standing rule: snapshot recognizers are not needed by the total delta algebra.
(defthm fn-lc-dirty-is-the-delta
  (let* ((old-pages (fn-lc-pages old old-header))
         (new-pages (fn-lc-pages new header))
         (limit (max (len old-pages) (len new-pages))))
    (equal (fn-lc-observe-pages
             (pgs-apply-dirty (fn-lc-observe-pages old-pages limit)
                              (fn-lc-dirty old old-header new header)) limit)
           (fn-lc-observe-pages new-pages limit)))
 :rule-classes nil
 :hints (("Goal" :use
   ((:instance fn-lc-delta-applies-to-observed-region
     (i 0) (count (max (len (fn-lc-pages old old-header))
                      (len (fn-lc-pages new header))))
     (prefix nil) (old (fn-lc-pages old old-header))
     (new (fn-lc-pages new header)))
    (:instance fn-lc-observe-existing-region
     (i 0) (pages (fn-lc-observe-pages (fn-lc-pages new header)
                    (max (len (fn-lc-pages old old-header))
                         (len (fn-lc-pages new header)))))
     (count (max (len (fn-lc-pages old old-header))
                 (len (fn-lc-pages new header))))))
   :in-theory (e/d (fn-lc-dirty fn-lc-observe-pages)
    (fn-lc-value-dirty-from fn-lc-observe-from fn-lc-pages pgs-apply-dirty
     fn-lc-delta-applies-to-observed-region fn-lc-observe-existing-region)))))

(defteeth fn-lc-dirty-is-the-delta
 :claim (() (let* ((old-pages (fn-lc-pages old old-header))
         (new-pages (fn-lc-pages new header))
         (limit (max (len old-pages) (len new-pages))))
    (equal (fn-lc-observe-pages
             (pgs-apply-dirty (fn-lc-observe-pages old-pages limit)
                              (fn-lc-dirty old old-header new header)) limit)
           (fn-lc-observe-pages new-pages limit))))
 :subject fn-lc-dirty
 :witness ((old '((1))) (new '((2))) (old-header '(:lc-header (0 0 0 0 nil) 1 nil nil nil)) (header '(:lc-header (0 0 0 0 nil) 1 nil nil nil)))
 :breaks nil
 :mutations ((lost-write (:conclusion (let* ((old-pages (fn-lc-pages old old-header))
         (new-pages (fn-lc-pages new header))
         (limit (max (len old-pages) (len new-pages))))
    (equal (fn-lc-observe-pages
             (pgs-apply-dirty (fn-lc-observe-pages old-pages limit)
                              nil) limit)
           (fn-lc-observe-pages new-pages limit))))
  ((old '((1))) (new '((2))) (old-header '(:lc-header (0 0 0 0 nil) 1 nil nil nil)) (header '(:lc-header (0 0 0 0 nil) 1 nil nil nil))) :fault "delta loses the changed column write")))
(defteeth-check (fn-lc-dirty-is-the-delta))

(defthm fn-lc-publish-plan-commits-the-delta
  (let* ((old-pages (fn-lc-pages old old-header))
         (new-pages (fn-lc-pages new header))
         (limit (max (len old-pages) (len new-pages))))
    (implies (equal (car (fn-lc-publish-plan old old-header new header)) :commit)
             (and (equal (cadr (fn-lc-publish-plan old old-header new header))
                         (fn-lc-dirty old old-header new header))
                  (equal (fn-lc-observe-pages
                           (pgs-apply-dirty (fn-lc-observe-pages old-pages limit)
                             (cadr (fn-lc-publish-plan old old-header new header))) limit)
                         (fn-lc-observe-pages new-pages limit)))))
  :rule-classes nil
 :hints (("Goal" :use fn-lc-dirty-is-the-delta
   :in-theory (e/d (fn-lc-publish-plan) (fn-lc-dirty fn-lc-observe-pages pgs-apply-dirty fn-lc-pages)))))

(defteeth fn-lc-publish-plan-commits-the-delta
 :claim (let* ((old-pages (fn-lc-pages old old-header))
         (new-pages (fn-lc-pages new header))
         (limit (max (len old-pages) (len new-pages)))) (((commit (equal (car (fn-lc-publish-plan old old-header new header)) :commit))) (and (equal (cadr (fn-lc-publish-plan old old-header new header))
                         (fn-lc-dirty old old-header new header))
                  (equal (fn-lc-observe-pages
                           (pgs-apply-dirty (fn-lc-observe-pages old-pages limit)
                             (cadr (fn-lc-publish-plan old old-header new header))) limit)
                         (fn-lc-observe-pages new-pages limit)))))
 :subject fn-lc-publish-plan :witness ((old '((1))) (new '((2))) (old-header '(:lc-header (0 0 0 0 nil) 1 nil nil nil)) (header '(:lc-header (0 0 0 0 nil) 1 nil nil nil)))
 :breaks ((commit ((old-header nil))))
 :mutations ((drops-delta (:conclusion (and (equal (cadr (fn-lc-publish-plan old old-header new header))
                         (fn-lc-dirty old old-header new header))
                  (equal (fn-lc-observe-pages
                           (pgs-apply-dirty (fn-lc-observe-pages old-pages limit)
                             nil) limit)
                         (fn-lc-observe-pages new-pages limit)))) ((old '((1))) (new '((2))) (old-header '(:lc-header (0 0 0 0 nil) 1 nil nil nil)) (header '(:lc-header (0 0 0 0 nil) 1 nil nil nil)))
  :fault "accepted publication plan loses its dirty writes")))
(defteeth-check (fn-lc-publish-plan-commits-the-delta))

(defthm fn-lc-dirty-past-both-extents
 (implies (and (natp i) (<= (len old) i) (<= (len new) i))
          (equal (fn-lc-value-dirty-from old new i count) nil))
 :hints (("Goal" :induct (fn-lc-value-dirty-from old new i count)
  :in-theory (e/d (fn-lc-page-at) (fn-lc-zero-page)))))
(defthm fn-lc-lpages-lower-low
 (implies (and (pgs-lpages-ok ls n hi) (<= (nfix lo) (nfix hi)))
          (pgs-lpages-ok ls n lo))
 :hints (("Goal" :induct (pgs-lpages-ok ls n hi)
          :in-theory (enable pgs-lpages-ok))))
(defthm fn-lc-value-dirty-lpages-ok
 (implies (natp i)
  (pgs-lpages-ok
   (pgs-dirty-lpages (fn-lc-value-dirty-from old new i count))
   (max (len old) i) i))
 :hints (("Goal" :induct (fn-lc-value-dirty-from old new i count)
  :in-theory (e/d (fn-lc-value-dirty-from pgs-dirty-lpages pgs-lpages-ok max)
                 (fn-lc-page-at fn-lc-zero-page)))))
(defthm fn-lc-dirty-lpages-ok
 (pgs-lpages-ok (pgs-dirty-lpages (fn-lc-dirty old old-header new header))
                (len (fn-lc-pages old old-header)) 0)
 :hints (("Goal" :use
  ((:instance fn-lc-value-dirty-lpages-ok (i 0)
    (old (fn-lc-pages old old-header)) (new (fn-lc-pages new header))
    (count (max (len (fn-lc-pages old old-header)) (len (fn-lc-pages new header))))))
  :in-theory (e/d (fn-lc-dirty) (fn-lc-pages fn-lc-value-dirty-from pgs-lpages-ok
                 fn-lc-value-dirty-lpages-ok pgs-dirty-lpages)))))

(defun fn-lc-exact-delta-induction (old new i count prefix)
 (declare (xargs :measure (nfix count) :guard t :verify-guards nil) (irrelevant old))
 (if (mbe :logic (zp count) :exec (not (posp count))) prefix
  (fn-lc-exact-delta-induction old new (+ 1 (nfix i)) (1- count)
                             (mbe :logic (append prefix (list (fn-lc-page-at (nfix i) new))) :exec (fn-lc-join prefix (list (fn-lc-page-at (nfix i) new)))))))
(defthm fn-lc-nthcdr-beyond
 (implies (and (true-listp x) (natp n) (<= (len x) n))
          (equal (nthcdr n x) nil))
 :hints (("Goal" :induct (nthcdr n x))))
(defthm fn-lc-cdr-nthcdr
 (implies (natp i) (equal (cdr (nthcdr i x)) (nthcdr (+ 1 i) x)))
 :hints (("Goal" :induct (nthcdr i x))))
; APPEND discards an improper prefix's final atom. UPDATE-NTH's append
; rule normalizes that prefix; the delta induction must identify both forms.
(local
 (defthm fn-lc-append-true-list-fix
  (equal (append (true-list-fix prefix) tail) (append prefix tail))
  :hints (("Goal" :induct (len prefix)
           :in-theory (enable true-list-fix binary-append)))))
(defthm fn-lc-exact-delta-region
 (implies (and (natp i) (natp count) (equal (len prefix) i)
               (true-listp old) (true-listp new)
               (<= (len old) (len new)) (equal (+ i count) (len new)))
  (equal (pgs-apply-dirty (append prefix (nthcdr i old))
                         (fn-lc-value-dirty-from old new i count))
         (append prefix (nthcdr i new))))
 :hints (("Goal" :induct (fn-lc-exact-delta-induction old new i count prefix)
  :in-theory (e/d (fn-lc-value-dirty-from fn-lc-page-at pgs-apply-dirty)
                 (fn-lc-zero-page nth nthcdr)))))
(defthm fn-lc-exact-delta-nonshrinking
 (implies (and (true-listp old) (true-listp new) (<= (len old) (len new)))
  (equal (pgs-apply-dirty old (fn-lc-value-dirty-from old new 0 (len new))) new))
 :hints (("Goal" :use ((:instance fn-lc-exact-delta-region
  (i 0) (count (len new)) (prefix nil)))
  :in-theory (disable fn-lc-value-dirty-from pgs-apply-dirty
                     fn-lc-exact-delta-region))))
