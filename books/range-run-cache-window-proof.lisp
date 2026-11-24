; The six range builds get disjoint cache addresses, including the last
; build whose physical units wrap past row 4095.
(in-package "ACL2")
(include-book "runs-built-cache-proof")
(local (include-book "arithmetic-3/floor-mod/floor-mod" :dir :system))

(defun fn2-range-run-unit-p (unit k)
  (declare (xargs :guard t))
  (and (natp unit) (natp k) (<= k 5) (< (* 1000 k) unit) (<= unit (+ 52 (* 1000 k)))))

(local
 (defthm fn2-range-only-positive-quotient
   (implies (and (integerp q) (< 0 q) (< q 2)) (equal q 1)) :rule-classes nil))

(local
 (defthm fn2-range-run-cache-row
   (implies (fn2-range-run-unit-p u k)
            (equal (mod u 4096) (if (equal k 5) (- u 4096) u)))
   :rule-classes nil
   :hints (("Goal" :use ((:instance floor-bounds-1 (x u) (y 4096)) (:instance fn2-range-only-positive-quotient (q (floor u 4096)))) :cases ((equal k 5) (equal (floor u 4096) 1))
            :in-theory (enable fn2-range-run-unit-p mod)))))

(local
 (defthm fn2-range-positive-run-index
   (implies (and (integerp k) (< 0 k)) (<= 1 k)) :rule-classes nil))

(local
 (defthm fn2-range-cache-gap-before-second-run
   (implies (fn2-range-run-unit-p u k) (or (<= u 52) (<= 1001 u)))
   :rule-classes nil
   :hints (("Goal" :use fn2-range-positive-run-index :cases ((equal k 0)) :in-theory (enable fn2-range-run-unit-p)))))

(defthmd fn2-range-run-cache-rows-distinguish-units
  (implies (and (fn2-range-run-unit-p u k) (fn2-range-run-unit-p v j))
           (equal (equal (mod u 4096) (mod v 4096)) (equal u v)))
  :hints (("Goal" :use (fn2-range-cache-gap-before-second-run (:instance fn2-range-cache-gap-before-second-run (u v) (k j))
                fn2-range-run-cache-row (:instance fn2-range-run-cache-row (u v) (k j)))
           :cases ((equal j 5) (equal k 5) (equal j 0) (equal k 0))
           :in-theory (e/d (fn2-range-run-unit-p) (mod)))))

(defun fn2-range-cache-page-units (pages)
  (declare (xargs :guard (true-listp pages) :verify-guards nil))
  (if (atom pages) nil (cons (nth 1 (car pages)) (fn2-range-cache-page-units (cdr pages)))))

(defun fn2-range-run-pages-p (pages k)
  (declare (xargs :guard t :verify-guards nil))
  (if (atom pages) (null pages)
    (and (fn2-run-page-addressp (car pages)) (fn2-range-run-unit-p (nth 1 (car pages)) k)
         (not (member-equal (nth 1 (car pages)) (fn2-range-cache-page-units (cdr pages))))
         (fn2-range-run-pages-p (cdr pages) k))))

(local
 (defthm fn2-range-member-has-page-unit
   (implies (member-equal page pages) (member-equal (nth 1 page) (fn2-range-cache-page-units pages)))
   :hints (("Goal" :induct (len pages) :in-theory (disable nth)))))

(local
 (defthm fn2-range-page-unit-outside-list
   (implies (and (fn2-range-run-pages-p pages k)
                 (fn2-range-run-unit-p (nth 1 page) j) (not (member-equal (nth 1 page) (fn2-range-cache-page-units pages))))
            (fn2-run-cache-compatible-pages-p page pages 4096))
   :hints (("Goal" :induct (len pages)
            :in-theory (e/d (fn2-run-cache-compatible-pages-p fn2-range-run-pages-p fn2-range-cache-page-units
                             fn2-range-run-cache-rows-distinguish-units)
                            (fn2-range-run-unit-p fn2-run-page-addressp mod nth))))))

(defthmd fn2-range-run-cache-finds-listed-page
  (implies (and (fn2-range-run-pages-p pages k) (member-equal page pages))
           (and (fn2-range-run-unit-p (nth 1 page) k) (fn2-run-page-addressp page)
                (fn2-run-cache-compatible-pages-p page pages 4096)))
  :hints (("Goal" :induct (len pages)
           :in-theory (e/d (fn2-run-cache-compatible-pages-p fn2-range-run-pages-p fn2-range-cache-page-units
                            fn2-range-run-cache-rows-distinguish-units)
                           (fn2-range-run-unit-p fn2-run-page-addressp mod nth)))))

(local
 (defthm fn2-range-earlier-unit-outside-later-run
   (implies (and (fn2-range-run-unit-p u j) (fn2-range-run-unit-p v k) (< j k))
            (< u v))
   :rule-classes nil
   :hints (("Goal" :in-theory (enable fn2-range-run-unit-p)
            :use ((:instance fn2-range-positive-run-index (k (- k j))))))))

(defthmd fn2-range-cache-keeps-earlier-run-address
  (implies (and (fn2-range-run-pages-p pages k) (fn2-range-run-unit-p (nth 1 page) j) (< j k))
           (fn2-run-cache-compatible-pages-p page pages 4096))
  :hints (("Goal" :induct (len pages)
           :in-theory (e/d (fn2-range-run-pages-p fn2-run-cache-compatible-pages-p)
                      (fn2-run-page-addressp fn2-range-run-unit-p fn2-range-cache-page-units mod nth)))
          ("Subgoal *1/1" :use ((:instance fn2-range-earlier-unit-outside-later-run (u (nth 1 page)) (v (nth 1 (car pages))))
                       (:instance fn2-range-run-cache-rows-distinguish-units
                           (u (nth 1 page)) (k j) (v (nth 1 (car pages))) (j k))))))
