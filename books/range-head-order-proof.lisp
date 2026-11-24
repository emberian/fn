; Selection among the resident heads of an overview range.
(in-package "ACL2")
(include-book "range-window-proof")

(defun-nx fn2-overview-head-base (s sources)
  (+ *fn2-run-reader-entry* (fn2-range-sources-rb s sources)))

(defun-nx fn2-overview-head-fitp (s sources f)
  (and (natp s) (< s (fn2-range-sources-rows sources))
       (natp (fn2-overview-head-base s sources))
       (<= (+ (fn2-overview-head-base s sources) *fn2-run-entry-rows*)
           (fn2-fields-rows f))))

(defun-nx fn2-overview-head-order (a b sources f)
  (fn2-run-key-order-spec *fn2-overview-range-key*
    (fn2-overview-range-key-at (fn2-overview-head-base a sources) f)
    (fn2-overview-range-key-at (fn2-overview-head-base b sources) f)))

(defthmd fn2-overview-range-orders-heads
  (implies (and (fn2-overview-head-fitp a sources f) (fn2-overview-head-fitp b sources f))
           (equal (fn2-range-order 3 a b sources f pool)
                  (list :ok (fn2-overview-head-order a b sources f))))
  :hints (("Goal" :in-theory
           (e/d (fn2-range-order)
                (fn2-fields-rows fn2-range-sources-rb fn2-range-sources-rows
                 fn2-run-key-order-spec fn2-overview-range-key-at
                 fn2-run-layout-compare)))))

(defun-nx fn2-overview-head-precedes (a b sources f)
  (let ((order (fn2-overview-head-order a b sources f)))
    (or (eq order :lt) (and (eq order :eq) (fn2-range-newer a b sources)))))

(defthmd fn2-overview-head-never-precedes-itself
  (not (fn2-overview-head-precedes a a sources f))
  :hints (("Goal" :in-theory
           (e/d (fn2-range-newer)
                (fn2-overview-head-base fn2-fields-value fn2-range-sources-rows
                 fn2-range-sources-run fn2-range-sources-kind nfix)))))

(defthmd fn2-overview-head-precedence-transitive
  (implies (and (fn2-overview-head-precedes a b sources f)
                (fn2-overview-head-precedes b c sources f))
           (fn2-overview-head-precedes a c sources f))
  :hints (("Goal" :in-theory
           (e/d (fn2-range-newer)
                (fn2-overview-head-base fn2-fields-value fn2-range-sources-rows
                 fn2-range-sources-run fn2-range-sources-kind nfix)))))
