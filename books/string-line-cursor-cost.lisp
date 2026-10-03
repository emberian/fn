; Logical cons allocation of the actual emitted-string implementation.
; Native host fnn-owner-render-next calls fn-splan-window, whose cursor
; calls FN-SL-STEP. This bridges derived constructors to the existing
; conservative recurrence. Integer/allocator/GC/vector tariffs stay separate.
(in-package "ACL2")
(include-book "def-cost")
(include-book "string-line-cursor")
(local (include-book "arithmetic/top" :dir :system))
(def-cost fn-cur-at :cons-unaccounted nil)
(defthm fn-cur-at-conses-zero
  (equal (fn-cur-at-conses n cur) 0)
  :hints (("Goal" :induct (fn-cur-at-conses n cur))))
(def-cost fn-sl-one :unaccounted (char length) :conses 6 :cons-unaccounted nil)
(local
 (defthm fn-sl-one-derived-conses-limit
   (<= (fn-sl-one-conses cur) 6)
   :rule-classes :linear
   :hints (("Goal" :use fn-sl-one-conses-bound
            :in-theory (e/d (fn-sl-one-route-conses)
                            (fn-sl-one-conses fn-sl-one-conses-bound))))))
(def-cost fn-sl-loop :unaccounted (char length mv-nth) :cons-unaccounted nil)
(defthm fn-sl-loop-derived-conses-within-source-count
  (<= (fn-sl-loop-conses cur bytes acc)
      (fn-sl-loop-cons-cells cur bytes (len acc)))
  :hints (("Goal" :induct (fn-sl-loop-conses cur bytes acc)
           :in-theory (e/d (fn-sl-loop-conses fn-sl-loop-cons-cells)
                           (fn-sl-one fn-sl-one-conses)))))
(def-cost fn-sl-step :unaccounted (char length mv-nth)
  :conses (+ (* 8 n) 2) :sizes ((n (nfix bytes))) :cons-unaccounted nil
  :cons-hints (("Goal" :in-theory (e/d (fn-sl-step-conses fn-sl-step-route-conses)
                                      (fn-sl-loop-conses fn-sl-loop-cons-cells
                           fn-sl-loop-derived-conses-within-source-count))
               :use ((:instance fn-sl-loop-derived-conses-within-source-count (acc nil))))))
(defthm fn-sl-step-derived-conses-within-source-count
  (<= (fn-sl-step-conses cur bytes) (fn-sl-step-cons-cells cur bytes))
  :hints (("Goal" :in-theory (e/d (fn-sl-step-conses fn-sl-step-cons-cells)
                                      (fn-sl-loop-conses fn-sl-loop-cons-cells
                           fn-sl-loop-derived-conses-within-source-count))
               :use ((:instance fn-sl-loop-derived-conses-within-source-count (acc nil))))))

(defthm fn-sl-step-derived-conses-bound
  (<= (fn-sl-step-conses cur bytes) (+ (* 8 (nfix bytes)) 2))
  :rule-classes :linear
  :hints (("Goal" :in-theory (disable fn-sl-step-conses fn-sl-step-cons-cells nfix
                               fn-sl-step-derived-conses-within-source-count
                               fn-sl-step-cons-cells-bound)
           :use (fn-sl-step-derived-conses-within-source-count
                 fn-sl-step-cons-cells-bound))))
(def-cost-check fn-cur-at)
(def-cost-check fn-sl-one)
(def-cost-check fn-sl-loop)
(def-cost-check fn-sl-step)
