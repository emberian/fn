; After a delivery every source tied at the winning key advances together.
(in-package "ACL2")
(include-book "range-head-pick-proof")

(defthmd fn2-overview-source-state-write
  (let ((after (fn2-range-sources-set-state i v sources)))
    (and (equal (fn2-range-sources-rows after) (fn2-range-sources-rows sources))
         (equal (fn2-range-sources-rb j after) (fn2-range-sources-rb j sources))
         (implies (and (natp i) (natp j))
                  (equal (fn2-range-sources-state j after)
                         (if (equal i j) v (fn2-range-sources-state j sources))))))
  :hints (("Goal" :in-theory (e/d (fn2-range-sources-set-state update-fn2-range-sources-state$ai
                                   fn2-range-sources-rb fn2-range-sources-state fn2-range-sources-rows
                                   nth-update-nth) (nth update-nth)))))

(local (in-theory (enable fn2-overview-source-state-write)))
(local (in-theory (disable fn2-range-sources-rows fn2-range-sources-rb
                           fn2-range-sources-state fn2-range-sources-set-state
                           fn2-fields-rows fn2-overview-range-key-at fn2-run-key-order-spec)))

(local
 (defthm fn2-overview-write-preserves-head-location
   (let ((after (fn2-range-sources-set-state i v sources)))
     (and (equal (fn2-overview-head-fitp s after f) (fn2-overview-head-fitp s sources f))
          (equal (fn2-overview-head-order s best after f) (fn2-overview-head-order s best sources f))))))

(local
 (defthm fn2-overview-write-above-heads
  (implies (and (natp base) (natp n) (natp i) (<= (+ base n) i))
           (equal (fn2-overview-heads-fitp n base (fn2-range-sources-set-state i v sources) f)
                  (fn2-overview-heads-fitp n base sources f)))
  :hints (("Goal" :induct (fn2-overview-heads-fitp n base sources f)
           :in-theory (disable fn2-overview-head-fitp)))))

(defthm fn2-overview-consume-matching-heads
  (let* ((result (fn2-range-consume n base 3 best sources f pool))
         (after (mv-nth 1 result)))
    (implies (and (natp n) (natp base) (natp j)
                  (fn2-overview-head-fitp best sources f)
                  (fn2-overview-heads-fitp n base sources f))
             (and (equal (car result) :ok)
                  (equal (fn2-range-sources-state j after)
                         (if (and (<= base j) (< j (+ base n))
                                  (fn2-overview-active-headp j sources)
                                  (eq (fn2-overview-head-order j best sources f) :eq))
                             *fn2-range-state-next*
                           (fn2-range-sources-state j sources))))))
  :rule-classes nil
  :hints (("Goal" :induct (fn2-range-consume n base 3 best sources f pool)
           :expand ((fn2-overview-heads-fitp n base sources f)
                    (fn2-range-consume n base 3 best sources f pool))
           :in-theory (e/d ((:induction fn2-range-consume) fn2-overview-range-orders-heads)
                           (fn2-overview-head-order fn2-overview-head-fitp fn2-overview-heads-fitp
                            fn2-range-order (:definition fn2-range-consume))))))
