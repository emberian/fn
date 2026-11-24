(in-package "ACL2")
(include-book "range-head-order-proof")

(defun-nx fn2-overview-active-headp (s sources)
  (and (natp s) (< s (fn2-range-sources-rows sources))
       (equal (fn2-range-sources-state s sources) *fn2-range-state-head*)))

(defun-nx fn2-overview-heads-fitp (n base sources f)
  (if (zp n) t
    (let ((s (+ base (1- n))))
      (and (implies (fn2-overview-active-headp s sources) (fn2-overview-head-fitp s sources f))
           (fn2-overview-heads-fitp (1- n) base sources f)))))

(local
 (defthm fn2-overview-pick-one-head
   (let* ((s (+ base (1- n)))
          (candidate (if (and (fn2-overview-active-headp s sources)
                             (or (not (natp best)) (fn2-overview-head-precedes s best sources f)))
                         s best)))
     (implies (and (posp n) (natp base) (fn2-overview-heads-fitp n base sources f)
                   (implies (natp best) (fn2-overview-head-fitp best sources f)))
              (equal (fn2-range-pick n base 3 best sources f pool)
                     (fn2-range-pick (1- n) base 3 candidate sources f pool))))
   :hints (("Goal" :expand ((fn2-range-pick n base 3 best sources f pool)
                            (fn2-overview-heads-fitp n base sources f))
            :in-theory (e/d (fn2-overview-range-orders-heads fn2-overview-head-precedes)
                            (fn2-overview-head-order fn2-overview-head-fitp fn2-overview-heads-fitp
                             fn2-range-newer fn2-range-order fn2-range-pick
                             fn2-range-sources-state fn2-range-sources-rows))))))

(defun-nx fn2-overview-best-head (n base best sources f)
   (if (zp n) best
     (let ((s (+ base (1- n))))
       (fn2-overview-best-head (1- n) base
         (if (and (fn2-overview-active-headp s sources)
                  (or (not (natp best)) (fn2-overview-head-precedes s best sources f)))
             s best)
         sources f))))

(local
 (defthm fn2-overview-headp-natural
   (implies (fn2-overview-active-headp s sources) (natp s))
   :rule-classes (:rewrite :forward-chaining)))

(defthm fn2-overview-pick-selects-best-head
  (implies (and (natp n) (natp base) (fn2-overview-heads-fitp n base sources f)
                (or (not best) (and (fn2-overview-active-headp best sources)
                                    (fn2-overview-head-fitp best sources f))))
           (equal (fn2-range-pick n base 3 best sources f pool)
                  (list :ok (fn2-overview-best-head n base best sources f))))
  :rule-classes nil
  :hints (("Goal" :do-not '(preprocess) :induct (fn2-overview-best-head n base best sources f)
           :expand ((fn2-overview-heads-fitp n base sources f)
                    (:free (prev) (fn2-overview-best-head n base prev sources f)))
           :in-theory (disable fn2-overview-head-fitp fn2-overview-active-headp
                               fn2-overview-head-precedes fn2-overview-heads-fitp
                               fn2-range-pick (:definition fn2-overview-best-head) fn2-overview-pick-one-head))
          ("Subgoal *1/2" :use fn2-overview-pick-one-head)
          ("Subgoal *1/1" :expand ((:free (prev) (fn2-range-pick n base 3 prev sources f pool))
                                   (:free (prev) (fn2-overview-best-head n base prev sources f))))))

(local
 (defthm fn2-overview-selecting-earlier-retains-bound
  (implies (and (fn2-overview-head-precedes candidate best sources f)
                (not (fn2-overview-head-precedes s best sources f)))
           (not (fn2-overview-head-precedes s candidate sources f)))
  :rule-classes nil
  :hints (("Goal" :use ((:instance fn2-overview-head-precedence-transitive
                                    (a s) (b candidate) (c best)))
           :in-theory (theory 'minimal-theory)))))

(defthmd fn2-overview-best-head-bounds-candidates
  (let ((winner (fn2-overview-best-head n base best sources f)))
    (implies (and (natp n) (natp base) (natp s) (fn2-overview-active-headp s sources)
                  (or (and (<= base s) (< s (+ base n)))
                      (and (natp best) (not (fn2-overview-head-precedes s best sources f)))))
             (and (natp winner) (not (fn2-overview-head-precedes s winner sources f)))))
  :hints (("Goal" :do-not '(preprocess) :induct (fn2-overview-best-head n base best sources f)
           :expand ((:free (prev) (fn2-overview-best-head n base prev sources f)))
           :in-theory (e/d (fn2-overview-head-never-precedes-itself)
                           (fn2-overview-head-precedes fn2-overview-active-headp
                            (:definition fn2-overview-best-head))))
          ("Subgoal *1/2" :cases ((equal s (+ base (1- n))))
           :use ((:instance fn2-overview-selecting-earlier-retains-bound
                            (candidate (+ base (1- n))))))))

(defthmd fn2-overview-best-head-is-supplied
  (let ((winner (fn2-overview-best-head n base best sources f)))
    (implies (and (natp n) (natp base)
                  (or (not best) (fn2-overview-active-headp best sources)))
             (or (not winner)
                 (and (fn2-overview-active-headp winner sources)
                      (or (equal best winner)
                          (and (<= base winner) (< winner (+ base n))))))))
  :hints (("Goal" :do-not '(preprocess) :induct (fn2-overview-best-head n base best sources f)
           :expand ((:free (prev) (fn2-overview-best-head n base prev sources f)))
           :in-theory (disable fn2-overview-head-precedes fn2-overview-active-headp
                               (:definition fn2-overview-best-head)))))

(defthm fn2-overview-pick-wins-among-heads
  (let* ((pick (fn2-range-pick n base 3 nil sources f pool)) (winner (cadr pick)))
    (implies (and (natp n) (natp base) (fn2-overview-heads-fitp n base sources f)
                  (fn2-overview-active-headp s sources) (<= base s) (< s (+ base n)))
             (and (equal (car pick) :ok) (fn2-overview-active-headp winner sources)
                  (<= base winner) (< winner (+ base n))
                  (not (fn2-overview-head-precedes s winner sources f)))))
  :rule-classes nil
  :hints (("Goal" :use ((:instance fn2-overview-pick-selects-best-head (best nil))
                        (:instance fn2-overview-best-head-bounds-candidates (best nil))
                        (:instance fn2-overview-best-head-is-supplied (best nil)))
           :in-theory (disable fn2-range-pick fn2-overview-best-head fn2-overview-heads-fitp
                               fn2-overview-head-precedes fn2-overview-active-headp))))
