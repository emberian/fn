; Pessimistic size of the canonical history image, including empty regions.
(in-package "ACL2")
(include-book "history-pages-write")
(local (include-book "arithmetic/top" :dir :system))

(local
 (defthm fn-hp-pow2-at-least-upper
   (implies (and (natp k) (posp acc))
            (<= (adt-pow2-at-least k acc) (max acc (* 2 (- k 1)))))
   :hints (("Goal" :induct (adt-pow2-at-least k acc)
            :in-theory (enable adt-pow2-at-least)))
   :rule-classes :linear))

(defthm fn-hp-cap-pessimistic
  (implies (natp u) (< (adt-cap u) (+ 1 (/ (* 2 u) 16384))))
  :hints (("Goal" :use ((:instance fn-hp-pow2-at-least-upper
                                  (k (ceiling u 16384)) (acc 1)))
           :in-theory (e/d (adt-cap ceiling floor) (adt-pow2-at-least))))
  :rule-classes nil)

(local
 (defthm fn-hp-caps-sum-pessimistic
   (implies (consp regs)
            (< (fn-hp-caps-sum regs)
               (+ (len regs) (/ (* 2 (fn-hp-regs-octets regs)) 16384))))
   :hints (("Goal" :induct (fn-hp-caps-sum regs)
            :in-theory (disable adt-cap))
           (and stable-under-simplificationp
                '(:use ((:instance fn-hp-cap-pessimistic (u (len (car regs))))))))))

(defthm fn-hp-npages-pessimistic
  (and (<= (fn-hp-npages h salt) (+ 1 (fn-hp-caps-sum (fn-hp-regs h salt))))
       (< (fn-hp-npages h salt) (+ 6 (/ (* 2 (fn-hp-regs-octets (fn-hp-regs h salt))) 16384))))
  :hints (("Goal" :use (fn-hp-npages-is-caps-sum fn-hp-len-regs-5
                  (:instance fn-hp-caps-sum-pessimistic (regs (fn-hp-regs h salt))))
           :in-theory (disable adt-cap fn-hp-caps-sum fn-hp-regs-octets fn-hp-regs
                               fn-hp-npages fn-hp-npages-is-end-l)))
  :rule-classes nil)
