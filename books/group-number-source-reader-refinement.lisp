; Endpoint refinement of the actual bounded reader consumed by OVER.
(in-package "ACL2")
(include-book "group-number-source-lookup")
(local (include-book "arithmetic-5/top" :dir :system))
(defthm fn-gns-catalog-number-seq-bounds
 (implies (and (natp ordinal) (fn-cat-number-seq group number catalog ordinal))
   (and (natp (fn-cat-number-seq group number catalog ordinal))
        (<= ordinal (fn-cat-number-seq group number catalog ordinal))
        (< (fn-cat-number-seq group number catalog ordinal) (+ ordinal (len catalog)))))
 :rule-classes nil
 :hints (("Goal" :induct (fn-cat-number-seq group number catalog ordinal))))
(local
 (defthm fn-gns-terminal-number-node-value
  (implies (and (fn-gns-number-cursorp c) (eq (fn-gns-at 0 c) :done))
    (equal (fn-gnix-get (fn-gns-at 1 c) (fn-gns-at 2 c))
           (fn-gnix-val (fn-gns-at 2 c))))
  :hints (("Goal" :in-theory (enable fn-gns-number-cursorp fn-gnix-get)))))
(defthm fn-gns-bounded-number-result-is-catalog-ordinal
 (implies
   (and (fn-gns-number-cursorp c)
        (eq (fn-gns-at 0 c) :done)
        (equal (fn-gns-at 3 c) (len catalog))
        (equal (fn-gnix-get (fn-gns-at 1 c) (fn-gns-at 2 c))
               (fn-gns-ordinal-option (fn-cat-number-seq group number catalog 0))))
   (equal (fn-gns-number-result c)
          (if (fn-cat-number-seq group number catalog 0)
              (list :ordinal (fn-cat-number-seq group number catalog 0))
            '(:missing))))
 :hints (("Goal"
   :use ((:instance fn-gns-catalog-number-seq-bounds (ordinal 0))
         (:instance fn-gns-catalog-number-seq-type (ordinal 0))
         (:instance fn-gns-terminal-number-node-value))
   :in-theory (e/d (fn-gns-number-result fn-gns-ordinal-option)
                   (fn-cat-number-seq fn-gnix-get fn-gns-number-cursorp)))))
