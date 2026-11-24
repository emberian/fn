; A predecessor restart below the query skips only earlier entries.
(in-package "ACL2")
(include-book "range-stored-page-rows-proof")
(include-book "range-page-lower-bound-proof")

(defun-nx fn2-run-overview-prefix-below-p (n rows query)
  (if (zp n) t
    (and (consp rows) (eq (fn2-run-key-order-spec *fn2-overview-range-key* (car rows) query) :lt)
         (fn2-run-overview-prefix-below-p (1- n) (cdr rows) query))))

(local
 (defthm fn2-run-overview-less-transitive
   (implies (and (eq (fn2-run-key-order-spec *fn2-overview-range-key* a b) :lt)
                 (eq (fn2-run-key-order-spec *fn2-overview-range-key* b c) :lt))
            (eq (fn2-run-key-order-spec *fn2-overview-range-key* a c) :lt))
   :rule-classes nil
   :hints (("Goal" :in-theory (disable nfix)))))

(defthmd fn2-run-overview-predecessor-bounds-prefix
  (implies (and (natp i) (< i (len rows)) (fn2-run-sorted-spec *fn2-overview-range-key* rows)
                (eq (fn2-run-key-order-spec *fn2-overview-range-key* (nth i rows) query) :lt))
           (and (eq (fn2-run-key-order-spec *fn2-overview-range-key* (car rows) query) :lt)
                (fn2-run-overview-prefix-below-p i rows query)))
  :hints (("Goal" :induct (nth i rows) :do-not '(preprocess)
           :expand ((len rows) (nth i rows) (fn2-run-overview-prefix-below-p i rows query)
                    (fn2-run-sorted-spec *fn2-overview-range-key* rows))
           :in-theory (disable fn2-run-key-order-spec fn2-run-overview-prefix-below-p fn2-run-sorted-spec))
          (and (equal (access clause-id id :pool-lst) '(1))
               (equal (len (access clause-id id :case-lst)) 1)
               (equal (access clause-id id :primes) 0)
               '(:use ((:instance fn2-run-overview-less-transitive (a (car rows)) (b (cadr rows)) (c query)))
                  :expand ((len (cdr rows)) (len rows) (nth i rows)
                          (fn2-run-sorted-spec *fn2-overview-range-key* rows)
                          (:free (j) (fn2-run-overview-prefix-below-p j rows query)))))))

(local
 (defun-nx fn2-run-overview-prefix-induct (n rows i level off)
   (if (or (zp n) (atom rows)) (list i off)
     (fn2-run-overview-prefix-induct (1- n) (cdr rows) (1+ i) level
                                     (fn2-run-overview-next-offset level (car rows) off)))))

(defthmd fn2-run-overview-lower-bound-skips-prefix
  (let* ((layout (if (and (integerp level) (< 0 level)) *fn2-overview-index* *fn2-overview-entry*))
         (tail (nthcdr n rows)) (at (fn2-run-row-offset n layout rows off)))
    (implies (and (natp n) (natp i) (fn2-run-overview-prefix-below-p n rows query))
             (and (equal (fn2-run-lower-bound-spec *fn2-overview-range-key* tail query (+ i n))
                         (fn2-run-lower-bound-spec *fn2-overview-range-key* rows query i))
                  (equal (fn2-run-overview-lower-bound-offset level tail query at)
                         (fn2-run-overview-lower-bound-offset level rows query off)))))
  :hints (("Goal" :induct (fn2-run-overview-prefix-induct n rows i level off) :do-not '(preprocess)
           :expand ((fn2-run-overview-prefix-below-p n rows query) (nthcdr n rows)
                    (fn2-run-overview-lower-bound-offset level rows query off)
                    (:free (layout) (fn2-run-row-offset n layout rows off))
                    (fn2-run-lower-bound-spec *fn2-overview-range-key* rows query i))
           :in-theory (e/d (fn2-run-overview-next-offset)
                       (fn2-run-lower-bound-spec fn2-run-row-offset fn2-run-overview-lower-bound-offset
                        fn2-run-key-order-spec fn2-run-overview-prefix-below-p fn2-layout-octets)))))
