; Existing relation/model events extracted verbatim for a narrow proof boundary.
(in-package "ACL2")
(include-book "catalog")

(defun fn-cat-handles-inp (n fn-arena fn-cat)
  (declare (xargs :stobjs (fn-arena fn-cat)
                  :guard (and (natp n) (<= n (fn-cat-count fn-cat)))
                  :guard-hints (("Goal" :in-theory (e/d (fn-cat-p-is-rowsp) (fn-held-p))
                                 :use ((:instance fn-cat-rowp-fields (h (nth (- n 1) fn-cat)))
                                       (:instance fn-cat-rowp-of-nth-of-rowsp
                                                  (xs fn-cat) (i (- n 1))))))))
  (if (zp n)
      t
    (and (< (fn-record-payload (fn-cat-at (- n 1) fn-cat)) (fn-arena-count fn-arena))
         (fn-cat-handles-inp (- n 1) fn-arena fn-cat))))

(defthm fn-cat-handles-inp-at
  (implies (and (fn-cat-handles-inp n fn-arena fn-cat) (natp n) (natp seq) (< seq n))
           (< (fn-record-payload (fn-cat-at seq fn-cat)) (fn-arena-count fn-arena))))

(defthm fn-cat-handles-inp-monotone
  (implies (and (fn-cat-handles-inp n fn-arena fn-cat) (natp n) (natp m) (<= m n))
           (fn-cat-handles-inp m fn-arena fn-cat)))

(defthm fn-cat-row-payload-natp
  (implies (and (fn-cat-p fn-cat) (natp seq) (< seq (fn-cat-count fn-cat)))
           (natp (fn-record-payload (fn-cat-at seq fn-cat))))
  :rule-classes (:rewrite :type-prescription)
  :hints (("Goal" :in-theory (e/d (fn-cat-p-is-rowsp) (fn-held-p))
           :use ((:instance fn-cat-rowp-fields (h (nth seq fn-cat)))
                 (:instance fn-cat-rowp-of-nth-of-rowsp (xs fn-cat) (i seq))))))

(defthm fn-cat-count-natp
  (natp (fn-cat-count fn-cat))
  :rule-classes (:rewrite :type-prescription)
  :hints (("Goal" :in-theory (enable fn-cat-count-is-len))))
