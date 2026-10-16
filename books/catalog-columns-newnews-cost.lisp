; NEWNEWS reads prefix maxima by binary search, then only the candidate tail.
; These counters are derived from the executed column workers.
(in-package "ACL2")
(include-book "catalog-columns-guards")
(include-book "def-cost")
(local (include-book "arithmetic-5/top" :dir :system))
(local (in-theory (disable fn-lbc-value fn-lbc-visiblep fn-lbc-flag fn-lbc-msgid fn-lbc-numbers fn-lbc-newnews-candidatep floor mod |(floor x 2)|)))

(local (defthm fn-lbnc-midpoint-bounds
 (implies (and (natp lo) (natp hi) (< lo hi))
  (and (natp (+ lo (floor (- hi lo) 2)))
       (<= lo (+ lo (floor (- hi lo) 2)))
       (< (+ lo (floor (- hi lo) 2)) hi)))
 :rule-classes nil
 :hints (("Goal" :in-theory (disable floor mod |(floor x 2)|)))))

(def-cost fn-lbc-first-reaching
 :unaccounted (fn-lbc-value)
 :measure-hints (("Goal" :use fn-lbnc-midpoint-bounds :in-theory (union-theories (theory 'ground-zero) '(nfix natp))))
 :calls ((prefix-reads (fn-lbc-value) :stop-at (fn-lbc-newnews-tail) :measure-hints (("Goal" :use fn-lbnc-midpoint-bounds :in-theory (union-theories (theory 'ground-zero) '(nfix natp)))))))
(def-cost fn-lbc-newnews-tail
 :unaccounted (fn-lbc-visiblep fn-lbc-flag fn-lbc-msgid fn-lbc-numbers fn-lbc-value fn-lbc-newnews-candidatep fn-nntp-article-idp fn-nntp-string-octets fn-ng-less-equal)
 :calls ((candidate-reads (fn-lbc-visiblep) :stop-at (fn-lbc-first-reaching))))
(def-cost fn-lbc-newnews-range
 :unaccounted (fn-lbc-value fn-lbc-visiblep fn-lbc-flag fn-lbc-msgid fn-lbc-numbers fn-lbc-newnews-candidatep fn-nntp-article-idp fn-nntp-string-octets fn-ng-less-equal)
 :calls ((prefix-reads (fn-lbc-value) :stop-at (fn-lbc-newnews-tail))
         (candidate-reads (fn-lbc-visiblep) :stop-at (fn-lbc-first-reaching))))

; A bound on binary splits, independent of catalog values or execution.
(defun fn-lbc-binary-depth (n)
 (declare (xargs :guard (natp n) :measure (nfix n)))
 (if (zp n) 0 (+ 1 (fn-lbc-binary-depth (floor n 2)))))

(local (defun fn-lbnc-depth-pair-induct (a b)
 (declare (xargs :measure (+ (nfix a) (nfix b))))
 (if (and (posp a) (posp b))
  (fn-lbnc-depth-pair-induct (floor a 2) (floor b 2)) nil)))
(local (defthm fn-lbnc-depth-monotone
 (implies (and (natp a) (natp b) (<= a b))
  (<= (fn-lbc-binary-depth a) (fn-lbc-binary-depth b)))
 :rule-classes nil
 :hints (("Goal" :induct (fn-lbnc-depth-pair-induct a b)
  :in-theory (enable fn-lbc-binary-depth fn-lbnc-depth-pair-induct)))))

(local (defthm fn-lbnc-depth-split
 (implies (and (natp lo) (natp hi) (< lo hi))
  (let ((mid (+ lo (floor (- hi lo) 2))))
   (and (< (fn-lbc-binary-depth (- hi (+ 1 mid))) (fn-lbc-binary-depth (- hi lo)))
        (< (fn-lbc-binary-depth (- mid lo)) (fn-lbc-binary-depth (- hi lo))))))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-lbnc-depth-monotone
    (a (- hi (+ 1 lo (floor (- hi lo) 2)))) (b (floor (- hi lo) 2))))
  :expand ((fn-lbc-binary-depth (- hi lo)))
  :in-theory (disable fn-lbc-binary-depth floor mod |(floor x 2)|)))))

(local (defthm fn-lbnc-typed-first-reaching-prefix-reads
 (implies (and (natp lo) (natp hi) (<= lo hi))
  (<= (fn-lbc-first-reaching-prefix-reads threshold lo hi fn-lbc-v)
      (fn-lbc-binary-depth (- hi lo))))
 :hints (("Goal" :induct (fn-lbc-first-reaching-prefix-reads threshold lo hi fn-lbc-v)
  :in-theory (set-difference-theories
   (union-theories (theory 'ground-zero) '(fn-lbc-first-reaching-prefix-reads natp nfix (:type-prescription fn-lbc-binary-depth)))
   '(floor mod (tau-system))))
 ("Subgoal *1/1" :use (fn-lbnc-midpoint-bounds fn-lbnc-depth-split))
 ("Subgoal *1/2" :use (fn-lbnc-midpoint-bounds fn-lbnc-depth-split))
 ("Subgoal *1/3" :expand ((fn-lbc-binary-depth (- hi lo)))))))

(local (defthm fn-lbnc-first-reaching-invalid-cost
 (implies (not (and (natp lo) (natp hi) (< lo hi)))
  (equal (fn-lbc-first-reaching-prefix-reads threshold lo hi fn-lbc-v) 0))
 :hints (("Goal" :do-not-induct t :in-theory (set-difference-theories
  (union-theories (theory 'ground-zero) '(fn-lbc-first-reaching-prefix-reads natp nfix))
  '(floor mod (tau-system)))))))

(defthm fn-lbc-first-reaching-logarithmic-prefix-reads
 (<= (fn-lbc-first-reaching-prefix-reads threshold lo hi fn-lbc-v)
  (fn-lbc-binary-depth (nfix (- hi lo))))
 :hints (("Goal" :do-not-induct t :cases ((and (natp lo) (natp hi) (<= lo hi)))
  :use (fn-lbnc-typed-first-reaching-prefix-reads fn-lbnc-first-reaching-invalid-cost)
  :in-theory (set-difference-theories
   (union-theories (theory 'ground-zero)
    '(natp nfix (:type-prescription fn-lbc-binary-depth)))
   '(floor mod (tau-system))))))

(defthm fn-lbc-newnews-tail-exact-candidate-reads
 (equal (fn-lbc-newnews-tail-candidate-reads groups threshold v lo hi fn-lbc-v)
  (if (and (natp lo) (natp hi)) (nfix (- hi lo)) 0))
 :hints (("Goal" :induct (fn-lbc-newnews-tail-candidate-reads groups threshold v lo hi fn-lbc-v)
  :in-theory (union-theories (theory 'ground-zero)
   '(fn-lbc-newnews-tail-candidate-reads natp nfix)))))

(defthm fn-lbc-newnews-range-logarithmic-prefix-reads
 (<= (fn-lbc-newnews-range-prefix-reads groups threshold v horizon fn-lbc-v)
     (fn-lbc-binary-depth v))
 :hints (("Goal" :cases ((natp v))
  :use ((:instance fn-lbc-first-reaching-logarithmic-prefix-reads (lo 0) (hi v)))
  :in-theory (set-difference-theories
   (union-theories (theory 'ground-zero)
    '(fn-lbc-newnews-range-prefix-reads fn-lbc-first-reaching-prefix-reads
      (:type-prescription fn-lbc-binary-depth) fn-lbc-binary-depth natp nfix))
   '(floor mod (tau-system))))))

(defthm fn-lbc-newnews-range-exact-tail-reads
 (equal (fn-lbc-newnews-range-candidate-reads groups threshold v horizon fn-lbc-v)
  (if (and (natp v) (natp (fn-lbc-first-reaching threshold 0 v fn-lbc-v)))
   (nfix (- v (fn-lbc-first-reaching threshold 0 v fn-lbc-v))) 0))
 :hints (("Goal" :in-theory (union-theories (theory 'ground-zero)
  '(fn-lbc-newnews-range-candidate-reads fn-lbc-newnews-tail-exact-candidate-reads)))))

(def-cost-check fn-lbc-first-reaching)
(def-cost-check fn-lbc-newnews-tail)
(def-cost-check fn-lbc-newnews-range)
