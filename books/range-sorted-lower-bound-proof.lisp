; A comparison at any checked row tells which side of the lower bound it
; occupies. This also covers a query in the gap between consecutive keys.
(in-package "ACL2")
(include-book "range-page-prefix-proof")

(local
 (defun-nx fn2-overview-bound-walk (rows j i)
   (if (or (zp j) (atom rows)) i (fn2-overview-bound-walk (cdr rows) (1- j) (1+ i)))))

(defthmd fn2-overview-bound-index-in-range
  (let ((index (cadr (fn2-run-lower-bound-spec *fn2-overview-range-key* rows query i))))
    (implies (natp i) (and (natp index) (<= i index) (<= index (+ i (len rows))))))
  :hints (("Goal" :induct (fn2-run-lower-bound-spec *fn2-overview-range-key* rows query i)
           :in-theory (disable fn2-run-key-order-spec))))

(defthmd fn2-overview-row-before-lower-bound
  (let ((bound (cadr (fn2-run-lower-bound-spec *fn2-overview-range-key* rows query i))))
    (implies (and (natp i) (natp j) (< j (len rows))
                  (fn2-run-sorted-spec *fn2-overview-range-key* rows))
             (equal (eq (fn2-run-key-order-spec *fn2-overview-range-key* (nth j rows) query) :lt)
                    (< (+ i j) bound))))
  :hints (("Goal" :induct (fn2-overview-bound-walk rows j i) :do-not '(preprocess)
           :expand ((fn2-run-lower-bound-spec *fn2-overview-range-key* rows query i)
                    (fn2-run-sorted-spec *fn2-overview-range-key* rows) (nth j rows) (len rows))
           :in-theory (disable fn2-run-lower-bound-spec fn2-run-sorted-spec fn2-run-key-order-spec nth))
          (and (equal (access clause-id id :pool-lst) '(1))
               (equal (len (access clause-id id :case-lst)) 1)
               (equal (access clause-id id :primes) 0)
               '(:use ((:instance fn2-run-overview-predecessor-bounds-prefix (i j))
                       (:instance fn2-overview-bound-index-in-range (i (1+ i)) (rows (cdr rows))))
                 :expand ((fn2-run-lower-bound-spec *fn2-overview-range-key* rows query i)
                          (fn2-run-sorted-spec *fn2-overview-range-key* rows) (nth j rows) (len rows))))))
