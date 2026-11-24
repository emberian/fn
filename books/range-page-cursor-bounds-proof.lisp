; Widths of the search interval and of the row selected on a stored page.
(in-package "ACL2")
(include-book "range-page-lower-bound-proof")

(local
 (defthm fn2-range-page-search-midpoint-width
   (let ((mid (floor (+ lo hi) 2)))
     (implies (and (unsigned-byte-p 32 lo) (unsigned-byte-p 32 hi) (< lo hi))
              (and (unsigned-byte-p 32 mid) (unsigned-byte-p 32 (+ 1 mid)))))))

(defthmd fn2-range-page-search-keeps-interval-width
  (let ((seek (fn2-run-seek sid level fuel lo hi idx off qbase rb slot gen pk ps pg qk qs qg f pool)))
    (implies (and (unsigned-byte-p 32 lo) (unsigned-byte-p 32 hi))
             (and (unsigned-byte-p 32 (mv-nth 1 seek)) (unsigned-byte-p 32 (mv-nth 2 seek)))))
  :hints (("Goal" :induct (fn2-run-seek sid level fuel lo hi idx off qbase rb slot gen pk ps pg qk qs qg f pool)
           :do-not '(preprocess)
           :expand ((:free (idx off) (fn2-run-seek sid level fuel lo hi idx off qbase rb slot gen pk ps pg qk qs qg f pool)))
           :in-theory (union-theories (theory 'minimal-theory)
                       '((:i fn2-run-seek) fn2-range-page-search-midpoint-width eq eql not
                         mv-nth car-cons cdr-cons (:e zp) (:e mv-nth) (:e consp) (:e equal) (:e binary-+) (:e unary--))))))

(defthmd fn2-range-page-selected-offset-fits
  (implies (and (fn2-run-overview-page-rowsp level rows base slot gen off end pk ps pg f pool)
                (unsigned-byte-p 32 off) (unsigned-byte-p 32 end))
           (unsigned-byte-p 32 (fn2-run-overview-lower-bound-offset level rows query off)))
  :hints (("Goal" :induct (fn2-run-overview-page-rowsp level rows base slot gen off end pk ps pg f pool)
           :in-theory (e/d (fn2-run-overview-lower-bound-offset fn2-run-overview-page-rowsp
                            fn2-run-overview-row-atp fn2-run-overview-next-offset)
                    (fn2-run-values-layoutp fn2-run-key-order-spec fn2-layout-octets len fn2-poolp fn2-pool-wfp
                     fn2-pool-base fn2-layout-range-code fn2-run-read-bytes fn2-fields-rows)))))

(defthmd fn2-range-lower-bound-result-limits
  (let* ((result (fn2-run-lower-bound-spec key rows query idx)) (index (cadr result)))
    (implies (natp idx)
             (and (member-eq (car result) '(:found :absent))
                  (natp index) (<= idx index) (<= index (+ idx (len rows)))
                  (implies (eq (car result) :found) (< index (+ idx (len rows)))))))
  :hints (("Goal" :induct (fn2-run-lower-bound-spec key rows query idx)
           :in-theory (disable fn2-run-key-order-spec))))
