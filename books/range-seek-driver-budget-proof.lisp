; A completed midpoint probe releases one full probe's worth of the fuel
; that the positioned seek driver reserves at its entry point.
(in-package "ACL2")
(include-book "range-seek-step-proof")
(local (include-book "centaur/bitops/integer-length" :dir :system))
(local (include-book "range-restart-count-proof"))

(local
 (defthmd fn2-range-halved-width-costs-one-fewer-bit
   (implies (and (posp width) (<= next (floor width 2)))
            (<= (1+ (integer-length (nfix next))) (integer-length width)))
   :hints (("Goal" :use ((:instance fn2-run-integer-length-monotonic
                                (i (nfix next)) (j (floor width 2))))
            :in-theory (disable integer-length floor)))))

(local
 (defthmd fn2-range-scaled-probe-budget
   (implies (and (natp count) (natp bits) (natp left) (<= (1+ left) bits))
            (<= (+ count (* left count)) (* bits count)))
   :hints (("Goal" :nonlinearp t))))

(defthmd fn2-range-half-width-frees-probe-budget
  (implies (and (posp width) (<= next (floor width 2)) (natp sources))
           (<= (+ (1- (fn2-rgs-step-limit 1 sources)) (fn2-rgs-step-limit (nfix next) sources))
               (fn2-rgs-step-limit width sources)))
  :hints (("Goal" :do-not '(preprocess) :use (fn2-range-halved-width-costs-one-fewer-bit
                  (:instance fn2-range-scaled-probe-budget (bits (integer-length width)) (left (integer-length (nfix next)))
                       (count (1- (fn2-rgs-step-limit 1 sources)))))
           :in-theory (e/d (fn2-rgs-step-limit) (integer-length floor)))))

(defthmd fn2-range-seek-step-frees-probe-budget
 (let* ((g (fn2-seeks-g k s)) (out (fn2-ranges-out g r))
        (lo (fn2-seeks-lo k s)) (mid (fn2-seeks-mid k s)) (hi (fn2-seeks-hi k s))
        (p (fn2-seeks-after k s)) (key *fn2-overview-range-key*) (prefix (list group))
        (window (fn2-range-spec key sources (list group mid) (list group (1- hi)) nil 0))
        (row (car window)) (answer (fn2-range-seek-spec key sources prefix p hi 3))
        (step (fn2-seek-step k budget s r rs ov ix runs curs paths cache f pool))
        (after (mv-nth 1 step)) (new-lo (fn2-seeks-lo k after)) (new-hi (fn2-seeks-hi k after)))
   (implies (and (fn2-range-inputp *fn2-overview-entry* key sources budget)
                 (fn2-range-monotonep key sources prefix 3)
                 (natp group) (natp k) (< k (fn2-seeks-rows s)) (natp g) (< g (fn2-ranges-rows r))
                 (equal (fn2-ranges-schema g r) 3) (equal (fn2-seeks-pfield k s) 3)
                 (natp out) (< (+ out 3) (fn2-fields-rows f))
                 (natp lo) (unsigned-byte-p 60 hi) (< lo hi)
                 (equal mid (floor (+ lo hi) 2)) (<= lo answer)
                 (equal (fn2-seeks-phase k s)
                        (if (consp window) *fn2-seek-phase-entry* *fn2-seek-phase-end*))
                 (implies (consp window)
                          (and (equal (fn2-fields-value (+ out 1) f) (cadr row))
                               (equal (fn2-fields-value (+ out 3) f) (nth 3 row)))))
            (<= (+ (1- (fn2-rgs-step-limit 1 (len sources)))
                   (fn2-rgs-step-limit (nfix (- new-hi new-lo)) (len sources)))
                (fn2-rgs-step-limit (- hi lo) (len sources)))))
  :hints (("Goal" :do-not '(preprocess)
           :use (fn2-overview-seek-step-interval
                 (:instance fn2-range-half-width-frees-probe-budget
                      (width (- (fn2-seeks-hi k s) (fn2-seeks-lo k s))) (sources (len sources))
                      (next (- (fn2-seeks-hi k (mv-nth 1 (fn2-seek-step k budget s r rs ov ix runs curs paths cache f pool)))
                               (fn2-seeks-lo k (mv-nth 1 (fn2-seek-step k budget s r rs ov ix runs curs paths cache f pool)))))))
           :in-theory (e/d (natp posp) (fn2-rgs-step-limit fn2-seek-step fn2-range-spec fn2-range-seek-spec
                       fn2-range-inputp fn2-range-monotonep fn2-seeks-phase fn2-seeks-rows fn2-seeks-g fn2-seeks-pfield
                       fn2-seeks-lo fn2-seeks-mid fn2-seeks-hi fn2-seeks-after fn2-ranges-out fn2-ranges-rows fn2-ranges-schema
                       fn2-fields-rows fn2-fields-value floor nfix len nth)))))
