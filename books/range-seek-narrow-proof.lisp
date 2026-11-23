; The bounds and answer after the seek consumes its probe result.
(in-package "ACL2")
(include-book "range-served")
(include-book "range-seek-probe-proof")

(defthmd fn2-range-integer-gap
  (implies (and (integerp x) (integerp y))
           (equal (< y (+ 1 x)) (<= y x))))

(defthm fn2-overview-seek-narrow-bounds
 (let* ((g (fn2-seeks-g k s)) (out (fn2-ranges-out g r))
        (n (nfix (fn2-fields-value (+ 1 out) f)))
        (pos (nfix (fn2-fields-value (+ 3 out) f)))
        (lower (and (eq code :entry) (<= pos (fn2-seeks-after k s))))
        (res (fn2-seek-narrow k code s r f)) (after (mv-nth 1 res)))
   (implies (and (natp k) (< k (fn2-seeks-rows s))
                 (natp g) (< g (fn2-ranges-rows r))
                 (or (eq code :end)
                     (and (eq code :entry) (equal (fn2-ranges-schema g r) 3)
                          (equal (fn2-seeks-pfield k s) 3) (natp out)
                          (< (+ out 3) (fn2-fields-rows f))
                          (unsigned-byte-p 60 (1+ n)))))
            (and (equal (mv-nth 0 res) :more)
                 (equal (fn2-seeks-phase k after) *fn2-seek-phase-probe*)
                 (equal (fn2-seeks-lo k after) (if lower (1+ n) (fn2-seeks-lo k s)))
                 (equal (fn2-seeks-hi k after) (if lower (fn2-seeks-hi k s) (fn2-seeks-mid k s))))))
 :rule-classes nil
 :hints (("Goal" :in-theory
          (e/d (fn2-seek-narrow fn2-seeks-set-lo fn2-seeks-set-hi fn2-seeks-set-phase
                update-fn2-seeks-lo$ai update-fn2-seeks-hi$ai update-fn2-seeks-phase$ai nth-update-nth)
               (nth update-nth fn2-ranges-schema fn2-ranges-rows fn2-ranges-out
                fn2-seeks-g fn2-seeks-rows fn2-seeks-pfield fn2-seeks-after
                fn2-fields-rows fn2-fields-value unsigned-byte-p nfix)))))

(defthm fn2-range-below-upper-fits
  (implies (and (unsigned-byte-p 60 hi) (natp n) (< n hi)) (unsigned-byte-p 60 (+ 1 n)))
  :rule-classes nil)
(local
 (defthm fn2-range-natural-fix
  (implies (natp n) (equal (nfix n) n))))
(local
 (defthm fn2-range-u60-integer
  (implies (unsigned-byte-p 60 hi) (integerp hi))
  :rule-classes :forward-chaining))

(local (defthm fn2-range-natp-integer (implies (natp n) (integerp n)) :rule-classes :forward-chaining))
; Given the first row of the specified window (or :end for an empty
; window), the concrete seek update preserves the answer and its bounds.
(defthm fn2-overview-seek-narrow-preserves-answer
 (let* ((g (fn2-seeks-g k s)) (out (fn2-ranges-out g r))
        (mid (fn2-seeks-mid k s)) (hi (fn2-seeks-hi k s))
        (p (fn2-seeks-after k s)) (window (fn2-overview-probe-window es group mid hi))
        (code (if (consp window) :entry :end)) (entry (car window))
        (ans (fn2-range-seek-scan es (list group) 2 p hi 3 0))
        (res (fn2-seek-narrow k code s r f)) (after (mv-nth 1 res)))
   (implies (and (natp group) (natp k) (< k (fn2-seeks-rows s))
                 (natp g) (< g (fn2-ranges-rows r))
                 (equal (fn2-ranges-schema g r) 3) (equal (fn2-seeks-pfield k s) 3)
                 (natp out) (< (+ out 3) (fn2-fields-rows f))
                 (natp mid) (unsigned-byte-p 60 hi) (< mid hi)
                 (fn2-range-natural-keysp es)
                 (fn2-run-sorted-spec *fn2-overview-range-key* es)
                 (fn2-range-monotone-scan es (list group) 3 -1)
                 (<= (fn2-seeks-lo k s) ans)
                 (implies (consp window)
                          (and (equal (fn2-fields-value (+ 1 out) f) (cadr entry))
                               (equal (fn2-fields-value (+ 3 out) f) (nth 3 entry)))))
            (and (equal (mv-nth 0 res) :more)
                 (equal (fn2-range-seek-scan es (list group) 2 p (fn2-seeks-hi k after) 3 0) ans)
                 (<= (fn2-seeks-lo k after) ans))))
 :rule-classes nil
 :hints (("Goal" :use ((:instance fn2-range-below-upper-fits
                              (hi (fn2-seeks-hi k s))
                              (n (fn2-fields-value (+ 1 (fn2-ranges-out (fn2-seeks-g k s) r)) f)))
                       (:instance fn2-range-integer-gap
                              (x (fn2-fields-value (+ 1 (fn2-ranges-out (fn2-seeks-g k s) r)) f))
                              (y (fn2-range-seek-scan es (list group) 2 (fn2-seeks-after k s) (fn2-seeks-hi k s) 3 0)))
                       (:instance fn2-range-seek-scan-natp (prefix (list group)) (nk 2)
                                  (p (fn2-seeks-after k s)) (hi (fn2-seeks-hi k s)) (pidx 3) (acc 0))
                       (:instance fn2-overview-probe-first-key (mid (fn2-seeks-mid k s)) (hi (fn2-seeks-hi k s)))
                       (:instance fn2-range-seek-upper-probe (mid (fn2-seeks-mid k s)) (hi (fn2-seeks-hi k s))
                                  (p (fn2-seeks-after k s)) (last -1) (acc 0))
                       (:instance fn2-range-seek-lower-probe (mid (fn2-seeks-mid k s)) (hi (fn2-seeks-hi k s))
                                  (p (fn2-seeks-after k s)) (acc 0))
                       (:instance fn2-overview-seek-narrow-bounds
                                  (code (if (consp (fn2-overview-probe-window es group (fn2-seeks-mid k s)
                                                                            (fn2-seeks-hi k s))) :entry :end))))
          :cases ((consp (fn2-overview-probe-window es group (fn2-seeks-mid k s) (fn2-seeks-hi k s))))
          :in-theory (union-theories (theory 'minimal-theory)
                        '(fn2-range-natural-fix fn2-range-u60-integer fn2-range-natp-integer (:e natp) commutativity-of-+ not eq
                          fn2-range-integer-gap (:type-prescription fn2-range-seek-scan-natp)
                          (:executable-counterpart expt) (:executable-counterpart binary-+)
                          (:executable-counterpart unary--) (:executable-counterpart <)
                          (:executable-counterpart equal))))))
