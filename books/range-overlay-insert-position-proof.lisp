; For a sorted input the next row belongs at the end of the populated
; index. Looking it up for insertion leaves its scalar and reference fields
; available to the encoder.
(in-package "ACL2")
(include-book "range-overlay-search-proof")
(include-book "range-overlay-search-fields-proof")

(local
 (defthm fn2-range-sorted-append-last-key
   (implies (fn2-run-sorted-spec *fn2-overview-range-key* (append rows (list query)))
            (and (fn2-run-sorted-spec *fn2-overview-range-key* rows)
                 (implies (consp rows)
                          (equal (fn2-run-key-order-spec *fn2-overview-range-key* (nth (1- (len rows)) rows) query) :lt))))
   :hints (("Goal" :induct (len rows) :do-not '(preprocess)
            :expand ((len rows) (len (cdr rows))
                     (fn2-run-sorted-spec *fn2-overview-range-key* rows)
                     (fn2-run-sorted-spec *fn2-overview-range-key* (append rows (list query))))
            :in-theory (disable fn2-run-key-order-spec)))))

(local
 (defthm fn2-range-input-lower-bound-at-end
   (implies (fn2-run-sorted-spec *fn2-overview-range-key* (append rows (list query)))
            (equal (cadr (fn2-run-lower-bound-spec *fn2-overview-range-key* rows query 0)) (len rows)))
   :hints (("Goal" :cases ((consp rows)) :do-not '(preprocess)
            :use ((:instance fn2-overview-bound-index-in-range (i 0))
                  (:instance fn2-overview-row-before-lower-bound (j (1- (len rows))) (i 0)))
            :in-theory (disable fn2-run-key-order-spec fn2-run-sorted-spec fn2-run-lower-bound-spec nth))
           ("Subgoal 2" :expand ((fn2-run-lower-bound-spec *fn2-overview-range-key* rows query 0))))))

(defthm fn2-ov-locates-sorted-append
  (let* ((query (fn2-overview-range-key-at base f)) (n (len rows))
         (loc (fn2-ov-locate o eb base 9 0 1 ov ix f pool)) (after (mv-nth 3 loc)))
    (implies (and (< n 48) (equal (fn2-overlays-count o ov) n)
                  (fn2-run-sorted-spec *fn2-overview-range-key* (append rows (list query)))
                  (fn2-ov-overview-reader-p o eb base ov ix f) (fn2-ov-indexed-rows-p n rows o eb ov ix f pool)
                  (natp j) (or (< j eb) (<= (+ 5 eb) j)))
             (and (equal (car loc) :ok) (equal (mv-nth 1 loc) n) (equal (mv-nth 2 loc) :end)
                  (equal (fn2-range-field-contents j after) (fn2-range-field-contents j f))
                  (fn2-ov-overview-reader-p o eb base ov ix after) (fn2-ov-indexed-rows-p n rows o eb ov ix after pool))))
  :rule-classes nil
  :hints (("Goal" :do-not '(preprocess)
           :use ((:instance fn2-run-integer-length-monotonic (i (len rows)) (j 48))
                 (:instance fn2-ov-locates-stored-lower-bound (qbase base) (qk 9) (qs 0) (qg 1))
                 (:instance fn2-ov-locate-keeps-outside-field (qbase base) (qk 9) (qs 0) (qg 1)))
           :in-theory (disable fn2-ov-locate fn2-run-key-order-spec fn2-run-sorted-spec fn2-run-lower-bound-spec
                     fn2-ov-overview-reader-p fn2-ov-indexed-rows-p fn2-range-field-contents fn2-overview-range-key-at
                     fn2-overlays-count binary-append nth integer-length len))))
