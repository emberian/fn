; The overview encoder depends on four identities and one line reference.
; Searching for an insertion position preserves those inputs in full.
(in-package "ACL2")
(include-book "range-overlay-search-fields-proof")

(defun-nx fn2-ov-same-input-p (base f f2)
  (let ((i (+ base 4)))
    (and (equal (fn2-fields-value base f) (fn2-fields-value base f2))
         (equal (fn2-fields-value (+ base 1) f) (fn2-fields-value (+ base 1) f2))
         (equal (fn2-fields-value (+ base 2) f) (fn2-fields-value (+ base 2) f2))
         (equal (fn2-fields-value (+ base 3) f) (fn2-fields-value (+ base 3) f2))
         (equal (fn2-fields-ref-slot i f) (fn2-fields-ref-slot i f2))
         (equal (fn2-fields-ref-gen i f) (fn2-fields-ref-gen i f2))
         (equal (fn2-fields-ref-off i f) (fn2-fields-ref-off i f2))
         (equal (fn2-fields-ref-len i f) (fn2-fields-ref-len i f2)))))

(local
 (defthm fn2-ov-same-input-size
   (implies (and (natp base) (fn2-ov-same-input-p base f f2))
            (equal (fn2-overview-entry-size base f) (fn2-overview-entry-size base f2)))
   :rule-classes nil
   :hints (("Goal" :in-theory (e/d (fn2-ov-same-input-p fn2-overview-entry-size fn2-overview-entry-size-group
                        fn2-overview-entry-size-number fn2-overview-entry-size-article fn2-overview-entry-size-position
                        fn2-overview-entry-size-line)
                       (fn2-fields-value fn2-fields-ref-slot fn2-fields-ref-gen fn2-fields-ref-off fn2-fields-ref-len fn2-layout-varsize))))))

(local
 (defthm fn2-ov-same-input-check
   (implies (and (natp base) (fn2-ov-same-input-p base f f2))
            (equal (fn2-overview-entry-check-values base dst off end pk ps pg f pool)
                   (fn2-overview-entry-check-values base dst off end pk ps pg f2 pool)))
   :rule-classes nil
   :hints (("Goal" :in-theory (e/d (fn2-ov-same-input-p fn2-overview-entry-check-values fn2-overview-entry-check-group
                        fn2-overview-entry-check-number fn2-overview-entry-check-article fn2-overview-entry-check-position
                        fn2-overview-entry-check-line)
                       (fn2-fields-value fn2-fields-ref-slot fn2-fields-ref-gen fn2-fields-ref-off fn2-fields-ref-len
                        fn2-layout-range-code unsigned-byte-p))))))

(local
 (defthm fn2-ov-same-input-emission
   (implies (and (natp base) (fn2-ov-same-input-p base f f2))
            (equal (fn2-overview-entry-emit-group base dst dg off off pk ps pg f pool)
                   (fn2-overview-entry-emit-group base dst dg off off pk ps pg f2 pool)))
   :rule-classes nil
   :hints (("Goal" :do-not '(preprocess)
            :in-theory (e/d (fn2-ov-same-input-p fn2-overview-entry-emit-group fn2-overview-entry-emit-number
                        fn2-overview-entry-emit-article fn2-overview-entry-emit-position fn2-overview-entry-emit-line)
                       (fn2-codec-emit-varint fn2-layout-copy fn2-fields-value fn2-fields-ref-slot fn2-fields-ref-gen
                        fn2-fields-ref-off fn2-fields-ref-len))))))

(defthm fn2-ov-same-input-encodes-identically
  (implies (and (natp base) (fn2-ov-same-input-p base f f2))
           (and (equal (fn2-run-layout-size 3 0 base f) (fn2-run-layout-size 3 0 base f2))
                (equal (fn2-run-layout-encode 3 0 base dst dg off pk ps pg f pool)
                       (fn2-run-layout-encode 3 0 base dst dg off pk ps pg f2 pool))))
  :rule-classes nil
  :hints (("Goal" :do-not '(preprocess)
           :use (fn2-ov-same-input-size fn2-ov-same-input-emission
                 (:instance fn2-ov-same-input-check (end (+ off (fn2-overview-entry-size base f)))))
           :in-theory (e/d (fn2-run-layout-encode fn2-run-layout-size fn2-overview-entry-encode)
                      (fn2-ov-same-input-p fn2-overview-entry-size fn2-overview-entry-check-values fn2-overview-entry-emit-group
                       fn2-layout-range-code unsigned-byte-p nfix)))))

(defthm fn2-ov-search-preserves-input-for-encode
  (let* ((loc (fn2-ov-locate o eb base 9 0 1 ov ix f pool)) (after (mv-nth 3 loc)))
    (implies (and (natp base) (< (+ base 4) eb)
                  (fn2-ov-overview-reader-p o eb base ov ix f) (equal (fn2-overlays-count o ov) (len rows))
                  (fn2-ov-indexed-rows-p (len rows) rows o eb ov ix f pool))
             (and (fn2-ov-same-input-p base after f) (equal (fn2-fields-rows after) (fn2-fields-rows f)))))
  :rule-classes nil
  :hints (("Goal" :do-not '(preprocess)
           :use ((:instance fn2-ov-locate-keeps-outside-field (qbase base) (qk 9) (qs 0) (qg 1) (j base))
                 (:instance fn2-ov-locate-keeps-outside-field (qbase base) (qk 9) (qs 0) (qg 1) (j (+ base 1)))
                 (:instance fn2-ov-locate-keeps-outside-field (qbase base) (qk 9) (qs 0) (qg 1) (j (+ base 2)))
                 (:instance fn2-ov-locate-keeps-outside-field (qbase base) (qk 9) (qs 0) (qg 1) (j (+ base 3)))
                 (:instance fn2-ov-locate-keeps-outside-field (qbase base) (qk 9) (qs 0) (qg 1) (j (+ base 4))))
           :in-theory (e/d (fn2-ov-same-input-p fn2-range-field-contents fn2-ov-overview-reader-p)
                      (fn2-ov-locate fn2-ov-okp fn2-ov-indexed-rows-p fn2-fields-rows fn2-fields-wfp fn2-fieldsp
                       fn2-fields-value fn2-fields-ref-slot fn2-fields-ref-gen fn2-fields-ref-off fn2-fields-ref-len
                       fn2-fields-status fn2-overlays-count fn2-overlays-schema len)))))
