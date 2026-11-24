; Looking up an overlay position can decode several rows. None of those
; reads overwrites the pending insert or a different source's head.
(in-package "ACL2")
(include-book "range-decoder-fields-proof")
(include-book "range-overlay-row-proof")

(local
 (defthm fn2-ov-indexed-entry-keeps-outside-field
   (let ((read (fn2-ov-entry o pos eb ov ix f pool)))
     (implies (and (fn2-ov-overview-reader-p o eb qbase ov ix f)
                   (natp n) (natp pos) (< pos n) (equal (fn2-overlays-count o ov) n)
                   (fn2-ov-indexed-rows-p n rows o eb ov ix f pool)
                   (natp j) (or (< j eb) (<= (+ 5 eb) j)))
              (equal (fn2-range-field-contents j (mv-nth 2 read)) (fn2-range-field-contents j f))))
   :rule-classes nil
   :hints (("Goal" :do-not '(preprocess)
            :use (fn2-ov-indexed-entry-reads-address
                  (:instance fn2-range-decoding-leaf-keeps-outside-field (base eb) (row (nth pos rows))
                    (slot (fn2-overlays-slot o ov)) (gen (fn2-overlays-gen o ov))
                    (off (fn2-overlay-index-off (+ (fn2-overlays-ibase o ov) pos) ix)) (end (fn2-overlays-fill o ov))
                    (pk (fn2-overlays-okind o ov)) (ps (fn2-overlays-oslot o ov)) (pg (fn2-overlays-ogen o ov))))
            :in-theory (union-theories (theory 'minimal-theory) '(commutativity-of-+ (:e equal) (:e not)))))))

(local
 (defthmd fn2-ov-order-keeps-outside-field
   (let* ((order (fn2-ov-order o pos eb qbase qk qs qg ov ix f pool)) (after (mv-nth 2 order)))
     (implies (and (fn2-ov-overview-reader-p o eb qbase ov ix f)
                   (natp n) (equal (fn2-overlays-count o ov) n) (fn2-ov-indexed-rows-p n rows o eb ov ix f pool)
                   (natp j) (or (< j eb) (<= (+ 5 eb) j)))
              (and (equal (fn2-range-field-contents j after) (fn2-range-field-contents j f))
                   (fn2-ov-overview-reader-p o eb qbase ov ix after)
                   (fn2-ov-indexed-rows-p n rows o eb ov ix after pool))))
   :hints (("Goal" :do-not '(preprocess)
            :cases ((and (natp pos) (< pos n)))
            :use (fn2-ov-indexed-entry-keeps-outside-field fn2-ov-search-reads-indexed-row)
            :in-theory (e/d (fn2-ov-order)
                       (fn2-ov-indexed-rows-p fn2-ov-overview-reader-p fn2-range-field-contents fn2-ov-entry
                        fn2-run-layout-compare fn2-run-key-order-spec fn2-overview-range-key-at
                        fn2-overlays-rows fn2-overlays-count fn2-overlays-schema fn2-overlays-okind fn2-overlays-oslot
                        fn2-overlays-ogen fn2-fields-rows nth))))))

(local
 (defthmd fn2-ov-search-keeps-outside-field
   (let* ((search (fn2-ov-search steps lo hi o eb qbase qk qs qg ov ix f pool)) (after (mv-nth 2 search)))
     (implies (and (fn2-ov-overview-reader-p o eb qbase ov ix f)
                   (natp n) (equal (fn2-overlays-count o ov) n) (fn2-ov-indexed-rows-p n rows o eb ov ix f pool)
                   (natp j) (or (< j eb) (<= (+ 5 eb) j)))
              (and (equal (fn2-range-field-contents j after) (fn2-range-field-contents j f))
                   (fn2-ov-overview-reader-p o eb qbase ov ix after)
                   (fn2-ov-indexed-rows-p n rows o eb ov ix after pool))))
   :hints (("Goal" :induct (fn2-ov-search steps lo hi o eb qbase qk qs qg ov ix f pool)
            :expand ((fn2-ov-search steps lo hi o eb qbase qk qs qg ov ix f pool)) :do-not '(preprocess)
            :in-theory (e/d ((:induction fn2-ov-search))
                       ((:definition fn2-ov-search) fn2-ov-order fn2-ov-overview-reader-p fn2-ov-indexed-rows-p
                        fn2-range-field-contents fn2-overlays-count floor nfix)))
           (and (equal (access clause-id id :pool-lst) '(1))
                (equal (len (access clause-id id :case-lst)) 1) (equal (access clause-id id :primes) 0)
                '(:use ((:instance fn2-ov-order-keeps-outside-field (pos (floor (+ (nfix lo) (nfix hi)) 2)))))))))

(defthm fn2-ov-locate-keeps-outside-field
  (let* ((loc (fn2-ov-locate o eb qbase qk qs qg ov ix f pool)) (after (mv-nth 3 loc)))
    (implies (and (fn2-ov-overview-reader-p o eb qbase ov ix f)
                  (equal (fn2-overlays-count o ov) (len rows))
                  (fn2-ov-indexed-rows-p (len rows) rows o eb ov ix f pool)
                  (natp j) (or (< j eb) (<= (+ 5 eb) j)))
             (equal (fn2-range-field-contents j after) (fn2-range-field-contents j f))))
  :rule-classes nil
  :hints (("Goal" :do-not '(preprocess)
           :use ((:instance fn2-ov-search-keeps-outside-field (steps *fn2-ov-search-steps*) (lo 0) (hi (len rows)) (n (len rows)))
                 (:instance fn2-ov-order-keeps-outside-field (n (len rows))
                    (pos (mv-nth 1 (fn2-ov-search *fn2-ov-search-steps* 0 (len rows) o eb qbase qk qs qg ov ix f pool)))
                    (f (mv-nth 2 (fn2-ov-search *fn2-ov-search-steps* 0 (len rows) o eb qbase qk qs qg ov ix f pool)))))
           :in-theory (e/d (fn2-ov-locate)
                      (fn2-ov-search fn2-ov-order fn2-ov-overview-reader-p fn2-ov-indexed-rows-p
                       fn2-range-field-contents fn2-overlays-rows fn2-overlays-count len)))))
