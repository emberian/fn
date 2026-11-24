; The overlay index addresses complete overview rows. Reading one leaves
; the remaining positions readable, including during the seal's copy.
(in-package "ACL2")
(include-book "range-overlay-row-proof")
(include-book "range-stored-row-proof")

(defthm fn2-ov-reads-indexed-overview
  (let* ((read (fn2-ov-entry o i eb ov ix f pool)) (after (mv-nth 2 read)))
    (implies (and (natp n) (natp i) (< i n) (<= n (fn2-overlays-count o ov))
                  (fn2-ov-overview-reader-p o eb qbase ov ix f)
                  (equal (fn2-overlays-okind o ov) 9) (equal (fn2-overlays-oslot o ov) 0)
                  (equal (fn2-overlays-ogen o ov) 1)
                  (fn2-ov-indexed-rows-p n rows o eb ov ix f pool))
             (and (equal (car read) :ok)
                  (equal (fn2-run-unload-values *fn2-overview-entry* eb after pool) (nth i rows))
                  (fn2-ov-overview-reader-p o eb qbase ov ix after)
                  (fn2-ov-indexed-rows-p n rows o eb ov ix after pool))))
  :rule-classes nil
  :hints (("Goal" :do-not '(preprocess)
           :use ((:instance fn2-ov-indexed-entry-reads-address (pos i))
                 (:instance fn2-range-unloads-stored-overview-row (row (nth i rows)) (base eb)
                  (slot (fn2-overlays-slot o ov)) (gen (fn2-overlays-gen o ov))
                  (off (fn2-overlay-index-off (+ (fn2-overlays-ibase o ov) i) ix)) (end (fn2-overlays-fill o ov))))
           :in-theory (union-theories (theory 'minimal-theory) '((:e equal) (:e not))))))

(local
 (defthm fn2-ov-read-next-suffix
   (implies (natp i)
            (and (equal (car (nthcdr i rows)) (nth i rows))
                 (equal (nthcdr (1+ i) rows) (cdr (nthcdr i rows)))))
   :hints (("Goal" :induct (nthcdr i rows) :in-theory (enable nth nthcdr)))))

(defthm fn2-ov-read-indexed-sequence
  (let ((read (fn2-ov-adapter-read k i *fn2-overview-entry* ov ix f pool)))
    (implies (and (natp n) (natp i) (natp k) (<= (+ i k) n)
                  (<= n (fn2-overlays-count 0 ov))
                  (fn2-ov-overview-reader-p 0 *fn2-run-adapter-reader* qbase ov ix f)
                  (equal (fn2-overlays-okind 0 ov) 9) (equal (fn2-overlays-oslot 0 ov) 0)
                  (equal (fn2-overlays-ogen 0 ov) 1)
                  (fn2-ov-indexed-rows-p n rows 0 *fn2-run-adapter-reader* ov ix f pool))
             (equal (car read) (take k (nthcdr i rows)))))
  :rule-classes nil
  :hints (("Goal" :induct (fn2-ov-adapter-read k i *fn2-overview-entry* ov ix f pool)
           :do-not '(preprocess generalize fertilize eliminate-destructors)
           :expand ((fn2-ov-adapter-read k i *fn2-overview-entry* ov ix f pool) (take k (nthcdr i rows)))
           :in-theory (e/d ((:induction fn2-ov-adapter-read))
                       ((:definition fn2-ov-adapter-read) fn2-ov-entry fn2-ov-indexed-rows-p
                        fn2-ov-overview-reader-p fn2-run-unload-values fn2-overlays-count fn2-overlays-okind
                        fn2-overlays-oslot fn2-overlays-ogen nth nthcdr take)))
          (and (equal (access clause-id id :pool-lst) '(1))
               (equal (len (access clause-id id :case-lst)) 1)
               (equal (access clause-id id :primes) 0)
               '(:use ((:instance fn2-ov-reads-indexed-overview (o 0) (eb *fn2-run-adapter-reader*)))))))

(local
 (defthm fn2-ov-frozen-position-address
   (let ((after (fn2-overlays-set-phase o *fn2-overlay-phase-frozen* ov)))
     (and (equal (fn2-overlays-rows after) (fn2-overlays-rows ov))
          (equal (fn2-overlays-schema o after) (fn2-overlays-schema o ov))
          (equal (fn2-overlays-ibase o after) (fn2-overlays-ibase o ov))
          (equal (fn2-overlays-icap o after) (fn2-overlays-icap o ov))
          (equal (fn2-ov-indexed-row-p o i row eb after ix f pool)
                 (fn2-ov-indexed-row-p o i row eb ov ix f pool))
          (equal (fn2-overlays-count o after) (fn2-overlays-count o ov))
          (equal (fn2-overlays-okind o after) (fn2-overlays-okind o ov))
          (equal (fn2-overlays-oslot o after) (fn2-overlays-oslot o ov))
          (equal (fn2-overlays-ogen o after) (fn2-overlays-ogen o ov))))
   :hints (("Goal" :in-theory (e/d (fn2-ov-indexed-row-p fn2-overlays-slot fn2-overlays-gen fn2-overlays-fill
                                  fn2-overlays-ibase fn2-overlays-okind fn2-overlays-oslot fn2-overlays-ogen
                                  fn2-overlays-count fn2-overlays-schema fn2-overlays-rows fn2-overlays-icap
                                  update-fn2-overlays-phase$ai nth-update-nth fn2-overlays-set-phase)
                                 (fn2-run-overview-row-atp fn2-overlay-index-off nth update-nth))))))

(local
 (defthm fn2-ov-freezing-retains-indexed-positions
   (equal (fn2-ov-indexed-rows-p n rows o eb (fn2-overlays-set-phase o *fn2-overlay-phase-frozen* ov) ix f pool)
          (fn2-ov-indexed-rows-p n rows o eb ov ix f pool))
   :hints (("Goal" :induct (fn2-ov-indexed-rows-p n rows o eb ov ix f pool)
            :in-theory (disable fn2-overlays-set-phase fn2-ov-indexed-row-p nth)))))

(local
 (defthm fn2-ov-freezing-retains-reader
   (implies (fn2-ov-overview-reader-p o eb qbase ov ix f)
            (fn2-ov-overview-reader-p o eb qbase (fn2-overlays-set-phase o *fn2-overlay-phase-frozen* ov) ix f))
   :hints (("Goal" :in-theory (e/d (fn2-ov-overview-reader-p fn2-ov-okp)
                   (fn2-overlays-count fn2-overlays-ibase fn2-overlays-icap fn2-overlays-rows fn2-overlays-schema
                    fn2-overlays-set-phase fn2-overlays-wfp fn2-overlay-index-wfp fn2-fields-wfp
                    fn2-fieldsp fn2-fields-rows fn2-overlay-index-rows nth update-nth))))))

(local
 (defthm fn2-ov-reader-has-overlay
   (implies (fn2-ov-overview-reader-p o eb qbase ov ix f) (< o (fn2-overlays-rows ov)))
   :rule-classes nil
   :hints (("Goal" :in-theory (e/d (fn2-ov-overview-reader-p fn2-ov-okp)
                                   (fn2-overlays-rows fn2-overlays-wfp fn2-overlay-index-wfp fn2-fieldsp fn2-fields-wfp))))))

(local
 (defthm fn2-ov-copy-whole-list
   (implies (true-listp rows) (equal (take (len rows) rows) rows))))

(defthm fn2-range-seal-reads-indexed-overlay
  (let* ((freeze (fn2-ov-freeze 0 ov)) (after (mv-nth 1 freeze))
         (read (fn2-ov-adapter-read (fn2-overlays-count 0 after) 0 *fn2-overview-entry* after ix f pool)))
    (implies (and (true-listp rows) (equal (fn2-overlays-count 0 ov) (len rows))
                  (equal (fn2-overlays-phase 0 ov) *fn2-overlay-phase-active*)
                  (equal (fn2-overlays-okind 0 ov) 9) (equal (fn2-overlays-oslot 0 ov) 0)
                  (equal (fn2-overlays-ogen 0 ov) 1)
                  (fn2-ov-overview-reader-p 0 *fn2-run-adapter-reader* qbase ov ix f)
                  (fn2-ov-indexed-rows-p (len rows) rows 0 *fn2-run-adapter-reader* ov ix f pool))
             (and (equal (car freeze) :ok) (equal (car read) rows))))
  :rule-classes nil
  :hints (("Goal" :do-not '(preprocess)
           :use ((:instance fn2-ov-reader-has-overlay (o 0) (eb *fn2-run-adapter-reader*))
                 (:instance fn2-ov-read-indexed-sequence (i 0) (k (len rows)) (n (len rows))
                  (ov (fn2-overlays-set-phase 0 *fn2-overlay-phase-frozen* ov))))
           :in-theory (e/d (fn2-ov-freeze fn2-ov-advance)
                (fn2-overlays-set-phase fn2-overlays-phase fn2-overlays-rows fn2-overlays-count fn2-ov-adapter-read
                 fn2-ov-overview-reader-p fn2-ov-indexed-rows-p fn2-overlays-okind fn2-overlays-oslot fn2-overlays-ogen)))))
