; The page domain is 20 bytes. A full writer call consumes those bytes,
; switches to the page, and returns after the first page span.
(in-package "ACL2")
(include-book "runs-page-hash-completion-proof")

(local
 (defthmd fn2-run-hash-prefix-byte-count
   (implies (and (natp n) (<= n 20) (fn2-ribbon-hash-cursor-p n b3))
            (and (equal (fn2-b3-counter 0 b3) 0) (equal (fn2-b3-blocks 0 b3) 0)
                 (equal (fn2-b3-pos 0 b3) n)))
   :hints (("Goal" :cases ((equal (fn2-b3-counter 0 b3) 0) (equal (fn2-b3-blocks 0 b3) 0))
            :in-theory (e/d (fn2-ribbon-hash-cursor-p)
                  (fn2-b3-counter fn2-b3-blocks fn2-b3-pos fn2-b3-verify-phase fn2-b3-origin fn2-b3-flags fn2-b3-depth))))))

(local
 (defthmd fn2-run-hash-prefix-stored-byte
   (let ((after (fn2-b3-set-pos 0 (1+ n) (fn2-b3-store 0 i word b3))))
     (implies (and (natp n) (< n 20) (fn2-ribbon-hash-cursor-p n b3))
              (fn2-ribbon-hash-cursor-p (1+ n) after)))
   :hints (("Goal" :use fn2-run-hash-prefix-byte-count
            :in-theory (e/d (fn2-ribbon-hash-cursor-p fn2-b3-store fn2-b3-set-pos update-fn2-b3-wordsi update-fn2-b3-pos$ai
                             fn2-b3-pos fn2-b3-blocks fn2-b3-counter fn2-b3-depth fn2-b3-flags fn2-b3-origin fn2-b3-verify-phase
                             nth-update-nth)
                            (nth update-nth))))))

(local
 (defthm fn2-run-domain-byte-advances-hash
   (implies (and (natp n) (< n 20) (fn2-ribbon-hash-cursor-p n b3))
            (fn2-ribbon-hash-cursor-p (1+ n) (mv-nth 1 (fn2-b3-byte 0 byte ds b3))))
   :hints (("Goal" :use (fn2-run-hash-prefix-byte-count)
            :in-theory (e/d (fn2-b3-byte fn2-run-hash-prefix-stored-byte)
                        (fn2-b3-pos fn2-b3-word fn2-b3-flush fn2-b3-set-pos fn2-b3-store fn-b3-word fn2-ribbon-hash-cursor-p))))))

(defmacro fn2-run-page-domain-ready-p (pos pad fc b3)
  `(and (equal (fn2-fc-phase 0 ,fc) *fn2-fc-phase-prefix*) (equal (fn2-fc-pos 0 ,fc) ,pos)
        (natp ,pos) (<= ,pos 20) (equal (fn2-fc-pad 0 ,fc) ,pad) (posp ,pad) (<= ,pad 2048)
        (equal (fn2-fc-pad-end 0 ,fc) 65536) (fn2-ribbon-hash-cursor-p ,pos ,b3)))

(defmacro fn2-run-page-domain-advance (fuel)
  `(fn2-fc-advance ,fuel 0 :page t slot gen 0 65536 base pk ps pg fc ctx b3 f pool ds))

(local
 (defthm fn2-run-page-domain-moves-offset
   (let ((after (fn2-fc-set-pos 0 next fc)))
     (and (equal (fn2-fc-phase 0 after) (fn2-fc-phase 0 fc)) (equal (fn2-fc-pos 0 after) next)
          (equal (fn2-fc-pad 0 after) (fn2-fc-pad 0 fc)) (equal (fn2-fc-pad-end 0 after) (fn2-fc-pad-end 0 fc))))
   :hints (("Goal" :in-theory (e/d (fn2-fc-set-pos fn2-fc-phase fn2-fc-pos fn2-fc-pad fn2-fc-pad-end update-fn2-fc-pos$ai
                                  nth-update-nth) (nth update-nth))))))

(local
 (defthm fn2-run-page-domain-selects-phase
   (let ((after (fn2-fc-set-phase 0 next fc)))
     (and (equal (fn2-fc-phase 0 after) next) (equal (fn2-fc-pos 0 after) (fn2-fc-pos 0 fc))
          (equal (fn2-fc-pad 0 after) (fn2-fc-pad 0 fc)) (equal (fn2-fc-pad-end 0 after) (fn2-fc-pad-end 0 fc))))
   :hints (("Goal" :in-theory (e/d (fn2-fc-set-phase fn2-fc-phase fn2-fc-pos fn2-fc-pad fn2-fc-pad-end update-fn2-fc-phase$ai
                                  nth-update-nth) (nth update-nth))))))

(local
 (defthmd fn2-run-page-domain-advances
   (let ((a (fn2-run-page-domain-advance fuel)))
     (implies (and (fn2-run-page-domain-ready-p pos pad fc b3) (< pos 20))
              (and (equal (car a) :more) (equal (mv-nth 1 a) 1) (equal (mv-nth 4 a) pool)
                   (fn2-run-page-domain-ready-p (1+ pos) pad (mv-nth 2 a) (mv-nth 3 a)))))
   :hints (("Goal" :do-not '(preprocess)
            :use ((:instance fn2-run-domain-byte-advances-hash (n pos) (byte (fn2-fc-prefix-byte 0 :page pos ctx))))
            :in-theory (e/d (fn2-fc-advance fn2-fc-byte fn2-fc-domain)
                       (fn2-fc-prefix-byte fn2-b3-byte fn2-fc-set-pos fn2-fc-set-phase fn2-fc-phase fn2-fc-pos
                        fn2-fc-pad fn2-fc-pad-end fn2-b3-finalize fn2-fc-page-span fn2-ribbon-hash-cursor-p))))))

(local
 (defthmd fn2-run-page-domain-completes
   (let ((a (fn2-run-page-domain-advance fuel)))
     (implies (and (fn2-run-page-domain-ready-p 20 pad fc b3) (fn2-run-filled-page-p slot gen pk ps pg pool)
                   (fn2-ribbon-zero-region-p (- 65536 pad) pad slot gen pool))
              (and (equal (car a) :more) (equal (mv-nth 1 a) 1) (equal (mv-nth 4 a) pool)
                   (equal (fn2-fc-pos 0 (mv-nth 2 a)) 0) (equal (fn2-fc-pad 0 (mv-nth 2 a)) pad)
                   (fn2-run-hash-page-input-p slot gen pk ps pg (mv-nth 2 a) (mv-nth 3 a) pool))))
   :hints (("Goal" :do-not '(preprocess)
            :in-theory (e/d (fn2-fc-advance fn2-fc-byte fn2-fc-domain fn2-run-hash-page-input-p)
                       (fn2-fc-prefix-byte fn2-b3-byte fn2-fc-set-pos fn2-fc-set-phase fn2-fc-phase fn2-fc-pos
                        fn2-fc-pad fn2-fc-pad-end fn2-b3-finalize fn2-fc-page-span fn2-ribbon-hash-cursor-p
                        fn2-layout-range-code fn2-pool-base fn2-ribbon-zero-region-p))))))

(local
 (defthmd fn2-run-first-span-fits-after-domain
   (implies (and (posp pad) (<= pad 2048))
            (equal (fn2-fc-span-size 4075 0 pad 65536 used) (fn2-fc-span-size 4096 0 pad 65536 used)))
   :hints (("Goal" :in-theory (e/d (fn2-fc-span-size) (fn2-fc-aligned-count))))))

(local
 (defthmd fn2-run-first-span-ignores-spent-domain-fuel
   (implies (and (equal (fn2-fc-pos 0 fc) 0) (posp (fn2-fc-pad 0 fc)) (<= (fn2-fc-pad 0 fc) 2048))
            (equal (fn2-fc-page-span 4075 0 slot gen 0 65536 base pk ps pg fc ctx b3 f pool ds)
                   (fn2-fc-page-span 4096 0 slot gen 0 65536 base pk ps pg fc ctx b3 f pool ds)))
   :hints (("Goal" :in-theory (e/d (fn2-fc-page-span fn2-run-first-span-fits-after-domain)
                       (fn2-fc-span-size fn2-b3-update fn2-fc-pad fn2-fc-pad-end fn2-fc-pos fn2-b3-blocks fn2-b3-pos
                        fn2-fc-set-pos fn2-fc-zero-prefix fn2-pool-slot-base fn2-layout-range-code fn2-pool-data-length fn2-pool-rows))))))

(defmacro fn2-run-domain-page-bytes (fuel)
  `(fn2-fc-run-bytes ,fuel 0 :page t slot gen 0 65536 base pk ps pg fc ctx b3 f pool ds))

(local
 (defthmd fn2-run-first-span-equals-checker-step
   (let ((r (fn2-run-domain-page-bytes 4075)) (check (fn2-run-check-page-hash))
         (s (fn2-fc-page-span 4096 0 slot gen 0 65536 base pk ps pg fc ctx b3 f pool ds)))
     (implies (and (equal (fn2-fc-phase 0 fc) *fn2-fc-phase-hash*) (equal (car s) :yield)
                   (equal (fn2-fc-pos 0 fc) 0) (posp (fn2-fc-pad 0 fc)) (<= (fn2-fc-pad 0 fc) 2048))
              (and (equal (car r) (car check)) (equal (mv-nth 1 r) (mv-nth 1 check))
                   (equal (mv-nth 2 r) (mv-nth 2 check)) (equal (mv-nth 3 r) (mv-nth 4 check)))))
   :hints (("Goal" :use fn2-run-first-span-ignores-spent-domain-fuel
            :expand ((fn2-run-domain-page-bytes 4075) (fn2-run-domain-page-bytes 4096))
            :in-theory (union-theories (theory 'minimal-theory)
                  '(fn2-format-run fn2-fc-step fn2-fc-advance eq eql mv-nth car-cons cdr-cons
                    (:t fn2-fc-page-span) (:e mv-nth) (:e member-equal) (:e posp) (:e zp) (:e binary-+)
                    (:e unary--) (:e equal) (:e <)))))))

(local
 (defthmd fn2-run-first-span-after-domain
   (let ((r (fn2-run-domain-page-bytes 4075)))
     (implies (and (fn2-run-hash-page-input-p slot gen pk ps pg fc b3 pool) (equal (fn2-fc-pos 0 fc) 0)
                   (posp (fn2-fc-pad 0 fc)))
              (and (equal (car r) :more) (equal (mv-nth 3 r) pool)
                   (fn2-run-hash-page-input-p slot gen pk ps pg (mv-nth 1 r) (mv-nth 2 r) pool))))
   :hints (("Goal" :do-not '(preprocess)
            :use (fn2-run-valid-hash-step-continues fn2-run-first-span-equals-checker-step fn2-run-hash-page-accepts-next-span
                  (:instance fn2-fc-span-size-bounds (fuel 4096) (pos 0) (pad (fn2-fc-pad 0 fc))
                             (end 65536) (used (fn2-run-hash-used 0 b3))))
            :in-theory (union-theories (theory 'minimal-theory)
                        '(fn2-run-hash-page-input-p natp posp not (:e zp) (:e <) (:e equal) (:e natp)
                          (:e binary-+) |(+ 0 x)|))))))

(local
 (defthmd fn2-run-domain-spends-one-byte
   (let* ((a (fn2-run-page-domain-advance fuel)) (r (fn2-run-domain-page-bytes fuel)))
     (implies (and (posp fuel) (equal (car a) :more) (equal (mv-nth 1 a) 1) (equal (mv-nth 4 a) pool))
              (equal r (fn2-fc-run-bytes (1- fuel) 0 :page t slot gen 0 65536 base pk ps pg
                             (mv-nth 2 a) ctx (mv-nth 3 a) f pool (mv-nth 5 a)))))
   :hints (("Goal" :expand ((fn2-run-domain-page-bytes fuel))
            :in-theory (union-theories (theory 'minimal-theory)
                      '(commutativity-of-+ mv-nth car-cons cdr-cons eq eql posp natp zp (:t fn2-fc-advance) (:e <) (:e posp) (:e zp)
                        (:e mv-nth) (:e binary-+) (:e unary--) (:e equal)))))))

(local
 (defun-nx fn2-run-domain-byte-walk (pos slot gen base pk ps pg fc ctx b3 f pool ds)
   (declare (xargs :measure (nfix (- 20 pos))))
   (if (or (not (natp pos)) (<= 20 pos)) (list fc b3 ds)
     (let ((a (fn2-run-page-domain-advance (- 4096 pos))))
       (fn2-run-domain-byte-walk (1+ pos) slot gen base pk ps pg (mv-nth 2 a) ctx (mv-nth 3 a) f pool (mv-nth 5 a))))))

(local
 (defthmd fn2-run-twentieth-domain-byte-starts-span
   (let ((r (fn2-run-domain-page-bytes 4076)))
     (implies (and (fn2-run-page-domain-ready-p 20 pad fc b3) (fn2-run-filled-page-p slot gen pk ps pg pool)
                   (fn2-ribbon-zero-region-p (- 65536 pad) pad slot gen pool))
              (and (equal (car r) :more) (equal (mv-nth 3 r) pool)
                   (fn2-run-hash-page-input-p slot gen pk ps pg (mv-nth 1 r) (mv-nth 2 r) pool))))
   :hints (("Goal" :do-not '(preprocess)
            :use ((:instance fn2-run-page-domain-completes (fuel 4076))
                  (:instance fn2-run-domain-spends-one-byte (fuel 4076))
                  (:instance fn2-run-first-span-after-domain (fc (mv-nth 2 (fn2-run-page-domain-advance 4076)))
                             (b3 (mv-nth 3 (fn2-run-page-domain-advance 4076))) (ds (mv-nth 5 (fn2-run-page-domain-advance 4076)))))
            :in-theory (union-theories (theory 'minimal-theory) '((:e posp) (:e equal) (:e binary-+) (:e unary--)))))))

(local
 (defthmd fn2-run-domain-and-first-span-complete
   (let ((r (fn2-run-domain-page-bytes (- 4096 pos))))
     (implies (and (fn2-run-page-domain-ready-p pos pad fc b3) (fn2-run-filled-page-p slot gen pk ps pg pool)
                   (fn2-ribbon-zero-region-p (- 65536 pad) pad slot gen pool))
              (and (equal (car r) :more) (equal (mv-nth 3 r) pool)
                   (fn2-run-hash-page-input-p slot gen pk ps pg (mv-nth 1 r) (mv-nth 2 r) pool))))
   :hints (("Goal" :induct (fn2-run-domain-byte-walk pos slot gen base pk ps pg fc ctx b3 f pool ds)
            :do-not '(preprocess)
            :in-theory (union-theories (theory 'minimal-theory)
                        '((:i fn2-run-domain-byte-walk) posp natp not |(- (+ x y))| |(+ c (+ d x))|
                          (:e equal) (:e posp) (:e natp) (:e binary-+) (:e unary--) (:e <))))
           ("Subgoal *1/1" :use fn2-run-twentieth-domain-byte-starts-span)
           ("Subgoal *1/2" :use ((:instance fn2-run-domain-spends-one-byte (fuel (- 4096 pos)))
                              (:instance fn2-run-page-domain-advances (fuel (- 4096 pos))))))))

(defthmd fn2-run-checker-hashes-domain-and-page
  (let ((check (fn2-run-check-page-hash)))
    (implies (and (fn2-run-page-domain-ready-p 0 pad fc b3) (fn2-run-filled-page-p slot gen pk ps pg pool)
                  (fn2-ribbon-zero-region-p (- 65536 pad) pad slot gen pool))
             (and (equal (car check) :more) (equal (mv-nth 3 check) f) (equal (mv-nth 4 check) pool)
                  (fn2-run-hash-page-input-p slot gen pk ps pg (mv-nth 1 check) (mv-nth 2 check) pool))))
  :hints (("Goal" :do-not '(preprocess) :use ((:instance fn2-run-domain-and-first-span-complete (pos 0)))
           :in-theory (union-theories (theory 'minimal-theory)
                     '(fn2-format-run fn2-fc-step eq eql mv-nth car-cons cdr-cons (:t fn2-fc-run-bytes)
                       (:e mv-nth) (:e member-equal) (:e posp) (:e zp) (:e equal) (:e <) (:e natp)
                       (:e binary-+) (:e unary--))))))
