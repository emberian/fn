; Hash progress across bulk reads, byte fallback, and yields.
(in-package "ACL2")
(include-book "format-page-hash-state-proof")

(local (in-theory (current-theory 'fc-u32-reconstruct)))

(defthmd fn2-page-span-frames
  (let ((r (fn2-page-hash-span-call)))
    (and (not (eq (car r) :ok))
         (equal (fn2-fc-phase 0 (mv-nth 2 r)) (fn2-fc-phase 0 fc))))
  :hints (("Goal" :in-theory (e/d (fn2-fc-page-span fc-phase-pos-updates)
                                 (fn2-b3-update fn2-fc-pos fn2-fc-pad fn2-fc-pad-end fn2-fc-phase
                                  fn2-fc-set-pos fn2-layout-range-code fn2-fc-span-size mv-nth)))))

(defthmd fn2-page-span-keeps-state
  (let ((r (fn2-page-hash-span-call)))
    (implies (and (equal (fn2-fc-phase 0 fc) *fn2-fc-phase-hash*) (natp fuel)
                  (fn2-page-hash-statep bytes ans fc ds b3)
                  (fn2-hash-page-windowp pool) (fn-b3-octet-listp bytes)
                  (equal (len bytes) 65536) (fn2-b3-covers bytes 0 pool))
             (fn2-page-hash-statep bytes ans (mv-nth 2 r) (mv-nth 4 r) (mv-nth 3 r))))
  :hints (("Goal" :do-not '(preprocess)
           :use ((:instance fn2-page-span-advances-hash (xs (fn-b3-nthcdrx (fn2-fc-pos 0 fc) bytes)))
                 (:instance fn2-b3-covers-drop (n (fn2-fc-pos 0 fc)) (off 0) (xs bytes) (fn2-pool pool))
                 (:instance fn2-b3-drop-twice (a (fn2-fc-pos 0 fc)) (b (mv-nth 1 (fn2-page-hash-span-call))) (xs bytes)))
           :in-theory (e/d (fn2-page-hash-statep fn2-page-span-frames fn2-b3-octets-drop fn-b3-len-of-nthcdrx)
                           (fn2-fc-phase fn2-fc-pos fn2-fc-page-span fn-b3-nthcdrx fc-g fn2-hash-page-windowp
                            fn2-b3-covers fn-b3-octet-listp len mv-nth)))))

(local
 (defthm fn2-page-check-byte-keeps-pool
   (equal (mv-nth 3 (fn2-page-check-call fn2-fc-byte)) pool)
   :hints (("Goal" :in-theory (e/d (fn2-fc-byte)
                                   (fn2-fc-phase fn2-fc-pos fn2-b3-byte fn2-b3-read fn2-fc-digest-byte
                                    fn2-fc-context-hash-word fn2-fc-check-byte mv-nth))))))

(defthmd fn2-page-check-advance-keeps-pool
  (equal (mv-nth 4 (fn2-page-check-call fn2-fc-advance fuel)) pool)
  :hints (("Goal" :in-theory (e/d (fn2-fc-advance fn2-page-check-byte-keeps-pool)
                                  (fn2-fc-byte fn2-fc-phase fn2-fc-page-span mv-nth)))))

(defthm fn2-page-hash-advance
  (implies (natp fuel) (fn2-page-hash-effect (fn2-page-check-call fn2-fc-advance fuel) 2 3 5))
  :rule-classes nil
  :hints (("Goal" :do-not '(preprocess) :cases ((equal (fn2-fc-phase 0 fc) *fn2-fc-phase-hash*))
           :use (fn2-page-span-frames fn2-page-hash-one-byte fn2-page-span-keeps-state
                 (:instance fn2-page-hash-one-byte (fc (mv-nth 2 (fn2-page-hash-span-call)))
                            (b3 (mv-nth 3 (fn2-page-hash-span-call))) (ds (mv-nth 4 (fn2-page-hash-span-call)))))
           :in-theory (e/d (fn2-fc-advance fc-mv-zero fc-mv-cons)
                           (fn2-page-hash-statep fn2-fc-byte fn2-fc-phase fn2-fc-page-span
                            fn2-hash-page-windowp fn2-b3-covers mv-nth)))))

(defthm fn2-page-hash-run
  (implies (natp fuel) (fn2-page-hash-effect (fn2-page-check-call fn2-fc-run-bytes fuel) 1 2 4))
  :rule-classes nil
  :hints (("Goal" :induct (fn2-page-check-call fn2-fc-run-bytes fuel)
           :expand (fn2-page-check-call fn2-fc-run-bytes fuel)
           :in-theory (e/d ((:induction fn2-fc-run-bytes) fn2-page-check-advance-keeps-pool fc-mv-zero fc-mv-cons)
                           (fn2-page-hash-statep fn2-fc-advance fn2-b3-covers fn2-hash-page-windowp mv-nth)))
          ("Subgoal *1/3" :use fn2-page-hash-advance)
          ("Subgoal *1/2" :use fn2-page-hash-advance)
          ("Subgoal *1/1" :expand ((fn2-page-check-call fn2-fc-run-bytes 0)))))
