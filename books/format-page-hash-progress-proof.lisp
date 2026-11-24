(in-package "ACL2")
(include-book "format-page-hash-update-proof")

(local (in-theory (current-theory 'fc-u32-reconstruct)))

(local
 (defthm fn2-page-rejoin-partial-span
   (implies (and (natp k) (natp n) (<= k n) (true-listp xs))
            (equal (append (fn-b3-nthcdrx k (fn-b3-firstn n xs)) (fn-b3-nthcdrx n xs))
                   (fn-b3-nthcdrx k xs)))
   :hints (("Goal" :use ((:instance fn2-b3-cut-rejoin (n (- n k)) (xs (fn-b3-nthcdrx k xs)))
                         (:instance fn2-b3-drop-twice (a k) (b (- n k)))
                         (:instance fn2-b3-drop-of-first (a k) (b n)))
            :in-theory (disable fn2-b3-drop-true-list)))))

(defthmd fn2-page-update-advances-hash
  (let* ((step (fn2-b3-update 0 0 1 pos n 9 0 1 ds b3 pool))
         (k (mv-nth 1 step)))
    (implies (and (fn2-hash-page-windowp pool) (natp pos) (natp n)
                  (<= n 4096) (<= n (len xs)) (<= (+ pos n) 65536)
                  (fn-b3-octet-listp xs) (fn2-b3-covers xs pos pool)
                  (fc-g xs ans ds b3))
             (and (natp k) (<= k n)
                  (fc-g (fn-b3-nthcdrx k xs) ans (mv-nth 2 step) (mv-nth 3 step)))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn2-page-update-consumes-octets (bytes (fn-b3-firstn n xs))
                            (rest (fn-b3-nthcdrx n xs)) (off pos))
                 (:instance fn2-b3-cut-rejoin))
           :in-theory (e/d (fn2-page-rejoin-partial-span min)
                           (fn2-b3-cut-rejoin mv-nth fn2-b3-drop-of-first)))))

(defun-nx fn2-page-hash-count (fuel fc b3 pool)
  (let* ((pos (fn2-fc-pos 0 fc)) (pad (fn2-fc-pad 0 fc))
         (limit (fn2-fc-span-size fuel pos pad 65536 (+ (* 64 (fn2-b3-blocks 0 b3)) (fn2-b3-pos 0 b3)))))
    (if (< pos pad) limit
      (fn2-fc-zero-prefix (+ (nfix (fn2-pool-slot-base 0 pool)) pos) limit pool))))

(defthmd fn2-page-hash-count-bounded
  (let ((pos (fn2-fc-pos 0 fc)) (n (fn2-page-hash-count fuel fc b3 pool)))
    (implies (and (natp fuel) (natp pos) (<= pos 65536) (natp (fn2-fc-pad 0 fc)))
             (and (natp n) (<= n 4096) (<= (+ pos n) 65536))))
  :hints (("Goal" :in-theory (e/d (fn2-page-hash-count fn2-fc-span-size-bounds fn2-fc-zero-prefix-bound
                                    fn2-fc-span-size-natural fn2-fc-zero-prefix-natural)
                                   (fn2-fc-span-size fn2-fc-zero-prefix fn2-fc-pos fn2-fc-pad)))))

(defmacro fn2-page-hash-span-call ()
 '(fn2-fc-page-span fuel 0 0 1 0 65536 0 9 0 1 fc ctx b3 f pool ds))

(defmacro fn2-page-hash-update-call ()
 '(fn2-b3-update 0 0 1 (fn2-fc-pos 0 fc) (fn2-page-hash-count fuel fc b3 pool) 9 0 1 ds b3 pool))

(local
 (defthm fn2-page-span-state-bytes
   (let ((step (fn2-page-hash-span-call)) (update (fn2-page-hash-update-call)) (pos (fn2-fc-pos 0 fc)))
     (implies (natp pos)
       (or (and (equal (mv-nth 1 step) 0) (equal (mv-nth 2 step) fc)
                (equal (mv-nth 3 step) b3) (equal (mv-nth 4 step) ds))
           (and (equal (mv-nth 1 step) (mv-nth 1 update))
                (equal (fn2-fc-pos 0 (mv-nth 2 step)) (+ pos (mv-nth 1 step)))
                (equal (mv-nth 3 step) (mv-nth 3 update)) (equal (mv-nth 4 step) (mv-nth 2 update))))))
   :rule-classes nil
   :hints (("Goal" :in-theory (e/d (fn2-fc-page-span fn2-page-hash-count fc-phase-pos-updates)
                                   (fn2-fc-pos fn2-fc-pad fn2-fc-set-pos fn2-b3-update fn2-fc-span-size
                                    fn2-fc-zero-prefix fn2-fc-pad-end fn2-layout-range-code mv-nth))))))

(defthm fn2-page-span-advances-hash
  (let* ((step (fn2-page-hash-span-call)) (pos (fn2-fc-pos 0 fc)) (k (mv-nth 1 step)))
    (implies (and (fn2-hash-page-windowp pool) (natp pos) (<= pos 65536)
                  (natp fuel) (natp (fn2-fc-pad 0 fc))
                  (fn-b3-octet-listp xs) (equal (len xs) (- 65536 pos))
                  (fn2-b3-covers xs pos pool) (fc-g xs ans ds b3))
             (and (natp k) (<= k (len xs))
                  (equal (fn2-fc-pos 0 (mv-nth 2 step)) (+ pos k))
                  (fc-g (fn-b3-nthcdrx k xs) ans (mv-nth 4 step) (mv-nth 3 step)))))
  :rule-classes nil
  :hints (("Goal" :use (fn2-page-span-state-bytes fn2-page-hash-count-bounded
                        (:instance fn2-page-update-advances-hash (pos (fn2-fc-pos 0 fc))
                                   (n (fn2-page-hash-count fuel fc b3 pool))))
           :in-theory (union-theories (theory 'minimal-theory)
                       '(natp (:e integerp) (:e binary-+) (:e <) (:e equal) (:e not)
                         fn2-b3-drop-zero commutativity-of-+ fc-zero-plus-len)))))
