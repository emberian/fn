; A full BLAKE3 chunk may start anywhere on the physical page.
(in-package "ACL2")
(include-book "format-binds-b3-proof")

(local (in-theory (current-theory 'fn2-b3-good-span)))

(defthm fn2-page-good-span
 (implies (and (fn2-b3-good past (append chunk xs) root answer fn2-digests fn2-b3)
               (or (and (equal (fn2-b3-pos 0 fn2-b3) 64) (equal (fn2-b3-blocks 0 fn2-b3) 15))
                   (and (equal (fn2-b3-pos 0 fn2-b3) 0) (equal (fn2-b3-blocks 0 fn2-b3) 0)))
               (natp off) (fn2-b3-covers chunk off fn2-pool) (fn-b3-octet-listp chunk)
               (fn-b3-octet-listp xs) (or lastp (consp xs)) (equal (len chunk) 1024))
  (mv-let (dg b3) (fn2-b3-span 0 off (fn2-b3-next-counter 0 fn2-b3) lastp fn2-digests fn2-b3 fn2-pool)
   (fn2-b3-good (append past chunk) xs root answer dg b3)))
 :hints (("Goal" :use ((:instance fn2-b3-good-bulk (ctr (fn2-b3-counter 0 fn2-b3))) (:instance fn2-b3-consp-by-length (xs (append chunk xs))) (:instance fn2-b3-good-counter-bounded (xs (append chunk xs)))
                       (:instance fn2-b3-good-counter (xs (append chunk xs)))
                       (:instance fn2-b3-good-flush (xs (append chunk xs)))
                       (:instance fn2-b3-good-bulk (ctr (1+ (fn2-b3-counter 0 fn2-b3)))
                          (fn2-digests (mv-nth 0 (fn2-b3-flush 0 fn2-digests fn2-b3)))
                          (fn2-b3 (mv-nth 1 (fn2-b3-flush 0 fn2-digests fn2-b3)))))
          :do-not-induct t
          :in-theory (enable fn2-b3-span fn2-b3-next-counter))))

(local (in-theory (current-theory 'fc-g-span)))

(defthm fn2-page-span-consumes-chunk
  (implies (and (fc-g (append bytes rest) ans ds b3)
                (fn2-b3-covers bytes off pool) (fn-b3-octet-listp bytes) (fn-b3-octet-listp rest) (natp off)
                (<= 1024 (len bytes)) (fn2-b3-can-span 0 0 1 off (len bytes) consumed 9 0 1 b3 pool))
   (mv-let (dg b3) (fn2-b3-span 0 off (fn2-b3-next-counter 0 b3) (< (len bytes) 2048) ds b3 pool)
    (fc-g (append (fn-b3-nthcdrx 1024 bytes) rest) ans dg b3)))
  :hints (("Goal" :use ((:instance fn2-page-good-span (chunk (fn-b3-firstn 1024 bytes))
                 (past (fc-g-witness (append bytes rest) ans ds b3)) (root t) (answer ans)
                 (fn2-digests ds) (fn2-b3 b3) (fn2-pool pool)
                 (xs (append (fn-b3-nthcdrx 1024 bytes) rest))
                 (lastp (< (len bytes) 2048)))
             (:instance fn2-b3-consp-by-length (xs (append (fn-b3-nthcdrx 1024 bytes) rest)))
             (:instance fc-g-suff (xs (append (fn-b3-nthcdrx 1024 bytes) rest))
                (past (append (fc-g-witness (append bytes rest) ans ds b3) (fn-b3-firstn 1024 bytes)))
                (ds (mv-nth 0 (fn2-b3-span 0 off (fn2-b3-next-counter 0 b3) (< (len bytes) 2048) ds b3 pool)))
                (b3 (mv-nth 1 (fn2-b3-span 0 off (fn2-b3-next-counter 0 b3) (< (len bytes) 2048) ds b3 pool)))))
           :expand ((fc-g (append bytes rest) ans ds b3))
           :do-not-induct t :in-theory (e/d (min fn2-b3-can-span) (fn2-page-good-span fn2-b3-pos fn2-b3-blocks fn2-layout-range-code)))))
