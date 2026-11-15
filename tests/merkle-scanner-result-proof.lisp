; Source-only result-domain leaves; ACL2 admission is unexecuted.
(in-package "ACL2")
(include-book "../books/merkle")
(defthm fn2-b3-feed-never-scanner-done
 (not (equal (mv-nth 0 (fn2-b3-feed row slot gen off left consumed okind oslot ogen
                       fn2-digests fn2-b3 fn2-pool)) :done))
 :hints (("Goal"
  :induct (fn2-b3-feed row slot gen off left consumed okind oslot ogen fn2-digests fn2-b3 fn2-pool)
  :in-theory (enable fn2-b3-feed fn2-b3-read fn2-pool-read
                     fn2-pool-readable-code fn2-pool-handle-code))))
(defthm fn2-mk-leaf-never-scanner-done
 (not (equal (mv-nth 0 (fn2-mk-leaf slot gen off len okind oslot ogen row fn2-digests fn2-b3 fn2-pool)) :done))
 :hints (("Goal" :in-theory (enable fn2-mk-leaf fn2-b3-update))))
(defthm fn2-mk-append-never-scanner-done
 (not (equal (mv-nth 0 (fn2-mk-append row leaf fn2-digests fn2-mk)) :done))
 :hints (("Goal" :in-theory (enable fn2-mk-append))))
