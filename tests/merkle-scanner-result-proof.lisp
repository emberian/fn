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
 ; MV-LET consumers project with CAR after translation. Retain the original
; MV-NTH statement and supply its exact projection corollary for those callers.
(defthm fn2-b3-feed-car-never-scanner-done
 (not (equal (car (fn2-b3-feed row slot gen off left consumed okind oslot ogen
                   fn2-digests fn2-b3 fn2-pool)) :done))
 :hints (("Goal" :use fn2-b3-feed-never-scanner-done
          :in-theory (e/d (mv-nth) (fn2-b3-feed-never-scanner-done)))))
 ; The result-code boundary does not inspect the fragment's numeric layout.
; Keep the real update operation's buffer/count terms opaque in this proof.
(defthm fn2-b3-update-car-never-scanner-done
 (not (equal (car (fn2-b3-update row slot gen off len okind oslot ogen
                   fn2-digests fn2-b3 fn2-pool)) :done))
 :hints (("Goal" :in-theory
  (e/d (fn2-b3-update)
       (fn2-b3-fragment-count fn2-b3-fragment-into fn2-pool-slot-base min)))))
(defthm fn2-mk-leaf-never-scanner-done
 (not (equal (mv-nth 0 (fn2-mk-leaf slot gen off len okind oslot ogen row fn2-digests fn2-b3 fn2-pool)) :done))
 :hints (("Goal" :in-theory (e/d (fn2-mk-leaf) (fn2-b3-counter fn2-b3-blocks fn2-b3-pos)))))
(defthm fn2-mk-append-never-scanner-done
 (not (equal (mv-nth 0 (fn2-mk-append row leaf fn2-digests fn2-mk)) :done))
 :hints (("Goal" :in-theory (enable fn2-mk-append))))
