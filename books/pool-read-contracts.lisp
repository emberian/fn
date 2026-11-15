; Output typing for the actual checked pool reader.
(in-package "ACL2")
(include-book "pool")
(fn2-book-layer :b)
(defthm fn2-pool-read-byte-type
 (implies (and (fn2-poolp fn2-pool) (fn2-pool-wfp fn2-pool))
  (unsigned-byte-p 8 (mv-nth 1 (fn2-pool-read slot gen idx okind oslot ogen fn2-pool))))
 :hints (("Goal" :in-theory (enable fn2-pool-read))))
