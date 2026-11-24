(in-package "ACL2")
(include-book "runs-page-copy-proof")

(defthmd fn2-run-fixed-writes-layout-octets
  (let* ((bytes (fn2-layout-le n v))
         (load (fn2-run-load-bytes bytes slot gen off pk ps pg pool))
         (write (fn2-codec-emit-fixed n v slot gen off pk ps pg pool)))
    (implies (and (natp v) (natp off))
             (and (equal (car write) (car load))
                  (equal (mv-nth 2 write) (mv-nth 1 load))
                  (implies (eq (car load) :ok)
                           (equal (mv-nth 1 write) (+ off (nfix n)))))))
  :hints (("Goal" :induct (fn2-codec-emit-fixed n v slot gen off pk ps pg pool)
           :expand ((fn2-layout-le n v))
           :in-theory (e/d (fn2-codec-emit-fixed fn2-run-load-bytes)
                           (fn2-pool-write fn2-layout-le mod floor)))))

(defthm fn2-run-le-word-octets
   (implies (natp v)
            (and (fn-b3-octet-listp (fn2-layout-le n v))
                 (equal (true-list-fix (fn2-layout-le n v)) (fn2-layout-le n v))
                 (equal (len (fn2-layout-le n v)) (nfix n))))
   :hints (("Goal" :induct (fn2-layout-le n v)
            :in-theory (enable fn2-layout-le))))

(defthmd fn2-run-restart-encode-stores-offset
  (let* ((v (fn2-fields-value base f))
         (write (fn2-run-restart-encode base slot gen off pk ps pg f pool))
         (load (fn2-run-load-bytes (fn2-layout-le 4 v) slot gen off pk ps pg pool)))
    (implies (and (natp base) (unsigned-byte-p 32 v) (unsigned-byte-p 32 off)
                  (natp (fn2-pool-base slot pool))
                  (equal (fn2-layout-range-code slot gen off (+ off 4) t pk ps pg pool) :ok))
             (equal write (list :ok (+ off 4) (mv-nth 1 load)))))
  :hints (("Goal" :use ((:instance fn2-run-fixed-writes-layout-octets (n 4) (v (fn2-fields-value base f)))
                        (:instance fn2-run-load-bytes-roundtrip (bytes (fn2-layout-le 4 (fn2-fields-value base f)))
                                   (cap (+ off 4))))
           :in-theory (e/d (fn2-run-restart-encode fn2-run-restart-size fn2-run-restart-size-offset fn2-run-restart-check-values
                            fn2-run-restart-check-offset fn2-run-restart-emit-offset)
                           (fn2-codec-emit-fixed fn2-run-load-bytes fn2-layout-le fn2-layout-range-code
                            fn2-fields-value fn2-run-read-bytes fn2-pool-base)))))
