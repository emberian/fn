; The promoted page's digest reference points at the 32 bytes supplied
; by the child writer's digest row.
(in-package "ACL2")
(include-book "page-parent-octets")
(include-book "runs-load-frame-proof")
(local (include-book "arithmetic-3/floor-mod/floor-mod" :dir :system))

(local
 (defthm fn2-run-parent-octet-shape
   (let ((bytes (fn2-page-parent-octets k n words)))
     (and (fn-b3-octet-listp bytes) (equal (true-list-fix bytes) bytes) (equal (len bytes) (nfix n))))
   :hints (("Goal" :induct (fn2-page-parent-octets k n words)
            :in-theory (e/d (fn2-page-parent-octets) (fn2-fc-word-byte floor mod nth))))))

(local
 (defthm fn2-run-store-parent-bytes
   (implies (and (natp left) (<= left 32) (natp off))
            (equal (fn2-digest-store left row slot gen off pk ps pg ds pool)
                   (fn2-run-load-bytes (fn2-page-parent-octets (- 32 left) left (fn2-digest-list row ds))
                      slot gen (+ off (- 32 left)) pk ps pg pool)))
   :hints (("Goal" :do-not '(preprocess) :induct (fn2-digest-store left row slot gen off pk ps pg ds pool)
            :expand ((:free (k words) (fn2-page-parent-octets k left words))
                     (:free (i) (fn2-run-load-bytes nil slot gen i pk ps pg pool))
                     (:free (x xs i) (fn2-run-load-bytes (cons x xs) slot gen i pk ps pg pool)))
            :in-theory (e/d (fn2-digest-store fn2-page-parent-word-from-list)
                          (fn2-pool-write fn2-digest-word fn2-digest-list fn2-fc-word-byte fn2-page-parent-octets
                           (:definition fn2-run-load-bytes) nth mod floor))))))

(defthmd fn2-run-child-digest-occupies-slot
  (let* ((bytes (fn2-page-parent-octets 0 32 (fn2-digest-list row ds)))
         (store (fn2-digest-store 32 row slot gen off pk ps pg ds pool)) (after (mv-nth 1 store)))
    (implies (and (natp off) (natp (fn2-pool-base slot pool))
                  (equal (fn2-layout-range-code slot gen off (+ off 32) t pk ps pg pool) :ok))
             (and (equal store (fn2-run-load-bytes bytes slot gen off pk ps pg pool))
                  (equal (car store) :ok)
                  (equal (fn2-run-read-bytes 32 slot gen off pk ps pg after) bytes))))
  :hints (("Goal" :use ((:instance fn2-run-store-parent-bytes (left 32))
                       (:instance fn2-run-load-bytes-roundtrip (bytes (fn2-page-parent-octets 0 32 (fn2-digest-list row ds))) (cap (+ off 32))))
           :in-theory (disable fn2-run-store-parent-bytes fn2-digest-store fn2-page-parent-octets fn2-digest-list
                               fn2-run-load-bytes fn2-run-read-bytes fn-b3-octet-listp fn2-pool-base fn2-layout-range-code true-list-fix))))
