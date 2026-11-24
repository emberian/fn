; Loading a source line, then appending its encoding, extends the readable
; arena prefix and leaves both workspaces writable at their new fills.
(in-package "ACL2")
(include-book "runs-page-copy-proof")
(include-book "runs-restart-lookup-proof")

(local
 (defthm fn2-ov-octets-fix
   (implies (fn-b3-octet-listp xs) (equal (true-list-fix xs) xs))))

(defthmd fn2-ov-appended-pool-windows
  (let* ((a (+ at (len line))) (b (+ off (len bytes)))
         (q (mv-nth 1 (fn2-run-load-bytes line src sg at 9 0 1 pool)))
         (p (mv-nth 1 (fn2-run-load-bytes bytes dst dg off 9 0 1 q))))
    (implies (and (natp src) (natp dst) (not (equal src dst))
                  (natp (fn2-pool-base src pool)) (natp (fn2-pool-base dst pool))
                  (natp at) (natp off) (<= a 65536) (<= b 65536)
                  (fn-b3-octet-listp line) (fn-b3-octet-listp bytes)
                  (equal (fn2-layout-range-code src sg at 65536 t 9 0 1 pool) :ok)
                  (equal (fn2-layout-range-code dst dg off 65536 t 9 0 1 pool) :ok))
             (and (equal (fn2-layout-range-code src sg a 65536 t 9 0 1 p) :ok)
                  (equal (fn2-layout-range-code dst dg b 65536 t 9 0 1 p) :ok)
                  (equal (fn2-layout-range-code dst dg 0 b nil 9 0 1 p) :ok)
                  (equal (fn2-run-read-bytes (len bytes) dst dg off 9 0 1 p) bytes))))
  :hints (("Goal" :do-not '(preprocess)
           :use ((:instance fn2-run-load-bytes-roundtrip (bytes line) (slot src) (gen sg) (off at) (cap 65536) (pk 9) (ps 0) (pg 1))
                 (:instance fn2-run-load-bytes-roundtrip (slot dst) (gen dg) (cap 65536) (pk 9) (ps 0) (pg 1)
                       (pool (mv-nth 1 (fn2-run-load-bytes line src sg at 9 0 1 pool)))))
           :in-theory (disable fn2-run-load-bytes fn2-run-read-bytes fn2-layout-range-code
                       fn2-pool-base fn-b3-octet-listp true-list-fix len))))

(defthmd fn2-ov-complete-appended-pool-bytes
  (let* ((a (+ at (len line))) (b (+ off (len bytes)))
         (q (mv-nth 1 (fn2-run-load-bytes line src sg at 9 0 1 pool)))
         (p (mv-nth 1 (fn2-run-load-bytes bytes dst dg off 9 0 1 q))))
    (implies (and (natp src) (natp dst) (not (equal src dst))
                  (natp (fn2-pool-base src pool)) (natp (fn2-pool-base dst pool))
                  (<= (+ (fn2-pool-base dst pool) 65536) (fn2-pool-base src pool))
                  (natp at) (natp off) (<= a 65536) (<= b 65536)
                  (fn-b3-octet-listp line) (fn-b3-octet-listp bytes)
                  (equal (fn2-layout-range-code src sg at 65536 t 9 0 1 pool) :ok)
                  (equal (fn2-layout-range-code dst dg off 65536 t 9 0 1 pool) :ok))
             (equal (fn2-run-read-bytes b dst dg 0 9 0 1 p)
                    (append (fn2-run-read-bytes off dst dg 0 9 0 1 pool) bytes))))
  :hints (("Goal" :do-not '(preprocess)
           :use (fn2-ov-appended-pool-windows
                 (:instance fn2-run-read-prefix (slot dst) (gen dg) (n off) (m (len bytes)) (at 0) (pk 9) (ps 0) (pg 1)
                     (pool (mv-nth 1 (fn2-run-load-bytes bytes dst dg off 9 0 1
                                      (mv-nth 1 (fn2-run-load-bytes line src sg at 9 0 1 pool))))))
                 (:instance fn2-run-load-preserves-earlier-bytes (n off) (src dst) (sg dg) (at 0)
                     (pk 9) (ps 0) (pg 1) (pool (mv-nth 1 (fn2-run-load-bytes line src sg at 9 0 1 pool))))
                 (:instance fn2-run-load-preserves-earlier-bytes (n off) (src dst) (sg dg) (at 0) (dst src)
                     (dg sg) (off at) (bytes line) (pk 9) (ps 0) (pg 1)))
           :in-theory (disable fn2-run-load-preserves-earlier-bytes fn2-run-read-bytes fn2-run-load-bytes
                       fn2-layout-range-code fn2-pool-base fn-b3-octet-listp true-list-fix binary-append len))))
