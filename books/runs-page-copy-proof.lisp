; Copying a payload after a variable-length header writes the complete byte sequence.
(in-package "ACL2")
(include-book "runs-load-bytes-proof")

(defthmd fn2-run-load-byte-segments
  (let ((head (fn2-run-load-bytes a slot gen off pk ps pg pool)))
    (implies (natp off)
             (equal (fn2-run-load-bytes (append a b) slot gen off pk ps pg pool)
                    (if (eq (car head) :ok)
                        (fn2-run-load-bytes b slot gen (+ off (len a)) pk ps pg (mv-nth 1 head))
                      head))))
  :hints (("Goal" :induct (fn2-run-load-bytes a slot gen off pk ps pg pool)
           :in-theory (e/d (fn2-run-load-bytes) (fn2-pool-write)))))

(local
 (defthm fn2-run-read-across-other-write
  (implies (and (natp src) (natp dst) (not (equal src dst))
                (natp (fn2-pool-base src pool)) (natp (fn2-pool-base dst pool))
                (natp at) (natp off)
                (not (equal (+ (fn2-pool-base src pool) at) (+ (fn2-pool-base dst pool) off))))
           (equal (fn2-pool-read src sg at pk ps pg
                                 (mv-nth 1 (fn2-pool-write dst dg off byte pk ps pg pool)))
                  (fn2-pool-read src sg at pk ps pg pool)))
  :hints (("Goal" :in-theory (e/d ( fn2-pool-write fn2-pool-read
                                     fn2-pool-readable-code fn2-pool-handle-code fn2-pool-ownerp
                                     fn2-pool-set-fill update-fn2-pool-fill$ai update-fn2-pool-datai nth-update-nth)
                           (nth update-nth unsigned-byte-p fn2-pool-workspace-code))))))

(local
 (defthm fn2-run-source-bytes-after-write
  (let ((start (+ (fn2-pool-base src pool) at))
        (target (+ (fn2-pool-base dst pool) off)))
    (implies (and (natp src) (natp dst) (not (equal src dst))
                  (natp (fn2-pool-base src pool)) (natp (fn2-pool-base dst pool))
                  (natp at) (natp off) (natp n)
                  (or (< target start) (<= (+ start n) target)))
             (equal (fn2-run-read-bytes n src sg at pk ps pg
                                        (mv-nth 1 (fn2-pool-write dst dg off byte pk ps pg pool)))
                    (fn2-run-read-bytes n src sg at pk ps pg pool))))
  :hints (("Goal" :induct (fn2-run-read-bytes n src sg at pk ps pg pool)
           :in-theory (e/d (fn2-run-read-bytes) (fn2-pool-write fn2-pool-read fn2-pool-base))))))

(local
 (defthm fn2-run-read-status-not-integer
  (let ((res (fn2-pool-read src sg at pk ps pg pool)))
    (not (integerp (car res))))
  :hints (("Goal" :in-theory (e/d (fn2-pool-read fn2-pool-readable-code fn2-pool-handle-code)
                                  (fn2-pool-ownerp fn2-pool-rows fn2-pool-base fn2-pool-fill
                                   fn2-pool-data-length fn2-pool-state fn2-pool-gen))))))

(local
 (defthm fn2-run-copy-writes-source-octets
  (let* ((source (+ (fn2-pool-base src pool) at)) (target (+ (fn2-pool-base dst pool) off))
         (bytes (fn2-run-read-bytes n src sg at pk ps pg pool)))
    (implies (and (natp src) (natp dst) (not (equal src dst))
                  (natp (fn2-pool-base src pool)) (natp (fn2-pool-base dst pool))
                  (natp at) (natp off) (natp n)
                  (or (<= (+ source n) target) (<= (+ target n) source))
                  (fn-b3-octet-listp bytes))
             (equal (fn2-layout-copy-loop src sg at dst dg off n pk ps pg pool)
                    (fn2-run-load-bytes bytes dst dg off pk ps pg pool))))
  :hints (("Goal" :induct (fn2-layout-copy-loop src sg at dst dg off n pk ps pg pool)
           :expand ((fn2-run-read-bytes n src sg at pk ps pg pool))
           :in-theory (e/d (fn2-layout-copy-loop fn2-run-load-bytes fn2-pool-write-keeps-extents)
                           (fn2-pool-write fn2-pool-read fn2-pool-base fn2-run-read-bytes unsigned-byte-p))))))

(local
 (defthm fn2-run-other-readable-range-after-write
  (implies (and (natp src) (natp dst) (not (equal src dst)) (natp (fn2-pool-base dst pool)))
           (equal (fn2-layout-range-code src sg at end nil pk ps pg
                                         (mv-nth 1 (fn2-pool-write dst dg off byte pk ps pg pool)))
                  (fn2-layout-range-code src sg at end nil pk ps pg pool)))
  :hints (("Goal" :in-theory
           (e/d (fn2-layout-range-code fn2-pool-slot-fill fn2-pool-slot-base fn2-pool-capacity-bytes
                 fn2-pool-write fn2-pool-readable-code fn2-pool-handle-code fn2-pool-ownerp
                 fn2-pool-set-fill update-fn2-pool-fill$ai update-fn2-pool-datai nth-update-nth)
                (nth update-nth fn2-pool-workspace-code unsigned-byte-p))))))

(local
 (defthm fn2-run-load-source-range-and-bases
  (let ((after (mv-nth 1 (fn2-run-load-bytes bytes dst dg off pk ps pg pool))))
    (and (equal (fn2-pool-base i after) (fn2-pool-base i pool))
         (implies (and (natp src) (natp dst) (not (equal src dst)) (natp (fn2-pool-base dst pool)))
                  (equal (fn2-layout-range-code src sg at end nil pk ps pg after)
                         (fn2-layout-range-code src sg at end nil pk ps pg pool)))))
  :hints (("Goal" :induct (fn2-run-load-bytes bytes dst dg off pk ps pg pool)
           :in-theory (e/d (fn2-run-load-bytes fn2-pool-write-keeps-extents)
                           (fn2-pool-write fn2-pool-base fn2-layout-range-code))))))

(local
 (defthm fn2-run-load-separate-from-source
  (let* ((source (+ (fn2-pool-base src pool) at)) (target (+ (fn2-pool-base dst pool) off))
         (after (mv-nth 1 (fn2-run-load-bytes bytes dst dg off pk ps pg pool))))
    (implies (and (natp src) (natp dst) (not (equal src dst))
                  (natp (fn2-pool-base src pool)) (natp (fn2-pool-base dst pool))
                  (natp at) (natp off) (natp n)
                  (or (<= (+ source n) target) (<= (+ target (len bytes)) source)))
             (equal (fn2-run-read-bytes n src sg at pk ps pg after)
                    (fn2-run-read-bytes n src sg at pk ps pg pool))))
  :hints (("Goal" :induct (fn2-run-load-bytes bytes dst dg off pk ps pg pool)
           :in-theory (e/d (fn2-run-load-bytes fn2-pool-write-keeps-extents)
                           (fn2-pool-write fn2-pool-read fn2-pool-base fn2-run-read-bytes))))))

(local
 (defthm fn2-run-octets-true-list-fix
  (implies (fn-b3-octet-listp xs) (equal (true-list-fix xs) xs))))

(defthm fn2-run-write-prefix-and-payload
  (let* ((body (fn2-run-read-bytes n src sg at pk ps pg pool))
         (bytes (append header body))
         (next (+ off (len header))) (end (+ next n))
         (src-base (+ at (fn2-pool-base src pool))) (dst-base (+ off (fn2-pool-base dst pool)))
         (head (fn2-run-load-bytes header dst dg off pk ps pg pool))
         (copy (fn2-layout-copy src sg at dst dg next n pk ps pg (mv-nth 1 head)))
         (load (fn2-run-load-bytes bytes dst dg off pk ps pg pool)))
    (implies (and (natp src) (natp dst) (not (equal src dst))
                  (natp (fn2-pool-base src pool)) (natp (fn2-pool-base dst pool))
                  (natp off) (unsigned-byte-p 32 next) (unsigned-byte-p 32 at) (unsigned-byte-p 32 n)
                  (or (<= (+ src-base n) dst-base) (<= (+ dst-base (len header) n) src-base))
                  (fn-b3-octet-listp header) (fn-b3-octet-listp body)
                  (eq (fn2-layout-range-code src sg at (+ at n) nil pk ps pg pool) :ok)
                  (eq (fn2-layout-range-code dst dg off end t pk ps pg pool) :ok))
             (and (equal (car head) :ok) (equal copy load))))
  :rule-classes nil
  :hints (("Goal" :use ((:instance fn2-run-load-bytes-roundtrip (bytes header) (slot dst)
                                   (gen dg) (cap (+ off (len header) n))))
           :in-theory (e/d (fn2-layout-copy fn2-run-copy-writes-source-octets fn2-run-load-byte-segments
                            fn2-run-load-source-range-and-bases fn2-run-load-separate-from-source)
                           (fn2-layout-copy-loop fn2-run-load-bytes fn2-run-read-bytes
                            fn2-pool-base fn2-layout-range-code fn-b3-octet-listp unsigned-byte-p)))))

