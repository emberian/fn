; Reading a writable ribbon page observes every octet, including a flipped byte.
(in-package "ACL2")
(include-book "ribbon-mutation-state")
(local (include-book "centaur/bitops/ihsext-basics" :dir :system))
(local
 (defthm fn2-ribbon-xor-twice
   (implies (integerp x) (equal (logxor (logxor x b) b) x))
   :hints (("Goal" :in-theory (enable commutativity-of-logxor)))))

(local (defthm fn2-ribbon-xor-with-self (equal (logxor b b) 0)))

(local
 (defthm fn2-ribbon-xor-changes-byte
   (implies (and (unsigned-byte-p 8 x) (unsigned-byte-p 8 b) (not (equal x 0)))
            (and (unsigned-byte-p 8 (logxor x b)) (not (equal (logxor x b) b))
                 (equal (nfix x) x) (equal (nfix b) b)))
   :rule-classes nil
   :hints (("Goal" :cases ((equal (logxor x b) b)) :use fn2-ribbon-xor-twice
            :in-theory (union-theories (theory 'minimal-theory)
                    '(fn2-ribbon-xor-with-self unsigned-byte-p-of-logxor
                      nfix unsigned-byte-p integer-range-p natp (:e expt)))))))

(include-book "format-page-hash-feed-proof")
(local (in-theory (current-theory 'fc-u32-reconstruct)))

(defthmd fn2-ribbon-arena-is-hash-window
  (implies (and (fn2-ribbon-arena-p 0 1 9 0 1 65536 65536 pool) (equal (fn2-pool-base 0 pool) 0))
           (fn2-hash-page-windowp pool))
  :hints (("Goal" :in-theory (e/d (fn2-ribbon-arena-p fn2-hash-page-windowp
                                   fn2-pool-readable-code fn2-pool-workspace-code)
                                  (fn2-pool-handle-code fn2-pool-state fn2-pool-ownerp fn2-pool-base
                                   fn2-pool-fill fn2-pool-data-length)))))

(local
 (defthm fn2-ribbon-window-octet
   (implies (and (fn2-hash-page-windowp pool) (fn2-poolp pool) (natp off) (< off 65536))
            (and (equal (fn2-pool-read 0 1 off 9 0 1 pool) (list :ok (fn2-pool-datai off pool)))
                 (unsigned-byte-p 8 (fn2-pool-datai off pool))))
   :hints (("Goal" :use ((:instance fn2-pool-datai-byte (i off) (fn2-pool pool)))
            :in-theory (e/d (fn2-hash-page-windowp fn2-pool-read)
                            (fn2-pool-datai fn2-pool-base fn2-pool-data-length fn2-pool-readable-code
                             fn2-pool-fill unsigned-byte-p fn2-poolp))))))

(local
 (defthm fn2-ribbon-window-octet-bounds
   (implies (and (fn2-poolp pool) (fn2-hash-page-windowp pool) (natp off) (< off 65536))
            (and (integerp (fn2-pool-datai off pool))
                 (<= 0 (fn2-pool-datai off pool)) (<= (fn2-pool-datai off pool) 255)))
   :hints (("Goal" :use fn2-ribbon-window-octet
            :in-theory (union-theories (theory 'minimal-theory)
                             '(unsigned-byte-p integer-range-p (:e expt)))))))

(defthmd fn2-ribbon-page-read-represents-window
  (let ((bytes (fn2-run-read-bytes n 0 1 off 9 0 1 pool)))
    (implies (and (fn2-hash-page-windowp pool) (fn2-poolp pool)
                  (natp off) (natp n) (<= (+ off n) 65536))
             (and (equal (len bytes) n) (fn-b3-octet-listp bytes) (fn2-b3-covers bytes off pool))))
  :hints (("Goal" :induct (fn2-run-read-bytes n 0 1 off 9 0 1 pool)
           :in-theory (e/d (fn2-run-read-bytes fn-b3-octet-listp fn2-b3-covers fn2-ribbon-window-octet)
                           (fn2-pool-read fn2-pool-datai fn2-hash-page-windowp fn2-poolp)))
          ("Subgoal *1/2" :use fn2-ribbon-window-octet-bounds
            :in-theory (e/d (fn2-run-read-bytes fn-b3-octet-listp fn2-b3-covers fn2-ribbon-window-octet natp)
                            (fn2-ribbon-window-octet-bounds fn2-pool-read fn2-pool-datai fn2-hash-page-windowp fn2-poolp)))))

(local
 (defun fn2-ribbon-page-index-induct (n i off)
   (if (or (zp n) (zp i)) off
     (fn2-ribbon-page-index-induct (1- n) (1- i) (1+ (nfix off))))))

(local
 (defthm fn2-ribbon-page-read-at
   (implies (and (natp n) (natp i) (< i n) (natp off) (<= (+ n off) 65536)
                 (fn2-poolp pool) (fn2-hash-page-windowp pool))
            (equal (nth i (fn2-run-read-bytes n 0 1 off 9 0 1 pool)) (fn2-pool-datai (+ i off) pool)))
   :hints (("Goal" :induct (fn2-ribbon-page-index-induct n i off)
            :expand ((fn2-run-read-bytes n 0 1 off 9 0 1 pool))
            :in-theory (e/d (nth fn2-ribbon-window-octet)
                            (fn2-pool-read fn2-pool-datai fn2-run-read-bytes fn2-hash-page-windowp fn2-poolp))))))

(local
 (defthmd fn2-ribbon-write-page-octet
   (let ((after (mv-nth 1 (fn2-pool-write 0 1 off byte 9 0 1 pool))))
     (implies (and (fn2-ribbon-arena-p 0 1 9 0 1 65536 65536 pool)
                   (equal (fn2-pool-base 0 pool) 0)
                   (natp off) (< off 65536) (unsigned-byte-p 8 byte))
              (and (fn2-hash-page-windowp after)
                   (equal (fn2-pool-datai off after) byte))))
   :hints (("Goal" :in-theory (e/d (fn2-ribbon-arena-p fn2-hash-page-windowp
                             fn2-pool-write fn2-pool-set-fill update-fn2-pool-fill$ai update-fn2-pool-datai
                             fn2-pool-readable-code fn2-pool-workspace-code fn2-pool-datai)
                            (unsigned-byte-p))))))

(defthmd fn2-ribbon-flip-writes-changed-octet
  (let ((after (fn2-ribbon-flipped-pool off x pool)))
    (implies (and (fn2-ribbon-arena-p 0 1 9 0 1 65536 65536 pool)
                  (equal (fn2-pool-base 0 pool) 0) (fn2-poolp pool) (fn2-pool-wfp pool)
                  (natp off) (< off 65536) (unsigned-byte-p 8 x) (not (equal x 0)))
             (and (fn2-poolp after) (fn2-hash-page-windowp after)
                  (not (equal (fn2-pool-datai off after) (fn2-pool-datai off pool))))))
  :hints (("Goal" :use (fn2-ribbon-arena-is-hash-window fn2-ribbon-window-octet
                        (:instance fn2-ribbon-xor-changes-byte (b (fn2-pool-datai off pool)))
                        (:instance fn2-ribbon-write-page-octet (byte (logxor x (fn2-pool-datai off pool)))))
           :in-theory (union-theories (theory 'minimal-theory)
                         '(fn2-ribbon-flipped-pool fn2-pool-write-preserves-type
                           fc-mv-cons (:e mv-nth) car-cons cdr-cons)))))

(defthm fn2-ribbon-mutated-window-differs
  (let ((after (fn2-ribbon-flipped-pool off x pool)))
    (implies (and (fn2-ribbon-arena-p 0 1 9 0 1 65536 65536 pool)
                  (equal (fn2-pool-base 0 pool) 0) (fn2-poolp pool) (fn2-pool-wfp pool)
                  (natp off) (< off 65536) (unsigned-byte-p 8 x) (not (equal x 0)))
             (and (fn2-hash-page-windowp pool) (fn2-hash-page-windowp after) (fn2-poolp after)
                  (not (equal (fn2-ribbon-read-page pool) (fn2-ribbon-read-page after))))))
  :rule-classes nil
  :hints (("Goal" :use (fn2-ribbon-arena-is-hash-window fn2-ribbon-flip-writes-changed-octet
                        (:instance fn2-ribbon-page-read-at (i off) (off 0) (n 65536))
                        (:instance fn2-ribbon-page-read-at (i off) (off 0) (n 65536) (pool (fn2-ribbon-flipped-pool off x pool))))
           :in-theory (union-theories (theory 'minimal-theory) '(fc-zero-plus-len commutativity-of-+ (:e natp) (:e binary-+) (:e <))))))
