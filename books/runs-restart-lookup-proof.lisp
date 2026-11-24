; Each saved offset in a complete directory can be read back at its own index.
(in-package "ACL2")
(include-book "runs-restart-directory-proof")
(include-book "runs-restart-reader-proof")

(local
 (defthm fn2-run-read-prefix
   (implies (and (natp n) (natp m) (natp at))
            (equal (fn2-run-read-bytes (+ n m) slot gen at pk ps pg pool)
                   (append (fn2-run-read-bytes n slot gen at pk ps pg pool)
                           (fn2-run-read-bytes m slot gen (+ at n) pk ps pg pool))))
   :rule-classes nil
   :hints (("Goal" :induct (fn2-run-read-bytes n slot gen at pk ps pg pool)
            :expand ((fn2-run-read-bytes (+ n m) slot gen at pk ps pg pool))
            :in-theory (disable fn2-pool-read)))))

(local
 (defthm fn2-run-word-read-is-four-bytes
   (equal (len (fn2-run-read-bytes n slot gen off pk ps pg pool)) (nfix n))
   :hints (("Goal" :induct (fn2-run-read-bytes n slot gen off pk ps pg pool)
            :in-theory (disable fn2-pool-read)))))

(local
 (defthm fn2-run-equal-byte-prefixes
   (implies (and (true-listp x) (true-listp y) (equal (len x) (len y)))
            (equal (equal (append x xs) (append y ys))
                   (and (equal x y) (equal xs ys))))
   :hints (("Goal" :induct (pairlis$ x y) :in-theory (enable len)))))

(local
 (defthm fn2-run-four-byte-encoding
   (and (equal (len (fn2-layout-le 4 v)) 4) (true-listp (fn2-layout-le 4 v)))
   :hints (("Goal" :expand ((:free (x) (fn2-layout-le 4 x)) (:free (x) (fn2-layout-le 3 x))
                            (:free (x) (fn2-layout-le 2 x)) (:free (x) (fn2-layout-le 1 x))
                            (:free (x) (fn2-layout-le 0 x)))
            :in-theory (disable mod floor)))))

(local
 (defthm fn2-run-read-directory-cons
  (implies (and (natp at)
                (equal (fn2-run-read-bytes (+ 4 (* 4 (len rest))) slot gen at pk ps pg pool)
                       (fn2-run-directory-octets (cons v rest))))
           (and (equal (fn2-run-read-bytes 4 slot gen at pk ps pg pool) (fn2-layout-le 4 v))
                (equal (fn2-run-read-bytes (* 4 (len rest)) slot gen (+ 4 at) pk ps pg pool)
                       (fn2-run-directory-octets rest))))
  :rule-classes nil
  :hints (("Goal" :use ((:instance fn2-run-read-prefix (n 4) (m (* 4 (len rest)))))
           :expand ((fn2-run-directory-octets (cons v rest)))
           :in-theory (disable fn2-run-read-bytes fn2-run-directory-octets fn2-layout-le binary-append)))))

(local
 (defun-nx fn2-run-directory-index-walk (j offsets at)
   (if (or (zp j) (atom offsets)) at
     (fn2-run-directory-index-walk (1- j) (cdr offsets) (+ 4 at)))))

(defthmd fn2-run-read-directory-index
  (implies (and (natp j) (< j (len offsets)) (natp at)
                (equal (fn2-run-read-bytes (* 4 (len offsets)) slot gen at pk ps pg pool)
                       (fn2-run-directory-octets offsets)))
           (equal (fn2-run-read-bytes 4 slot gen (+ at (* 4 j)) pk ps pg pool)
                  (fn2-layout-le 4 (nth j offsets))))
  :hints (("Goal" :induct (fn2-run-directory-index-walk j offsets at)
           :expand ((len offsets) (nth j offsets))
           :in-theory (disable fn2-run-read-bytes fn2-run-directory-octets fn2-layout-le))
          ("Subgoal *1/1" :use ((:instance fn2-run-read-directory-cons (v (car offsets)) (rest (cdr offsets)))))
          ("Subgoal *1/2" :use ((:instance fn2-run-read-directory-cons (v (car offsets)) (rest (cdr offsets)))))))

(local
 (defthm fn2-run-four-byte-octets
   (fn-b3-octet-listp (fn2-layout-le 4 v))
   :hints (("Goal" :expand ((:free (x) (fn2-layout-le 4 x)) (:free (x) (fn2-layout-le 3 x))
                            (:free (x) (fn2-layout-le 2 x)) (:free (x) (fn2-layout-le 1 x))
                            (:free (x) (fn2-layout-le 0 x)))
            :in-theory (enable fn-b3-octet-listp)))))
(local
 (defthm fn2-run-directory-append-shape
   (and (equal (len (append a b)) (+ (len a) (len b)))
        (implies (and (fn-b3-octet-listp a) (fn-b3-octet-listp b))
                 (fn-b3-octet-listp (append a b))))
   :hints (("Goal" :induct (append a b)))))
(local
 (defthm fn2-run-directory-shape
   (let ((bytes (fn2-run-directory-octets offsets)))
     (and (equal (len bytes) (* 4 (len offsets))) (true-listp bytes)
          (fn-b3-octet-listp bytes)))
   :hints (("Goal" :induct (fn2-run-directory-octets offsets)
            :in-theory (disable fn2-layout-le)))))
(local
 (defthm fn2-run-saved-offset-count
   (equal (len (fn2-run-saved-offsets k row restarts)) (nfix k))
   :hints (("Goal" :induct (fn2-run-saved-offsets k row restarts)
            :in-theory (disable fn2-run-restarts-offset)))))
(local
 (defun-nx fn2-run-saved-offset-index (i k row)
   (if (or (zp i) (zp k)) row
     (fn2-run-saved-offset-index (1- i) (1- k) (1+ row)))))
(local
 (defthm fn2-run-saved-offset-at
   (implies (and (natp row) (natp k) (natp i) (< i k))
            (equal (nth i (fn2-run-saved-offsets k row restarts))
                   (fn2-run-restarts-offset (+ row i) restarts)))
   :hints (("Goal" :induct (fn2-run-saved-offset-index i k row)
            :expand ((fn2-run-saved-offsets k row restarts))
            :in-theory (disable fn2-run-restarts-offset)))))

(local (defthm fn2-run-directory-list-fix
  (implies (true-listp x) (equal (true-list-fix x) x))))

(defthm fn2-run-written-directory-lookup
  (let* ((at (+ cursor (* 4 j))) (end (+ at (* 4 k)))
         (row (+ (* w *fn2-run-restart-capacity*) j))
         (write (fn2-run-write-restarts k j w cursor scratch slot gen pk ps pg restarts f pool)))
    (implies (and (natp k) (natp j) (natp w) (natp cursor) (natp scratch)
                  (natp i) (< i k) (<= (+ j k) *fn2-run-restart-capacity*)
                  (<= (+ row k) (fn2-run-restarts-rows restarts))
                  (fn2-run-restartsp restarts) (fn2-run-restarts-wfp restarts)
                  (unsigned-byte-p 32 end) (natp (fn2-pool-base slot pool))
                  (equal (fn2-layout-range-code slot gen at end t pk ps pg pool) :ok))
             (and (equal (car write) :ok)
                  (equal (fn2-run-read-bytes 4 slot gen (+ at (* 4 i)) pk ps pg (mv-nth 2 write))
                         (fn2-layout-le 4 (fn2-run-restarts-offset (+ row i) restarts))))))
  :rule-classes nil
  :hints (("Goal" :use (fn2-run-write-restarts-serializes-directory
            (:instance fn2-run-load-bytes-roundtrip (off (+ cursor (* 4 j))) (cap (+ cursor (* 4 j) (* 4 k)))
                       (bytes (fn2-run-directory-octets
                                (fn2-run-saved-offsets k (+ (* w *fn2-run-restart-capacity*) j) restarts))))
            (:instance fn2-run-read-directory-index (j i) (at (+ cursor (* 4 j)))
                       (offsets (fn2-run-saved-offsets k (+ (* w *fn2-run-restart-capacity*) j) restarts))
                       (pool (mv-nth 2 (fn2-run-write-restarts k j w cursor scratch slot gen pk ps pg restarts f pool)))))
           :in-theory (disable fn2-run-saved-offsets fn2-run-directory-octets fn2-layout-le
                               fn2-run-read-bytes fn2-run-load-bytes fn2-run-write-restarts
                               fn2-pool-base fn2-layout-range-code fn2-run-restarts-rows fn2-run-restarts-offset
                               fn2-run-restartsp fn2-run-restarts-wfp))))

(defthm fn2-run-seek-reads-saved-restart
  (let* ((dir (fn2-run-directory base fn2-fields)) (at (+ dir (* 4 i)))
         (offsets (fn2-run-saved-offsets k row restarts))
         (v (fn2-run-restarts-offset (+ row i) restarts))
         (read (fn2-run-restart-offset i slot gen base pk ps pg fn2-fields pool)))
    (implies (and (natp i) (natp k) (< i k) (equal k (fn2-run-hdr base restarts))
                  (natp row) (natp base) (< (+ base *fn2-run-reader-restart*) (fn2-fields-rows fn2-fields))
                  (natp dir) (unsigned-byte-p 32 (+ 4 at))
                  (unsigned-byte-p 32 v) (<= *fn2-run-entries-base* v) (< v dir)
                  (unsigned-byte-p 32 slot) (unsigned-byte-p 60 gen)
                  (fn2-poolp pool) (fn2-pool-wfp pool) (natp (fn2-pool-base slot pool))
                  (equal (fn2-layout-range-code slot gen at (+ 4 at) nil pk ps pg pool) :ok)
                  (equal (fn2-run-read-bytes (* 4 k) slot gen dir pk ps pg pool)
                         (fn2-run-directory-octets offsets)))
             (and (equal (car read) :ok) (equal (mv-nth 1 read) v))))
  :rule-classes nil
  :hints (("Goal" :use ((:instance fn2-run-restart-offset-reads-directory-word
                                   (j i) (v (fn2-run-restarts-offset (+ row i) restarts)))
                        (:instance fn2-run-read-directory-index (j i) (at (fn2-run-directory base fn2-fields))
                                   (offsets (fn2-run-saved-offsets k row restarts))))
           :in-theory (disable fn2-run-restart-offset fn2-run-saved-offsets fn2-run-directory-octets
                         fn2-run-directory fn2-run-header-value fn2-run-restarts-offset fn2-layout-le
                         fn2-layout-range-code fn2-run-read-bytes fn2-fields-rows fn2-pool-base
                         fn2-poolp fn2-pool-wfp))))
