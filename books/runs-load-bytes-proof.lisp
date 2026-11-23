; Writing a run payload advances the pool fill and preserves every input byte.
(in-package "ACL2")
(include-book "runs-page")

(local
 (defthm fn2-run-load-one-progress
   (let ((wr (fn2-pool-write slot gen off byte pk ps pg pool)))
     (implies (and (natp (fn2-pool-base slot pool))
                   (equal (fn2-layout-range-code slot gen off end t pk ps pg pool) :ok)
                   (< off end) (unsigned-byte-p 8 byte))
              (and (equal (mv-nth 0 wr) :ok)
                   (equal (fn2-pool-base slot (mv-nth 1 wr)) (fn2-pool-base slot pool))
                   (equal (fn2-layout-range-code slot gen (+ 1 off) end t pk ps pg (mv-nth 1 wr)) :ok))))
   :hints (("Goal" :in-theory
            (enable fn2-layout-range-code fn2-pool-slot-fill fn2-pool-slot-cap fn2-pool-slot-base
                    fn2-pool-capacity-bytes fn2-pool-write fn2-pool-workspace-code fn2-pool-handle-code
                    fn2-pool-ownerp fn2-pool-set-fill update-fn2-pool-fill$ai update-fn2-pool-datai)))))

(local
 (defthm fn2-run-byte-tail-ok
   (implies (fn-b3-octet-listp (true-list-fix bytes))
            (and (implies (consp bytes) (unsigned-byte-p 8 (car bytes)))
                 (fn-b3-octet-listp (true-list-fix (cdr bytes)))))
   :hints (("Goal" :expand ((true-list-fix bytes) (fn-b3-octet-listp (true-list-fix bytes)))))))

(local
 (defthm fn2-run-load-octets-progress
   (let ((load (fn2-run-load-bytes bytes slot gen off pk ps pg pool)))
     (implies (and (natp (fn2-pool-base slot pool)) (natp off)
                   (fn-b3-octet-listp (true-list-fix bytes)) (<= (+ off (len bytes)) end)
                   (equal (fn2-layout-range-code slot gen off end t pk ps pg pool) :ok))
              (and (equal (mv-nth 0 load) :ok)
                   (equal (fn2-pool-base slot (mv-nth 1 load)) (fn2-pool-base slot pool))
                   (equal (fn2-layout-range-code slot gen (+ off (len bytes)) end t pk ps pg (mv-nth 1 load))
                          :ok))))
   :hints (("Goal" :induct (fn2-run-load-bytes bytes slot gen off pk ps pg pool)
            :in-theory (e/d (fn2-run-load-bytes) (fn2-layout-range-code fn2-pool-base fn2-pool-write
                         unsigned-byte-p fn-b3-octet-listp true-list-fix)))
           ("Subgoal *1/3" :use ((:instance fn2-run-load-one-progress (byte (car bytes)))))
           ("Subgoal *1/2" :use ((:instance fn2-run-load-one-progress (byte (car bytes))))))))

(local
 (defthm fn2-run-load-one-read
   (let* ((wr (fn2-pool-write slot gen off byte pk ps pg pool))
          (prev (fn2-pool-read slot gen i pk ps pg pool)))
     (implies (and (natp (fn2-pool-base slot pool)) (natp i) (equal (mv-nth 0 wr) :ok)
                   (or (equal i off) (eq (mv-nth 0 prev) :ok)))
              (and (equal (fn2-pool-base slot (mv-nth 1 wr)) (fn2-pool-base slot pool))
                   (equal (fn2-pool-read slot gen i pk ps pg (mv-nth 1 wr))
                          (if (equal i off) (list :ok byte) prev)))))
   :hints (("Goal" :in-theory (enable fn2-pool-write fn2-pool-read fn2-pool-workspace-code
                    fn2-pool-readable-code fn2-pool-handle-code fn2-pool-ownerp
                    fn2-pool-set-fill update-fn2-pool-fill$ai update-fn2-pool-datai)))))
(local
 (defthm fn2-run-load-byte-readable
   (let ((wr (fn2-run-load-bytes bytes slot gen off pk ps pg pool)) (prev (fn2-pool-read slot gen i pk ps pg pool)))
     (implies (and (natp off) (natp i) (natp (fn2-pool-base slot pool))
                   (< i (+ off (len bytes))) (or (<= off i) (equal (mv-nth 0 prev) :ok))
                   (equal (mv-nth 0 wr) :ok))
              (equal (fn2-pool-read slot gen i pk ps pg (mv-nth 1 wr))
                     (if (< i off) prev (list :ok (nth (- i off) bytes))))))
   :hints (("Goal" :induct (fn2-run-load-bytes bytes slot gen off pk ps pg pool)
            :in-theory (e/d (fn2-run-load-bytes) (fn2-pool-read fn2-pool-write fn2-pool-base)))
           ("Subgoal *1/2" :use ((:instance fn2-run-load-one-read (byte (car bytes))))))))

(local
 (defun fn2-run-loaded-suffix-induct (n idx)
   (declare (xargs :measure (nfix n)))
   (if (zp n) idx (fn2-run-loaded-suffix-induct (1- n) (1+ idx)))))
(local
 (defthm fn2-run-loaded-suffix-nthcdr
   (implies (natp idx)
            (and (equal (consp (nthcdr idx bytes)) (< idx (len bytes)))
                 (equal (car (nthcdr idx bytes)) (nth idx bytes))
                 (equal (nthcdr (+ 1 idx) bytes) (cdr (nthcdr idx bytes)))))
   :hints (("Goal" :induct (nthcdr idx bytes))
           ("Subgoal *1/1" :expand (len bytes)))))
(local
 (defthm fn2-run-read-loaded-suffix
  (let ((load (fn2-run-load-bytes bytes slot gen off pk ps pg pool)))
    (implies (and (natp idx) (natp off) (natp n) (equal (+ n idx) (len bytes))
                  (natp (fn2-pool-base slot pool)) (eq (mv-nth 0 load) :ok))
             (equal (fn2-run-read-bytes n slot gen (+ off idx) pk ps pg (mv-nth 1 load))
                    (true-list-fix (nthcdr idx bytes)))))
  :hints (("Goal" :induct (fn2-run-loaded-suffix-induct n idx)
           :expand ((:free (origin pool) (fn2-run-read-bytes n slot gen origin pk ps pg pool))
                    (true-list-fix (nthcdr idx bytes)))
           :in-theory (disable fn2-run-load-bytes fn2-pool-read fn2-pool-base fn2-run-read-bytes nthcdr
                               fn2-run-loaded-suffix-nthcdr))
          ("Subgoal *1/2" :use ((:instance fn2-run-load-byte-readable (i (+ off idx)))
                                fn2-run-loaded-suffix-nthcdr))
          ("Subgoal *1/1" :use fn2-run-loaded-suffix-nthcdr :in-theory (e/d (fn2-run-read-bytes) (fn2-run-load-bytes fn2-pool-read fn2-pool-base nthcdr fn2-run-loaded-suffix-nthcdr))))))

(defthm fn2-run-load-bytes-roundtrip
 (let* ((end (+ off (len bytes))) (load (fn2-run-load-bytes bytes slot gen off pk ps pg pool))
        (after (mv-nth 1 load)))
   (implies (and (natp off) (natp (fn2-pool-base slot pool)) (fn-b3-octet-listp (true-list-fix bytes))
                 (<= end cap) (equal (fn2-layout-range-code slot gen off cap t pk ps pg pool) :ok))
            (and (eq (mv-nth 0 load) :ok)
                 (equal (fn2-layout-range-code slot gen end cap t pk ps pg after) :ok)
                 (equal (fn2-run-read-bytes (len bytes) slot gen off pk ps pg after)
                        (true-list-fix bytes)))))
 :rule-classes nil
 :hints (("Goal" :use ((:instance fn2-run-read-loaded-suffix (n (len bytes)) (idx 0))
                       (:instance fn2-run-load-octets-progress (end cap)))
          :in-theory (disable fn2-run-read-bytes fn2-layout-range-code fn2-pool-base
                              fn-b3-octet-listp true-list-fix fn2-run-load-bytes))))
