; Closing the page serializes the writer's saved row offsets in order.
(in-package "ACL2")
(include-book "runs-restart-write-proof")

(defun-nx fn2-run-saved-offsets (k row restarts)
  (if (zp k) nil
    (cons (fn2-run-restarts-offset row restarts)
          (fn2-run-saved-offsets (1- k) (1+ row) restarts))))

(local
 (defthm fn2-run-restart-field-prepared
   (implies (natp scratch)
            (equal (fn2-fields-value scratch (fn2-fields-set-value scratch v f)) v))
   :hints (("Goal" :in-theory (e/d (fn2-fields-value fn2-fields-set-value update-fn2-fields-value$ai)
                                   (update-nth nth))))))

(local
 (defthm fn2-run-restart-write-subrange
   (implies (and (natp at) (<= (+ at 4) end)
                 (equal (fn2-layout-range-code slot gen at end t pk ps pg pool) :ok))
            (equal (fn2-layout-range-code slot gen at (+ at 4) t pk ps pg pool) :ok))
   :hints (("Goal" :in-theory (e/d (fn2-layout-range-code)
                                      (fn2-pool-workspace-code fn2-pool-slot-base
                                       fn2-pool-slot-fill fn2-pool-capacity-bytes fn2-pool-data-length))))))

(local
 (defthm fn2-run-directory-word-shape
   (implies (unsigned-byte-p 32 v)
            (and (equal (len (fn2-layout-le 4 v)) 4)
                 (fn-b3-octet-listp (true-list-fix (fn2-layout-le 4 v)))))
   :hints (("Goal" :in-theory (enable fn2-layout-le)))))

(local
 (defthm fn2-run-directory-word-progress
   (let ((load (fn2-run-load-bytes (fn2-layout-le 4 v) slot gen at pk ps pg pool)))
     (implies (and (natp at) (natp (fn2-pool-base slot pool)) (unsigned-byte-p 32 v)
                   (<= (+ at 4) end)
                   (equal (fn2-layout-range-code slot gen at end t pk ps pg pool) :ok))
              (and (equal (car load) :ok)
                   (equal (fn2-layout-range-code slot gen (+ at 4) end t pk ps pg (mv-nth 1 load)) :ok))))
   :hints (("Goal" :use ((:instance fn2-run-load-bytes-roundtrip (off at) (cap end)
                                     (bytes (fn2-layout-le 4 v))))
            :in-theory (disable fn2-run-load-bytes fn2-run-read-bytes fn2-layout-le
                                fn2-layout-range-code fn2-pool-base unsigned-byte-p)))))

(local
 (defthm fn2-run-write-directory-word
   (let* ((fields (fn2-fields-set-value scratch v f))
          (write (fn2-run-restart-encode scratch slot gen at pk ps pg fields pool))
          (load (fn2-run-load-bytes (fn2-layout-le 4 v) slot gen at pk ps pg pool)))
     (implies (and (natp scratch) (unsigned-byte-p 32 v) (unsigned-byte-p 32 at)
                   (natp (fn2-pool-base slot pool)) (<= (+ at 4) end)
                   (equal (fn2-layout-range-code slot gen at end t pk ps pg pool) :ok))
              (and (equal write (list :ok (+ at 4) (mv-nth 1 load)))
                   (equal (car load) :ok)
                   (equal (fn2-layout-range-code slot gen (+ at 4) end t pk ps pg (mv-nth 1 load)) :ok))))
   :rule-classes nil
   :hints (("Goal" :use (fn2-run-restart-write-subrange fn2-run-directory-word-progress
                         (:instance fn2-run-restart-encode-stores-offset (base scratch) (off at)
                                    (f (fn2-fields-set-value scratch v f))))
            :in-theory (disable fn2-layout-range-code fn2-layout-le fn2-run-load-bytes fn2-pool-base
                                fn2-run-restart-encode fn2-fields-set-value fn2-fields-value)))))

(defthm fn2-run-write-restarts-serializes-directory
  (let* ((at (+ cursor (* 4 j))) (end (+ at (* 4 k)))
         (row (+ (* w *fn2-run-restart-capacity*) j))
         (bytes (fn2-run-directory-octets (fn2-run-saved-offsets k row restarts)))
         (load (fn2-run-load-bytes bytes slot gen at pk ps pg pool))
         (write (fn2-run-write-restarts k j w cursor scratch slot gen pk ps pg restarts f pool)))
    (implies (and (natp k) (natp j) (natp w) (natp cursor) (natp scratch)
                  (<= (+ j k) *fn2-run-restart-capacity*)
                  (<= (+ row k) (fn2-run-restarts-rows restarts))
                  (fn2-run-restartsp restarts) (fn2-run-restarts-wfp restarts)
                  (unsigned-byte-p 32 end) (natp (fn2-pool-base slot pool))
                  (equal (fn2-layout-range-code slot gen at end t pk ps pg pool) :ok))
             (and (equal (car write) :ok) (equal (mv-nth 2 write) (mv-nth 1 load)))))
  :rule-classes nil
  :hints (("Goal" :do-not '(preprocess)
           :induct (fn2-run-write-restarts k j w cursor scratch slot gen pk ps pg restarts f pool)
           :expand ((fn2-run-write-restarts k j w cursor scratch slot gen pk ps pg restarts f pool)
                    (:free (r) (fn2-run-saved-offsets k r restarts)))
           :in-theory (e/d ((:induction fn2-run-write-restarts) fn2-run-load-byte-segments fn2-run-restart-encode-stores-offset
                            fn2-run-load-preserves-base fn2-run-directory-octets)
                           (fn2-run-load-bytes fn2-run-restart-encode fn2-run-saved-offsets
                            fn2-run-restarts-rows fn2-run-restarts-offset fn2-fields-set-value
                            fn2-fields-value fn2-layout-le fn2-pool-base fn2-layout-range-code
                            fn2-run-restartsp fn2-run-restarts-wfp)))
          ("Subgoal *1/2" :use ((:instance fn2-run-write-directory-word (at (+ cursor (* 4 j))) (end (+ cursor (* 4 j) (* 4 k)))
               (v (fn2-run-restarts-offset (+ (* w *fn2-run-restart-capacity*) j) restarts)))))
          ("Subgoal *1/3" :use ((:instance fn2-run-write-directory-word (at (+ cursor (* 4 j))) (end (+ cursor (* 4 j) (* 4 k)))
               (v (fn2-run-restarts-offset (+ (* w *fn2-run-restart-capacity*) j) restarts)))))
          ("Subgoal *1/1" :expand ((fn2-run-write-restarts 0 j w cursor scratch slot gen pk ps pg restarts f pool)
                                    (:free (row) (fn2-run-saved-offsets 0 row restarts))
                                    (fn2-run-load-bytes nil slot gen (+ cursor (* 4 j)) pk ps pg pool)))))
