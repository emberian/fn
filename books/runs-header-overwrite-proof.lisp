; Rewriting a header in a filled page keeps every other byte readable.
(in-package "ACL2")
(include-book "runs-page-copy-proof")

(defmacro fn2-run-filled-page-p (slot gen pk ps pg pool)
  `(and (natp (fn2-pool-base ,slot ,pool))
        (equal (fn2-layout-range-code ,slot ,gen *fn2-run-page-size* *fn2-run-page-size* t ,pk ,ps ,pg ,pool) :ok)))

(defthmd fn2-run-filled-page-allows-subrange
  (implies (and (fn2-run-filled-page-p slot gen pk ps pg pool) (natp start) (natp end)
                (<= start end) (<= end *fn2-run-page-size*))
           (equal (fn2-layout-range-code slot gen start end writep pk ps pg pool) :ok))
  :hints (("Goal" :in-theory (e/d (fn2-layout-range-code fn2-pool-workspace-code fn2-pool-readable-code)
                                  (fn2-pool-slot-base fn2-pool-slot-fill fn2-pool-slot-cap fn2-pool-capacity-bytes
                                   fn2-pool-handle-code fn2-pool-ownerp fn2-pool-state fn2-pool-base)))))

(local
 (defthm fn2-run-overwrite-one-page-byte
   (let* ((write (fn2-pool-write slot gen off byte pk ps pg pool)) (after (mv-nth 1 write)))
     (implies (and (fn2-run-filled-page-p slot gen pk ps pg pool) (natp off) (< off *fn2-run-page-size*)
                   (and (integerp byte) (<= 0 byte) (<= byte 255)))
              (and (equal (car write) :ok) (fn2-run-filled-page-p slot gen pk ps pg after)
                   (implies (and (natp i) (< i *fn2-run-page-size*) (not (equal i off)))
                            (equal (fn2-pool-read slot gen i pk ps pg after) (fn2-pool-read slot gen i pk ps pg pool))))))
   :hints (("Goal" :in-theory (e/d (fn2-pool-write fn2-pool-read fn2-layout-range-code fn2-pool-slot-base
                             fn2-pool-slot-fill fn2-pool-slot-cap fn2-pool-capacity-bytes fn2-pool-workspace-code
                             fn2-pool-readable-code fn2-pool-handle-code fn2-pool-ownerp fn2-pool-set-fill
                             update-fn2-pool-fill$ai update-fn2-pool-datai nth-update-nth)
                           (nth update-nth unsigned-byte-p))))))

(defthm fn2-run-overwrite-filled-page
  (let ((write (fn2-run-load-bytes bytes slot gen off pk ps pg pool)))
    (implies (and (fn2-run-filled-page-p slot gen pk ps pg pool) (natp off)
                  (fn-b3-octet-listp bytes) (<= (+ off (len bytes)) *fn2-run-page-size*))
             (and (equal (car write) :ok) (fn2-run-filled-page-p slot gen pk ps pg (mv-nth 1 write))
                  (implies (and (natp i) (< i *fn2-run-page-size*) (or (< i off) (<= (+ off (len bytes)) i)))
                           (equal (fn2-pool-read slot gen i pk ps pg (mv-nth 1 write))
                                  (fn2-pool-read slot gen i pk ps pg pool))))))
  :rule-classes nil
  :hints (("Goal" :induct (fn2-run-load-bytes bytes slot gen off pk ps pg pool)
           :expand ((fn-b3-octet-listp bytes) (len bytes))
           :in-theory (e/d (fn2-run-load-bytes) (fn2-pool-read fn2-pool-write fn2-layout-range-code fn2-pool-base unsigned-byte-p)))))

(defthmd fn2-run-header-overwrite-retains-span
  (let ((after (mv-nth 1 (fn2-run-load-bytes bytes slot gen off pk ps pg pool))))
    (implies (and (fn2-run-filled-page-p slot gen pk ps pg pool) (natp off)
                  (fn-b3-octet-listp bytes) (<= (+ off (len bytes)) *fn2-run-page-size*)
                  (natp n) (natp at) (<= (+ at n) *fn2-run-page-size*)
                  (or (<= (+ at n) off) (<= (+ off (len bytes)) at)))
             (equal (fn2-run-read-bytes n slot gen at pk ps pg after)
                    (fn2-run-read-bytes n slot gen at pk ps pg pool))))
  :hints (("Goal" :induct (fn2-run-read-bytes n slot gen at pk ps pg pool)
           :expand ((:free (p) (fn2-run-read-bytes n slot gen at pk ps pg p)) (:free (p) (fn2-run-read-bytes 0 slot gen at pk ps pg p)))
           :in-theory (disable fn2-run-load-bytes (:definition fn2-run-read-bytes) fn2-pool-read fn2-layout-range-code fn2-pool-base fn-b3-octet-listp))
          ("Subgoal *1/2" :use ((:instance fn2-run-overwrite-filled-page (i at))))))
