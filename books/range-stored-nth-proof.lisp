; Read a numbered overview entry through the physical restart directory,
; the bounded skips and the layout decoder used by child descent.
(in-package "ACL2")
(include-book "range-stored-row-skip-proof")
(include-book "range-stored-page-scan-proof")
(local (include-book "arithmetic-3/floor-mod/floor-mod" :dir :system))

(local
 (defthm fn2-run-row-restart-arithmetic
   (let ((j (floor k *fn2-run-restart-interval*)) (m (mod k *fn2-run-restart-interval*)))
     (implies (and (natp k) (< k total) (natp total) (natp count) (<= total (* 16 count)))
              (and (natp j) (< j count) (natp m) (< m (- total (* 16 j)))
                   (equal (+ m (* 16 j)) k))))
   :rule-classes nil))

(local
 (defthm fn2-run-nth-after-stored-prefix
   (implies (and (natp i) (natp m))
            (equal (nth m (nthcdr i rows)) (nth (+ m i) rows)))
   :hints (("Goal" :induct (nthcdr i rows)
            :expand ((:free (k) (nth k rows)) (nthcdr i rows))))))

(local
 (defmacro fn2-run-at-index-restart ()
   '(fn2-run-restart-offset (floor k *fn2-run-restart-interval*) slot gen rb pk ps pg f pool)))

(local
 (defthm fn2-run-index-restart-supplies-suffix
   (let* ((j (floor k *fn2-run-restart-interval*)) (i (* j *fn2-run-restart-interval*))
          (m (mod k *fn2-run-restart-interval*)) (suffix (nthcdr i rows))
          (read (fn2-run-at-index-restart)) (rf (mv-nth 2 read)))
     (implies (and (natp k) (< k (len rows)) (fn2-fieldsp f) (fn2-run-readerp rb f)
                   (fn2-run-stored-overview-page-p rows level rb slot gen pk ps pg f pool))
              (and (equal (car read) :ok) (natp m) (< m (len suffix))
                   (equal (nth m suffix) (nth k rows))
                   (fn2-run-overview-page-rowsp level suffix (+ rb *fn2-run-reader-entry*) slot gen
                         (mv-nth 1 read) (fn2-run-directory rb rf) pk ps pg rf pool))))
   :rule-classes nil
   :hints (("Goal" :do-not '(preprocess)
            :use ((:instance fn2-run-row-restart-arithmetic (total (len rows))
                          (count (len (fn2-run-restart-offsets-spec (fn2-run-overview-layout-at level) rows 0 *fn2-run-entries-base*))))
                  (:instance fn2-run-page-restarts-cover-rows (layout (fn2-run-overview-layout-at level)) (off *fn2-run-entries-base*))
                  (:instance fn2-run-stored-scan-input (j (floor k 16)))
                  (:instance fn2-run-page-restart-recovers-row (j (floor k 16))
                        (at (fn2-run-row-offset (* 16 (floor k 16)) (fn2-run-overview-layout-at level) rows *fn2-run-entries-base*)))
                  (:instance fn2-run-restart-keeps-header-and-query (j (floor k 16)) (qbase 0))
                  (:instance fn2-run-page-rows-use-field-count (rows (nthcdr (* 16 (floor k 16)) rows))
                        (base (+ rb *fn2-run-reader-entry*))
                        (off (fn2-run-row-offset (* 16 (floor k 16)) (fn2-run-overview-layout-at level) rows *fn2-run-entries-base*))
                        (end (fn2-run-directory rb f)) (f2 (mv-nth 2 (fn2-run-at-index-restart)))))
            :in-theory (e/d (fn2-run-readerp fn2-run-stored-overview-page-p)
                    (fn2-run-page-restart-word-p fn2-run-overview-page-rowsp fn2-run-directory fn2-run-header-value
                     fn2-run-read-bytes fn2-run-directory-octets fn2-run-restart-offsets-spec fn2-run-row-offset
                     fn2-run-restart-offset fn2-layout-range-code fn2-poolp fn2-pool-wfp fn2-pool-base
                     fn2-fields-rows fn2-fields-value fn2-fieldsp fn2-fields-wfp nth nthcdr floor mod len))))))

(local
 (defthm fn2-run-read-stored-row-scalar
   (let* ((read (fn2-run-layout-decode 3 level base slot gen off end pk ps pg f pool)))
     (implies (and (fn2-run-overview-row-atp level row base slot gen off end pk ps pg f pool)
                   (natp j) (< j (if (posp level) 6 4)))
              (and (equal (car read) :ok)
                   (equal (fn2-fields-value (+ j base) (mv-nth 2 read)) (nth j row)))))
   :rule-classes nil
   :hints (("Goal" :use (fn2-run-overview-page-row-id fn2-run-overview-page-row-boundary)
            :in-theory (e/d (fn2-run-overview-row-atp)
                    (fn2-run-layout-decode fn2-fields-value fn2-fields-rows fn2-run-values-layoutp
                     fn2-layout-octets fn2-run-read-bytes fn2-poolp fn2-pool-wfp fn2-pool-base
                     fn2-layout-range-code unsigned-byte-p nth))))))

(defthmd fn2-run-nth-reads-stored-scalar
  (let* ((read (fn2-run-nth 3 level k slot gen rb pk ps pg f pool)))
    (implies (and (natp k) (< k (len rows)) (natp j) (< j (if (posp level) 6 4))
                  (fn2-fieldsp f) (fn2-run-readerp rb f)
                  (fn2-run-stored-overview-page-p rows level rb slot gen pk ps pg f pool))
             (and (equal (car read) :ok)
                  (equal (fn2-fields-value (+ j rb *fn2-run-reader-entry*) (mv-nth 2 read))
                         (nth j (nth k rows))))))
  :hints (("Goal" :do-not '(preprocess)
           :use (fn2-run-index-restart-supplies-suffix
                 (:instance fn2-run-skip-to-stored-overview-row (m (mod k 16)) (off (mv-nth 1 (fn2-run-at-index-restart)))
                    (rows (nthcdr (* 16 (floor k 16)) rows)) (f (mv-nth 2 (fn2-run-at-index-restart))))
                 (:instance fn2-run-read-stored-row-scalar (row (nth k rows)) (base (+ rb *fn2-run-reader-entry*))
                    (off (mv-nth 1 (fn2-run-skip 3 level (mod k 16) (mv-nth 1 (fn2-run-at-index-restart))
                                  slot gen rb pk ps pg (mv-nth 2 (fn2-run-at-index-restart)) pool)))
                    (end (fn2-run-directory rb (mv-nth 2 (fn2-run-at-index-restart))))
                    (f (mv-nth 2 (fn2-run-skip 3 level (mod k 16) (mv-nth 1 (fn2-run-at-index-restart))
                                  slot gen rb pk ps pg (mv-nth 2 (fn2-run-at-index-restart)) pool)))))
           :in-theory (e/d (fn2-run-nth fn2-run-readerp)
                    (fn2-run-stored-overview-page-p fn2-run-overview-page-rowsp fn2-run-overview-row-atp
                     fn2-run-layout-decode fn2-run-skip fn2-run-restart-offset fn2-run-directory
                     fn2-fields-value fn2-fields-rows fn2-fieldsp fn2-fields-wfp nth nthcdr floor mod len)))))
