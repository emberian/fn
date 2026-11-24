; One unit of the actual page search compares the stored row to the query.
(in-package "ACL2")
(include-book "runs-overview-cursor-id-proof")
(include-book "range-window-proof")

(defun-nx fn2-run-overview-row-atp (level row base slot gen off end pk ps pg f pool)
 (let* ((indexp (and (integerp level) (< 0 level)))
        (layout (if indexp *fn2-overview-index* *fn2-overview-entry*))
        (bytes (fn2-layout-octets layout row))
        (bound (+ off (len bytes))))
   (and (fn2-run-values-layoutp layout row)
        (unsigned-byte-p 32 slot) (unsigned-byte-p 60 gen) (natp base)
        (<= (+ base (len layout)) (fn2-fields-rows f))
        (unsigned-byte-p 32 off) (unsigned-byte-p 32 end) (<= bound end)
        (fn2-poolp pool) (fn2-pool-wfp pool) (natp (fn2-pool-base slot pool))
        (eq (fn2-layout-range-code slot gen off end nil pk ps pg pool) :ok)
        (equal (fn2-run-read-bytes (len bytes) slot gen off pk ps pg pool) bytes))))

(local
 (defthm fn2-overview-order-of-key-pair
 (equal (fn2-run-key-order-spec *fn2-overview-range-key* (list (nth 0 row) (nth 1 row)) query)
        (fn2-run-key-order-spec *fn2-overview-range-key* row query))
 :hints (("Goal" :expand ((nth 0 row) (nth 1 row) (nth 0 (cdr row))) :in-theory (disable nfix)))))

(defthm fn2-run-overview-decoded-key-pair
 (let* ((read (fn2-run-layout-decode 3 level base slot gen off end pk ps pg f pool)) (after (mv-nth 2 read)))
  (implies (and (fn2-run-overview-row-atp level row base slot gen off end pk ps pg f pool)
                (natp qbase) (< (1+ qbase) base))
           (and (equal (fn2-overview-range-key-at base after) (list (nth 0 row) (nth 1 row)))
                (equal (fn2-overview-range-key-at qbase after) (fn2-overview-range-key-at qbase f)))))
 :rule-classes nil
 :hints (("Goal" :cases ((and (integerp level) (< 0 level)))
          :use ((:instance fn2-run-overview-page-row-id (j 0)) (:instance fn2-run-overview-page-row-id (j 1))
                (:instance fn2-run-overview-page-row-keeps-query (target qbase))
                (:instance fn2-run-overview-page-row-keeps-query (target (+ 1 qbase))))
          :in-theory (e/d (fn2-run-overview-row-atp fn2-overview-range-key-at)
                         (fn2-run-layout-decode fn2-fields-value fn2-run-values-layoutp unsigned-byte-p nth
                          fn2-layout-octets fn2-run-read-bytes fn2-poolp fn2-pool-wfp fn2-pool-base
                          fn2-layout-range-code fn2-fields-rows)))))

(defthm fn2-run-overview-page-key-order
 (let* ((read (fn2-run-layout-decode 3 level base slot gen off end pk ps pg f pool))
        (after (mv-nth 2 read)) (indexp (and (integerp level) (< 0 level)))
        (bytes (fn2-layout-octets (if indexp *fn2-overview-index* *fn2-overview-entry*) row)))
  (implies (and (fn2-run-overview-row-atp level row base slot gen off end pk ps pg f pool)
                (natp qbase) (< (1+ qbase) base))
           (and (equal (car read) :ok) (equal (mv-nth 1 read) (+ off (len bytes)))
                (equal (fn2-run-layout-compare 3 base qbase pk ps pg qk qs qg after pool)
                       (list :ok (fn2-run-key-order-spec *fn2-overview-range-key* row
                                                         (fn2-overview-range-key-at qbase f)))))))
 :rule-classes nil
 :hints (("Goal" :use (fn2-run-overview-page-row-boundary fn2-run-overview-decoded-key-pair)
          :in-theory (e/d (fn2-run-overview-row-atp)
                         (fn2-run-layout-compare fn2-run-layout-decode fn2-overview-range-key-at fn2-run-key-order-spec
                          fn2-fields-value fn2-run-values-layoutp unsigned-byte-p nth fn2-layout-octets
                          fn2-run-read-bytes fn2-poolp fn2-pool-wfp fn2-pool-base fn2-layout-range-code fn2-fields-rows)))))

(local
 (defthm fn2-run-empty-octets-have-zero-length
 (implies (fn-b3-octet-listp xs) (iff (equal (len xs) 0) (equal xs nil)))
 :hints (("Goal" :cases ((consp xs)) :expand ((len xs) (fn-b3-octet-listp xs))))))

(local
 (defthm fn2-run-overview-row-has-bytes
 (let ((layout (if indexp *fn2-overview-index* *fn2-overview-entry*)))
  (implies (fn2-run-values-layoutp layout row) (< 0 (len (fn2-layout-octets layout row)))))
 :rule-classes nil
 :hints (("Goal" :cases (indexp)
          :use ((:instance fn2-run-empty-octets-have-zero-length
                   (xs (fn2-layout-octets (if indexp *fn2-overview-index* *fn2-overview-entry*) row))))
          :in-theory (union-theories (theory 'minimal-theory)
                       '(fn2-run-values-layoutp (:type-prescription len) (:e fn2-layout-parse)
                         (:e mv-nth) (:e car) (:e equal) (:e <) (:e len) eq iff not))))))

(defthm fn2-run-overview-next-row-offset
 (let* ((indexp (and (integerp level) (< 0 level)))
        (wire (fn2-layout-octets (if indexp *fn2-overview-index* *fn2-overview-entry*) row))
        (next (+ off (len wire))))
  (implies (fn2-run-overview-row-atp level row base slot gen off end pk ps pg f pool)
           (and (natp next) (< off next) (<= next end))))
 :rule-classes nil
 :hints (("Goal" :use ((:instance fn2-run-overview-row-has-bytes (indexp (and (integerp level) (< 0 level)))))
          :in-theory (e/d (fn2-run-overview-row-atp)
                         (fn2-run-values-layoutp nth fn2-layout-octets fn2-run-read-bytes fn2-poolp
                          fn2-pool-wfp fn2-pool-base fn2-layout-range-code fn2-fields-rows)))))

(defthm fn2-run-overview-seek-first-row
 (let* ((base (+ rb *fn2-run-reader-entry*)) (end (fn2-run-directory rb f))
        (entries (fn2-run-header-value rb (+ *fn2-run-c-header-fields* *fn2-run-page-header-field-entries*) f))
        (layout (if (and (integerp level) (< 0 level)) *fn2-overview-index* *fn2-overview-entry*))
        (next (+ off (len (fn2-layout-octets layout row))))
        (order (fn2-run-key-order-spec *fn2-overview-range-key* row (fn2-overview-range-key-at qbase f)))
        (read (fn2-run-layout-decode 3 level base slot gen off end pk ps pg f pool))
        (seek (fn2-run-seek 3 level fuel lo hi idx off qbase rb slot gen pk ps pg qk qs qg f pool)))
  (implies (and (posp fuel) (natp rb) (posp off) (natp qbase) (< (1+ qbase) base)
                (natp lo) (natp hi) (<= hi lo) (natp idx) (natp entries) (< idx entries)
                (fn2-run-overview-row-atp level row base slot gen off end pk ps pg f pool))
           (equal seek (case order
                         (:eq (list :found lo hi idx off (mv-nth 2 read)))
                         (:gt (list :absent lo hi idx off (mv-nth 2 read)))
                         (otherwise (fn2-run-seek 3 level (1- fuel) lo hi (1+ idx) next
                                      qbase rb slot gen pk ps pg qk qs qg (mv-nth 2 read) pool))))))
 :rule-classes nil
 :hints (("Goal" :use ((:instance fn2-run-overview-page-key-order
                           (base (+ rb *fn2-run-reader-entry*)) (end (fn2-run-directory rb f)))
                       (:instance fn2-run-overview-next-row-offset
                           (base (+ rb *fn2-run-reader-entry*)) (end (fn2-run-directory rb f))))
          :expand ((fn2-run-seek 3 level fuel lo hi idx off qbase rb slot gen pk ps pg qk qs qg f pool))
          :in-theory (disable fn2-run-overview-row-atp fn2-run-layout-decode fn2-run-layout-compare
                              fn2-overview-layout-compare-keys fn2-run-key-order-spec fn2-overview-range-key-at
                              fn2-run-header-value fn2-run-directory fn2-layout-octets fn2-run-seek))))

(defthm fn2-run-overview-seek-one-row
 (let* ((base (+ rb *fn2-run-reader-entry*)) (end (fn2-run-directory rb f))
        (entries (fn2-run-header-value rb (+ *fn2-run-c-header-fields* *fn2-run-page-header-field-entries*) f))
        (layout (if (and (integerp level) (< 0 level)) *fn2-overview-index* *fn2-overview-entry*))
        (next (+ off (len (fn2-layout-octets layout row))))
        (order (fn2-run-key-order-spec *fn2-overview-range-key* row (fn2-overview-range-key-at qbase f)))
        (read (fn2-run-layout-decode 3 level base slot gen off end pk ps pg f pool))
        (seek (fn2-run-seek 3 level 1 lo hi idx off qbase rb slot gen pk ps pg qk qs qg f pool)))
  (implies (and (natp rb) (posp off) (natp qbase) (< (1+ qbase) base)
                (natp lo) (natp hi) (<= hi lo) (natp idx) (natp entries) (< idx entries)
                (fn2-run-overview-row-atp level row base slot gen off end pk ps pg f pool))
           (equal seek (case order
                         (:eq (list :found lo hi idx off (mv-nth 2 read)))
                         (:gt (list :absent lo hi idx off (mv-nth 2 read)))
                         (otherwise (list :more lo hi (1+ idx) next (mv-nth 2 read)))))))
 :rule-classes nil
 :hints (("Goal" :use ((:instance fn2-run-overview-page-key-order
                           (base (+ rb *fn2-run-reader-entry*)) (end (fn2-run-directory rb f)))
                       (:instance fn2-run-overview-next-row-offset
                           (base (+ rb *fn2-run-reader-entry*)) (end (fn2-run-directory rb f))))
          :expand ((fn2-run-seek 3 level 1 lo hi idx off qbase rb slot gen pk ps pg qk qs qg f pool)
                   (:free (idx off f) (fn2-run-seek 3 level 0 lo hi idx off qbase rb slot gen pk ps pg qk qs qg f pool)))
          :in-theory (disable fn2-run-overview-row-atp fn2-run-layout-decode fn2-run-layout-compare
                              fn2-overview-layout-compare-keys fn2-run-key-order-spec fn2-overview-range-key-at
                              fn2-run-header-value fn2-run-directory fn2-layout-octets fn2-run-seek))))

(defthm fn2-run-overview-seek-one-restart
 (let* ((base (+ rb *fn2-run-reader-entry*)) (end (fn2-run-directory rb f))
        (entries (fn2-run-header-value rb (+ *fn2-run-c-header-fields* *fn2-run-page-header-field-entries*) f))
        (mid (floor (+ lo hi) 2))
        (restart (fn2-run-restart-offset mid slot gen rb pk ps pg f pool))
        (at (mv-nth 1 restart)) (rf (mv-nth 2 restart))
        (order (fn2-run-key-order-spec *fn2-overview-range-key* row (fn2-overview-range-key-at qbase rf)))
        (read (fn2-run-layout-decode 3 level base slot gen at end pk ps pg rf pool))
        (seek (fn2-run-seek 3 level 1 lo hi idx off qbase rb slot gen pk ps pg qk qs qg f pool)))
  (implies (and (natp rb) (natp qbase) (< (1+ qbase) base) (natp lo) (natp hi) (< lo hi)
                (posp entries) (equal (car restart) :ok)
                (fn2-run-overview-row-atp level row base slot gen at end pk ps pg rf pool))
           (equal seek (list :more (if (eq order :lt) (1+ mid) lo) (if (eq order :lt) hi mid)
                             idx off (mv-nth 2 read)))))
 :rule-classes nil
 :hints (("Goal" :use ((:instance fn2-run-overview-page-key-order
                (base (+ rb *fn2-run-reader-entry*)) (end (fn2-run-directory rb f))
                (off (mv-nth 1 (fn2-run-restart-offset (floor (+ lo hi) 2) slot gen rb pk ps pg f pool)))
                (f (mv-nth 2 (fn2-run-restart-offset (floor (+ lo hi) 2) slot gen rb pk ps pg f pool)))))
          :expand ((fn2-run-seek 3 level 1 lo hi idx off qbase rb slot gen pk ps pg qk qs qg f pool)
                   (:free (lo hi f) (fn2-run-seek 3 level 0 lo hi idx off qbase rb slot gen pk ps pg qk qs qg f pool)))
          :in-theory (disable fn2-run-overview-row-atp fn2-run-layout-decode fn2-run-layout-compare
                              fn2-overview-layout-compare-keys fn2-run-key-order-spec fn2-overview-range-key-at
                              fn2-run-header-value fn2-run-directory fn2-run-restart-offset floor fn2-layout-octets fn2-run-seek))))
