; Cursor advancement over the encoded entry at a checked page offset.
(in-package "ACL2")
(include-book "runs-seek-budget-proof")
(include-book "runs-overview-decode-proof")
(include-book "runs-page-scan-proof")
(include-book "runs-page-row-budget-proof")

(local
 (defthm fn2-run-readable-page-prefix
 (implies (and (natp off) (natp bound) (natp end) (<= off bound) (<= bound end)
               (eq (fn2-layout-range-code slot gen off end nil pk ps pg pool) :ok))
          (equal (fn2-layout-range-code slot gen off bound nil pk ps pg pool) :ok))
 :hints (("Goal" :in-theory
          (e/d (fn2-layout-range-code) (fn2-pool-readable-code fn2-pool-slot-base
                                         fn2-pool-slot-fill fn2-pool-capacity-bytes))))))

(defthm fn2-run-overview-page-row-boundary
 (let* ((indexp (and (integerp level) (< 0 level)))
        (layout (if indexp *fn2-overview-index* *fn2-overview-entry*))
        (bytes (fn2-layout-octets layout row))
        (bound (+ off (len bytes)))
        (read (fn2-run-layout-decode 3 level base slot gen off end pk ps pg f pool)))
   (implies (and (fn2-run-values-layoutp layout row) (natp base)
                 (<= (+ base (len layout)) (fn2-fields-rows f))
                 (unsigned-byte-p 32 off) (unsigned-byte-p 32 end) (<= bound end)
                 (fn2-poolp pool) (fn2-pool-wfp pool) (natp (fn2-pool-base slot pool))
                 (eq (fn2-layout-range-code slot gen off end nil pk ps pg pool) :ok)
                 (equal (fn2-run-read-bytes (len bytes) slot gen off pk ps pg pool) bytes))
            (and (equal (car read) :ok) (equal (mv-nth 1 read) bound))))
 :rule-classes nil
 :hints (("Goal" :cases ((and (integerp level) (< 0 level)))
          :use ((:instance fn2-run-overview-admission-fits-decoder
                   (layout (if (and (integerp level) (< 0 level)) *fn2-overview-index* *fn2-overview-entry*)))
                fn2-run-overview-page-decode-refines-layout
                (:instance fn2-run-readable-page-prefix
                   (bound (+ off (len (fn2-layout-octets
                       (if (and (integerp level) (< 0 level)) *fn2-overview-index* *fn2-overview-entry*) row)))))
                (:instance fn2-run-page-scan-consumes-admitted-row
                   (layout (if (and (integerp level) (< 0 level)) *fn2-overview-index* *fn2-overview-entry*))
                   (fuel *fn2-codec-decode-fuel*)
                   (f (if (and (integerp level) (< 0 level)) (fn2-overview-index-start base f)
                            (fn2-overview-entry-start base f)))))
          :in-theory (e/d (fn2-overview-entry-start fn2-overview-index-start)
                         (fn2-codec-save fn2-run-layout-decode fn2-layout-scan fn2-run-values-layoutp
                          fn2-layout-octets fn2-run-read-bytes fn2-poolp fn2-pool-wfp
                          fn2-pool-base fn2-layout-range-code fn2-fields-rows)))))

(defthm fn2-run-overview-cursor-consumes-page-row
 (let* ((base (+ rb *fn2-run-reader-entry*)) (path (fn2-run-path-row c 0))
        (end (fn2-run-directory rb f)) (bytes (fn2-layout-octets *fn2-overview-entry* row))
        (bound (+ off (len bytes)))
        (read (fn2-run-layout-decode 3 0 base slot gen off end pk ps pg f pool))
        (step (fn2-run-step-deliver c 3 idx off slot gen unit counter rb pk ps pg curs paths f pool))
        (after (mv-nth 1 step)))
  (implies (and (fn2-run-values-layoutp *fn2-overview-entry* row)
                (natp c) (< c (fn2-run-cursors-rows curs)) (< path (fn2-run-paths-rows paths))
                (natp idx) (< idx (fn2-run-paths-entries path paths)) (unsigned-byte-p 32 (1+ idx))
                (unsigned-byte-p 32 slot) (unsigned-byte-p 60 gen)
                (unsigned-byte-p 60 unit) (unsigned-byte-p 60 counter)
                (natp rb) (<= (+ base (len *fn2-overview-entry*)) (fn2-fields-rows f))
                (posp off) (unsigned-byte-p 32 end) (<= bound end)
                (fn2-poolp pool) (fn2-pool-wfp pool) (natp (fn2-pool-base slot pool))
                (eq (fn2-layout-range-code slot gen off end nil pk ps pg pool) :ok)
                (equal (fn2-run-read-bytes (len bytes) slot gen off pk ps pg pool) bytes))
           (and (equal (car step) :entry)
                (equal (fn2-run-cursors-phase c after) *fn2-run-cursor-phase-at*)
                (equal (fn2-run-cursors-idx c after) (1+ idx))
                (equal (fn2-run-cursors-off c after) bound)
                (equal (mv-nth 2 step) (mv-nth 2 read)))))
 :rule-classes nil
 :hints (("Goal" :use ((:instance fn2-run-overview-page-row-boundary
                         (level 0) (base (+ rb *fn2-run-reader-entry*)) (end (fn2-run-directory rb f))))
          :in-theory (e/d (fn2-run-step-deliver fn2-run-saved-cursor-position)
                          (fn2-run-layout-decode fn2-run-cursor-save fn2-run-nth fn2-run-path-row
                           fn2-run-paths-rows fn2-run-paths-entries fn2-run-directory fn2-run-cursors-rows
                           fn2-run-cursors-phase fn2-run-cursors-idx fn2-run-cursors-off
                           fn2-layout-range-code fn2-fields-rows fn2-poolp fn2-pool-wfp fn2-pool-base
                           fn2-layout-octets fn2-run-read-bytes fn2-run-values-layoutp)))))
