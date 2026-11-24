; The group, number, article and position delivered from a stored overview row.
(in-package "ACL2")
(include-book "runs-overview-cursor-proof")
(local (include-book "runs-page-id-proof"))
(local (include-book "runs-layout-id-proof"))

(local
 (defthm fn2-run-field-value-after-codec-save
 (equal (fn2-fields-value i (fn2-codec-save base phase pos v hi size ref payload next f))
        (fn2-fields-value i f))
 :hints (("Goal" :in-theory (e/d (fn2-codec-save fn2-fields-value) (nth update-nth unsigned-byte-p))))))

(local
 (defthm fn2-run-overview-id-fits-field
 (let ((layout (if indexp *fn2-overview-index* *fn2-overview-entry*)))
  (implies (and (fn2-run-values-layoutp layout row) (natp j) (< j (if indexp 2 4)))
           (and (fn2-run-scalar-prefixp j layout) (unsigned-byte-p 60 (nth j row)))))
 :rule-classes nil
 :hints (("Goal" :cases ((equal j 0) (equal j 1) (equal j 2) (equal j 3))
          :do-not '(preprocess)
          :use ((:instance fn2-run-layout-id-width
                  (layout (if indexp *fn2-overview-index* *fn2-overview-entry*))
                  (i j) (values row)
                  (id (cadr (cadr (nth j (if indexp *fn2-overview-index* *fn2-overview-entry*)))))))
          :in-theory (disable fn2-run-values-layoutp unsigned-byte-p nth)))))

(local
 (defthm fn2-run-overview-scan-row-id
 (let* ((indexp (and (integerp level) (< 0 level)))
        (layout (if indexp *fn2-overview-index* *fn2-overview-entry*))
        (bytes (fn2-layout-octets layout row))
        (bound (+ off (len bytes)))
        (scan (fn2-layout-scan layout *fn2-codec-decode-fuel* base 0 0 0 0 0 0 off slot gen end pk ps pg f pool)))
   (implies (and (fn2-run-values-layoutp layout row) (natp j) (< j (if indexp 2 4))
                 (unsigned-byte-p 32 slot) (unsigned-byte-p 60 gen) (natp base)
                 (<= (+ base (len layout)) (fn2-fields-rows f))
                 (unsigned-byte-p 32 off) (unsigned-byte-p 32 end) (<= bound end)
                 (fn2-poolp pool) (fn2-pool-wfp pool) (natp (fn2-pool-base slot pool))
                 (eq (fn2-layout-range-code slot gen off end nil pk ps pg pool) :ok)
                 (equal (fn2-run-read-bytes (len bytes) slot gen off pk ps pg pool) bytes))
            (and (equal (car scan) :ok) (equal (fn2-fields-value (+ base j) (mv-nth 9 scan)) (nth j row)))))
 :rule-classes nil
 :hints (("Goal" :use ((:instance fn2-run-overview-id-fits-field (indexp (and (integerp level) (< 0 level))))
              (:instance fn2-run-overview-admission-fits-decoder (layout (if (and (integerp level) (< 0 level)) *fn2-overview-index* *fn2-overview-entry*)))
              (:instance fn2-run-readable-page-prefix (bound (+ off (len (fn2-layout-octets (if (and (integerp level) (< 0 level)) *fn2-overview-index* *fn2-overview-entry*) row)))))
              (:instance fn2-run-page-scan-returns-source-scalar (layout (if (and (integerp level) (< 0 level)) *fn2-overview-index* *fn2-overview-entry*)) (fuel *fn2-codec-decode-fuel*))
              (:instance fn2-run-page-scan-consumes-admitted-row (layout (if (and (integerp level) (< 0 level)) *fn2-overview-index* *fn2-overview-entry*)) (fuel *fn2-codec-decode-fuel*)))
          :cases ((and (integerp level) (< 0 level)))
          :in-theory (disable fn2-fields-value nth fn2-run-values-layoutp fn2-run-scalar-prefixp fn2-layout-octets fn2-layout-scan fn2-run-read-bytes fn2-layout-range-code fn2-poolp fn2-pool-wfp fn2-pool-base fn2-fields-rows)))))

(defthm fn2-run-overview-page-row-id
 (let* ((indexp (and (integerp level) (< 0 level)))
        (layout (if indexp *fn2-overview-index* *fn2-overview-entry*))
        (bytes (fn2-layout-octets layout row))
        (bound (+ off (len bytes)))
        (read (fn2-run-layout-decode 3 level base slot gen off end pk ps pg f pool)))
   (implies (and (fn2-run-values-layoutp layout row) (natp j) (< j (if indexp 2 4))
                 (unsigned-byte-p 32 slot) (unsigned-byte-p 60 gen) (natp base)
                 (<= (+ base (len layout)) (fn2-fields-rows f))
                 (unsigned-byte-p 32 off) (unsigned-byte-p 32 end) (<= bound end)
                 (fn2-poolp pool) (fn2-pool-wfp pool) (natp (fn2-pool-base slot pool))
                 (eq (fn2-layout-range-code slot gen off end nil pk ps pg pool) :ok)
                 (equal (fn2-run-read-bytes (len bytes) slot gen off pk ps pg pool) bytes))
            (equal (fn2-fields-value (+ base j) (mv-nth 2 read)) (nth j row))))
 :rule-classes nil
 :hints (("Goal" :cases ((and (integerp level) (< 0 level)))
          :use (fn2-run-overview-page-decode-refines-layout
                (:instance fn2-run-overview-scan-row-id
                 (f (if (and (integerp level) (< 0 level)) (fn2-overview-index-start base f)
                       (fn2-overview-entry-start base f)))))
          :in-theory (e/d (fn2-overview-entry-start fn2-overview-index-start)
                         (fn2-codec-save fn2-run-layout-decode fn2-layout-scan fn2-run-values-layoutp
                          unsigned-byte-p nth fn2-fields-value fn2-layout-octets fn2-run-read-bytes
                          fn2-poolp fn2-pool-wfp fn2-pool-base fn2-layout-range-code fn2-fields-rows)))))

(defthm fn2-run-overview-cursor-supplies-source-id
 (let* ((base (+ rb *fn2-run-reader-entry*)) (path (fn2-run-path-row c 0))
        (end (fn2-run-directory rb f)) (bytes (fn2-layout-octets *fn2-overview-entry* row))
        (bound (+ off (len bytes)))
        (step (fn2-run-step-deliver c 3 idx off slot gen unit counter rb pk ps pg curs paths f pool))
        (after (mv-nth 1 step)))
  (implies (and (fn2-run-values-layoutp *fn2-overview-entry* row)
                (natp j) (< j 4) (natp c) (< c (fn2-run-cursors-rows curs)) (< path (fn2-run-paths-rows paths))
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
                (equal (fn2-fields-value (+ base j) (mv-nth 2 step)) (nth j row)))))
 :rule-classes nil
 :hints (("Goal" :use (fn2-run-overview-cursor-consumes-page-row
                 (:instance fn2-run-overview-page-row-id (level 0)
                    (base (+ rb *fn2-run-reader-entry*)) (end (fn2-run-directory rb f))))
          :in-theory (disable fn2-run-layout-decode fn2-run-step-deliver fn2-run-path-row fn2-run-directory
                      fn2-fields-value nth fn2-run-cursors-rows fn2-run-paths-rows
                      fn2-run-paths-entries fn2-fields-rows fn2-run-cursors-phase fn2-run-cursors-idx
                      fn2-run-cursors-off fn2-layout-range-code fn2-layout-octets fn2-run-read-bytes
                      fn2-run-values-layoutp fn2-pool-base fn2-poolp fn2-pool-wfp))))

(defthm fn2-run-overview-page-row-keeps-query
 (let* ((indexp (and (integerp level) (< 0 level)))
        (layout (if indexp *fn2-overview-index* *fn2-overview-entry*))
        (bytes (fn2-layout-octets layout row))
        (bound (+ off (len bytes)))
        (read (fn2-run-layout-decode 3 level base slot gen off end pk ps pg f pool)))
   (implies (and (fn2-run-values-layoutp layout row) (natp target) (< target base)
                 (unsigned-byte-p 32 slot) (unsigned-byte-p 60 gen) (natp base)
                 (<= (+ base (len layout)) (fn2-fields-rows f))
                 (unsigned-byte-p 32 off) (unsigned-byte-p 32 end) (<= bound end)
                 (fn2-poolp pool) (fn2-pool-wfp pool) (natp (fn2-pool-base slot pool))
                 (eq (fn2-layout-range-code slot gen off end nil pk ps pg pool) :ok)
                 (equal (fn2-run-read-bytes (len bytes) slot gen off pk ps pg pool) bytes))
            (equal (fn2-fields-value target (mv-nth 2 read)) (fn2-fields-value target f))))
 :rule-classes nil
 :hints (("Goal" :cases ((and (integerp level) (< 0 level)))
          :use (fn2-run-overview-page-decode-refines-layout
                (:instance fn2-run-overview-scan-row-id (j 0)
                 (f (if (and (integerp level) (< 0 level)) (fn2-overview-index-start base f)
                       (fn2-overview-entry-start base f)))))
          :in-theory (e/d (fn2-overview-entry-start fn2-overview-index-start)
                         (fn2-codec-save fn2-run-layout-decode fn2-layout-scan fn2-run-values-layoutp
                          unsigned-byte-p nth fn2-fields-value fn2-layout-octets fn2-run-read-bytes
                          fn2-poolp fn2-pool-wfp fn2-pool-base fn2-layout-range-code fn2-fields-rows)))))
