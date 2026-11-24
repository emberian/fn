; The page decoder used by both overlay and run cursors delivers the
; complete overview row, including the line read by the range adapter.
(in-package "ACL2")
(include-book "runs-overview-scan-line-proof")
(include-book "range-page-search-proof")
(local (include-book "runs-page-row-budget-proof"))

(local
 (defthm fn2-range-saved-decoder-keeps-line
   (equal (fn2-run-line-at i (fn2-codec-save base phase pos v hi size ref payload next f) pool)
          (fn2-run-line-at i f pool))
   :hints (("Goal" :in-theory (e/d (fn2-codec-save fn2-run-line-at fn2-fields-ref-slot fn2-fields-ref-gen
                                    fn2-fields-ref-off fn2-fields-ref-len)
                                   (fn2-run-read-bytes nth update-nth unsigned-byte-p))))))

(local
 (defthm fn2-range-decoded-line-at-address
   (let* ((read (fn2-run-layout-decode 3 0 base slot gen off end 9 0 1 f pool))
          (bound (+ off (len (fn2-layout-octets *fn2-overview-entry* row)))))
     (implies (fn2-run-overview-row-atp 0 row base slot gen off end 9 0 1 f pool)
              (and (equal (car read) :ok) (equal (mv-nth 1 read) bound)
                   (equal (fn2-run-line-at (+ base 4) (mv-nth 2 read) pool) (nth 4 row)))))
   :rule-classes nil
   :hints (("Goal" :do-not '(preprocess)
            :use ((:instance fn2-run-overview-page-decode-refines-layout (level 0) (pk 9) (ps 0) (pg 1))
                  (:instance fn2-run-overview-admission-fits-decoder (layout *fn2-overview-entry*))
                  (:instance fn2-run-overview-scan-recovers-line (fuel *fn2-codec-decode-fuel*) (f (fn2-overview-entry-start base f))))
            :in-theory (e/d (fn2-run-overview-row-atp fn2-overview-entry-start)
                        (fn2-run-line-at fn2-run-layout-decode fn2-codec-save fn2-layout-scan fn2-layout-octets nth
                         fn2-fields-rows fn2-run-read-bytes fn2-run-values-layoutp fn2-layout-range-code
                         fn2-pool-wfp fn2-poolp fn2-pool-base unsigned-byte-p))))))

(local
 (defthm fn2-range-unload-five-fields
   (implies (natp base)
            (equal (fn2-run-unload-values *fn2-overview-entry* base f pool)
                   (list (fn2-fields-value base f) (fn2-fields-value (+ base 1) f)
                         (fn2-fields-value (+ base 2) f) (fn2-fields-value (+ base 3) f)
                         (fn2-run-line-at (+ base 4) f pool))))
   :hints (("Goal" :in-theory (e/d (fn2-run-line-at fn2-run-unload-values)
                         (fn2-fields-value fn2-fields-ref-slot fn2-fields-ref-gen fn2-fields-ref-off
                          fn2-fields-ref-len fn2-run-read-bytes))))))

(local
 (defthm fn2-range-take-admitted-fields
   (implies (true-listp x) (equal (take (len x) x) x))))

(local
 (defthm fn2-range-take-five-field-values
   (equal (take 5 row) (list (nth 0 row) (nth 1 row) (nth 2 row) (nth 3 row) (nth 4 row)))
   :hints (("Goal" :in-theory (enable take nth)
            :expand ((:free (x) (take 5 x)) (:free (x) (take 4 x)) (:free (x) (take 3 x))
                     (:free (x) (take 2 x)) (:free (x) (take 1 x))
                     (:free (x) (nth 4 x)) (:free (x) (nth 3 x)) (:free (x) (nth 2 x))
                     (:free (x) (nth 1 x)) (:free (x) (nth 0 x)))))))

(local
 (defthm fn2-range-reconstruct-five-fields
   (implies (and (true-listp row) (equal (len row) 5))
            (equal (list (nth 0 row) (nth 1 row) (nth 2 row) (nth 3 row) (nth 4 row)) row))
   :hints (("Goal" :use ((:instance fn2-range-take-admitted-fields (x row)))
            :in-theory (union-theories (theory 'minimal-theory) '(fn2-range-take-five-field-values))))))

(defthm fn2-range-unloads-stored-overview-row
  (let ((read (fn2-run-layout-decode 3 0 base slot gen off end 9 0 1 f pool)))
    (implies (fn2-run-overview-row-atp 0 row base slot gen off end 9 0 1 f pool)
             (and (equal (car read) :ok) (equal (mv-nth 1 read) (+ off (len (fn2-layout-octets *fn2-overview-entry* row))))
                  (equal (fn2-run-unload-values *fn2-overview-entry* base (mv-nth 2 read) pool) row))))
  :rule-classes nil
  :hints (("Goal" :do-not '(preprocess) :use (fn2-range-decoded-line-at-address
             (:instance fn2-run-overview-admitted-row (values row))
             (:instance fn2-run-overview-page-row-id (level 0) (pk 9) (ps 0) (pg 1) (j 0))
             (:instance fn2-run-overview-page-row-id (level 0) (pk 9) (ps 0) (pg 1) (j 1))
             (:instance fn2-run-overview-page-row-id (level 0) (pk 9) (ps 0) (pg 1) (j 2))
             (:instance fn2-run-overview-page-row-id (level 0) (pk 9) (ps 0) (pg 1) (j 3)))
           :in-theory (e/d (fn2-run-overview-row-atp)
                    (fn2-run-layout-decode fn2-run-unload-values fn2-run-line-at fn2-fields-value fn2-fields-rows
                     fn2-layout-octets fn2-run-read-bytes fn2-run-values-layoutp fn2-layout-range-code
                     fn2-pool-wfp fn2-poolp fn2-pool-base nth unsigned-byte-p)))))
