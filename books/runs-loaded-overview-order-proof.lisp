; Loading the next overview row supplies the exact key and size used for
; admission and leaves the preceding writer key available for comparison.
(in-package "ACL2")
(include-book "runs-overview-write-read-proof")
(include-book "range-window-proof")

(local (defthm fn2-run-nfix-field-offset (implies (natp i) (equal (nfix i) i))))

(defthmd fn2-run-loaded-keys-and-field-count
  (let* ((load (fn2-run-load-values *fn2-overview-entry* row base slot gen off 9 0 1 f pool))
         (sf (mv-nth 2 load)))
    (implies (and (natp base) (natp off) (natp prev) (< (1+ prev) base))
             (and (equal (fn2-fields-rows sf) (fn2-fields-rows f))
                  (equal (fn2-overview-range-key-at base sf) (list (nfix (car row)) (nfix (cadr row))))
                  (equal (fn2-overview-range-key-at prev sf) (fn2-overview-range-key-at prev f)))))
  :hints (("Goal" :in-theory (e/d (fn2-run-load-values fn2-run-load-ref fn2-overview-range-key-at
                     fn2-fields-value fn2-fields-set-value update-fn2-fields-value$ai fn2-fields-rows
                     fn2-fields-set-ref-slot update-fn2-fields-ref-slot$ai fn2-fields-set-ref-gen update-fn2-fields-ref-gen$ai
                     fn2-fields-set-ref-off update-fn2-fields-ref-off$ai fn2-fields-set-ref-len update-fn2-fields-ref-len$ai
                     nth-update-nth) (nth update-nth nfix fn2-run-load-bytes)))))

(defthmd fn2-run-loaded-overview-wire-size
  (let* ((load (fn2-run-load-values *fn2-overview-entry* row base slot gen off 9 0 1 f pool))
         (sf (mv-nth 2 load)) (after (mv-nth 3 load)))
    (implies (and (fn2-run-values-layoutp *fn2-overview-entry* row) (natp base) (natp off)
                  (natp (fn2-pool-base slot pool)) (<= (+ off (len (nth 4 row))) cap)
                  (equal (fn2-layout-range-code slot gen off cap t 9 0 1 pool) :ok))
             (and (equal (car load) :ok) (equal (fn2-run-unload-values *fn2-overview-entry* base sf after) row)
                  (equal (fn2-run-layout-size 3 0 base sf) (len (fn2-layout-octets *fn2-overview-entry* row))))))
  :hints (("Goal" :use (fn2-run-load-overview-roundtrip fn2-run-overview-source-fields
                       (:instance fn2-run-overview-wire-size
                         (f (mv-nth 2 (fn2-run-load-values *fn2-overview-entry* row base slot gen off 9 0 1 f pool)))
                         (pool (mv-nth 3 (fn2-run-load-values *fn2-overview-entry* row base slot gen off 9 0 1 f pool)))))
           :in-theory (e/d (fn2-run-layout-size)
                          (fn2-run-load-values fn2-run-unload-values fn2-overview-entry-size fn2-run-values-layoutp
                           fn2-layout-octets fn2-fields-value fn2-fields-ref-slot fn2-fields-ref-gen fn2-fields-ref-off
                           fn2-fields-ref-len fn2-run-load-bytes fn2-pool-base fn2-layout-range-code nth)))))
