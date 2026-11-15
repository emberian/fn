(defun fn2-seal-release (fn2-seals fn2-run-installed fn2-run-cache fn2-pool)
 (declare (xargs :stobjs (fn2-seals fn2-run-installed fn2-run-cache fn2-pool)
  :guard (and (fn2-seals-wfp fn2-seals) (fn2-run-installed-wfp fn2-run-installed) (fn2-run-cache-wfp fn2-run-cache) (fn2-pool-wfp fn2-pool))
  :guard-hints (("Goal" :in-theory (disable fn2-seal-retired-row fn2-run-cache-drop fn2-run-retired-next fn2-pool-release
                                            fn2-pool-release-countp fn2-seals-rows fn2-run-installed-rows fn2-seals-okind
                                            fn2-seals-oslot fn2-seals-ogen)))))
 (b* (((unless (< 0 (fn2-seals-rows fn2-seals))) (mv :bounds fn2-seals fn2-run-installed fn2-run-cache fn2-pool))
      (rows (fn2-run-installed-rows fn2-run-installed))
      (r (fn2-seal-retired-row rows 0 fn2-run-installed))
      ((unless (< r rows))
       (let ((fn2-seals (fn2-seals-set-phase 0 *fn2-seal-phase-idle* fn2-seals)))
        (mv :done fn2-seals fn2-run-installed fn2-run-cache fn2-pool)))
      ;; Physical roots have no resident-cache unit interval. Their catalog
      ;; promise and query leases must drain through summary retirement.
      ((when (= (fn2-run-installed-physical r fn2-run-installed) 1))
       (mv :cache fn2-seals fn2-run-installed fn2-run-cache fn2-pool))
      (u (fn2-run-installed-ufirst r fn2-run-installed))
      ((mv code fn2-run-cache fn2-pool)
       (if (<= (nfix u) (nfix (fn2-run-installed-ulast r fn2-run-installed)))
           (b* (((mv code slot gen fn2-run-cache) (fn2-run-cache-drop (nfix u) fn2-run-cache))
                ((unless (eq code :ok)) (mv (if (eq code :absent) :ok code) fn2-run-cache fn2-pool))
                ((unless (fn2-pool-release-countp slot fn2-pool)) (mv :bounds fn2-run-cache fn2-pool))
                ((mv code fn2-pool) (fn2-pool-release slot gen (fn2-seals-okind 0 fn2-seals) (fn2-seals-oslot 0 fn2-seals)
                                                      (fn2-seals-ogen 0 fn2-seals) fn2-pool)))
             (mv code fn2-run-cache fn2-pool))
         (mv :ok fn2-run-cache fn2-pool)))
      ((unless (eq code :ok)) (mv code fn2-seals fn2-run-installed fn2-run-cache fn2-pool))
      ((mv code fn2-run-installed) (fn2-run-retired-next r fn2-run-installed)))
  (mv (if (eq code :ok) :more code) fn2-seals fn2-run-installed fn2-run-cache fn2-pool)))
(fn2-seal-shape fn2-seal-release (fn2-seals fn2-run-installed fn2-run-cache fn2-pool)
 (fn2-seals fn2-run-installed fn2-run-cache fn2-pool) (fn2-seals fn2-run-installed fn2-run-cache fn2-pool) t
 (fn2-seal-retired-row fn2-run-cache-drop fn2-run-retired-next fn2-pool-release fn2-pool-release-countp fn2-seals-okind
  fn2-seals-oslot fn2-seals-ogen fn2-run-installed-ufirst fn2-run-installed-ulast))
