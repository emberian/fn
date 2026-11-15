; Original actual function expressions before shared cleanup wrappers.
(defun fn2-succ-resolve (tx budget b0 fn2-succ-txns fn2-succ-slots fn2-id-decides fn2-run-installed fn2-run-cursors fn2-run-paths
                         fn2-run-cache fn2-fields fn2-pool)
 (declare (xargs :stobjs (fn2-succ-txns fn2-succ-slots fn2-id-decides fn2-run-installed fn2-run-cursors fn2-run-paths fn2-run-cache
                          fn2-fields fn2-pool) :guard t
  :guard-hints (("Goal" :in-theory (disable fn2-succ-resolve-step)))))
 (b* (((unless (and (fn2-succ-txns-wfp fn2-succ-txns) (fn2-succ-slots-wfp fn2-succ-slots) (fn2-id-decides-wfp fn2-id-decides)
                    (fn2-run-installed-wfp fn2-run-installed) (fn2-run-cursors-wfp fn2-run-cursors) (fn2-run-paths-wfp fn2-run-paths)
                    (fn2-run-cache-wfp fn2-run-cache) (fn2-fields-wfp fn2-fields) (fn2-pool-wfp fn2-pool)))
       (mv :state fn2-succ-txns fn2-succ-slots fn2-run-cursors fn2-run-paths fn2-fields))
      ((unless (and (natp tx) (< tx (fn2-succ-txns-rows fn2-succ-txns)) (< tx (fn2-id-decides-rows fn2-id-decides))
                    (natp budget) (<= budget 4096) (natp b0) (<= (+ b0 *fn2-idc-stride*) (fn2-fields-rows fn2-fields))))
       (mv :bounds fn2-succ-txns fn2-succ-slots fn2-run-cursors fn2-run-paths fn2-fields))
      ((unless (and (member (fn2-succ-txns-phase tx fn2-succ-txns) (list *fn2-succ-phase-open* *fn2-succ-phase-staged*))
                    (member (fn2-id-decides-phase tx fn2-id-decides)
                            (list *fn2-id-decide-phase-idle* *fn2-id-decide-phase-done*))))
       (mv :state fn2-succ-txns fn2-succ-slots fn2-run-cursors fn2-run-paths fn2-fields))
      (fn2-succ-txns (fn2-succ-txns-set-phase tx *fn2-succ-phase-open* fn2-succ-txns)))
  (fn2-succ-resolve-step tx budget b0 fn2-succ-txns fn2-succ-slots fn2-run-installed fn2-run-cursors fn2-run-paths fn2-run-cache fn2-fields fn2-pool)))

(defun fn2-succ-stage (tx b0 fn2-succ-txns fn2-succ-slots fn2-run-installed fn2-id-engine
                       fn2-overlays fn2-overlay-index fn2-fields fn2-pool)
 (declare (xargs :stobjs (fn2-succ-txns fn2-succ-slots fn2-run-installed fn2-id-engine
                          fn2-overlays fn2-overlay-index fn2-fields fn2-pool) :guard t
  :guard-hints (("Goal" :in-theory (disable fn2-succ-stage-slots fn2-succ-room fn2-idc-scratch fn2-idc-hold-spares
                                            fn2-overlays-rows fn2-overlay-index-rows)))))
 (b* (((unless (and (fn2-succ-txns-wfp fn2-succ-txns) (fn2-succ-slots-wfp fn2-succ-slots)
                    (fn2-run-installed-wfp fn2-run-installed) (fn2-id-engine-wfp fn2-id-engine)
                    (fn2-overlays-wfp fn2-overlays) (fn2-overlay-index-wfp fn2-overlay-index) (fn2-fields-wfp fn2-fields)
                    (fn2-pool-wfp fn2-pool) (< 0 (fn2-id-engine-rows fn2-id-engine))))
       (mv :state 0 fn2-succ-txns fn2-succ-slots fn2-id-engine fn2-overlays fn2-fields fn2-pool))
      ((unless (and (natp tx) (< tx (fn2-succ-txns-rows fn2-succ-txns)) (natp b0)))
       (mv :bounds 0 fn2-succ-txns fn2-succ-slots fn2-id-engine fn2-overlays fn2-fields fn2-pool))
      ((unless (and (member (fn2-succ-txns-phase tx fn2-succ-txns) (list *fn2-succ-phase-open* *fn2-succ-phase-staged*))
                    (<= *fn2-succ-slots* (nfix (fn2-succ-txns-ri tx fn2-succ-txns)))))
       (mv :state 0 fn2-succ-txns fn2-succ-slots fn2-id-engine fn2-overlays fn2-fields fn2-pool))
      (fn2-succ-txns (fn2-succ-txns-set-phase tx *fn2-succ-phase-open* fn2-succ-txns))
      ((mv code i fn2-succ-slots fn2-fields)
       (fn2-succ-stage-slots *fn2-succ-slots* 0 tx b0 fn2-succ-slots fn2-run-installed fn2-id-engine
                             fn2-overlays fn2-overlay-index fn2-fields fn2-pool))
      ((unless (eq code :ok)) (mv code i fn2-succ-txns fn2-succ-slots fn2-id-engine fn2-overlays fn2-fields fn2-pool))
      (orows (fn2-overlays-rows fn2-overlays))
      ((unless (posp orows)) (mv :state 0 fn2-succ-txns fn2-succ-slots fn2-id-engine fn2-overlays fn2-fields fn2-pool))
      ((mv code need) (fn2-succ-room *fn2-succ-slots* 0 tx (fn2-id-engine-arena 0 fn2-id-engine)
                                     (floor (fn2-overlay-index-rows fn2-overlay-index) orows) 0 fn2-succ-slots fn2-overlays))
      ((unless (eq code :ok)) (mv code 0 fn2-succ-txns fn2-succ-slots fn2-id-engine fn2-overlays fn2-fields fn2-pool))
      ((mv code fn2-id-engine fn2-pool) (fn2-idc-scratch fn2-id-engine fn2-pool))
      ((unless (eq code :ok)) (mv code 0 fn2-succ-txns fn2-succ-slots fn2-id-engine fn2-overlays fn2-fields fn2-pool))
      ((mv code fn2-overlays fn2-pool) (fn2-idc-hold-spares need need fn2-id-engine fn2-overlays fn2-overlay-index fn2-pool))
      ((unless (eq code :ok)) (mv code 0 fn2-succ-txns fn2-succ-slots fn2-id-engine fn2-overlays fn2-fields fn2-pool))
      (fn2-succ-txns (fn2-succ-txns-set-phase tx *fn2-succ-phase-staged* fn2-succ-txns)))
  (mv :ok 0 fn2-succ-txns fn2-succ-slots fn2-id-engine fn2-overlays fn2-fields fn2-pool)))
