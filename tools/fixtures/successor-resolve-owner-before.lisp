(defun fn2-succ-resolve-raw (tx budget b0 fn2-succ-txns fn2-succ-slots fn2-id-decides fn2-run-installed fn2-run-cursors fn2-run-paths
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
(fn2-idc-fn-shape fn2-succ-resolve-raw (tx budget b0 fn2-succ-txns fn2-succ-slots fn2-id-decides fn2-run-installed fn2-run-cursors fn2-run-paths
                                    fn2-run-cache fn2-fields fn2-pool)
 (fn2-succ-txns fn2-succ-slots fn2-run-cursors fn2-run-paths fn2-fields)
 (fn2-succ-txns fn2-succ-slots fn2-id-decides fn2-run-installed fn2-run-cursors fn2-run-paths fn2-run-cache fn2-fields fn2-pool) t
 (fn2-succ-txns-phase fn2-id-decides-phase))
(defun fn2-succ-resolve (tx budget b0 fn2-succ-txns fn2-succ-slots fn2-id-decides fn2-run-installed fn2-run-cursors fn2-run-paths
                         fn2-run-cache fn2-fields fn2-pool)
 (declare (xargs :stobjs (fn2-succ-txns fn2-succ-slots fn2-id-decides fn2-run-installed fn2-run-cursors fn2-run-paths fn2-run-cache
                          fn2-fields fn2-pool) :guard t
                 :guard-hints (("Goal" :in-theory (disable fn2-succ-resolve-raw fn2-succ-clear-ref-rows fn2-fields-rows)))))
 (b* (((mv code fn2-succ-txns fn2-succ-slots fn2-run-cursors fn2-run-paths fn2-fields)
       (fn2-succ-resolve-raw tx budget b0 fn2-succ-txns fn2-succ-slots fn2-id-decides fn2-run-installed fn2-run-cursors fn2-run-paths
                             fn2-run-cache fn2-fields fn2-pool))
      (fn2-fields (if (and (eq code :ok) (fn2-fields-wfp fn2-fields) (natp b0)
                           (<= (+ b0 *fn2-idc-stride*) (fn2-fields-rows fn2-fields)))
                     (fn2-succ-clear-ref-rows *fn2-run-reader-fields* (+ b0 *fn2-idc-rb*) fn2-fields)
                   fn2-fields)))
  (mv code fn2-succ-txns fn2-succ-slots fn2-run-cursors fn2-run-paths fn2-fields)))
(fn2-idc-fn-shape fn2-succ-resolve (tx budget b0 fn2-succ-txns fn2-succ-slots fn2-id-decides fn2-run-installed fn2-run-cursors fn2-run-paths
                                    fn2-run-cache fn2-fields fn2-pool)
 (fn2-succ-txns fn2-succ-slots fn2-run-cursors fn2-run-paths fn2-fields)
 (fn2-succ-txns fn2-succ-slots fn2-id-decides fn2-run-installed fn2-run-cursors fn2-run-paths fn2-run-cache fn2-fields fn2-pool) t
 (fn2-succ-resolve-raw fn2-succ-clear-ref-rows fn2-fields-wfp fn2-fields-rows))
