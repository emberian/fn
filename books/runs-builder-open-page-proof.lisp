; A fresh page supplied by the range builder starts with an empty row
; body, an empty restart list, and a writable tail following both headers.
(in-package "ACL2")
(include-book "runs-open-workspace-proof")
(include-book "runs-builder-page-contents-proof")

(defun-nx fn2-run-empty-open-writer-p (w sid level slot gen pk ps pg writers)
  (and (equal (fn2-run-writers-phase w writers) *fn2-run-writer-phase-open*)
       (equal (fn2-run-writers-schema w writers) sid) (equal (fn2-run-writers-level w writers) level)
       (equal (fn2-run-writers-prev w writers) 0) (equal (fn2-run-writers-pos w writers) 0)
       (equal (fn2-run-writers-entries w writers) 0) (equal (fn2-run-writers-restarts w writers) 0)
       (equal (fn2-run-writers-cursor w writers) *fn2-run-entries-base*)
       (equal (fn2-run-writers-slot w writers) slot) (equal (fn2-run-writers-gen w writers) gen)
       (equal (fn2-run-writers-okind w writers) pk) (equal (fn2-run-writers-oslot w writers) ps)
       (equal (fn2-run-writers-ogen w writers) pg)))

(local
 (defthm fn2-run-initial-page-metadata
   (let ((after (fn2-run-writers-put w (phase *fn2-run-writer-phase-open*) (schema sid) (schema-version version)
          (level level) (run run) (ordinal ordinal) (page-kind page-kind) (slot slot) (gen gen)
          (cursor *fn2-run-entries-base*) (entries 0) (restarts 0) (pos 0) (prev 0) (fields fields) (limit limit)
          (unit unit) (epoch epoch) (counter counter) (history history) (incarnation incarnation)
          (okind pk) (oslot ps) (ogen pg))))
     (implies (natp w)
              (and (fn2-run-empty-open-writer-p w sid level slot gen pk ps pg after)
                   (equal (fn2-run-writers-fields w after) fields) (equal (fn2-run-writers-limit w after) limit))))
   :hints (("Goal" :in-theory (e/d (fn2-run-empty-open-writer-p nth-update-nth)
                                   (nth update-nth))))))

(defthmd fn2-run-open-establishes-empty-page
  (let* ((open (fn2-run-open w slot gen sid version level run ordinal page-kind unit epoch counter history incarnation
                             pk ps pg fields limit writers pool)) (after (mv-nth 2 open)))
    (implies (and (natp w) (equal (fn2-run-writers-phase w writers) *fn2-run-writer-phase-idle*)
                  (unsigned-byte-p 32 slot) (unsigned-byte-p 60 gen) (unsigned-byte-p 60 sid)
                  (unsigned-byte-p 8 version) (unsigned-byte-p 8 level) (unsigned-byte-p 60 run)
                  (unsigned-byte-p 60 ordinal) (unsigned-byte-p 8 page-kind) (unsigned-byte-p 60 unit)
                  (unsigned-byte-p 60 epoch) (unsigned-byte-p 60 counter) (unsigned-byte-p 60 history)
                  (unsigned-byte-p 60 incarnation) (unsigned-byte-p 8 pk) (unsigned-byte-p 32 ps) (unsigned-byte-p 60 pg)
                  (unsigned-byte-p 32 fields) (unsigned-byte-p 32 limit)
                  (<= (+ *fn2-run-entries-base* *fn2-run-min-fill*) limit) (<= limit *fn2-run-page-size*)
                  (natp (fn2-pool-base slot pool)) (natp (fn2-pool-slot-cap slot pool))
                  (equal (fn2-layout-range-code slot gen 0 *fn2-run-page-size* t pk ps pg pool) :ok))
             (and (equal (car open) :ok)
                  (fn2-run-empty-open-writer-p w sid level slot gen pk ps pg (mv-nth 1 open))
                  (equal (fn2-run-writers-fields w (mv-nth 1 open)) fields) (equal (fn2-run-writers-limit w (mv-nth 1 open)) limit)
                  (equal (fn2-pool-base slot after) (fn2-pool-base slot pool))
                  (equal (fn2-layout-range-code slot gen *fn2-run-entries-base* *fn2-run-page-size* t pk ps pg after) :ok))))
  :hints (("Goal" :use (fn2-run-reset-writable-page fn2-run-reserves-page-header-space)
           :in-theory (e/d (fn2-run-open) (fn2-run-empty-open-writer-p fn2-run-writers-fields fn2-run-writers-limit fn2-pool-reset fn2-run-zero
                   unsigned-byte-p fn2-pool-slot-cap fn2-pool-rows fn2-pool-base fn2-run-writers-phase fn2-layout-range-code)))))

(defthmd fn2-run-build-opens-empty-overview-page
  (let* ((w (+ level (fn2-run-builds-wbase 0 builds)))
         (open (fn2-run-build-page 0 level slot gen unit 2 unit builds writers pool))
         (after (mv-nth 2 open)) (p (mv-nth 3 open)))
    (implies (and (fn2-run-buildsp builds) (fn2-run-builds-wfp builds) (< 0 (fn2-run-builds-rows builds))
                  (fn2-run-writersp writers) (fn2-run-writers-wfp writers) (< w (fn2-run-writers-rows writers))
                  (natp level) (< level *fn2-run-max-levels*) (< level (fn2-run-builds-height 0 builds))
                  (equal (fn2-run-writers-phase w writers) *fn2-run-writer-phase-idle*)
                  (equal (fn2-run-builds-schema 0 builds) 3) (equal (fn2-run-builds-fields 0 builds) 0)
                  (equal (fn2-run-builds-limit 0 builds) 2048)
                  (equal (fn2-run-builds-okind 0 builds) 9) (equal (fn2-run-builds-oslot 0 builds) 0) (equal (fn2-run-builds-ogen 0 builds) 1)
                  (unsigned-byte-p 32 slot) (unsigned-byte-p 60 gen) (unsigned-byte-p 60 unit)
                  (natp (fn2-pool-base slot pool)) (natp (fn2-pool-slot-cap slot pool))
                  (equal (fn2-layout-range-code slot gen 0 *fn2-run-page-size* t 9 0 1 pool) :ok))
             (and (equal (car open) :ok) (equal (mv-nth 1 open) builds)
                  (fn2-run-empty-open-writer-p w 3 level slot gen 9 0 1 after)
                  (equal (fn2-run-writers-fields w after) (* level *fn2-run-writer-fields*))
                  (equal (fn2-run-writers-limit w after) 2048)
                  (fn2-run-open-overview-contents-p nil w (fn2-run-writers-entries w after) (fn2-run-writers-restarts w after)
                     (fn2-run-writers-cursor w after) slot gen restarts p)
                  (equal (fn2-pool-base slot p) (fn2-pool-base slot pool))
                  (equal (fn2-layout-range-code slot gen *fn2-run-entries-base* *fn2-run-page-size* t 9 0 1 p) :ok))))
  :hints (("Goal" :do-not '(preprocess)
           :use ((:instance fn2-run-open-establishes-empty-page
                     (w (+ level (fn2-run-builds-wbase 0 builds))) (sid 3) (version 1) (run (fn2-run-builds-run 0 builds))
                     (ordinal (fn2-run-writers-ordinal (+ level (fn2-run-builds-wbase 0 builds)) writers))
                     (page-kind (if (zp level) *page-kind-run-data* *page-kind-run-index*))
                     (epoch 2) (counter unit) (history (fn2-run-builds-history 0 builds))
                     (incarnation (fn2-run-builds-incarnation 0 builds)) (pk 9) (ps 0) (pg 1)
                     (fields (* level *fn2-run-writer-fields*)) (limit 2048)))
           :in-theory (e/d (fn2-run-build-page fn2-run-build-page-kind fn2-run-empty-open-writer-p fn2-run-open-overview-contents-p)
                     (fn2-run-open fn2-run-builds-wbase fn2-run-builds-fields fn2-run-builds-limit fn2-run-builds-rows fn2-run-builds-height
                      fn2-run-builds-schema fn2-run-builds-run fn2-run-builds-history fn2-run-builds-incarnation
                      fn2-run-builds-okind fn2-run-builds-oslot fn2-run-builds-ogen fn2-run-buildsp fn2-run-builds-wfp
                      fn2-run-writers-phase fn2-run-writers-rows fn2-run-writers-schema fn2-run-writers-ordinal fn2-run-writers-slot
                      fn2-run-writers-gen fn2-run-writers-okind fn2-run-writers-oslot fn2-run-writers-ogen fn2-run-writers-level
                      fn2-run-writers-cursor fn2-run-writers-entries fn2-run-writers-restarts fn2-run-writers-prev fn2-run-writers-pos
                      fn2-run-writersp fn2-run-writers-wfp fn2-run-writers-fields fn2-run-writers-limit fn2-layout-range-code fn2-pool-slot-cap fn2-pool-base)))))
