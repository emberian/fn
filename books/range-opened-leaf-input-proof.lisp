; Opening a first leaf establishes the input for its first append.
(in-package "ACL2")
(include-book "range-empty-leaf-append-proof")
(include-book "range-open-page-input-proof")

(defthmd fn2-range-opening-first-leaf-prepares-append
  (let* ((r (fn2-run-build-page 0 0 dst dg unit 2 unit b w p))
         (b2 (mv-nth 1 r)) (w2 (mv-nth 2 r)) (p2 (mv-nth 3 r)))
    (implies (and (fn2-run-buildsp b) (fn2-run-builds-wfp b) (< 0 (fn2-run-builds-rows b))
                  (equal (fn2-run-builds-phase 0 b) *fn2-run-build-phase-adding*) (equal (fn2-run-builds-height 0 b) 1)
                  (equal (fn2-run-builds-wbase 0 b) 0) (equal (fn2-run-builds-crow 0 b) 0) (equal (fn2-run-builds-hbase 0 b) 136)
                  (equal (fn2-run-builds-entries 0 b) 0) (equal (fn2-run-builds-schema 0 b) 3)
                  (equal (fn2-run-builds-fields 0 b) 0) (equal (fn2-run-builds-limit 0 b) 2048)
                  (equal (fn2-run-builds-okind 0 b) 9) (equal (fn2-run-builds-oslot 0 b) 0) (equal (fn2-run-builds-ogen 0 b) 1)
                  (fn2-run-writersp w) (fn2-run-writers-wfp w) (<= *fn2-run-max-levels* (fn2-run-writers-rows w))
                  (equal (fn2-run-writers-phase 0 w) *fn2-run-writer-phase-idle*)
                  (fn2-run-restarts-wfp rs) (<= *fn2-run-restart-capacity* (fn2-run-restarts-rows rs))
                  (fn2-fields-wfp f) (<= (+ *fn2-run-run-entry* *fn2-run-entry-rows*) (fn2-fields-rows f))
                  (< 0 (fn2-fc-rows fc)) (< 0 (fn2-fc-context-rows ctx))
                  (fn2-poolp p) (fn2-pool-wfp p) (natp src) (natp dst) (not (equal src dst))
                  (unsigned-byte-p 32 dst) (unsigned-byte-p 60 dg) (unsigned-byte-p 60 unit)
                  (natp (fn2-pool-slot-cap dst p)) (natp (fn2-pool-base src p)) (natp (fn2-pool-base dst p))
                  (<= (+ 65536 (fn2-pool-base src p)) (fn2-pool-base dst p))
                  (equal (fn2-layout-range-code src sg 0 65536 t 9 0 1 p) :ok)
                  (equal (fn2-layout-range-code dst dg 0 65536 t 9 0 1 p) :ok))
             (and (equal (car r) :ok) (fn2-range-empty-leaf-input-p src sg dst dg b2 w2 rs f p2 fc ctx))))
  :hints (("Goal" :do-not '(preprocess)
           :use ((:instance fn2-run-build-opens-empty-overview-page (builds b) (writers w)
                    (slot dst) (gen dg) (level 0) (restarts rs) (pool p))
                 (:instance fn2-range-builder-page-keeps-input-slot (b 0) (builds b) (writers w) (pool p) (level 0)
                    (at 0) (cap 65536) (epoch 2) (counter unit) (j src)))
           :in-theory (e/d (fn2-range-empty-leaf-input-p fn2-run-writerp fn2-run-buildp fn2-run-empty-open-writer-p)
              (fn2-run-open-overview-contents-p fn2-run-build-page fn2-run-buildsp fn2-run-builds-wfp fn2-run-builds-rows
               fn2-run-builds-phase fn2-run-builds-height fn2-run-builds-wbase fn2-run-builds-crow fn2-run-builds-hbase
               fn2-run-builds-entries fn2-run-builds-schema fn2-run-builds-fields fn2-run-builds-limit fn2-run-builds-okind
               fn2-run-builds-oslot fn2-run-builds-ogen fn2-run-writersp fn2-run-writers-wfp fn2-run-writers-rows
               fn2-run-writers-phase fn2-run-writers-schema fn2-run-writers-level fn2-run-writers-prev fn2-run-writers-pos
               fn2-run-writers-entries fn2-run-writers-restarts fn2-run-writers-cursor fn2-run-writers-slot fn2-run-writers-gen
               fn2-run-writers-okind fn2-run-writers-oslot fn2-run-writers-ogen fn2-run-writers-fields fn2-run-writers-limit
               fn2-fc-rows fn2-fc-context-rows fn2-poolp fn2-pool-wfp fn2-pool-base fn2-pool-slot-cap fn2-layout-range-code
               fn2-fields-wfp fn2-fields-rows fn2-run-restarts-wfp fn2-run-restarts-rows unsigned-byte-p)))))
