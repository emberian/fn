; An empty overview leaf with two disjoint workspaces consumes its
; pending row and stores its complete encoding on the next builder step.
(in-package "ACL2")
(include-book "range-page-capacity-proof")
(include-book "runs-builder-input-step-proof")
(include-book "runs-builder-open-page-proof")
(local (include-book "runs-overview-source-proof"))

(local
 (defthmd fn2-range-writable-part
   (implies (and (natp off) (natp end) (<= off end) (<= end 65536)
                 (equal (fn2-layout-range-code slot gen off 65536 t 9 0 1 p) :ok))
            (equal (fn2-layout-range-code slot gen off end t 9 0 1 p) :ok))
   :hints (("Goal" :in-theory (e/d (fn2-layout-range-code)
                         (fn2-pool-workspace-code fn2-pool-slot-fill fn2-pool-slot-cap fn2-pool-slot-base fn2-pool-capacity-bytes))))))

(defun-nx fn2-range-empty-leaf-input-p (src sg dst dg b w rs f p fc ctx)
  (and (equal (fn2-run-builds-phase 0 b) *fn2-run-build-phase-adding*) (equal (fn2-run-builds-height 0 b) 1)
       (equal (fn2-run-builds-wbase 0 b) 0) (equal (fn2-run-builds-crow 0 b) 0) (equal (fn2-run-builds-hbase 0 b) 136)
       (equal (fn2-run-builds-entries 0 b) 0) (equal (fn2-run-builds-schema 0 b) 3)
       (fn2-run-writerp 0 w rs f) (< 0 (fn2-fc-rows fc)) (< 0 (fn2-fc-context-rows ctx))
       (<= (+ *fn2-run-run-entry* *fn2-run-entry-rows*) (fn2-fields-rows f))
       (equal (fn2-run-writers-fields 0 w) 0) (equal (fn2-run-writers-limit 0 w) 2048)
       (fn2-run-empty-open-writer-p 0 3 0 dst dg 9 0 1 w)
       (fn2-run-open-overview-contents-p nil 0 0 0 *fn2-run-entries-base* dst dg rs p)
       (fn2-poolp p) (fn2-pool-wfp p) (natp src) (natp dst) (not (equal src dst))
       (natp (fn2-pool-base src p)) (natp (fn2-pool-base dst p))
       (<= (+ 65536 (fn2-pool-base src p)) (fn2-pool-base dst p))
       (equal (fn2-layout-range-code src sg 0 65536 t 9 0 1 p) :ok)
       (equal (fn2-layout-range-code dst dg *fn2-run-entries-base* 65536 t 9 0 1 p) :ok)))

(local (in-theory (disable fn2-run-builds-phase fn2-run-builds-height fn2-run-builds-wbase fn2-run-builds-crow fn2-run-builds-hbase
      fn2-run-builds-entries fn2-run-builds-schema fn2-run-writers-phase fn2-run-writers-entries fn2-run-writers-prev fn2-run-writers-pos
      fn2-run-writers-restarts fn2-run-writers-level fn2-run-writers-slot fn2-run-writers-gen fn2-run-writers-schema fn2-run-writers-cursor
      fn2-run-writers-fields fn2-run-writers-limit fn2-run-writers-okind fn2-run-writers-oslot fn2-run-writers-ogen fn2-run-writers-rows
      fn2-run-restarts-rows fn2-fields-rows fn2-run-writers-wfp fn2-run-restarts-wfp fn2-fields-wfp fn2-fc-rows fn2-fc-context-rows
      fn2-layout-range-code fn2-run-open-overview-contents-p fn2-run-values-layoutp fn2-layout-octets fn2-pool-base
      fn2-poolp fn2-pool-wfp fn2-run-key-order-spec fn2-overview-range-key-at fn2-run-pack-bound len nth)))

(local
 (defthmd fn2-range-empty-leaf-accepts-input
   (implies (and (fn2-range-empty-leaf-input-p src sg dst dg b w rs f p fc ctx) (fn2-run-values-layoutp *fn2-overview-entry* row))
            (and (fn2-run-build-awaits-input-p b w rs f fc ctx)
                 (fn2-run-next-overview-row-p nil row src sg 0 b w rs f p)
                 (car (fn2-run-leaf-packed-end row 0 w))))
   :hints (("Goal" :do-not '(preprocess)
            :expand ((fn2-run-scan 0 0 nil b w) (fn2-run-scan -1 0 nil b w))
            :use (fn2-run-admitted-line-fits-source fn2-range-empty-leaf-fits-admitted-row
                  (:instance fn2-run-overview-admission-fits-decoder (layout *fn2-overview-entry*))
                  (:instance fn2-range-writable-part (off 0) (end (len (nth 4 row))) (slot src) (gen sg))
                  (:instance fn2-range-writable-part (off *fn2-run-entries-base*)
                    (end (+ *fn2-run-entries-base* (len (fn2-layout-octets *fn2-overview-entry* row)))) (slot dst) (gen dg)))
            :in-theory (enable fn2-range-empty-leaf-input-p fn2-run-build-awaits-input-p fn2-run-next-overview-row-p fn2-run-writerp
                     fn2-run-overview-append-workspace-p fn2-run-empty-open-writer-p fn2-run-scan)))))

(defthmd fn2-range-empty-leaf-stores-first-row
  (let* ((step (fn2-run-run-onestep *fn2-overview-entry* (cons row tail) src sg 0 unit pages b curs paths cache w rs f p fc ctx b3 ds))
         (after (mv-nth 10 step)))
    (implies (and (fn2-range-empty-leaf-input-p src sg dst dg b w rs f p fc ctx)
                  (fn2-run-values-layoutp *fn2-overview-entry* row))
             (and (not (car step)) (equal (mv-nth 1 step) :more) (equal (mv-nth 2 step) tail)
                  (equal (mv-nth 3 step) (len (nth 4 row))) (equal (mv-nth 5 step) pages)
                  (fn2-run-open-overview-contents-p (list row) 0 (fn2-run-writers-entries 0 after)
                      (fn2-run-writers-restarts 0 after) (fn2-run-writers-cursor 0 after) dst dg (mv-nth 11 step) (mv-nth 13 step)))))
  :hints (("Goal" :do-not '(preprocess)
           :use (fn2-range-empty-leaf-accepts-input
                 (:instance fn2-run-idle-build-appends-fitting-overview (rows nil) (builds b) (writers w)
                    (restarts rs) (pool p) (at 0)))
           :in-theory (e/d (fn2-range-empty-leaf-input-p fn2-run-empty-open-writer-p)
                    (fn2-run-writerp fn2-run-build-awaits-input-p fn2-run-next-overview-row-p fn2-run-run-onestep)))))
