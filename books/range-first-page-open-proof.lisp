; Given the page returned by the first reservation, the actual first
; builder step opens an empty overview leaf and retries the pending row.
(in-package "ACL2")
(include-book "range-initial-writer-proof")
(include-book "runs-builder-open-page-proof")

(local
 (defthmd fn2-range-height-one-opens-first-leaf
   (let* ((b1 (fn2-run-builds-set-height 0 1 b))
          (page (fn2-run-build-page 0 0 dst dg unit 2 unit b1 w p)) (w2 (mv-nth 2 page)) (p2 (mv-nth 3 page)))
     (implies (and (fn2-range-empty-build-state-p run b) (fn2-run-buildsp b) (fn2-run-builds-wfp b)
                   (< 0 (fn2-run-builds-rows b)) (fn2-run-writersp w) (fn2-run-writers-wfp w)
                   (< 0 (fn2-run-writers-rows w)) (equal (fn2-run-writers-phase 0 w) *fn2-run-writer-phase-idle*)
                   (unsigned-byte-p 32 dst) (unsigned-byte-p 60 dg) (unsigned-byte-p 60 unit)
                   (natp (fn2-pool-base dst p)) (natp (fn2-pool-slot-cap dst p))
                   (equal (fn2-layout-range-code dst dg 0 *fn2-run-page-size* t 9 0 1 p) :ok))
              (and (equal (car page) :ok) (equal (mv-nth 1 page) b1)
                   (fn2-run-empty-open-writer-p 0 3 0 dst dg 9 0 1 w2)
                   (equal (fn2-run-writers-fields 0 w2) 0) (equal (fn2-run-writers-limit 0 w2) 2048)
                   (fn2-run-open-overview-contents-p nil 0 (fn2-run-writers-entries 0 w2) (fn2-run-writers-restarts 0 w2)
                           (fn2-run-writers-cursor 0 w2) dst dg rs p2)
                   (equal (fn2-layout-range-code dst dg *fn2-run-entries-base* *fn2-run-page-size* t 9 0 1 p2) :ok))))
   :hints (("Goal" :do-not '(preprocess)
            :use ((:instance fn2-run-build-opens-empty-overview-page (builds (fn2-run-builds-set-height 0 1 b))
                    (level 0) (slot dst) (gen dg) (writers w) (restarts rs) (pool p)))
            :in-theory (e/d (fn2-range-empty-build-state-p fn2-run-builds-height fn2-run-builds-wbase fn2-run-builds-schema
                      fn2-run-builds-fields fn2-run-builds-limit fn2-run-builds-okind fn2-run-builds-oslot fn2-run-builds-ogen
                      fn2-run-builds-rows nth-update-nth)
                      (fn2-run-build-page fn2-run-builds-set-height fn2-run-empty-open-writer-p fn2-run-open-overview-contents-p
                       fn2-run-buildsp fn2-run-builds-wfp fn2-run-writersp fn2-run-writers-wfp fn2-run-writers-rows
                       fn2-run-writers-phase fn2-run-writers-fields fn2-run-writers-entries fn2-run-writers-restarts
                       fn2-run-writers-cursor fn2-run-writers-limit fn2-pool-base fn2-pool-slot-cap fn2-layout-range-code
                       fn2-run-builds-phase fn2-run-builds-run fn2-run-builds-entries fn2-run-builds-pages fn2-run-builds-crow
                       fn2-run-builds-hbase unsigned-byte-p nth update-nth))))))

(defmacro fn2-range-pending-leaf ()
  '(fn2-pool-reserve 0 9 0 1 (mv-nth 3 (fn2-run-load-values *fn2-overview-entry* row *fn2-run-run-entry* src sg 0 9 0 1 f p))))

(defthmd fn2-range-first-step-opens-overview-leaf
  (fn2-range-first-leaf-bindings
   (let ((dst (mv-nth 1 reserve)) (dg (mv-nth 2 reserve)) (p0 (mv-nth 3 reserve)) (w2 (mv-nth 10 step)) (p2 (mv-nth 13 step)))
     (implies (and (fn2-range-empty-build-state-p run b) (fn2-run-buildsp b) (fn2-run-builds-wfp b) (< 0 (fn2-run-builds-rows b))
                   (fn2-run-writersp w) (fn2-run-writers-wfp w) (< 0 (fn2-run-writers-rows w))
                   (equal (fn2-run-writers-phase 0 w) *fn2-run-writer-phase-idle*) (fn2-run-writerp 0 w rs f)
                   (< 0 (fn2-fc-rows fc)) (< 0 (fn2-fc-context-rows ctx))
                   (equal (car load) :ok) (equal (car reserve) :ok)
                   (unsigned-byte-p 32 dst) (unsigned-byte-p 60 dg) (unsigned-byte-p 60 unit)
                   (natp (fn2-pool-base dst p0)) (natp (fn2-pool-slot-cap dst p0))
                   (equal (fn2-layout-range-code dst dg 0 *fn2-run-page-size* t 9 0 1 p0) :ok))
              (and (not (car step)) (equal (mv-nth 1 step) :more) (equal (mv-nth 2 step) (cons row tail))
                   (equal (mv-nth 3 step) 0) (equal (mv-nth 4 step) (1+ unit)) (equal (mv-nth 5 step) pages)
                   (equal (mv-nth 6 step) b1) (equal w2 (mv-nth 2 page)) (equal p2 (mv-nth 3 page))
                   (fn2-run-empty-open-writer-p 0 3 0 dst dg 9 0 1 w2)
                   (equal (fn2-run-writers-fields 0 w2) 0) (equal (fn2-run-writers-limit 0 w2) 2048)
                   (fn2-run-open-overview-contents-p nil 0 (fn2-run-writers-entries 0 w2) (fn2-run-writers-restarts 0 w2)
                        (fn2-run-writers-cursor 0 w2) dst dg (mv-nth 11 step) p2)
                   (equal (fn2-layout-range-code dst dg *fn2-run-entries-base* *fn2-run-page-size* t 9 0 1 p2) :ok)))))
  :hints (("Goal" :do-not '(preprocess) :use (fn2-range-first-step-supplies-leaf
                 (:instance fn2-range-height-one-opens-first-leaf
                    (dst (mv-nth 1 (fn2-range-pending-leaf)))
                    (dg (mv-nth 2 (fn2-range-pending-leaf)))
                    (p (mv-nth 3 (fn2-range-pending-leaf)))))
           :in-theory (union-theories (theory 'minimal-theory)
                      '(mv-nth car-cons cdr-cons (:e zp) (:e equal) (:e unary--) (:e binary-+) (:e mv-nth) (:e not))))))
