; The actual page-request step leaves the pending row and a fully usable
; empty leaf for the following call, with its two workspaces disjoint.
(in-package "ACL2")
(include-book "range-first-page-build-state-proof")
(include-book "range-opened-leaf-input-proof")

(defmacro fn2-range-next-append-state (src sg dst dg step)
  `(fn2-range-empty-leaf-input-p ,src ,sg ,dst ,dg (mv-nth 6 ,step) (mv-nth 10 ,step)
        (mv-nth 11 ,step) (mv-nth 12 ,step) (mv-nth 13 ,step) (mv-nth 14 ,step) (mv-nth 15 ,step)))

(defthmd fn2-range-first-step-prepares-pending-row
  (fn2-range-first-leaf-bindings
   (let ((dst (mv-nth 1 reserve)) (dg (mv-nth 2 reserve)) (p0 (mv-nth 3 reserve)) (f2 (mv-nth 2 load)))
     (implies (and (fn2-range-empty-build-state-p run b) (fn2-range-first-page-build-p b1)
                   (fn2-run-writersp w) (fn2-run-writers-wfp w) (<= *fn2-run-max-levels* (fn2-run-writers-rows w))
                   (equal (fn2-run-writers-phase 0 w) *fn2-run-writer-phase-idle*) (fn2-run-writerp 0 w rs f)
                   (fn2-run-restarts-wfp rs) (<= *fn2-run-restart-capacity* (fn2-run-restarts-rows rs))
                   (fn2-fields-wfp f2) (<= (+ *fn2-run-run-entry* *fn2-run-entry-rows*) (fn2-fields-rows f2))
                   (< 0 (fn2-fc-rows fc)) (< 0 (fn2-fc-context-rows ctx)) (equal (car load) :ok) (equal (car reserve) :ok)
                   (fn2-poolp p0) (fn2-pool-wfp p0) (natp src) (natp dst) (not (equal src dst))
                   (unsigned-byte-p 32 dst) (unsigned-byte-p 60 dg) (unsigned-byte-p 60 unit)
                   (natp (fn2-pool-slot-cap dst p0)) (natp (fn2-pool-base src p0)) (natp (fn2-pool-base dst p0))
                   (<= (+ 65536 (fn2-pool-base src p0)) (fn2-pool-base dst p0))
                   (equal (fn2-layout-range-code src sg 0 65536 t 9 0 1 p0) :ok)
                   (equal (fn2-layout-range-code dst dg 0 65536 t 9 0 1 p0) :ok))
              (and (equal (car page) :ok) (fn2-range-next-append-state src sg dst dg step)))))
  :hints (("Goal" :do-not '(preprocess)
           :use (fn2-range-first-step-supplies-leaf
                 (:instance fn2-range-opening-first-leaf-prepares-append
                   (b (fn2-run-builds-set-height 0 1 b))
                   (dst (mv-nth 1 (fn2-pool-reserve 0 9 0 1 (mv-nth 3 (fn2-run-load-values *fn2-overview-entry* row *fn2-run-run-entry* src sg 0 9 0 1 f p)))))
                   (dg (mv-nth 2 (fn2-pool-reserve 0 9 0 1 (mv-nth 3 (fn2-run-load-values *fn2-overview-entry* row *fn2-run-run-entry* src sg 0 9 0 1 f p)))))
                   (p (mv-nth 3 (fn2-pool-reserve 0 9 0 1 (mv-nth 3 (fn2-run-load-values *fn2-overview-entry* row *fn2-run-run-entry* src sg 0 9 0 1 f p)))))
                   (f (mv-nth 2 (fn2-run-load-values *fn2-overview-entry* row *fn2-run-run-entry* src sg 0 9 0 1 f p)))))
           :in-theory (union-theories (theory 'minimal-theory)
                     '(fn2-range-first-page-build-p mv-nth car-cons cdr-cons (:e zp) (:e mv-nth) (:e binary-+) (:e unary--) (:e equal) (:e <))))))
