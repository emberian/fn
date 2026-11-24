; On the first nonempty build from fresh setup the adapter reserves and
; opens the first overview leaf, with the original input still pending.
(in-package "ACL2")
(include-book "range-first-builder-input-proof")
(include-book "range-first-writer-geometry-proof")
(include-book "range-first-page-open-proof")

(defmacro fn2-range-initial-build-step ()
  '(fn2-run-run-onestep *fn2-overview-entry* (cons row tail) src sg 0 (+ 1 (* 1000 k)) nil
      (mv-nth 1 start) (mv-nth 7 setup) (mv-nth 8 setup) (mv-nth 9 setup) (mv-nth 2 start)
      (mv-nth 11 setup) (mv-nth 12 setup) (mv-nth 3 start) (mv-nth 14 setup) (mv-nth 15 setup)
      (mv-nth 16 setup) (mv-nth 17 setup)))

(local
 (defthmd fn2-range-initial-page-identity
   (implies (and (natp k) (<= k 5)) (unsigned-byte-p 60 (+ 1 (* 1000 k))))
   :hints (("Goal" :in-theory (enable unsigned-byte-p)))))

(defun-nx fn2-range-first-open-result-p (step pending unit dst dg)
  (let ((w (mv-nth 10 step)) (p (mv-nth 13 step)))
    (and (not (car step)) (equal (mv-nth 1 step) :more)
                   (equal (mv-nth 2 step) pending) (equal (mv-nth 3 step) 0)
                   (equal (mv-nth 4 step) (1+ unit)) (equal (mv-nth 5 step) nil)
                   (fn2-run-empty-open-writer-p 0 3 0 dst dg 9 0 1 w)
                   (fn2-run-open-overview-contents-p nil 0 (fn2-run-writers-entries 0 w) (fn2-run-writers-restarts 0 w)
                       (fn2-run-writers-cursor 0 w) dst dg (mv-nth 11 step) p)
                   (equal (fn2-layout-range-code dst dg *fn2-run-entries-base* *fn2-run-page-size* t 9 0 1 p) :ok))))

(local
 (defthmd fn2-range-first-open-result
  (fn2-range-first-leaf-bindings
   (let ((dst (mv-nth 1 reserve)) (dg (mv-nth 2 reserve)) (p0 (mv-nth 3 reserve)))
     (implies (and (fn2-range-empty-build-state-p run b) (fn2-run-buildsp b) (fn2-run-builds-wfp b) (< 0 (fn2-run-builds-rows b))
                   (fn2-run-writersp w) (fn2-run-writers-wfp w) (< 0 (fn2-run-writers-rows w))
                   (equal (fn2-run-writers-phase 0 w) *fn2-run-writer-phase-idle*) (fn2-run-writerp 0 w rs f)
                   (< 0 (fn2-fc-rows fc)) (< 0 (fn2-fc-context-rows ctx))
                   (equal (car load) :ok) (equal (car reserve) :ok) (equal pages nil)
                   (unsigned-byte-p 32 dst) (unsigned-byte-p 60 dg) (unsigned-byte-p 60 unit)
                   (natp (fn2-pool-base dst p0)) (natp (fn2-pool-slot-cap dst p0))
                   (equal (fn2-layout-range-code dst dg 0 *fn2-run-page-size* t 9 0 1 p0) :ok))
              (fn2-range-first-open-result-p step (cons row tail) unit dst dg))))
  :hints (("Goal" :use (fn2-range-first-step-opens-overview-leaf)
            :in-theory (union-theories (theory 'minimal-theory) '(fn2-range-first-open-result-p))))))

(defthmd fn2-range-fresh-builder-ready-for-first-page
   (fn2-range-first-builder-bindings
    (let ((b (mv-nth 1 start)) (w (mv-nth 2 start)))
      (implies (and (equal fn2-pool (create-fn2-pool)) (fn2-run-buildsp fn2-run-builds)
                    (fn2-run-writersp fn2-run-writers) (natp k) (<= k 5))
               (and (fn2-range-empty-build-state-p (1+ k) b) (fn2-run-buildsp b) (fn2-run-builds-wfp b) (< 0 (fn2-run-builds-rows b))
                    (fn2-run-writersp w) (fn2-run-writers-wfp w) (< 0 (fn2-run-writers-rows w))
                    (equal (fn2-run-writers-phase 0 w) *fn2-run-writer-phase-idle*)
                    (fn2-run-writerp 0 w (mv-nth 11 setup) (mv-nth 12 setup))))))
   :hints (("Goal" :do-not '(preprocess)
            :use (fn2-range-setup-first-writer-geometry fn2-range-setup-starts-first-builder
                 (:instance fn2-range-start-preserves-first-writer-geometry
                   (run (1+ k)) (h (fn2-range-first-builder-bindings (mv-nth 1 hash))) (hg (fn2-range-first-builder-bindings (mv-nth 2 hash)))
                   (b (mv-nth 6 (fn2-rga-call fn2-rga-setup))) (w (mv-nth 10 (fn2-rga-call fn2-rga-setup)))
                   (rs (mv-nth 11 (fn2-rga-call fn2-rga-setup))) (f (mv-nth 12 (fn2-rga-call fn2-rga-setup)))
                   (p (fn2-range-first-builder-bindings (mv-nth 3 src-res)))))
            :in-theory (theory 'minimal-theory))))

(defthmd fn2-range-setup-opens-first-overview-leaf
  (fn2-range-first-builder-bindings
   (implies (and (equal fn2-pool (create-fn2-pool))
                 (fn2-run-buildsp fn2-run-builds) (fn2-run-writersp fn2-run-writers)
                 (natp k) (<= k 5) (fn2-run-values-layoutp *fn2-overview-entry* row))
            (fn2-range-first-open-result-p (fn2-range-initial-build-step) (cons row tail) (+ 1 (* 1000 k)) 2 1)))
  :hints (("Goal" :do-not '(preprocess)
           :use ((:instance fn2-range-first-open-result
                   (run (1+ k)) (src (fn2-range-first-builder-bindings src)) (sg (fn2-range-first-builder-bindings sg))
                   (unit (+ 1 (* 1000 k))) (pages nil) (b (fn2-range-first-builder-bindings (mv-nth 1 start)))
                   (curs (mv-nth 7 (fn2-rga-call fn2-rga-setup))) (paths (mv-nth 8 (fn2-rga-call fn2-rga-setup)))
                   (cache (mv-nth 9 (fn2-rga-call fn2-rga-setup))) (w (fn2-range-first-builder-bindings (mv-nth 2 start)))
                   (rs (mv-nth 11 (fn2-rga-call fn2-rga-setup))) (f (mv-nth 12 (fn2-rga-call fn2-rga-setup)))
                   (p (fn2-range-first-builder-bindings (mv-nth 3 start))) (fc (mv-nth 14 (fn2-rga-call fn2-rga-setup)))
                   (ctx (mv-nth 15 (fn2-rga-call fn2-rga-setup))) (b3 (mv-nth 16 (fn2-rga-call fn2-rga-setup)))
                   (ds (mv-nth 17 (fn2-rga-call fn2-rga-setup)))))
           :in-theory (union-theories (theory 'minimal-theory)
                     '(fn2-range-first-builder-loads-admitted-row fn2-range-setup-reserves-first-leaf fn2-range-initial-page-identity
                       fn2-range-setup-first-writer-geometry fn2-range-fresh-builder-ready-for-first-page
                       (:e unsigned-byte-p) (:e natp) (:e binary-+) (:e binary-*) (:e unary--) (:e equal) (:e <) (:e not))))))
