; Setup sizes the writer, restart, and field tables used by the first run.
(in-package "ACL2")
(include-book "range-initial-writer-proof")
(include-book "range-served")

(defthmd fn2-range-setup-first-writer-geometry
  (let* ((setup (fn2-rga-call fn2-rga-setup)) (b (mv-nth 6 setup)) (w (mv-nth 10 setup))
         (rs (mv-nth 11 setup)) (f (mv-nth 12 setup)))
    (implies (and (fn2-run-buildsp fn2-run-builds) (fn2-run-writersp fn2-run-writers))
             (and (fn2-run-buildsp b) (fn2-run-builds-wfp b) (equal (fn2-run-builds-rows b) 1)
                  (fn2-run-writersp w) (fn2-run-writers-wfp w) (equal (fn2-run-writers-rows w) *fn2-run-max-levels*)
                  (equal (fn2-run-writers-fields 0 w) 0) (fn2-run-restarts-wfp rs)
                  (<= *fn2-run-restart-capacity* (fn2-run-restarts-rows rs))
                  (fn2-fields-wfp f) (<= *fn2-run-writer-fields* (fn2-fields-rows f))
                  (equal (fn2-fc-rows (mv-nth 14 setup)) 1) (equal (fn2-fc-context-rows (mv-nth 15 setup)) 1))))
  :hints (("Goal" :in-theory (e/d (fn2-rga-setup fn2-run-writers-fields)
                       (fn2-run-builds-init fn2-run-writers-init fn2-run-restarts-init fn2-fields-init fn2-fc-init fn2-fc-context-init
                        fn2-run-buildsp fn2-run-builds-wfp fn2-run-writersp fn2-run-writers-wfp fn2-run-restarts-wfp fn2-fields-wfp)))))

(defthmd fn2-range-start-preserves-first-writer-geometry
  (let* ((r (fn2-run-build-start 0 3 run 0 0 136 h hg 0 2048 1 1 9 0 1 b w p))
         (b2 (mv-nth 1 r)) (w2 (mv-nth 2 r)))
    (implies (and (equal (car r) :ok) (fn2-run-buildsp b) (fn2-run-builds-wfp b) (< 0 (fn2-run-builds-rows b))
                  (fn2-run-writersp w) (fn2-run-writers-wfp w) (< 0 (fn2-run-writers-rows w))
                  (equal (fn2-run-writers-fields 0 w) 0) (fn2-run-restarts-wfp rs)
                  (<= *fn2-run-restart-capacity* (fn2-run-restarts-rows rs))
                  (fn2-fields-wfp f) (<= *fn2-run-writer-fields* (fn2-fields-rows f)))
             (and (fn2-range-empty-build-state-p run b2) (fn2-run-buildsp b2) (fn2-run-builds-wfp b2) (< 0 (fn2-run-builds-rows b2))
                  (fn2-run-writersp w2) (fn2-run-writers-wfp w2) (< 0 (fn2-run-writers-rows w2))
                  (equal (fn2-run-writers-phase 0 w2) *fn2-run-writer-phase-idle*) (fn2-run-writerp 0 w2 rs f))))
  :hints (("Goal" :use fn2-range-start-initializes-first-writer
           :in-theory (e/d (fn2-run-writerp)
                      (fn2-range-empty-build-state-p fn2-run-build-start fn2-run-buildsp fn2-run-builds-wfp
                       fn2-run-builds-rows fn2-run-writersp fn2-run-writers-wfp fn2-run-writers-rows fn2-run-writers-phase
                       fn2-run-writers-fields fn2-run-restarts-rows fn2-fields-rows fn2-fields-wfp fn2-run-restarts-wfp)))))
