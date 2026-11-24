; Both the requested page and the pending row's load come directly from
; the builder in the fresh range image.
(in-package "ACL2")
(include-book "range-first-load-geometry-proof")
(include-book "range-first-step-input-proof")
(include-book "range-first-leaf-workspaces-proof")
(include-book "range-first-leaf-proof")

(local
 (defthm fn2-range-setup-first-writer-count
   (fn2-range-first-builder-bindings
    (implies (and (fn2-run-buildsp fn2-run-builds) (fn2-run-writersp fn2-run-writers))
             (equal (fn2-run-writers-rows (mv-nth 2 start)) *fn2-run-max-levels*)))
   :hints (("Goal" :use fn2-range-setup-first-writer-geometry
            :in-theory (union-theories (theory 'minimal-theory) '(fn2-run-build-start-writers-preserves-rows))))))

(local
 (defthm fn2-range-setup-pending-build-has-height-one
   (fn2-range-first-builder-bindings
    (implies (and (equal fn2-pool (create-fn2-pool)) (fn2-run-buildsp fn2-run-builds) (fn2-run-writersp fn2-run-writers)
                  (natp k) (<= k 5))
             (fn2-range-first-page-build-p (fn2-run-builds-set-height 0 1 (mv-nth 1 start)))))
   :hints (("Goal" :use ((:instance fn2-range-first-page-has-requested-height
                     (run (1+ k)) (b (fn2-range-first-builder-bindings (mv-nth 1 start)))))
            :in-theory (union-theories (theory 'minimal-theory) '(fn2-range-fresh-builder-ready-for-first-page))))))

(local
 (defthm fn2-range-fresh-run-unit-fits
   (implies (and (natp k) (<= k 5)) (unsigned-byte-p 60 (+ 1 (* 1000 k))))
   :hints (("Goal" :in-theory (enable unsigned-byte-p)))))

(defthmd fn2-range-setup-prepares-first-row-append
  (fn2-range-first-builder-bindings
   (implies (and (equal fn2-pool (create-fn2-pool)) (fn2-fieldsp fn2-fields)
                 (fn2-run-buildsp fn2-run-builds) (fn2-run-writersp fn2-run-writers)
                 (natp k) (<= k 5) (fn2-run-values-layoutp *fn2-overview-entry* row))
            (fn2-range-next-append-state 1 1 2 1 (fn2-range-initial-build-step))))
  :hints (("Goal" :do-not '(preprocess)
           :use (fn2-range-first-leaf-has-separate-input-slot fn2-range-setup-reserves-first-leaf fn2-range-setup-leaf-keeps-input-tables
                 fn2-range-first-builder-loads-admitted-row (:instance fn2-range-first-step-prepares-pending-row
                   (run (1+ k)) (src (fn2-range-first-builder-bindings src)) (sg (fn2-range-first-builder-bindings sg))
                   (unit (+ 1 (* 1000 k))) (pages nil) (b (fn2-range-first-builder-bindings (mv-nth 1 start)))
                   (curs (mv-nth 7 (fn2-rga-call fn2-rga-setup))) (paths (mv-nth 8 (fn2-rga-call fn2-rga-setup)))
                   (cache (mv-nth 9 (fn2-rga-call fn2-rga-setup))) (w (fn2-range-first-builder-bindings (mv-nth 2 start)))
                   (rs (mv-nth 11 (fn2-rga-call fn2-rga-setup))) (f (mv-nth 12 (fn2-rga-call fn2-rga-setup)))
                   (p (fn2-range-first-builder-bindings (mv-nth 3 start))) (fc (mv-nth 14 (fn2-rga-call fn2-rga-setup)))
                   (ctx (mv-nth 15 (fn2-rga-call fn2-rga-setup))) (b3 (mv-nth 16 (fn2-rga-call fn2-rga-setup)))
                   (ds (mv-nth 17 (fn2-rga-call fn2-rga-setup)))))
           :in-theory (union-theories (theory 'minimal-theory)
                     '(fn2-range-setup-pending-build-has-height-one fn2-range-setup-first-writer-count fn2-range-setup-first-writer-geometry
                       fn2-range-first-builder-loads-admitted-row fn2-range-setup-reserves-first-leaf fn2-range-first-leaf-has-separate-input-slot
                       fn2-range-fresh-builder-ready-for-first-page fn2-range-setup-leaf-keeps-input-tables
                       fn2-range-fresh-run-unit-fits
                       (:e unsigned-byte-p) (:e natp) (:e binary-+) (:e binary-*) (:e unary--) (:e equal) (:e <) (:e not))))))
