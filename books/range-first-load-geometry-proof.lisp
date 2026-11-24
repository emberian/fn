; The first load and the subsequent reservation keep both actor tables
; in the shapes needed by the next call to the builder.
(in-package "ACL2")
(include-book "range-first-builder-input-proof")
(include-book "range-builder-input-tables-proof")

(local
 (defthm fn2-range-fresh-input-table-sizes
   (let* ((setup (fn2-rga-call fn2-rga-setup)) (f (mv-nth 12 setup)) (p (mv-nth 13 setup)))
     (implies (and (fn2-fieldsp fn2-fields) (fn2-poolp fn2-pool))
              (and (fn2-fieldsp f) (fn2-fields-wfp f) (<= (+ *fn2-run-run-entry* *fn2-run-entry-rows*) (fn2-fields-rows f))
                   (fn2-poolp p) (fn2-pool-wfp p))))
   :hints (("Goal" :in-theory (e/d (fn2-rga-setup)
                       (fn2-fields-init fn2-pool-init fn2-fieldsp fn2-fields-wfp fn2-poolp fn2-pool-wfp))))))

(local
 (defthm fn2-range-initial-pool-is-typed
   (fn2-poolp (create-fn2-pool))
   :hints (("Goal" :in-theory (enable create-fn2-pool fn2-poolp)))))

(local
 (defthm fn2-range-initial-fields-cover-input-row
   (implies (and (fn2-fieldsp fn2-fields) (equal fn2-pool (create-fn2-pool)))
            (<= (+ *fn2-run-run-entry* 5) (fn2-fields-rows (mv-nth 12 (fn2-rga-call fn2-rga-setup)))))
   :hints (("Goal" :in-theory (e/d (fn2-rga-setup) (fn2-fields-init fn2-pool-init fn2-fieldsp create-fn2-pool))))))

(defthmd fn2-range-setup-leaf-keeps-input-tables
  (fn2-range-first-builder-bindings
   (implies (and (equal fn2-pool (create-fn2-pool)) (fn2-fieldsp fn2-fields)
                 (natp k) (<= k 5) (fn2-run-values-layoutp *fn2-overview-entry* row))
            (and (fn2-fields-wfp (mv-nth 2 load)) (<= (+ *fn2-run-run-entry* *fn2-run-entry-rows*) (fn2-fields-rows (mv-nth 2 load)))
                 (fn2-poolp (mv-nth 3 leaf)) (fn2-pool-wfp (mv-nth 3 leaf)))))
  :hints (("Goal" :do-not '(preprocess)
           :use (fn2-range-first-builder-input-after-start
                 (:instance fn2-range-builder-load-keeps-typed-tables
                    (src 1) (sg 1) (at 0) (base *fn2-run-run-entry*) (f (mv-nth 12 (fn2-rga-call fn2-rga-setup)))
                    (pool (fn2-range-first-builder-bindings (mv-nth 3 start)))))
           :in-theory (union-theories (theory 'minimal-theory)
                   '(fn2-range-initial-fields-cover-input-row fn2-range-initial-pool-is-typed fn2-range-fresh-input-table-sizes
                     fn2-run-build-start-pool-preserves-type fn2-run-build-start-pool-preserves-wfp
                     fn2-pool-reserve-preserves-type fn2-pool-reserve-preserves-wfp
                     (:e natp) (:e unsigned-byte-p) (:e binary-+) (:e unary--) (:e <) (:e equal) (:e not))))))
