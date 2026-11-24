; Retrying the first row after allocating a leaf still has the original
; source workspace. Loading the row and reserving the leaf preserve it.
(in-package "ACL2")
(include-book "range-first-builder-input-proof")
(include-book "range-open-page-input-proof")
(local (include-book "runs-load-overview-proof"))
(local (include-book "runs-overview-source-proof"))
(local (include-book "runs-load-frame-proof"))

(local
 (defthmd fn2-range-row-load-retains-its-input-slot
   (let* ((load (fn2-run-load-values *fn2-overview-entry* row base src sg 0 9 0 1 f p))
          (after (mv-nth 3 load)) (line (nth 4 row)))
     (implies (and (fn2-run-values-layoutp *fn2-overview-entry* row) (natp base) (natp (fn2-pool-base src p))
                   (equal (fn2-layout-range-code src sg 0 65536 t 9 0 1 p) :ok))
              (and (equal (fn2-pool-base src after) (fn2-pool-base src p))
                   (equal (fn2-layout-range-code src sg 0 65536 t 9 0 1 after) :ok)
                   (equal (fn2-layout-range-code src sg (len line) 65536 t 9 0 1 after) :ok))))
   :hints (("Goal" :do-not '(preprocess)
            :use (fn2-run-admitted-line-fits-source
                  (:instance fn2-run-load-overview-roundtrip (slot src) (gen sg) (off 0) (cap 65536) (pool p))
                  (:instance fn2-run-overview-source-fields (slot src) (gen sg) (off 0) (pool p))
                  (:instance fn2-range-can-rewrite-input-prefix (at (len (nth 4 row))) (cap 65536)
                      (p (mv-nth 3 (fn2-run-load-values *fn2-overview-entry* row base src sg 0 9 0 1 f p)))))
            :in-theory (e/d (nth) (fn2-run-values-layoutp fn2-run-load-values fn2-run-load-bytes fn2-run-unload-values
                            fn2-layout-range-code fn2-pool-base len fn2-fields-value fn2-fields-ref-slot fn2-fields-ref-gen
                            fn2-fields-ref-off fn2-fields-ref-len))))))

(defthmd fn2-range-first-leaf-has-separate-input-slot
  (fn2-range-first-builder-bindings
   (implies (and (equal fn2-pool (create-fn2-pool)) (natp k) (<= k 5) (fn2-run-values-layoutp *fn2-overview-entry* row))
            (and (equal src 1) (equal sg 1) (equal (mv-nth 1 leaf) 2) (equal (mv-nth 2 leaf) 1)
                 (equal (fn2-pool-base 1 (mv-nth 3 leaf)) 65536) (equal (fn2-pool-base 2 (mv-nth 3 leaf)) 131072)
                 (equal (fn2-layout-range-code 1 1 0 65536 t 9 0 1 (mv-nth 3 leaf)) :ok)
                 (equal (fn2-layout-range-code 2 1 0 65536 t 9 0 1 (mv-nth 3 leaf)) :ok))))
  :hints (("Goal" :do-not '(preprocess)
           :use (fn2-range-first-builder-input-after-start fn2-range-setup-reserves-first-leaf
                 (:instance fn2-range-row-load-retains-its-input-slot (src 1) (sg 1) (base *fn2-run-run-entry*)
                      (f (mv-nth 12 (fn2-rga-call fn2-rga-setup))) (p (fn2-range-first-builder-bindings (mv-nth 3 start))))
                 (:instance fn2-range-reserve-keeps-writable-slot (i 1) (g 1) (p (fn2-range-first-builder-bindings (mv-nth 3 load)))))
           :in-theory (union-theories (theory 'minimal-theory)
                     '((:e natp) (:e binary-+) (:e unary--) (:e equal) (:e <) (:e not))))))
