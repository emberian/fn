; From a fresh range setup, the builder's first load writes the entire
; admitted input line into its own slot and recovers the original row.
(in-package "ACL2")
(include-book "range-first-page-reservation-proof")
(include-book "range-builder-source-space-proof")
(local (include-book "runs-load-overview-proof"))
(local (include-book "runs-overview-source-proof"))

(local
 (defthmd fn2-range-loads-first-row-at-base
   (let* ((load (fn2-run-load-values *fn2-overview-entry* row *fn2-run-run-entry* 1 1 0 9 0 1 f p))
          (after (mv-nth 3 load)))
     (implies (and (fn2-run-values-layoutp *fn2-overview-entry* row) (natp (fn2-pool-base 1 p))
                   (equal (fn2-layout-range-code 1 1 0 65536 t 9 0 1 p) :ok))
              (and (equal (car load) :ok)
                   (equal (fn2-run-unload-values *fn2-overview-entry* *fn2-run-run-entry* (mv-nth 2 load) after) row))))
   :hints (("Goal" :do-not '(preprocess)
            :use (fn2-run-admitted-line-fits-source
                  (:instance fn2-run-load-overview-roundtrip (slot 1) (gen 1) (off 0) (cap 65536) (pool p) (base *fn2-run-run-entry*)))
            :in-theory (e/d (mv-nth) (fn2-run-load-values fn2-run-unload-values fn2-run-values-layoutp fn2-layout-range-code
                                    fn2-pool-base nth len))))))

(defthmd fn2-range-first-builder-input-after-start
  (fn2-range-first-builder-bindings
   (implies (and (equal fn2-pool (create-fn2-pool)) (natp k) (<= k 5))
            (and (equal src 1) (equal sg 1)
                 (equal (fn2-pool-base 1 (mv-nth 3 start)) 65536)
                 (equal (fn2-layout-range-code 1 1 0 65536 t 9 0 1 (mv-nth 3 start)) :ok))))
  :hints (("Goal" :do-not '(preprocess)
           :use (fn2-range-setup-has-all-reservations
                 (:instance fn2-range-build-reserves-workspaces (n 327) (p (mv-nth 13 (fn2-rga-call fn2-rga-setup))))
                 (:instance fn2-range-start-keeps-input-slot (run (1+ k)) (dst 0) (dg 1) (src 1) (sg 1) (j 1)
                     (at 0) (cap 65536) (b (mv-nth 6 (fn2-rga-call fn2-rga-setup)))
                     (w (mv-nth 10 (fn2-rga-call fn2-rga-setup))) (pool (fn2-range-first-builder-bindings (mv-nth 3 src-res)))))
           :in-theory (union-theories (theory 'minimal-theory)
                     '((:e natp) (:e binary-*) (:e binary-+) (:e unary--) (:e equal) (:e <) (:e not))))))

(defthmd fn2-range-first-builder-loads-admitted-row
  (fn2-range-first-builder-bindings
   (implies (and (equal fn2-pool (create-fn2-pool)) (natp k) (<= k 5)
                 (fn2-run-values-layoutp *fn2-overview-entry* row))
            (and (equal (car start) :ok) (equal (car load) :ok)
                 (equal (fn2-run-unload-values *fn2-overview-entry* *fn2-run-run-entry* (mv-nth 2 load) (mv-nth 3 load)) row))))
  :hints (("Goal" :do-not '(preprocess)
           :use (fn2-range-setup-starts-first-builder fn2-range-first-builder-input-after-start
                 (:instance fn2-range-loads-first-row-at-base (f (mv-nth 12 (fn2-rga-call fn2-rga-setup)))
                     (p (fn2-range-first-builder-bindings (mv-nth 3 start)))))
           :in-theory (union-theories (theory 'minimal-theory)
                     '((:e natp) (:e binary-*) (:e binary-+) (:e unary--) (:e equal) (:e <) (:e not))))))
