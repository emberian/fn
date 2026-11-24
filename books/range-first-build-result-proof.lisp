; The range build's returned status, catalog, and cache are those of
; completing the builder from the state with its first row already stored.
(in-package "ACL2")
(include-book "range-first-row-continuation-proof")

(defun-nx fn2-range-build-catalog-result-p (build result k n inst)
  (let* ((pages (mv-nth 1 result)) (cache (mv-nth 5 result))
         (write (fn2-rga-install-pages 3 k n pages inst cache))
         (root (equal (car result) :root)))
    (and (equal (car build) (if root (car write) (list :build (car result))))
         (equal (mv-nth 5 build) (if root (mv-nth 1 write) inst))
         (equal (mv-nth 9 build) (if root (mv-nth 2 write) cache)))))

(local
 (defthmd fn2-range-started-build-reports-loop-result
   (let* ((hash (fn2-pool-reserve 0 9 0 1 fn2-pool)) (src-res (fn2-pool-reserve 0 9 0 1 (mv-nth 3 hash)))
          (start (fn2-run-build-start 0 3 (1+ k) 0 0 136 (mv-nth 1 hash) (mv-nth 2 hash) 0 2048 1 1 9 0 1
                                     fn2-run-builds fn2-run-writers (mv-nth 3 src-res)))
          (result (fn2-run-run-loop 1000000 *fn2-overview-entry* (cons row tail) (mv-nth 1 src-res) (mv-nth 2 src-res) 0
                       (+ 1 (* 1000 k)) nil (mv-nth 1 start) fn2-run-cursors fn2-run-paths fn2-run-cache
                       (mv-nth 2 start) fn2-run-restarts fn2-fields (mv-nth 3 start) fn2-fc fn2-fc-context fn2-b3 fn2-digests))
          (build (fn2-rga-call fn2-rga-build 3 *fn2-overview-entry* (cons row tail) k)))
     (implies (equal (car start) :ok)
              (fn2-range-build-catalog-result-p build result k (len (cons row tail)) fn2-run-installed)))
   :hints (("Goal" :do-not '(preprocess)
            :in-theory (union-theories (theory 'minimal-theory)
                      '(fn2-range-build-catalog-result-p fn2-rga-build atom eq eql mv-nth car-cons cdr-cons
                        (:t fn2-run-build-start) (:t fn2-run-run-loop) (:t fn2-rga-install-pages)
                        (:e mv-nth) (:e zp) (:e consp) (:e binary-+) (:e unary--) (:e equal) (:e not)))))))

(defmacro fn2-range-build-from-fresh-setup ()
  `(b* (((mv & ,@*fn2-rga-stobjs*) (fn2-rga-call fn2-rga-setup)))
     (fn2-rga-call fn2-rga-build 3 *fn2-overview-entry* (cons row tail) k)))

(defthmd fn2-range-actual-build-continues-after-storing-first-row
  (fn2-range-first-builder-bindings
   (let* ((first (fn2-range-initial-build-step)) (second (fn2-range-retry-pending-row first src sg))
          (result (fn2-range-continue-overview-build 999998 second src sg)))
     (implies (and (equal fn2-pool (create-fn2-pool)) (fn2-fieldsp fn2-fields)
                   (fn2-run-buildsp fn2-run-builds) (fn2-run-writersp fn2-run-writers)
                   (natp k) (<= k 5) (fn2-run-values-layoutp *fn2-overview-entry* row))
              (and (fn2-range-first-row-stored-p second row tail 2 1)
                   (fn2-range-build-catalog-result-p (fn2-range-build-from-fresh-setup) result k (len (cons row tail)) (mv-nth 5 setup))))))
  :hints (("Goal" :do-not '(preprocess)
           :use (fn2-range-first-build-continues-from-stored-row fn2-range-setup-starts-first-builder
                 (:instance fn2-range-started-build-reports-loop-result
                    (fn2-ranges (mv-nth 1 (fn2-rga-call fn2-rga-setup)))
                    (fn2-range-sources (mv-nth 2 (fn2-rga-call fn2-rga-setup)))
                    (fn2-overlays (mv-nth 3 (fn2-rga-call fn2-rga-setup)))
                    (fn2-overlay-index (mv-nth 4 (fn2-rga-call fn2-rga-setup)))
                    (fn2-run-installed (mv-nth 5 (fn2-rga-call fn2-rga-setup)))
                    (fn2-run-builds (mv-nth 6 (fn2-rga-call fn2-rga-setup)))
                    (fn2-run-cursors (mv-nth 7 (fn2-rga-call fn2-rga-setup)))
                    (fn2-run-paths (mv-nth 8 (fn2-rga-call fn2-rga-setup)))
                    (fn2-run-cache (mv-nth 9 (fn2-rga-call fn2-rga-setup)))
                    (fn2-run-writers (mv-nth 10 (fn2-rga-call fn2-rga-setup)))
                    (fn2-run-restarts (mv-nth 11 (fn2-rga-call fn2-rga-setup)))
                    (fn2-fields (mv-nth 12 (fn2-rga-call fn2-rga-setup)))
                    (fn2-pool (mv-nth 13 (fn2-rga-call fn2-rga-setup)))
                    (fn2-fc (mv-nth 14 (fn2-rga-call fn2-rga-setup)))
                    (fn2-fc-context (mv-nth 15 (fn2-rga-call fn2-rga-setup)))
                    (fn2-b3 (mv-nth 16 (fn2-rga-call fn2-rga-setup)))
                    (fn2-digests (mv-nth 17 (fn2-rga-call fn2-rga-setup)))))
           :in-theory (union-theories (theory 'minimal-theory)
                       '((:t fn2-rga-setup) mv-nth (:e mv-nth) (:e zp) (:e consp) (:e binary-+) (:e unary--) (:e equal))))))
