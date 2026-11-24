; The first page reservation follows initialization of the hash workspace
; and loading the first input. Both leave the remaining free slots intact.
(in-package "ACL2")
(include-book "range-workspace-reservations-proof")
(include-book "range-build-workspace-proof")

(defmacro fn2-range-first-builder-bindings (body)
  `(let* ((setup (fn2-rga-call fn2-rga-setup)) (p0 (mv-nth 13 setup))
          (hash (fn2-pool-reserve 0 9 0 1 p0)) (src-res (fn2-pool-reserve 0 9 0 1 (mv-nth 3 hash)))
          (src (mv-nth 1 src-res)) (sg (mv-nth 2 src-res))
          (start (fn2-run-build-start 0 3 (1+ k) 0 0 136 (mv-nth 1 hash) (mv-nth 2 hash) 0 2048 1 1 9 0 1
                                     (mv-nth 6 setup) (mv-nth 10 setup) (mv-nth 3 src-res)))
          (load (fn2-run-load-values *fn2-overview-entry* row *fn2-run-run-entry* src sg 0 9 0 1 (mv-nth 12 setup) (mv-nth 3 start)))
          (leaf (fn2-pool-reserve 0 9 0 1 (mv-nth 3 load))))
     (declare (ignorable setup p0 hash src-res src sg start load leaf))
     ,body))

(local
 (defthmd fn2-range-reserving-after-row-load
   (let ((leaf (fn2-pool-reserve 0 9 0 1 (mv-nth 3 (fn2-run-load-values layout row base src sg off 9 0 1 f p)))))
     (implies (fn2-range-pool-available-p 325 p)
              (and (equal (car leaf) :ok) (equal (mv-nth 1 leaf) 2) (equal (mv-nth 2 leaf) 1)
                   (fn2-range-pool-available-p 324 (mv-nth 3 leaf)) (equal (fn2-pool-base 2 (mv-nth 3 leaf)) 131072)
                   (equal (fn2-pool-slot-cap 2 (mv-nth 3 leaf)) 65536)
                   (equal (fn2-layout-range-code 2 1 0 65536 t 9 0 1 (mv-nth 3 leaf)) :ok))))
   :hints (("Goal" :do-not '(preprocess)
            :use ((:instance fn2-range-row-load-retains-reservations (n 325) (slot src) (gen sg) (pk 9) (ps 0) (pg 1))
                  (:instance fn2-range-reservation-provides-workspace (n 325) (pk 9) (ps 0) (pg 1)
                             (p (mv-nth 3 (fn2-run-load-values layout row base src sg off 9 0 1 f p))))
                  (:instance fn2-range-reserve-preserves-remaining-capacity (n 325) (pk 9) (ps 0) (pg 1)
                             (p (mv-nth 3 (fn2-run-load-values layout row base src sg off 9 0 1 f p)))))
            :in-theory (union-theories (theory 'minimal-theory)
                      '((:e fn2-pool-mrefp) (:e posp) (:e binary-*) (:e binary-+) (:e unary--) (:e equal) (:e <)))))))

(defthmd fn2-range-setup-reserves-first-leaf
  (fn2-range-first-builder-bindings
   (implies (and (equal fn2-pool (create-fn2-pool)) (natp k) (<= k 5))
            (and (equal (car start) :ok) (equal (car leaf) :ok)
                 (equal (mv-nth 1 leaf) 2) (equal (mv-nth 2 leaf) 1)
                 (fn2-range-pool-available-p 324 (mv-nth 3 leaf)) (equal (fn2-pool-base 2 (mv-nth 3 leaf)) 131072)
                 (equal (fn2-pool-slot-cap 2 (mv-nth 3 leaf)) 65536)
                 (equal (fn2-layout-range-code 2 1 0 65536 t 9 0 1 (mv-nth 3 leaf)) :ok))))
  :hints (("Goal" :do-not '(preprocess)
           :use (fn2-range-setup-has-all-reservations fn2-range-setup-starts-first-builder
                 (:instance fn2-range-build-reserves-workspaces (n 327) (p (mv-nth 13 (fn2-rga-call fn2-rga-setup))))
                 (:instance fn2-range-start-retains-page-reservations (n 325) (run (1+ k)) (h 0) (hg 1)
                    (b (mv-nth 6 (fn2-rga-call fn2-rga-setup))) (w (mv-nth 10 (fn2-rga-call fn2-rga-setup)))
                    (p (mv-nth 3 (fn2-pool-reserve 0 9 0 1 (mv-nth 3 (fn2-pool-reserve 0 9 0 1 (mv-nth 13 (fn2-rga-call fn2-rga-setup))))))))
                 (:instance fn2-range-reserving-after-row-load (layout *fn2-overview-entry*) (base *fn2-run-run-entry*) (src 1) (sg 1)
                     (off 0) (f (mv-nth 12 (fn2-rga-call fn2-rga-setup))) (p (fn2-range-first-builder-bindings (mv-nth 3 start)))))
           :in-theory (union-theories (theory 'minimal-theory)
                     '((:e natp) (:e posp) (:e binary-+) (:e unary--) (:e equal) (:e <) (:e not))))))
