; Consecutive reservations supply the distinct hash and input workspaces
; that the range adapter passes to the run builder.
(in-package "ACL2")
(include-book "range-pool-reservation-proof")
(local (include-book "runs-open-workspace-proof"))

(local
 (defthm fn2-range-reserve-keeps-writable-slot
   (let* ((r (fn2-pool-reserve 0 9 0 1 p)) (after (mv-nth 3 r)))
     (implies (and (equal (car r) :ok) (natp i) (natp (mv-nth 1 r)) (not (equal i (mv-nth 1 r))))
              (and (equal (fn2-layout-range-code i g 0 65536 t 9 0 1 after)
                          (fn2-layout-range-code i g 0 65536 t 9 0 1 p))
                   (equal (fn2-pool-base i after) (fn2-pool-base i p)))))
   :hints (("Goal" :do-not '(preprocess)
            :in-theory (e/d (fn2-layout-range-code fn2-pool-reserve fn2-pool-reserve-body fn2-pool-workspace-code
                    fn2-pool-handle-code fn2-pool-ownerp fn2-pool-slot-base fn2-pool-slot-cap fn2-pool-slot-fill
                    fn2-pool-capacity-bytes fn2-pool-data-length fn2-pool-rows fn2-pool-gen fn2-pool-state
                    fn2-pool-owner-kind fn2-pool-owner-slot fn2-pool-owner-gen fn2-pool-query-ref-count
                    fn2-pool-base fn2-pool-cap fn2-pool-fill fn2-pool-out-count fn2-pool-set-state
                    fn2-pool-set-owner-kind fn2-pool-set-owner-slot fn2-pool-set-owner-gen
                    fn2-pool-set-out-count fn2-pool-set-query-ref-count fn2-pool-set-fill
                    update-fn2-pool-state$ai update-fn2-pool-owner-kind$ai update-fn2-pool-owner-slot$ai
                    update-fn2-pool-owner-gen$ai update-fn2-pool-out-count$ai update-fn2-pool-query-ref-count$ai update-fn2-pool-fill$ai
                    update-fn2-pool-class-headsi update-fn2-pool-class-countsi nth-update-nth)
                  (fn2-pool-reservable-count fn2-pool-mrefp fn2-pool-nclasses fn2-pool-class-headsi
                   fn2-pool-class-countsi fn2-pool-next-free fn2-pool-class nth update-nth))))))

(defthm fn2-range-build-reserves-workspaces
  (let* ((hash (fn2-pool-reserve 0 9 0 1 p)) (h (mv-nth 1 hash))
         (src (fn2-pool-reserve 0 9 0 1 (mv-nth 3 hash))) (s (mv-nth 1 src)) (after (mv-nth 3 src)))
    (implies (and (natp n) (<= 2 n) (fn2-range-pool-available-p n p))
             (and (equal (car hash) :ok) (equal (car src) :ok) (equal (mv-nth 2 hash) 1) (equal (mv-nth 2 src) 1)
                  (equal h (- 327 n)) (equal s (- 328 n)) (natp h) (natp s) (< h s)
                  (equal (fn2-pool-base h after) (* h 65536)) (equal (fn2-pool-base s after) (* s 65536))
                  (equal (fn2-layout-range-code h 1 0 65536 t 9 0 1 after) :ok)
                  (equal (fn2-layout-range-code s 1 0 65536 t 9 0 1 after) :ok)
                  (fn2-range-pool-available-p (- n 2) after))))
  :rule-classes nil
  :hints (("Goal" :do-not '(preprocess)
           :use ((:instance fn2-range-reserve-preserves-remaining-capacity (pk 9) (ps 0) (pg 1))
                 (:instance fn2-range-reservation-provides-workspace (pk 9) (ps 0) (pg 1))
                 (:instance fn2-range-reserve-preserves-remaining-capacity (pk 9) (ps 0) (pg 1) (n (1- n))
                            (p (mv-nth 3 (fn2-pool-reserve 0 9 0 1 p))))
                 (:instance fn2-range-reservation-provides-workspace (pk 9) (ps 0) (pg 1) (n (1- n))
                            (p (mv-nth 3 (fn2-pool-reserve 0 9 0 1 p))))
                 (:instance fn2-range-reserve-keeps-writable-slot (g 1) (i (- 327 n))
                            (p (mv-nth 3 (fn2-pool-reserve 0 9 0 1 p)))))
           :in-theory (e/d (fn2-range-pool-available-p)
                    (fn2-pool-reserve fn2-pool-base fn2-layout-range-code fn2-pool-class-headsi fn2-pool-class-countsi
                     fn2-pool-credit-configured fn2-pool-nclasses fn2-pool-rows fn2-pool-capacity-bytes fn2-range-free-suffix-p)))))

(local
 (defthm fn2-range-resets-builder-writers
   (implies (and (natp n) (natp w) (<= (+ w n) (fn2-run-writers-rows writers)))
            (equal (car (fn2-run-reset-writers n w writers)) :ok))
   :hints (("Goal" :induct (fn2-run-reset-writers n w writers)
            :in-theory (e/d (fn2-run-reset-writers) (fn2-run-writers-rows fn2-run-writers-set-phase fn2-run-writers-set-ordinal))))))

(local
 (defthm fn2-range-starts-builder-with-workspace
   (let ((res (fn2-run-build-start 0 3 run 0 0 136 h 1 0 2048 1 1 9 0 1 b w p)))
     (implies (and (unsigned-byte-p 60 run) (unsigned-byte-p 32 h)
                   (< 0 (fn2-run-builds-rows b)) (<= *fn2-run-max-levels* (fn2-run-writers-rows w))
                   (member-equal (fn2-run-builds-phase 0 b) (list *fn2-run-build-phase-idle* *fn2-run-build-phase-done*))
                   (natp (fn2-pool-base h p)) (equal (fn2-layout-range-code h 1 0 65536 t 9 0 1 p) :ok))
              (equal (car res) :ok)))
   :rule-classes nil
   :hints (("Goal" :do-not '(preprocess)
            :use ((:instance fn2-run-reset-writable-page (slot h) (gen 1) (pk 9) (ps 0) (pg 1) (pool p))
                  (:instance fn2-run-padding-keeps-page-prefix (slot h) (gen 1) (pk 9) (ps 0) (pg 1)
                    (off 0) (at 0) (size 0) (cap 65536) (n (* 32 *fn2-run-max-levels*))
                    (pool (mv-nth 1 (fn2-pool-reset h 1 9 0 1 p)))))
            :in-theory (e/d (fn2-run-build-start)
                     (unsigned-byte-p fn2-run-builds-phase fn2-run-builds-rows fn2-run-writers-rows
                      fn2-pool-reset fn2-run-zero fn2-run-reset-writers fn2-layout-range-code fn2-pool-base fn2-pool-slot-cap
                      fn2-pool-rows fn2-run-read-bytes))))))

(defthm fn2-range-adapter-starts-allocated-build
  (let* ((hash (fn2-pool-reserve 0 9 0 1 p)) (src (fn2-pool-reserve 0 9 0 1 (mv-nth 3 hash)))
         (start (fn2-run-build-start 0 3 (1+ k) 0 0 136 (mv-nth 1 hash) (mv-nth 2 hash)
                                    0 2048 1 1 9 0 1 b w (mv-nth 3 src))))
    (implies (and (natp k) (<= k 5) (natp n) (<= 2 n) (fn2-range-pool-available-p n p)
                  (< 0 (fn2-run-builds-rows b)) (<= *fn2-run-max-levels* (fn2-run-writers-rows w))
                  (member-equal (fn2-run-builds-phase 0 b) (list *fn2-run-build-phase-idle* *fn2-run-build-phase-done*)))
             (equal (car start) :ok)))
  :rule-classes nil
  :hints (("Goal" :use (fn2-range-build-reserves-workspaces
                 (:instance fn2-range-starts-builder-with-workspace (run (1+ k)) (h (- 327 n))
                    (p (mv-nth 3 (fn2-pool-reserve 0 9 0 1 (mv-nth 3 (fn2-pool-reserve 0 9 0 1 p)))))))
           :in-theory (disable fn2-pool-reserve fn2-range-pool-available-p fn2-run-build-start fn2-pool-base
                      fn2-run-builds-rows fn2-run-builds-phase fn2-run-writers-rows fn2-layout-range-code))))

(local
 (defthm fn2-range-setup-builder-geometry
   (let ((setup (fn2-rga-call fn2-rga-setup)))
     (and (equal (fn2-run-builds-rows (mv-nth 6 setup)) 1)
          (equal (fn2-run-builds-phase 0 (mv-nth 6 setup)) *fn2-run-build-phase-idle*)
          (equal (fn2-run-writers-rows (mv-nth 10 setup)) *fn2-run-max-levels*)))
   :hints (("Goal" :in-theory (e/d (fn2-rga-setup fn2-run-builds-phase)
                          (fn2-pool-init fn2-run-builds-init fn2-run-writers-init))))))

(defthm fn2-range-setup-starts-first-builder
  (let* ((setup (fn2-rga-call fn2-rga-setup)) (p (mv-nth 13 setup))
         (b (mv-nth 6 setup)) (w (mv-nth 10 setup))
         (hash (fn2-pool-reserve 0 9 0 1 p)) (src (fn2-pool-reserve 0 9 0 1 (mv-nth 3 hash)))
         (start (fn2-run-build-start 0 3 (1+ k) 0 0 136 (mv-nth 1 hash) (mv-nth 2 hash) 0 2048
                                     1 1 9 0 1 b w (mv-nth 3 src))))
    (implies (and (equal fn2-pool (create-fn2-pool)) (natp k) (<= k 5))
             (and (equal (car hash) :ok) (equal (mv-nth 1 hash) 0)
                  (equal (car src) :ok) (equal (mv-nth 1 src) 1) (equal (car start) :ok))))
  :rule-classes nil
  :hints (("Goal" :do-not '(preprocess) :use (fn2-range-setup-has-all-reservations
             (:instance fn2-range-build-reserves-workspaces (n 327) (p (mv-nth 13 (fn2-rga-call fn2-rga-setup))))
             (:instance fn2-range-adapter-starts-allocated-build (n 327) (p (mv-nth 13 (fn2-rga-call fn2-rga-setup)))
                        (b (mv-nth 6 (fn2-rga-call fn2-rga-setup))) (w (mv-nth 10 (fn2-rga-call fn2-rga-setup)))))
           :in-theory (union-theories (theory 'minimal-theory)
                    '(fn2-range-setup-builder-geometry (:e member-equal) (:e natp) (:e <) (:e equal)
                      (:e unary--) (:e binary-+) (:e not))))))
