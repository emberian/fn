; The run builder in range setup uses two of its million steps to reach
; the first stored row. Its remaining computation receives the exact state
; from that append, including the pending tail and the next source offset.
(in-package "ACL2")
(include-book "range-setup-first-row-proof")

(defun-nx fn2-range-continue-overview-build (fuel state src sg)
  (fn2-run-run-loop fuel *fn2-overview-entry* (mv-nth 2 state) src sg (mv-nth 3 state)
      (mv-nth 4 state) (mv-nth 5 state) (mv-nth 6 state) (mv-nth 7 state) (mv-nth 8 state)
      (mv-nth 9 state) (mv-nth 10 state) (mv-nth 11 state) (mv-nth 12 state) (mv-nth 13 state)
      (mv-nth 14 state) (mv-nth 15 state) (mv-nth 16 state) (mv-nth 17 state)))

(local
 (defthmd fn2-range-open-build-continues
   (let* ((step (fn2-run-run-onestep *fn2-overview-entry* entries src sg at unit pages b curs paths cache w rs f p fc ctx b3 ds))
          (run (fn2-run-run-loop fuel *fn2-overview-entry* entries src sg at unit pages b curs paths cache w rs f p fc ctx b3 ds)))
     (implies (and (posp fuel) (not (car step))) (equal run (fn2-range-continue-overview-build (1- fuel) step src sg))))
   :hints (("Goal" :expand ((fn2-run-run-loop fuel *fn2-overview-entry* entries src sg at unit pages b curs paths cache w rs f p fc ctx b3 ds))
            :in-theory (e/d (fn2-range-continue-overview-build) (fn2-run-run-loop fn2-run-run-onestep))))))

(local
 (defthmd fn2-range-pending-row-continues
   (let ((second (fn2-range-retry-pending-row first src sg)))
     (implies (and (posp fuel) (not (car second)))
              (equal (fn2-range-continue-overview-build fuel first src sg)
                     (fn2-range-continue-overview-build (1- fuel) second src sg))))
   :hints (("Goal" :do-not '(preprocess)
            :use ((:instance fn2-range-open-build-continues (entries (mv-nth 2 first)) (at (mv-nth 3 first))
                      (unit (mv-nth 4 first)) (pages (mv-nth 5 first)) (b (mv-nth 6 first)) (curs (mv-nth 7 first))
                      (paths (mv-nth 8 first)) (cache (mv-nth 9 first)) (w (mv-nth 10 first)) (rs (mv-nth 11 first))
                      (f (mv-nth 12 first)) (p (mv-nth 13 first)) (fc (mv-nth 14 first)) (ctx (mv-nth 15 first))
                      (b3 (mv-nth 16 first)) (ds (mv-nth 17 first))))
            :expand ((fn2-range-continue-overview-build fuel first src sg)) :in-theory (theory 'minimal-theory)))))

(defmacro fn2-range-initial-build-loop ()
  '(fn2-run-run-loop 1000000 *fn2-overview-entry* (cons row tail) src sg 0 (+ 1 (* 1000 k)) nil
      (mv-nth 1 start) (mv-nth 7 setup) (mv-nth 8 setup) (mv-nth 9 setup) (mv-nth 2 start)
      (mv-nth 11 setup) (mv-nth 12 setup) (mv-nth 3 start) (mv-nth 14 setup) (mv-nth 15 setup)
      (mv-nth 16 setup) (mv-nth 17 setup)))

(local
 (defthm fn2-range-open-result-yields
   (implies (fn2-range-first-open-result-p step pending unit dst dg) (not (car step)))
   :rule-classes nil :hints (("Goal" :in-theory (enable fn2-range-first-open-result-p)))))

(local
 (defthm fn2-range-stored-row-yields
   (implies (fn2-range-first-row-stored-p step row tail dst dg) (not (car step)))
   :rule-classes nil :hints (("Goal" :in-theory (enable fn2-range-first-row-stored-p)))))

(local
 (defthmd fn2-range-two-yields-leave-remaining-build
   (let* ((first (fn2-run-run-onestep *fn2-overview-entry* (cons row tail) src sg at unit pages b curs paths cache w rs f p fc ctx b3 ds))
          (second (fn2-range-retry-pending-row first src sg))
          (run (fn2-run-run-loop 1000000 *fn2-overview-entry* (cons row tail) src sg at unit pages b curs paths cache w rs f p fc ctx b3 ds)))
     (implies (and (fn2-range-first-open-result-p first (cons row tail) unit dst dg) (fn2-range-first-row-stored-p second row tail dst dg))
              (equal run (fn2-range-continue-overview-build 999998 second src sg))))
   :hints (("Goal" :do-not '(preprocess)
            :use ((:instance fn2-range-open-build-continues (fuel 1000000) (entries (cons row tail)))
                  (:instance fn2-range-pending-row-continues (fuel 999999)
                     (first (fn2-run-run-onestep *fn2-overview-entry* (cons row tail) src sg at unit pages b curs paths cache w rs f p fc ctx b3 ds)))
                  (:instance fn2-range-open-result-yields (pending (cons row tail))
                     (step (fn2-run-run-onestep *fn2-overview-entry* (cons row tail) src sg at unit pages b curs paths cache w rs f p fc ctx b3 ds)))
                  (:instance fn2-range-stored-row-yields
                     (step (fn2-range-retry-pending-row
                           (fn2-run-run-onestep *fn2-overview-entry* (cons row tail) src sg at unit pages b curs paths cache w rs f p fc ctx b3 ds) src sg))))
            :in-theory (union-theories (theory 'minimal-theory) '((:e posp) (:e binary-+) (:e unary--) (:e equal) (:e not)))))))

(defthmd fn2-range-first-build-continues-from-stored-row
  (fn2-range-first-builder-bindings
   (let* ((first (fn2-range-initial-build-step)) (second (fn2-range-retry-pending-row first src sg)))
     (implies (and (equal fn2-pool (create-fn2-pool)) (fn2-fieldsp fn2-fields)
                   (fn2-run-buildsp fn2-run-builds) (fn2-run-writersp fn2-run-writers)
                   (natp k) (<= k 5) (fn2-run-values-layoutp *fn2-overview-entry* row))
              (and (fn2-range-first-row-stored-p second row tail 2 1)
                   (equal (fn2-range-initial-build-loop) (fn2-range-continue-overview-build 999998 second src sg))))))
  :hints (("Goal" :do-not '(preprocess)
           :use ((:instance fn2-range-two-yields-leave-remaining-build (dst 2) (dg 1)
                   (src (fn2-range-first-builder-bindings src)) (sg (fn2-range-first-builder-bindings sg))
                   (unit (+ 1 (* 1000 k))) (at 0) (pages nil) (b (fn2-range-first-builder-bindings (mv-nth 1 start)))
                   (curs (mv-nth 7 (fn2-rga-call fn2-rga-setup))) (paths (mv-nth 8 (fn2-rga-call fn2-rga-setup)))
                   (cache (mv-nth 9 (fn2-rga-call fn2-rga-setup))) (w (fn2-range-first-builder-bindings (mv-nth 2 start)))
                   (rs (mv-nth 11 (fn2-rga-call fn2-rga-setup))) (f (mv-nth 12 (fn2-rga-call fn2-rga-setup)))
                   (p (fn2-range-first-builder-bindings (mv-nth 3 start))) (fc (mv-nth 14 (fn2-rga-call fn2-rga-setup)))
                   (ctx (mv-nth 15 (fn2-rga-call fn2-rga-setup))) (b3 (mv-nth 16 (fn2-rga-call fn2-rga-setup)))
                   (ds (mv-nth 17 (fn2-rga-call fn2-rga-setup)))))
           :in-theory (union-theories (theory 'minimal-theory) '(fn2-range-setup-opens-first-overview-leaf fn2-range-setup-stores-first-overview-row (:e posp) (:e binary-+) (:e unary--) (:e equal) (:e not))))))
