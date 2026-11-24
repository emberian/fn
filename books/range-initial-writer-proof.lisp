; The first add on an empty build requests a leaf. The returned sequence
; retains that first row for encoding after supplying the new page.
(in-package "ACL2")
(include-book "range-served")

(local
 (defthmd fn2-range-reset-first-writer
   (let ((r (fn2-run-reset-writers n 0 w)))
     (implies (and (posp n) (equal (car r) :ok))
              (and (equal (fn2-run-writers-phase 0 (mv-nth 1 r)) *fn2-run-writer-phase-idle*)
                   (equal (fn2-run-writers-ordinal 0 (mv-nth 1 r)) 0)
                   (equal (fn2-run-writers-fields 0 (mv-nth 1 r)) (fn2-run-writers-fields 0 w)))))
   :hints (("Goal" :induct (fn2-run-reset-writers n 0 w)
            :in-theory (e/d (fn2-run-reset-writers fn2-run-writers-phase fn2-run-writers-fields fn2-run-writers-ordinal
                          fn2-run-writers-set-phase fn2-run-writers-set-ordinal update-fn2-run-writers-phase$ai
                          update-fn2-run-writers-ordinal$ai nth-update-nth)
                          (fn2-run-writers-rows nth update-nth))))))

(defun-nx fn2-range-empty-build-state-p (run b)
  (and (equal (fn2-run-builds-phase 0 b) *fn2-run-build-phase-adding*)
       (equal (fn2-run-builds-schema 0 b) 3) (equal (fn2-run-builds-run 0 b) run)
       (equal (fn2-run-builds-entries 0 b) 0) (equal (fn2-run-builds-pages 0 b) 0)
       (equal (fn2-run-builds-height 0 b) 0) (equal (fn2-run-builds-wbase 0 b) 0)
       (equal (fn2-run-builds-crow 0 b) 0) (equal (fn2-run-builds-hbase 0 b) 136)
       (equal (fn2-run-builds-fields 0 b) 0) (equal (fn2-run-builds-limit 0 b) 2048)
       (equal (fn2-run-builds-okind 0 b) 9) (equal (fn2-run-builds-oslot 0 b) 0) (equal (fn2-run-builds-ogen 0 b) 1)))

(defthmd fn2-range-start-initializes-first-writer
  (let* ((r (fn2-run-build-start 0 3 run 0 0 136 h hg 0 2048 1 1 9 0 1 b w p)) (w2 (mv-nth 2 r)))
    (implies (equal (car r) :ok)
             (and (fn2-range-empty-build-state-p run (mv-nth 1 r))
                  (equal (fn2-run-writers-phase 0 w2) *fn2-run-writer-phase-idle*)
                  (equal (fn2-run-writers-ordinal 0 w2) 0)
                  (equal (fn2-run-writers-fields 0 w2) (fn2-run-writers-fields 0 w)))))
  :hints (("Goal" :do-not '(preprocess) :use ((:instance fn2-range-reset-first-writer (n *fn2-run-max-levels*)))
           :in-theory (e/d (fn2-run-build-start fn2-range-empty-build-state-p nth-update-nth
                      fn2-run-builds-phase fn2-run-builds-schema fn2-run-builds-run fn2-run-builds-entries fn2-run-builds-pages
                      fn2-run-builds-height fn2-run-builds-wbase fn2-run-builds-crow fn2-run-builds-hbase fn2-run-builds-fields
                      fn2-run-builds-limit fn2-run-builds-okind fn2-run-builds-oslot fn2-run-builds-ogen)
                     (fn2-run-reset-writers fn2-run-zero fn2-pool-reset fn2-run-builds-rows fn2-run-writers-rows
                      fn2-run-writers-fields fn2-run-writers-phase fn2-run-writers-ordinal unsigned-byte-p nth update-nth)))))

(local
 (defthmd fn2-range-height-zero-idles
   (implies (and (fn2-range-empty-build-state-p run b) (fn2-run-writerp 0 w rs f)
                 (< 0 (fn2-run-writers-rows w)) (< 0 (fn2-fc-rows fc)) (< 0 (fn2-fc-context-rows ctx)))
            (equal (fn2-run-build-work 0 4096 b w rs f p fc ctx b3 ds)
                   (list :idle 0 b w rs f p fc ctx b3 ds)))
   :hints (("Goal" :in-theory (e/d (fn2-range-empty-build-state-p fn2-run-build-work fn2-run-scan)
               (fn2-run-writerp fn2-run-builds-phase fn2-run-builds-height fn2-run-builds-wbase fn2-run-builds-hbase fn2-run-builds-crow
                fn2-run-writers-rows fn2-fc-rows fn2-fc-context-rows fn2-run-close-step fn2-run-head fn2-run-seal-step
                fn2-run-close fn2-run-seal-context))))))

(local
 (defthmd fn2-range-height-zero-requests-leaf
   (implies (fn2-range-empty-build-state-p run b)
            (equal (fn2-run-build-add 0 base b w rs f p)
                   (list :need-page (fn2-run-builds-set-height 0 1 b) w rs f p)))
   :hints (("Goal" :in-theory (e/d (fn2-run-build-add fn2-range-empty-build-state-p)
                           (fn2-run-add fn2-run-builds-set-height fn2-run-builds-phase fn2-run-builds-height))))))

(defmacro fn2-range-first-leaf-bindings (body)
  `(let* ((load (fn2-run-load-values *fn2-overview-entry* row *fn2-run-run-entry* src sg 0 9 0 1 f p))
          (reserve (fn2-pool-reserve 0 9 0 1 (mv-nth 3 load)))
          (b1 (fn2-run-builds-set-height 0 1 b))
          (page (fn2-run-build-page 0 0 (mv-nth 1 reserve) (mv-nth 2 reserve) unit 2 unit b1 w (mv-nth 3 reserve)))
          (step (fn2-run-run-onestep *fn2-overview-entry* (cons row tail) src sg 0 unit pages b curs paths cache w rs f p fc ctx b3 ds)))
     ,body))

(defthmd fn2-range-first-step-supplies-leaf
  (fn2-range-first-leaf-bindings
   (implies (and (fn2-range-empty-build-state-p run b) (fn2-run-writerp 0 w rs f)
                 (< 0 (fn2-run-writers-rows w)) (< 0 (fn2-fc-rows fc)) (< 0 (fn2-fc-context-rows ctx))
                 (equal (car load) :ok) (equal (car reserve) :ok) (equal (car page) :ok))
            (equal step (list nil :more (cons row tail) 0 (+ 1 unit) pages (mv-nth 1 page)
                              curs paths cache (mv-nth 2 page) rs (mv-nth 2 load) (mv-nth 3 page) fc ctx b3 ds))))
  :hints (("Goal" :do-not '(preprocess)
           :use (fn2-range-height-zero-idles
                 (:instance fn2-range-height-zero-requests-leaf (base *fn2-run-run-entry*)
                  (f (mv-nth 2 (fn2-run-load-values *fn2-overview-entry* row *fn2-run-run-entry* src sg 0 9 0 1 f p)))
                  (p (mv-nth 3 (fn2-run-load-values *fn2-overview-entry* row *fn2-run-run-entry* src sg 0 9 0 1 f p)))))
           :in-theory (union-theories (theory 'minimal-theory)
                     '(fn2-run-run-onestep eq eql mv-nth car-cons cdr-cons (:t fn2-run-load-values)
                       (:t fn2-pool-reserve) (:t fn2-run-build-page) (:e equal) (:e zp) (:e consp) (:e member-equal)
                       (:e unary--) (:e binary-+) (:e mv-nth))))))
