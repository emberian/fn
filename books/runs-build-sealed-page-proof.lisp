; The adapter retains the physical page during sealing and publishes the
; writer's exact address when the final seal step succeeds.
(in-package "ACL2")
(include-book "runs-served")
(include-book "runs-seal-storage-proof")

(defun-nx fn2-run-build-sealing-at-p (l builds writers restarts f fc ctx)
  (let* ((height (fn2-run-builds-height 0 builds)) (w (+ l (fn2-run-builds-wbase 0 builds)))
         (crow (fn2-run-builds-crow 0 builds)) (hrow (+ l (fn2-run-builds-hbase 0 builds)))
         (finishing (equal (fn2-run-builds-phase 0 builds) *fn2-run-build-phase-finishing*)))
    (and (<= height *fn2-run-max-levels*) (natp l)
         (equal (fn2-run-scan (1- height) 0 finishing builds writers) (list :seal-step l))
         (< w (fn2-run-writers-rows writers)) (fn2-run-writerp w writers restarts f)
         (< crow (fn2-fc-rows fc)) (< crow (fn2-fc-context-rows ctx)) (unsigned-byte-p 32 hrow))))

(defmacro fn2-run-build-page-seal (l builds writers f pool fc ctx b3 ds)
  `(fn2-run-seal-step (+ ,l (fn2-run-builds-wbase 0 ,builds)) (fn2-run-builds-crow 0 ,builds)
                       (+ ,l (fn2-run-builds-hbase 0 ,builds)) 4096 ,writers ,fc ,ctx ,b3 ,f ,pool ,ds))

(local
 (defthmd fn2-run-build-seals-selected-page
   (let* ((seal (fn2-run-build-page-seal l builds writers f pool fc ctx b3 ds))
          (work (fn2-run-build-work 0 4096 builds writers restarts f pool fc ctx b3 ds))
          (pages (1+ (fn2-run-builds-pages 0 builds))))
     (implies (fn2-run-build-sealing-at-p l builds writers restarts f fc ctx)
              (equal work (list (case (car seal) (:ok :sealed) (otherwise (car seal))) l
                     (if (and (eq (car seal) :ok) (unsigned-byte-p 60 pages))
                         (fn2-run-builds-set-pages 0 pages builds) builds)
                     (mv-nth 1 seal) restarts (mv-nth 4 seal) pool (mv-nth 2 seal) ctx (mv-nth 3 seal) (mv-nth 6 seal)))))
   :hints (("Goal" :in-theory (e/d (fn2-run-build-work fn2-run-build-sealing-at-p)
                       (fn2-run-scan fn2-run-close-step fn2-run-writerp fn2-run-writers-rows fn2-run-builds-set-pages
                        fn2-run-builds-height fn2-run-builds-wbase fn2-run-builds-crow fn2-run-builds-hbase
                        fn2-run-builds-pages fn2-run-builds-phase fn2-fc-rows fn2-fc-context-rows
                        fn2-run-head fn2-run-seal-context fn2-run-seal-step fn2-run-close unsigned-byte-p))))))

(local
 (defthm fn2-run-build-page-count-keeps-writer-base
   (equal (fn2-run-builds-wbase 0 (fn2-run-builds-set-pages 0 n builds)) (fn2-run-builds-wbase 0 builds))
   :hints (("Goal" :in-theory (e/d (fn2-run-builds-wbase fn2-run-builds-set-pages update-fn2-run-builds-pages$ai)
                                    (nth update-nth unsigned-byte-p))))))

(defthmd fn2-run-adapter-seal-state
  (let* ((w (+ l (fn2-run-builds-wbase 0 builds)))
         (seal (fn2-run-build-page-seal l builds writers f pool fc ctx b3 ds))
         (finished (equal (car seal) :ok)) (count (1+ (fn2-run-builds-pages 0 builds)))
         (page (list l (fn2-run-writers-unit w writers) (fn2-run-writers-counter w writers)
                       (fn2-run-writers-slot w writers) (fn2-run-writers-gen w writers)))
         (step (fn2-run-run-onestep layout entries src sg off unit pages builds curs paths cache
                                    writers restarts f pool fc ctx b3 ds)))
    (implies (and (fn2-run-build-sealing-at-p l builds writers restarts f fc ctx)
                  (member-eq (car seal) '(:more :ok)))
             (equal step (list nil :more entries off unit (if finished (cons page pages) pages)
                     (if (and finished (unsigned-byte-p 60 count)) (fn2-run-builds-set-pages 0 count builds) builds)
                     curs paths cache (mv-nth 1 seal) restarts (mv-nth 4 seal) pool (mv-nth 2 seal)
                     ctx (mv-nth 3 seal) (mv-nth 6 seal)))))
  :hints (("Goal" :do-not '(preprocess) :cases ((equal (car (fn2-run-build-page-seal l builds writers f pool fc ctx b3 ds)) :ok))
           :use (fn2-run-build-seals-selected-page
                 (:instance fn2-run-seal-keeps-writer-address (w (+ l (fn2-run-builds-wbase 0 builds)))
                            (row (fn2-run-builds-crow 0 builds)) (hrow (+ l (fn2-run-builds-hbase 0 builds))) (budget 4096)))
           :in-theory (union-theories (theory 'minimal-theory)
                    '(fn2-run-run-onestep fn2-run-build-page-count-keeps-writer-base
                      commutativity-of-+ mv-nth car-cons cdr-cons eq eql member-equal
                      (:e equal) (:e zp) (:e consp) (:e binary-+) (:e mv-nth) (:e member-equal))))))

(defthmd fn2-run-adapter-seal-records-page
  (let* ((w (+ l (fn2-run-builds-wbase 0 builds))) (seal (fn2-run-build-page-seal l builds writers f pool fc ctx b3 ds))
         (page (list l (fn2-run-writers-unit w writers) (fn2-run-writers-counter w writers)
                       (fn2-run-writers-slot w writers) (fn2-run-writers-gen w writers)))
         (step (fn2-run-run-onestep layout entries src sg off unit pages builds curs paths cache
                                    writers restarts f pool fc ctx b3 ds)))
    (implies (and (fn2-run-build-sealing-at-p l builds writers restarts f fc ctx)
                  (member-eq (car seal) '(:more :ok)))
             (and (equal (car step) nil) (equal (mv-nth 1 step) :more)
                  (equal (mv-nth 2 step) entries) (equal (mv-nth 3 step) off) (equal (mv-nth 4 step) unit)
                  (equal (mv-nth 5 step) (if (equal (car seal) :ok) (cons page pages) pages))
                  (equal (mv-nth 13 step) pool))))
  :hints (("Goal" :use fn2-run-adapter-seal-state
           :in-theory (union-theories (theory 'minimal-theory)
                       '(mv-nth car-cons cdr-cons (:e zp) (:e equal) (:e binary-+) (:e mv-nth))))))
