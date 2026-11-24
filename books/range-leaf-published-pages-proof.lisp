; Admitting the next row, or closing a full leaf and retrying that row,
; keeps every previously published subtree available to the reader.
(in-package "ACL2")
(include-book "range-published-page-write-proof")
(include-book "runs-builder-full-page-proof")

(defmacro fn2-range-leaf-input-pool ()
  '(mv-nth 1 (fn2-run-load-bytes (nth 4 row) src sg at 9 0 1 pool)))

(local
 (defthmd fn2-range-overview-load-writes-only-line
   (equal (mv-nth 3 (fn2-run-load-values *fn2-overview-entry* row base src sg at 9 0 1 f pool))
          (fn2-range-leaf-input-pool))
   :hints (("Goal" :in-theory (e/d (fn2-run-load-values fn2-run-load-ref nth)
                             (fn2-run-load-bytes fn2-fields-set-value fn2-fields-set-ref-slot fn2-fields-set-ref-gen
                               fn2-fields-set-ref-off fn2-fields-set-ref-len len))))))

(local
 (defthmd fn2-range-next-leaf-row-passes-ready-check
   (let* ((w (fn2-run-builds-wbase 0 builds)) (base *fn2-run-run-entry*)
          (load (fn2-run-load-values *fn2-overview-entry* row base src sg at 9 0 1 f pool)))
     (implies (and (fn2-run-next-overview-row-p rows row src sg at builds writers restarts f pool)
                   (car (fn2-run-leaf-packed-end row w writers)))
              (and (equal (car load) :ok)
                   (equal (fn2-run-add-ready w 3 base writers restarts (mv-nth 2 load) (mv-nth 3 load)) :ok))))
   :hints (("Goal" :do-not '(preprocess)
            :use ((:instance fn2-run-sorted-overview-admission (w (fn2-run-builds-wbase 0 builds)) (base *fn2-run-run-entry*)))
            :in-theory (union-theories (theory 'minimal-theory) '(fn2-run-next-overview-row-p unsigned-byte-p
                         integer-range-p natp (:e expt) (:e equal) (:e <)))))))

(defthmd fn2-range-fitting-leaf-build-pool
  (let* ((w (fn2-run-builds-wbase 0 builds)) (base *fn2-run-run-entry*)
         (load (fn2-run-load-values *fn2-overview-entry* row base src sg at 9 0 1 f pool))
         (build (fn2-run-build-add 0 base builds writers restarts (mv-nth 2 load) (mv-nth 3 load))))
    (implies (and (fn2-run-build-awaits-input-p builds writers restarts f fc ctx)
                  (fn2-run-next-overview-row-p rows row src sg at builds writers restarts f pool)
                  (car (fn2-run-leaf-packed-end row w writers)))
             (and (equal (car load) :ok) (equal (car build) :ok)
                  (equal (mv-nth 5 build)
                         (mv-nth 1 (fn2-run-load-bytes (fn2-layout-octets *fn2-overview-entry* row)
                         (fn2-run-writers-slot w writers) (fn2-run-writers-gen w writers)
                         (fn2-run-writers-cursor w writers) 9 0 1 (fn2-range-leaf-input-pool)))))))
  :hints (("Goal" :do-not '(preprocess)
           :use (fn2-range-next-leaf-row-passes-ready-check fn2-run-builder-appends-overview-source-row)
           :in-theory (e/d (fn2-run-next-overview-row-p fn2-run-overview-append-workspace-p fn2-run-build-awaits-input-p)
                       (fn2-run-open-overview-contents-p fn2-run-values-layoutp fn2-run-key-order-spec fn2-overview-range-key-at
                        fn2-run-builds-wbase fn2-run-builds-schema fn2-run-builds-height fn2-run-builds-phase
                        fn2-run-builds-entries fn2-run-writers-phase fn2-run-writers-fields fn2-run-writers-rows
                        fn2-run-writers-schema fn2-run-writers-level fn2-run-writers-slot fn2-run-writers-gen fn2-run-writers-cursor
                        fn2-run-writers-prev fn2-run-writers-entries fn2-run-writers-restarts fn2-run-writers-limit
                        fn2-run-writers-okind fn2-run-writers-oslot fn2-run-writers-ogen fn2-run-restarts-rows fn2-pool-base
                        fn2-poolp fn2-pool-wfp fn2-layout-range-code fn2-layout-octets fn2-run-pack-bound fn2-run-writerp
                        fn2-run-builds-crow fn2-run-builds-hbase fn2-run-scan fn2-fc-rows fn2-fc-context-rows fn2-fields-rows
                        fn2-run-load-values fn2-run-load-bytes fn2-run-build-add fn2-run-add-ready unsigned-byte-p len nth)))))

(local
 (defthmd fn2-range-fitting-leaf-writes-two-slots
   (let* ((w (fn2-run-builds-wbase 0 builds)) (bytes (fn2-layout-octets *fn2-overview-entry* row))
          (step (fn2-run-run-onestep *fn2-overview-entry* (cons row tail) src sg at unit pages builds curs paths cache
                                     writers restarts f pool fc ctx b3 ds)))
     (implies (and (fn2-run-build-awaits-input-p builds writers restarts f fc ctx)
                   (fn2-run-next-overview-row-p rows row src sg at builds writers restarts f pool)
                   (car (fn2-run-leaf-packed-end row w writers)))
              (equal (mv-nth 13 step) (mv-nth 1 (fn2-run-load-bytes bytes (fn2-run-writers-slot w writers)
                        (fn2-run-writers-gen w writers) (fn2-run-writers-cursor w writers) 9 0 1 (fn2-range-leaf-input-pool))))))
   :hints (("Goal" :do-not '(preprocess)
            :use (fn2-range-fitting-leaf-build-pool
                  (:instance fn2-run-idle-build-consumes-accepted-row (layout *fn2-overview-entry*)))
            :in-theory (union-theories (theory 'minimal-theory)
                       '(mv-nth car-cons cdr-cons member-equal eq not (:e mv-nth) (:e equal) (:e consp) (:e zp) (:e binary-+)))))))

(local
 (defthmd fn2-range-open-leaf-stays-within-page
   (let* ((w (fn2-run-builds-wbase 0 builds)) (off (fn2-run-writers-cursor w writers)))
     (implies (fn2-run-next-overview-row-p rows row src sg at builds writers restarts f pool)
              (and (natp at) (natp off)
                   (implies (car (fn2-run-leaf-packed-end row w writers))
                            (<= (+ off (len (fn2-layout-octets *fn2-overview-entry* row))) 65536)))))
   :hints (("Goal" :in-theory (e/d (fn2-run-next-overview-row-p fn2-run-pack-bound)
              (fn2-run-overview-append-workspace-p fn2-run-values-layoutp fn2-run-open-overview-contents-p
               fn2-run-key-order-spec fn2-overview-range-key-at fn2-run-builds-wbase fn2-run-builds-schema fn2-run-builds-entries
               fn2-run-writers-cursor fn2-run-writers-limit fn2-run-writers-entries fn2-run-writers-restarts fn2-run-writers-prev
               fn2-run-writers-fields fn2-run-writers-slot fn2-run-writers-gen fn2-run-writers-okind fn2-run-writers-oslot
               fn2-run-writers-ogen fn2-layout-range-code fn2-layout-octets fn2-pool-base fn2-poolp fn2-pool-wfp nth mod len))))))

(defthm fn2-range-leaf-add-keeps-published-pages
  (let* ((w (fn2-run-builds-wbase 0 builds)) (dst (fn2-run-writers-slot w writers))
         (fits (car (fn2-run-leaf-packed-end row w writers)))
         (step (fn2-run-run-onestep *fn2-overview-entry* (cons row tail) src sg at unit pages builds curs paths cache
                                    writers restarts f pool fc ctx b3 ds)))
    (implies (and (fn2-run-build-awaits-input-p builds writers restarts f fc ctx)
                  (fn2-run-next-overview-row-p rows row src sg at builds writers restarts f pool)
                  (equal (fn2-run-writers-limit w writers) 2048)
                  (fn2-range-published-run-pages-p records pages pool)
                  (fn2-range-fixed-page-slot-p src pool) (fn2-range-published-slots-apart-p pages src pool)
                  (<= (+ at (len (nth 4 row))) 65536)
                  (implies fits (and (fn2-range-fixed-page-slot-p dst pool) (fn2-range-published-slots-apart-p pages dst pool))))
             (and (not (car step)) (equal (mv-nth 1 step) :more) (equal (mv-nth 2 step) (if fits tail (cons row tail)))
                  (equal (mv-nth 5 step) pages) (fn2-range-published-run-pages-p records (mv-nth 5 step) (mv-nth 13 step)))))
  :rule-classes nil
  :hints (("Goal" :do-not '(preprocess) :cases ((car (fn2-run-leaf-packed-end row (fn2-run-builds-wbase 0 builds) writers)))
           :use (fn2-range-open-leaf-stays-within-page fn2-range-fitting-leaf-writes-two-slots fn2-run-idle-build-appends-fitting-overview
                 fn2-run-idle-build-retries-unconsumed-overview
                 (:instance fn2-range-overview-load-writes-only-line (base *fn2-run-run-entry*))
                 (:instance fn2-range-two-writes-retain-published-pages
                    (first-bytes (nth 4 row)) (first-slot src) (first-gen sg) (first-off at)
                    (bytes (fn2-layout-octets *fn2-overview-entry* row))
                    (dst (fn2-run-writers-slot (fn2-run-builds-wbase 0 builds) writers))
                    (dg (fn2-run-writers-gen (fn2-run-builds-wbase 0 builds) writers))
                    (off (fn2-run-writers-cursor (fn2-run-builds-wbase 0 builds) writers))
                    (secondp (car (fn2-run-leaf-packed-end row (fn2-run-builds-wbase 0 builds) writers)))))
           :in-theory (theory 'minimal-theory))))
