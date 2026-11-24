; An idle build appends a sorted row exactly when its encoded bytes and
; restart fit. On overflow it closes the nonempty leaf and retries that row.
(in-package "ACL2")
(include-book "runs-builder-overview-admission-proof")

(defun-nx fn2-run-build-awaits-input-p (builds writers restarts f fc ctx)
  (let ((height (fn2-run-builds-height 0 builds)) (w (fn2-run-builds-wbase 0 builds))
        (crow (fn2-run-builds-crow 0 builds)) (hrow (fn2-run-builds-hbase 0 builds)))
    (and (natp w) (integerp hrow) (fn2-run-writerp w writers restarts f) (< w (fn2-run-writers-rows writers))
         (equal (fn2-run-builds-phase 0 builds) *fn2-run-build-phase-adding*)
         (posp height) (<= height *fn2-run-max-levels*) (equal (fn2-run-scan (1- height) 0 nil builds writers) '(:idle 0))
         (< crow (fn2-fc-rows fc)) (< crow (fn2-fc-context-rows ctx)) (unsigned-byte-p 32 hrow))))

(local
 (defthm fn2-run-idle-build-work
   (implies (fn2-run-build-awaits-input-p builds writers restarts f fc ctx)
            (equal (fn2-run-build-work 0 4096 builds writers restarts f pool fc ctx b3 ds)
                   (list :idle 0 builds writers restarts f pool fc ctx b3 ds)))
   :hints (("Goal" :in-theory (e/d (fn2-run-build-work)
                       (fn2-run-scan fn2-run-writerp fn2-run-builds-height fn2-run-builds-wbase fn2-run-writers-rows
                        fn2-run-builds-crow fn2-run-builds-hbase fn2-run-builds-phase fn2-fc-rows fn2-fc-context-rows
                        fn2-run-close-step fn2-run-head fn2-run-seal-context fn2-run-seal-step fn2-run-close unsigned-byte-p))))))

(defthm fn2-run-idle-build-consumes-accepted-row
   (let* ((load (fn2-run-load-values layout row *fn2-run-run-entry* src sg at 9 0 1 f pool))
          (build (fn2-run-build-add 0 *fn2-run-run-entry* builds writers restarts (mv-nth 2 load) (mv-nth 3 load)))
          (step (fn2-run-run-onestep layout (cons row tail) src sg at unit pages builds curs paths cache writers restarts f pool fc ctx b3 ds)))
     (implies (and (fn2-run-build-awaits-input-p builds writers restarts f fc ctx) (equal (car load) :ok)
                   (member-eq (car build) '(:ok :more)))
              (equal step
                     (list nil :more (if (equal (car build) :ok) tail (cons row tail))
                           (if (equal (car build) :ok) (mv-nth 1 load) at) unit pages
                           (mv-nth 1 build) curs paths cache (mv-nth 2 build) (mv-nth 3 build)
                           (mv-nth 4 build) (mv-nth 5 build) fc ctx b3 ds))))
   :rule-classes nil
   :hints (("Goal" :cases ((equal (car (fn2-run-build-add 0 *fn2-run-run-entry* builds writers restarts
                                  (mv-nth 2 (fn2-run-load-values layout row *fn2-run-run-entry* src sg at 9 0 1 f pool))
                                  (mv-nth 3 (fn2-run-load-values layout row *fn2-run-run-entry* src sg at 9 0 1 f pool)))) :ok))
            :in-theory (union-theories (theory 'minimal-theory)
                    '(fn2-run-run-onestep fn2-run-idle-build-work mv-nth car-cons cdr-cons eq eql member-equal
                      (:e equal) (:e zp) (:e consp) (:e unary--) (:e binary-+) (:e mv-nth) (:e member-equal))))))

(defmacro fn2-run-leaf-packed-end (row w writers)
  `(fn2-run-pack-bound (len (fn2-layout-octets *fn2-overview-entry* ,row))
       (fn2-run-writers-cursor ,w ,writers) (fn2-run-writers-entries ,w ,writers)
       (fn2-run-writers-restarts ,w ,writers) (fn2-run-writers-limit ,w ,writers)))

(defun-nx fn2-run-next-overview-row-p (rows row src sg at builds writers restarts f pool)
  (let* ((w (fn2-run-builds-wbase 0 builds)) (base *fn2-run-run-entry*)
         (idx (fn2-run-writers-entries w writers)) (nr (fn2-run-writers-restarts w writers))
         (dst (fn2-run-writers-slot w writers)) (dg (fn2-run-writers-gen w writers)) (off (fn2-run-writers-cursor w writers))
         (line (nth 4 row)) (n (len line)) (end (+ off (len (fn2-layout-octets *fn2-overview-entry* row))))
         (source (+ at (fn2-pool-base src pool))))
    (and (fn2-run-overview-append-workspace-p w base writers restarts f)
         (fn2-run-values-layoutp *fn2-overview-entry* row) (equal (fn2-run-builds-schema 0 builds) 3)
         (fn2-run-open-overview-contents-p rows w idx nr off dst dg restarts pool)
         (or (not (equal (fn2-run-writers-prev w writers) 1))
             (equal (fn2-run-key-order-spec *fn2-overview-range-key* row
                     (fn2-overview-range-key-at (+ (fn2-run-writers-fields w writers) *fn2-run-prev-fields*) f)) :gt))
         (equal (fn2-run-writers-okind w writers) 9) (equal (fn2-run-writers-oslot w writers) 0) (equal (fn2-run-writers-ogen w writers) 1)
         (natp nr) (< nr *fn2-run-restart-capacity*) (unsigned-byte-p 32 (1+ idx)) (unsigned-byte-p 60 (1+ (fn2-run-builds-entries 0 builds)))
         (fn2-poolp pool) (fn2-pool-wfp pool) (natp src) (natp dst) (not (equal src dst))
         (natp (fn2-pool-base src pool)) (natp (fn2-pool-base dst pool))
         (unsigned-byte-p 32 off) (unsigned-byte-p 32 at) (unsigned-byte-p 32 end)
         (or (<= (+ source n) (+ *fn2-run-entries-base* (fn2-pool-base dst pool))) (<= (+ (fn2-pool-base dst pool) end) source))
         (<= *fn2-run-entries-base* off)
         (equal (fn2-layout-range-code src sg at (+ at n) t 9 0 1 pool) :ok)
         (equal (fn2-layout-range-code dst dg off end t 9 0 1 pool) :ok))))

(local (in-theory (disable fn2-run-open-overview-contents-p fn2-run-values-layoutp fn2-run-key-order-spec fn2-overview-range-key-at
        fn2-run-builds-wbase fn2-run-builds-schema fn2-run-builds-height fn2-run-builds-phase fn2-run-layout-size
        fn2-run-builds-entries fn2-run-writersp fn2-run-writers-wfp fn2-run-writers-phase fn2-run-writers-fields fn2-run-writers-rows
        fn2-run-writers-schema fn2-run-writers-level fn2-run-writers-slot fn2-run-writers-gen fn2-run-writers-cursor
        fn2-run-writers-prev fn2-run-writers-entries fn2-run-writers-restarts fn2-run-writers-limit fn2-run-writers-okind
        fn2-run-writers-oslot fn2-run-writers-ogen fn2-run-restarts-rows fn2-pool-base fn2-poolp fn2-pool-wfp
        fn2-layout-range-code fn2-layout-octets fn2-run-pack-bound fn2-run-writerp fn2-run-builds-crow fn2-run-builds-hbase
        fn2-run-scan fn2-fc-rows fn2-fc-context-rows fn2-fields-rows fn2-run-load-values fn2-run-unload-values
        fn2-run-build-add fn2-run-add-ready fn2-run-run-onestep unsigned-byte-p len nth)))

(local
 (defthm fn2-run-fitting-row-is-ready
  (let* ((w (fn2-run-builds-wbase 0 builds)) (base *fn2-run-run-entry*)
         (load (fn2-run-load-values *fn2-overview-entry* row base src sg at 9 0 1 f pool)))
    (implies (and (fn2-run-next-overview-row-p rows row src sg at builds writers restarts f pool)
                  (car (fn2-run-leaf-packed-end row w writers)))
             (and (equal (car load) :ok) (equal (mv-nth 1 load) (+ at (len (nth 4 row))))
                  (equal (fn2-run-add-ready w 3 base writers restarts (mv-nth 2 load) (mv-nth 3 load)) :ok))))
  :rule-classes nil
  :hints (("Goal" :do-not '(preprocess)
           :use ((:instance fn2-run-sorted-overview-admission (w (fn2-run-builds-wbase 0 builds)) (base *fn2-run-run-entry*))
                 (:instance fn2-run-load-overview-roundtrip (base *fn2-run-run-entry*) (slot src) (gen sg) (off at)
                            (cap (+ at (len (nth 4 row))))))
           :in-theory (disable fn2-run-overview-append-workspace-p fn2-run-build-awaits-input-p)))))

(local
 (defthm fn2-run-fitting-row-extends-body
  (let* ((w (fn2-run-builds-wbase 0 builds)) (base *fn2-run-run-entry*)
         (load (fn2-run-load-values *fn2-overview-entry* row base src sg at 9 0 1 f pool))
         (build (fn2-run-build-add 0 base builds writers restarts (mv-nth 2 load) (mv-nth 3 load))) (after (mv-nth 2 build)))
    (implies (and (fn2-run-build-awaits-input-p builds writers restarts f fc ctx)
                  (fn2-run-next-overview-row-p rows row src sg at builds writers restarts f pool)
                  (car (fn2-run-leaf-packed-end row w writers)))
             (and (equal (car build) :ok)
                  (fn2-run-open-overview-contents-p (append rows (list row)) w (fn2-run-writers-entries w after)
                      (fn2-run-writers-restarts w after) (fn2-run-writers-cursor w after)
                      (fn2-run-writers-slot w writers) (fn2-run-writers-gen w writers) (mv-nth 3 build) (mv-nth 5 build)))))
  :rule-classes nil
  :hints (("Goal" :do-not '(preprocess) :use (fn2-run-fitting-row-is-ready fn2-run-builder-extends-overview-page)
           :in-theory (enable fn2-run-next-overview-row-p fn2-run-overview-append-workspace-p fn2-run-build-awaits-input-p)))))

(defthmd fn2-run-idle-build-appends-fitting-overview
  (let* ((w (fn2-run-builds-wbase 0 builds)) (dst (fn2-run-writers-slot w writers)) (dg (fn2-run-writers-gen w writers))
         (step (fn2-run-run-onestep *fn2-overview-entry* (cons row tail) src sg at unit pages builds curs paths cache
                                    writers restarts f pool fc ctx b3 ds)) (after (mv-nth 10 step)))
    (implies (and (fn2-run-build-awaits-input-p builds writers restarts f fc ctx)
                  (fn2-run-next-overview-row-p rows row src sg at builds writers restarts f pool)
                  (car (fn2-run-leaf-packed-end row w writers)))
             (and (not (car step)) (equal (mv-nth 1 step) :more)
                  (equal (mv-nth 2 step) tail) (equal (mv-nth 3 step) (+ at (len (nth 4 row))))
                  (equal (mv-nth 5 step) pages)
                  (fn2-run-open-overview-contents-p (append rows (list row)) w (fn2-run-writers-entries w after)
                      (fn2-run-writers-restarts w after) (fn2-run-writers-cursor w after) dst dg (mv-nth 11 step) (mv-nth 13 step)))))
  :hints (("Goal" :use (fn2-run-fitting-row-is-ready fn2-run-fitting-row-extends-body
                 (:instance fn2-run-idle-build-consumes-accepted-row (layout *fn2-overview-entry*)))
           :in-theory (union-theories (theory 'minimal-theory)
                       '(mv-nth car-cons cdr-cons member-equal eq not (:e mv-nth) (:e equal) (:e consp) (:e zp) (:e binary-+))))))
