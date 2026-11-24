; The open parent accepts a promoted key in strict order until its
; entries and restart directory would exceed the page limit.
(in-package "ACL2")
(include-book "runs-index-append-proof")
(include-book "range-page-capacity-proof")
(include-book "range-window-proof")

(defun-nx fn2-run-open-index-workspace-p (w base writers restarts f)
  (let ((prev (+ (nfix (fn2-run-writers-fields w writers)) *fn2-run-prev-fields*)))
    (and (natp w) (< w (fn2-run-writers-rows writers))
         (<= (* (1+ w) *fn2-run-restart-capacity*) (fn2-run-restarts-rows restarts))
         (natp base) (<= (+ base *fn2-run-entry-rows*) (fn2-fields-rows f))
         (<= (+ (fn2-run-writers-fields w writers) *fn2-run-writer-fields*) (fn2-fields-rows f))
         (<= (+ prev *fn2-run-entry-rows*) (fn2-fields-rows f))
         (equal (fn2-run-writers-phase w writers) *fn2-run-writer-phase-open*)
         (equal (fn2-run-writers-schema w writers) 3) (posp (fn2-run-writers-level w writers))
         (or (not (equal (fn2-run-writers-prev w writers) 1))
             (equal (fn2-run-key-order-spec *fn2-overview-range-key*
                       (fn2-overview-range-key-at base f) (fn2-overview-range-key-at prev f)) :gt)))))

(local
 (defthm fn2-run-index-checks-packing
   (let ((size (nfix (fn2-overview-index-size base f))))
     (implies (fn2-run-open-index-workspace-p w base writers restarts f)
              (equal (fn2-run-add-ready w 3 base writers restarts f pool)
                     (if (fn2-run-roomp w size writers) :ok :full))))
   :hints (("Goal" :do-not-induct t
            :in-theory (e/d (fn2-run-open-index-workspace-p fn2-run-add-ready fn2-run-add-check
                             fn2-run-layout-fields fn2-run-layout-size)
                         (fn2-run-layout-compare fn2-run-roomp fn2-run-roomp-by-definition fn2-overview-index-size
                          fn2-run-writers-rows fn2-run-writers-fields fn2-run-restarts-rows fn2-fields-rows
                          fn2-run-writers-phase fn2-run-writers-schema fn2-run-writers-level fn2-run-writers-prev
                          fn2-overview-range-key-at fn2-run-key-order-spec nfix))))))

(local
 (defthm fn2-run-index-packing-size
   (let ((row (fn2-run-unload-values *fn2-overview-index* base f pool)))
     (implies (and (natp base) (equal (fn2-fields-value (fn2-run-index-digest-field base) f) 1)
                   (equal (fn2-fields-ref-len (fn2-run-index-digest-field base) f) 32))
              (equal (nfix (fn2-overview-index-size base f)) (len (fn2-layout-octets *fn2-overview-index* row)))))
   :rule-classes nil
   :hints (("Goal" :use fn2-run-index-wire-segments
            :in-theory (e/d (fn2-run-encode-span-length)
                       (fn2-overview-index-size fn2-layout-octets fn2-run-unload-values fn2-fields-value fn2-fields-ref-len
                        fn2-run-index-digest-octets fn2-run-index-prefix-octets fn2-run-index-count-octets binary-append len))))))

(defthmd fn2-run-parent-packs-index-by-wire-size
  (let* ((row (fn2-run-unload-values *fn2-overview-index* base f pool)) (size (len (fn2-layout-octets *fn2-overview-index* row)))
         (fits (car (fn2-run-pack-bound size (fn2-run-writers-cursor w writers) (fn2-run-writers-entries w writers)
                           (fn2-run-writers-restarts w writers) (fn2-run-writers-limit w writers)))))
    (implies (and (fn2-run-open-index-workspace-p w base writers restarts f)
                  (equal (fn2-fields-value (fn2-run-index-digest-field base) f) 1)
                  (equal (fn2-fields-ref-len (fn2-run-index-digest-field base) f) 32))
             (and (equal (fn2-run-add-ready w 3 base writers restarts f pool) (if fits :ok :full))
                  (implies (not fits) (equal (fn2-run-add w 3 base writers restarts f pool)
                                            (list :full writers restarts f pool))))))
  :hints (("Goal" :use (fn2-run-index-checks-packing fn2-run-index-packing-size)
           :in-theory (union-theories (theory 'minimal-theory)
                          '(eq not mv-nth (:e zp) (:e equal) fn2-run-open-index-workspace-p fn2-run-add fn2-run-roomp)))))

(defthmd fn2-run-open-parent-fits-sixteen-index-rows
  (let* ((row (fn2-run-unload-values *fn2-overview-index* base f pool))
         (body (fn2-run-entries-octets *fn2-overview-index* rows))
         (offsets (fn2-run-restart-offsets-spec *fn2-overview-index* rows 0 *fn2-run-entries-base*)))
    (implies (and (fn2-run-open-index-workspace-p w base writers restarts f)
                  (fn2-run-entries-layoutp *fn2-overview-index* rows) (fn2-run-values-layoutp *fn2-overview-index* row)
                  (< (len rows) 16) (equal (fn2-run-writers-entries w writers) (len rows))
                  (equal (fn2-run-writers-cursor w writers) (+ *fn2-run-entries-base* (len body)))
                  (equal (fn2-run-writers-restarts w writers) (len offsets)) (equal (fn2-run-writers-limit w writers) 2048)
                  (equal (fn2-fields-value (fn2-run-index-digest-field base) f) 1)
                  (equal (fn2-fields-ref-len (fn2-run-index-digest-field base) f) 32))
             (equal (fn2-run-add-ready w 3 base writers restarts f pool) :ok)))
  :hints (("Goal" :use (fn2-run-parent-packs-index-by-wire-size
                        (:instance fn2-range-index-fits-sixteen-children (row (fn2-run-unload-values *fn2-overview-index* base f pool))))
           :in-theory (theory 'minimal-theory))))
