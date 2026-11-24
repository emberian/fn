; Promotion preserves every previous reference and restart. On a fit, the
; complete physical parent represents the old sequence followed by the child.
(in-package "ACL2")
(include-book "runs-promotion-page-bytes-proof")
(include-book "runs-promotion-restarts-proof")
(include-book "runs-stored-index-rows-proof")

(defmacro fn2-run-parent-octets (rows) `(fn2-run-entries-octets *fn2-overview-index* ,rows))

(local
 (defthm fn2-run-parent-tail-outside-previous-rows
   (implies (and (fn2-run-parent-index-position-p w parent-rows writers)
                 (natp dst) (natp (fn2-pool-base dst pool)))
            (fn2-run-write-outside-read-p dst *fn2-run-entries-base* (len (fn2-run-parent-octets parent-rows))
                                          dst (fn2-run-writers-cursor w writers) size pool))
   :hints (("Goal" :in-theory (e/d (fn2-run-write-outside-read-p fn2-run-parent-index-position-p)
                        (fn2-pool-base fn2-run-entries-layoutp fn2-run-writers-entries fn2-run-writers-cursor
                         fn2-run-writers-restarts fn2-run-writers-limit fn2-run-entries-octets fn2-run-restart-offsets-spec))))))

(local
 (defthm fn2-run-parent-keeps-old-index-sequence
   (let ((n (len (fn2-run-parent-octets parent-rows))))
     (implies (and (fn2-run-stored-index-rows-p parent-rows w dst dg rs p)
                   (equal (fn2-run-read-bytes n dst dg *fn2-run-entries-base* 9 0 1 after)
                          (fn2-run-read-bytes n dst dg *fn2-run-entries-base* 9 0 1 p)))
              (fn2-run-stored-index-rows-p parent-rows w dst dg rs after)))
   :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory) '(fn2-run-stored-index-rows-p))))))

(local
 (defthm fn2-run-appended-reference-or-previous-sequence
   (let* ((w (1+ level)) (idx (fn2-run-writers-entries w writers)) (nr (fn2-run-writers-restarts w writers))
          (off (fn2-run-writers-cursor w writers)) (size (len (fn2-run-parent-octets parent-rows)))
          (bytes (fn2-layout-octets *fn2-overview-index* row)) (after (mv-nth 5 promote)) (newrs (mv-nth 3 promote)))
     (implies (and (natp level) (equal (fn2-run-builds-wbase 0 builds) 0)
                   (fn2-run-index-promotion-result-p fits level w ordinal dst dg off idx nr bytes rp builds writers restarts commit promote)
                   (equal promote (fn2-run-build-promote 0 level builds writers restarts f pool ds))
                   (fn2-run-parent-index-position-p w parent-rows writers)
                   (< nr *fn2-run-restart-capacity*) (< (+ (* w *fn2-run-restart-capacity*) nr) (fn2-run-restarts-rows restarts))
                   (fn2-run-stored-index-rows-p parent-rows w dst dg restarts pool)
                   (equal (fn2-run-read-bytes size dst dg *fn2-run-entries-base* 9 0 1 after)
                          (fn2-run-read-bytes size dst dg *fn2-run-entries-base* 9 0 1 pool)))
              (fn2-run-stored-index-rows-p (if fits (append parent-rows (list row)) parent-rows) w dst dg newrs after)))
   :rule-classes nil
   :hints (("Goal" :cases (fits) :do-not '(preprocess) :do-not-induct t
            :use (fn2-run-promoted-parent-keeps-restart-list
                  (:instance fn2-run-index-extends-stored-sequence (rows parent-rows) (w (1+ level)) (rs restarts) (p pool)
                             (after (mv-nth 5 promote)) (newrs (mv-nth 3 promote))))
            :in-theory (e/d (fn2-run-index-promotion-result-p fn2-run-parent-index-position-p)
                     (fn2-run-build-promote fn2-run-stored-index-rows-p fn2-run-writers-entries fn2-run-writers-restarts
                      fn2-run-writers-cursor fn2-run-writers-limit fn2-run-writers-phase fn2-run-writers-ordinal fn2-run-writers-pos
                      fn2-run-writers-slot fn2-run-writers-gen fn2-run-restarts-offset fn2-run-builds-wbase fn2-run-restarts-rows
                      fn2-run-entries-layoutp fn2-run-entries-octets fn2-run-restart-offsets-spec fn2-run-saved-offsets
                      fn2-run-load-bytes fn2-run-read-bytes fn2-layout-octets binary-append mod))))))

(local
 (defthm fn2-run-index-storage-bounds
   (let* ((w (1+ level)) (nr (fn2-run-writers-restarts w writers)))
     (implies (and (fn2-run-overview-promotion-ready-p level builds writers)
                   (fn2-run-open-index-workspace-p w base writers restarts rf) (< nr *fn2-run-restart-capacity*)
                   (fn2-run-parent-index-position-p w parent-rows writers)
                   (fn2-run-write-outside-read-p dst *fn2-run-entries-base* (len (fn2-run-parent-octets parent-rows))
                                                  hslot hash-offset 32 pool))
              (and (natp level) (equal (fn2-run-builds-wbase 0 builds) 0)
                   (< (+ (* w *fn2-run-restart-capacity*) nr) (fn2-run-restarts-rows restarts))
                   (fn2-run-write-outside-read-p dst *fn2-run-entries-base* (len (fn2-run-parent-octets parent-rows))
                                                 dst (fn2-run-writers-cursor w writers) size pool))))
   :rule-classes nil
   :hints (("Goal" :use ((:instance fn2-run-parent-tail-outside-previous-rows (w (1+ level))))
            :in-theory (e/d (fn2-run-write-outside-read-p fn2-run-overview-promotion-ready-p fn2-run-open-index-workspace-p)
                       (fn2-run-parent-index-position-p fn2-run-entries-octets fn2-run-writers-cursor fn2-pool-base
                        fn2-run-restarts-rows fn2-run-writers-restarts fn2-run-writers-rows fn2-fields-rows
                        fn2-run-writers-fields fn2-run-writers-phase fn2-run-writers-schema fn2-run-writers-level
                        fn2-run-writers-prev fn2-overview-range-key-at fn2-run-key-order-spec fn2-run-builds-height
                        fn2-run-builds-wbase fn2-run-builds-fields fn2-run-builds-schema fn2-run-builds-hbase
                        fn2-run-builds-okind fn2-run-builds-oslot fn2-run-builds-ogen))))))

(defthm fn2-run-parent-stores-all-promoted-children
  (fn2-run-promoting-index-row
   (let* ((size (len (fn2-run-parent-octets parent-rows))) (at *fn2-run-entries-base*)
          (row (fn2-run-overview-child-row (list (nth 0 (car rows)) (nth 1 (car rows))) level hrow writers ds)))
     (implies (and (fn2-run-stored-index-rows-p parent-rows w dst dg restarts pool)
                   (fn2-run-write-outside-read-p dst at size hslot (* 32 level) 32 pool))
              (and (fn2-run-parent-promotion-effects)
                   (fn2-run-stored-index-rows-p (if fits (append parent-rows (list row)) parent-rows)
                                                w dst dg (mv-nth 3 promote) (mv-nth 5 promote))))))
  :rule-classes nil
  :hints (("Goal" :do-not '(preprocess) :do-not-induct t
           :use ((:instance fn2-run-index-storage-bounds (base *fn2-run-build-index*) (hash-offset (* 32 level))
                     (hslot (fn2-run-builds-hslot 0 builds)) (dst (fn2-run-writers-slot (1+ level) writers))
                     (size (len (fn2-run-child-index-bytes rows level (+ 136 level) writers ds)))
                     (rf (mv-nth 1 (fn2-run-promotion-input level level *fn2-run-build-index* (fn2-run-writers-cursor level writers)
                                   (+ 136 level) (fn2-run-builds-hslot 0 builds) (fn2-run-builds-hgen 0 builds) writers f pool ds))))
                 (:instance fn2-run-promoting-child-preserves-page-bytes
                     (at *fn2-run-entries-base*) (n (len (fn2-run-parent-octets parent-rows)))
                     (view (fn2-run-writers-slot (1+ level) writers)) (vg (fn2-run-writers-gen (1+ level) writers)))
                 (:instance fn2-run-appended-reference-or-previous-sequence
                     (row (fn2-run-overview-child-row (list (nth 0 (car rows)) (nth 1 (car rows))) level (+ 136 level) writers ds))
                     (fits (fn2-run-index-fits-writer (1+ level) (fn2-run-child-index-bytes rows level (+ 136 level) writers ds) writers))
                     (dst (fn2-run-writers-slot (1+ level) writers)) (dg (fn2-run-writers-gen (1+ level) writers))
                     (ordinal (1+ (fn2-run-writers-ordinal level writers)))
                     (rp (mv-nth 2 (fn2-run-promotion-input level level *fn2-run-build-index* (fn2-run-writers-cursor level writers)
                                   (+ 136 level) (fn2-run-builds-hslot 0 builds) (fn2-run-builds-hgen 0 builds) writers f pool ds)))
                     (promote (fn2-run-build-promote 0 level builds writers restarts f pool ds))
                     (commit (let* ((ref (fn2-run-promotion-input level level *fn2-run-build-index* (fn2-run-writers-cursor level writers)
                                              (+ 136 level) (fn2-run-builds-hslot 0 builds) (fn2-run-builds-hgen 0 builds) writers f pool ds))
                                    (parent (fn2-run-add (1+ level) 3 *fn2-run-build-index* writers restarts (mv-nth 1 ref) (mv-nth 2 ref))))
                               (fn2-run-promote-commit level (car parent) (mv-nth 1 parent))))))
           :in-theory (theory 'minimal-theory))))
