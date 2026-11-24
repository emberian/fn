; A fitting child reference is committed to the open parent. If its
; directory would overflow the limit, close the parent and retry that child.
(in-package "ACL2")
(include-book "runs-index-packing-proof")
(include-book "runs-promotion-writer-proof")
(include-book "runs-index-destination-proof")
(include-book "runs-builder-promoted-row-proof")

(defmacro fn2-run-index-fits-writer (w bytes writers)
  `(car (fn2-run-pack-bound (len ,bytes) (fn2-run-writers-cursor ,w ,writers) (fn2-run-writers-entries ,w ,writers)
                            (fn2-run-writers-restarts ,w ,writers) (fn2-run-writers-limit ,w ,writers))))

(defun-nx fn2-run-parent-index-position-p (w rows writers)
  (and (fn2-run-entries-layoutp *fn2-overview-index* rows) (equal (fn2-run-writers-entries w writers) (len rows))
       (equal (fn2-run-writers-cursor w writers) (+ *fn2-run-entries-base* (len (fn2-run-entries-octets *fn2-overview-index* rows))))
       (equal (fn2-run-writers-restarts w writers) (len (fn2-run-restart-offsets-spec *fn2-overview-index* rows 0 *fn2-run-entries-base*)))
       (equal (fn2-run-writers-limit w writers) 2048)))

(local
 (defthm fn2-run-full-index-already-has-sixteen-children
   (let ((bytes (fn2-layout-octets *fn2-overview-index* row)))
     (implies (and (fn2-run-parent-index-position-p w rows writers) (fn2-run-values-layoutp *fn2-overview-index* row)
                   (not (fn2-run-index-fits-writer w bytes writers)))
              (and (<= 16 (fn2-run-writers-entries w writers)) (posp (fn2-run-writers-entries w writers)))))
   :hints (("Goal" :use fn2-range-index-fits-sixteen-children
            :in-theory (e/d (fn2-run-parent-index-position-p)
                     (fn2-run-entries-layoutp fn2-run-values-layoutp fn2-run-writers-entries fn2-run-writers-cursor
                      fn2-run-writers-restarts fn2-run-writers-limit fn2-run-pack-bound fn2-run-entries-octets
                      fn2-run-restart-offsets-spec fn2-layout-octets len))))))

(defmacro fn2-run-promoting-index-row (body)
  `(fn2-run-overview-promote-bindings
    (let* ((w (1+ level)) (rf (mv-nth 1 ref)) (rp (mv-nth 2 ref))
           (dst (fn2-run-writers-slot w writers)) (dg (fn2-run-writers-gen w writers))
           (off (fn2-run-writers-cursor w writers)) (idx (fn2-run-writers-entries w writers))
           (nr (fn2-run-writers-restarts w writers)) (ordinal (1+ (fn2-run-writers-ordinal level writers)))
           (bytes (fn2-run-child-index-bytes rows level hrow writers ds))
           (fits (fn2-run-index-fits-writer w bytes writers)))
      (implies (and (fn2-run-overview-promotion-ready-p level builds writers)
                    (fn2-run-encoded-child-input-p level level ib hrow hslot hgen rows bvals cvals writers f pool ds)
                    (<= (+ ib *fn2-run-entry-rows*) (fn2-fields-rows f))
                    (fn2-run-open-index-workspace-p w ib writers restarts rf)
                    (fn2-run-parent-index-position-p w parent-rows writers)
                    (equal (fn2-run-writers-okind w writers) 9) (equal (fn2-run-writers-oslot w writers) 0)
                    (equal (fn2-run-writers-ogen w writers) 1)
                    (implies fits (fn2-run-child-index-destination-p (len bytes) level hslot dst dg off pool))
                    (< nr *fn2-run-restart-capacity*) (unsigned-byte-p 32 (1+ idx)) (unsigned-byte-p 60 ordinal))
               ,body))))

(local
 (defthm fn2-run-parent-position-counts-restarts
   (implies (fn2-run-parent-index-position-p w rows writers) (natp (fn2-run-writers-restarts w writers)))
   :hints (("Goal" :in-theory (e/d (fn2-run-parent-index-position-p)
                     (fn2-run-writers-restarts fn2-run-restart-offsets-spec))))))

(local
 (defthm fn2-run-parent-writer-bounds
   (implies (fn2-run-overview-promotion-ready-p level builds writers)
            (and (natp level) (< (1+ level) (fn2-run-writers-rows writers))
                 (equal (fn2-run-writers-phase (1+ level) writers) *fn2-run-writer-phase-open*)))
   :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory) '(fn2-run-overview-promotion-ready-p))))))

(local
 (defthm fn2-run-open-index-writer-level
   (implies (fn2-run-open-index-workspace-p w base writers restarts f)
            (posp (fn2-run-writers-level w writers)))
   :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory) '(fn2-run-open-index-workspace-p))))))

(local
 (defthm fn2-run-index-result-component
   (equal (mv-nth n (cons a b)) (if (zp n) a (mv-nth (1- n) b)))
   :hints (("Goal" :expand ((mv-nth n (cons a b)))))))

(defun-nx fn2-run-index-promotion-result-p
  (fits level w ordinal dst dg off idx nr bytes rp builds writers restarts commit promote)
  (let ((after (mv-nth 2 promote)))
    (and (equal (mv-nth 1 promote) builds) (equal after (mv-nth 1 commit))
        (if fits
            (and (equal (car promote) :ok)
                 (equal (fn2-run-writers-phase level after) *fn2-run-writer-phase-idle*)
                 (equal (fn2-run-writers-ordinal level after) ordinal)
                 (equal (fn2-run-writers-cursor w after) (+ off (len bytes)))
                 (equal (fn2-run-writers-entries w after) (1+ idx))
                 (equal (fn2-run-writers-restarts w after) (if (equal (mod idx *fn2-run-restart-interval*) 0) (1+ nr) nr))
                 (implies (equal (mod idx *fn2-run-restart-interval*) 0)
                          (equal (fn2-run-restarts-offset (+ (* w *fn2-run-restart-capacity*) nr) (mv-nth 3 promote)) off))
                 (equal (mv-nth 5 promote) (mv-nth 1 (fn2-run-load-bytes bytes dst dg off 9 0 1 rp)))
                 (equal (fn2-run-read-bytes (len bytes) dst dg off 9 0 1 (mv-nth 5 promote)) bytes))
          (and (equal (car promote) :more) (<= 16 (fn2-run-writers-entries w after))
               (equal (fn2-run-writers-phase w after) *fn2-run-writer-phase-closing*) (equal (fn2-run-writers-pos w after) 0)
               (equal (fn2-run-writers-phase level after) (fn2-run-writers-phase level writers))
               (equal (fn2-run-writers-ordinal level after) (fn2-run-writers-ordinal level writers))
               (equal (fn2-run-writers-slot level after) (fn2-run-writers-slot level writers))
               (equal (fn2-run-writers-gen level after) (fn2-run-writers-gen level writers))
               (equal (mv-nth 3 promote) restarts) (equal (mv-nth 5 promote) rp))))))

(defmacro fn2-run-parent-promotion-effects ()
  '(fn2-run-index-promotion-result-p fits level w ordinal dst dg off idx nr bytes rp builds writers restarts commit promote))

(local
 (defthm fn2-run-fitting-index-append
   (let* ((row (fn2-run-unload-values *fn2-overview-index* base f pool))
          (bytes (fn2-layout-octets *fn2-overview-index* row))
          (nr (fn2-run-writers-restarts w writers)) (idx (fn2-run-writers-entries w writers))
          (off (fn2-run-writers-cursor w writers)) (dst (fn2-run-writers-slot w writers)) (dg (fn2-run-writers-gen w writers))
          (add (fn2-run-add w 3 base writers restarts f pool)) (after (mv-nth 1 add)))
     (implies (and (fn2-run-open-index-workspace-p w base writers restarts f) (fn2-run-parent-index-position-p w parent-rows writers)
                   (fn2-run-values-layoutp *fn2-overview-index* row) (fn2-poolp pool) (fn2-pool-wfp pool)
                   (equal (fn2-fields-value (fn2-run-index-digest-field base) f) 1)
                   (equal (fn2-fields-ref-len (fn2-run-index-digest-field base) f) 32)
                   (equal (fn2-run-writers-okind w writers) 9) (equal (fn2-run-writers-oslot w writers) 0)
                   (equal (fn2-run-writers-ogen w writers) 1) (< nr *fn2-run-restart-capacity*) (unsigned-byte-p 32 (1+ idx))
                   (fn2-run-index-fits-writer w bytes writers) (fn2-run-overview-index-write-room-p base dst dg off f pool))
              (and (equal (car add) :ok) (equal (fn2-run-writers-cursor w after) (+ off (len bytes)))
                   (equal (fn2-run-writers-entries w after) (1+ idx))
                   (equal (fn2-run-writers-restarts w after) (if (equal (mod idx *fn2-run-restart-interval*) 0) (1+ nr) nr))
                   (implies (equal (mod idx *fn2-run-restart-interval*) 0)
                            (equal (fn2-run-restarts-offset (+ (* w *fn2-run-restart-capacity*) nr) (mv-nth 2 add)) off))
                   (equal (mv-nth 4 add) (mv-nth 1 (fn2-run-load-bytes bytes dst dg off 9 0 1 pool)))
                   (equal (fn2-run-read-bytes (len bytes) dst dg off 9 0 1 (mv-nth 4 add)) bytes))))
   :rule-classes nil
   :hints (("Goal" :do-not '(preprocess)
            :use (fn2-run-parent-packs-index-by-wire-size fn2-run-parent-appends-index-row fn2-run-open-index-writer-level
                  (:instance fn2-run-parent-position-counts-restarts (rows parent-rows)))
            :in-theory (theory 'minimal-theory)))))

(local
 (defthm fn2-run-prepared-parent-promotion
   (let* ((w (1+ level)) (dst (fn2-run-writers-slot w writers)) (dg (fn2-run-writers-gen w writers))
          (off (fn2-run-writers-cursor w writers)) (idx (fn2-run-writers-entries w writers))
          (nr (fn2-run-writers-restarts w writers)) (ordinal (1+ (fn2-run-writers-ordinal level writers)))
          (row (fn2-run-unload-values *fn2-overview-index* ib rf rp)) (bytes (fn2-layout-octets *fn2-overview-index* row))
          (fits (fn2-run-index-fits-writer w bytes writers)) (parent (fn2-run-add w 3 ib writers restarts rf rp))
          (commit (fn2-run-promote-commit level (car parent) (mv-nth 1 parent))))
     (implies (and (fn2-run-overview-promotion-ready-p level builds writers)
                   (fn2-run-open-index-workspace-p w ib writers restarts rf) (fn2-run-parent-index-position-p w parent-rows writers)
                   (fn2-run-values-layoutp *fn2-overview-index* row) (fn2-poolp rp) (fn2-pool-wfp rp)
                   (equal (fn2-fields-value (fn2-run-index-digest-field ib) rf) 1)
                   (equal (fn2-fields-ref-len (fn2-run-index-digest-field ib) rf) 32)
                   (equal (fn2-run-writers-okind w writers) 9) (equal (fn2-run-writers-oslot w writers) 0)
                   (equal (fn2-run-writers-ogen w writers) 1)
                   (implies fits (fn2-run-overview-index-write-room-p ib dst dg off rf rp))
                   (< nr *fn2-run-restart-capacity*) (unsigned-byte-p 32 (1+ idx)) (unsigned-byte-p 60 ordinal)
                   (equal promote (list (car commit) builds (mv-nth 1 commit) (mv-nth 2 parent)
                                        (mv-nth 3 parent) (mv-nth 4 parent) ds)))
              (fn2-run-parent-promotion-effects)))
   :rule-classes nil
   :hints (("Goal" :do-not '(preprocess)
            :cases ((fn2-run-index-fits-writer (1+ level)
                            (fn2-layout-octets *fn2-overview-index* (fn2-run-unload-values *fn2-overview-index* ib rf rp)) writers))
            :in-theory (union-theories (theory 'minimal-theory)
                         '(fn2-run-index-promotion-result-p fn2-run-index-result-component car-cons cdr-cons (:e equal) (:e zp) (:e mv-nth) (:e binary-+) not)))
           ("Subgoal 1" :do-not '(preprocess)
            :use (fn2-run-parent-writer-bounds
                  (:instance fn2-run-fitting-index-append (w (1+ level)) (base ib) (f rf) (pool rp))
                  (:instance fn2-run-parent-append-keeps-writer-ordinals (w (1+ level)) (j level) (sid 3) (base ib) (f rf) (pool rp))
                  (:instance fn2-run-promotion-releases-appended-child (writers (mv-nth 1 (fn2-run-add (1+ level) 3 ib writers restarts rf rp))))))
           ("Subgoal 2" :do-not '(preprocess)
            :use (fn2-run-parent-writer-bounds
                  (:instance fn2-run-parent-packs-index-by-wire-size (w (1+ level)) (base ib) (f rf) (pool rp))
                  (:instance fn2-run-full-index-already-has-sixteen-children (w (1+ level)) (rows parent-rows)
                               (row (fn2-run-unload-values *fn2-overview-index* ib rf rp)))
                  fn2-run-promotion-keeps-child-on-full-parent)))))

(local
 (defthm fn2-run-promotion-input-equations
   (fn2-run-overview-promote-bindings
    (let* ((w (1+ level)) (rf (mv-nth 1 ref)) (rp (mv-nth 2 ref))
           (size (len (fn2-run-child-index-bytes rows level hrow writers ds)))
           (dst (fn2-run-writers-slot w writers)) (dg (fn2-run-writers-gen w writers)) (off (fn2-run-writers-cursor w writers)))
      (implies (and (fn2-run-overview-promotion-ready-p level builds writers)
                    (fn2-run-encoded-child-input-p level level ib hrow hslot hgen rows bvals cvals writers f pool ds)
                    (<= (+ ib *fn2-run-entry-rows*) (fn2-fields-rows f)))
               (and (equal (fn2-layout-octets *fn2-overview-index* (fn2-run-unload-values *fn2-overview-index* ib rf rp))
                           (fn2-run-child-index-bytes rows level hrow writers ds))
                    (fn2-run-values-layoutp *fn2-overview-index* (fn2-run-unload-values *fn2-overview-index* ib rf rp))
                    (fn2-poolp rp) (fn2-pool-wfp rp)
                    (equal (fn2-fields-value (fn2-run-index-digest-field ib) rf) 1)
                    (equal (fn2-fields-ref-len (fn2-run-index-digest-field ib) rf) 32)
                    (implies (fn2-run-child-index-destination-p size level hslot dst dg off pool)
                             (fn2-run-overview-index-write-room-p ib dst dg off rf rp))
                    (equal promote (list (car commit) builds (mv-nth 1 commit) (mv-nth 2 parent)
                                         (mv-nth 3 parent) (mv-nth 4 parent) ds))))))
   :rule-classes nil
   :hints (("Goal" :do-not '(preprocess)
            :use (fn2-run-builder-promotes-encoded-child
                  (:instance fn2-run-child-prepares-parent-destination (w level) (ib *fn2-run-build-index*) (hrow (+ 136 level))
                    (hslot (fn2-run-builds-hslot 0 builds)) (hgen (fn2-run-builds-hgen 0 builds))
                    (dst (fn2-run-writers-slot (1+ level) writers)) (dg (fn2-run-writers-gen (1+ level) writers))
                    (off (fn2-run-writers-cursor (1+ level) writers)))
                  (:instance fn2-run-promoted-index-row-is-admitted (w level) (ib *fn2-run-build-index*) (hrow (+ 136 level))
                    (hslot (fn2-run-builds-hslot 0 builds)) (hgen (fn2-run-builds-hgen 0 builds))))
            :in-theory (theory 'minimal-theory)))))

(defthm fn2-run-builder-appends-or-retries-promoted-index
  (fn2-run-promoting-index-row (fn2-run-parent-promotion-effects))
  :rule-classes nil
  :hints (("Goal" :do-not '(preprocess)
           :use (fn2-run-promotion-input-equations
                 (:instance fn2-run-prepared-parent-promotion (ib *fn2-run-build-index*) (promote (fn2-run-build-promote 0 level builds writers restarts f pool ds))
                   (rf (mv-nth 1 (fn2-run-promotion-input level level *fn2-run-build-index* (fn2-run-writers-cursor level writers)
                            (+ 136 level) (fn2-run-builds-hslot 0 builds) (fn2-run-builds-hgen 0 builds) writers f pool ds)))
                   (rp (mv-nth 2 (fn2-run-promotion-input level level *fn2-run-build-index* (fn2-run-writers-cursor level writers)
                            (+ 136 level) (fn2-run-builds-hslot 0 builds) (fn2-run-builds-hgen 0 builds) writers f pool ds)))))
           :in-theory (theory 'minimal-theory))))
