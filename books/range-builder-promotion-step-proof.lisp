; One driver call submits a sealed child to its parent. Only a fitting
; reference extends the parent index. Both paths retain the pending input.
(in-package "ACL2")
(include-book "runs-index-promotion-proof")
(include-book "runs-promotion-schedule-proof")
(include-book "range-promoted-child-proof")

(local
 (defthm fn2-run-index-promotion-continues
   (implies (fn2-run-index-promotion-result-p fits level w ordinal dst dg off idx nr bytes rp builds writers restarts commit promote)
            (member-eq (car promote) '(:ok :more)))
   :rule-classes nil
   :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory) '(fn2-run-index-promotion-result-p member-equal (:e member-equal) (:e equal)) )))))

(local
 (defthm fn2-run-promoted-parent-continues
   (fn2-run-promoting-index-row (and (fn2-run-parent-promotion-effects) (member-eq (car promote) '(:ok :more))))
   :rule-classes nil
   :hints (("Goal" :do-not '(preprocess)
            :use (fn2-run-builder-appends-or-retries-promoted-index
                  (:instance fn2-run-index-promotion-continues (level level) (w (1+ level))
                    (dst (fn2-run-writers-slot (1+ level) writers)) (dg (fn2-run-writers-gen (1+ level) writers))
                    (idx (fn2-run-writers-entries (1+ level) writers)) (nr (fn2-run-writers-restarts (1+ level) writers))
                    (off (fn2-run-writers-cursor (1+ level) writers)) (ordinal (1+ (fn2-run-writers-ordinal level writers)))
                    (bytes (fn2-run-child-index-bytes rows level (+ 136 level) writers ds))
                    (fits (fn2-run-index-fits-writer (1+ level) (fn2-run-child-index-bytes rows level (+ 136 level) writers ds) writers))
                    (rp (mv-nth 2 (fn2-run-promotion-input level level *fn2-run-build-index* (fn2-run-writers-cursor level writers)
                               (+ 136 level) (fn2-run-builds-hslot 0 builds) (fn2-run-builds-hgen 0 builds) writers f pool ds)))
                    (commit (let* ((ref (fn2-run-promotion-input level level *fn2-run-build-index* (fn2-run-writers-cursor level writers)
                                               (+ 136 level) (fn2-run-builds-hslot 0 builds) (fn2-run-builds-hgen 0 builds) writers f pool ds))
                                   (parent (fn2-run-add (1+ level) 3 *fn2-run-build-index* writers restarts (mv-nth 1 ref) (mv-nth 2 ref))))
                              (fn2-run-promote-commit level (car parent) (mv-nth 1 parent))))
                    (promote (fn2-run-build-promote 0 level builds writers restarts f pool ds))))
            :in-theory (theory 'minimal-theory)))))

(local
 (defthm fn2-run-driver-carries-promoted-state
   (let ((promote (fn2-run-build-promote 0 level builds writers restarts f pool ds)))
     (implies (and (equal (fn2-run-build-work 0 4096 builds writers restarts f pool fc ctx b3 ds)
                          (list :promote level builds writers restarts f pool fc ctx b3 ds))
                   (member-eq (car promote) '(:ok :more)))
              (equal (fn2-run-run-onestep layout entries src sg at unit pages builds curs paths cache writers restarts f pool fc ctx b3 ds)
                     (list nil :more entries at unit pages (mv-nth 1 promote) curs paths cache (mv-nth 2 promote)
                           (mv-nth 3 promote) (mv-nth 4 promote) (mv-nth 5 promote) fc ctx b3 (mv-nth 6 promote)))))
   :rule-classes nil
   :hints (("Goal" :cases ((equal (car (fn2-run-build-promote 0 level builds writers restarts f pool ds)) :ok))
            :in-theory (union-theories (theory 'minimal-theory)
                         '(fn2-run-run-onestep eq eql member-equal mv-nth car-cons cdr-cons (:e equal) (:e zp) (:e binary-+) (:e mv-nth)))))))

(local
 (defthm fn2-run-scheduled-promotion-result
   (let ((promote (fn2-run-build-promote 0 level builds writers restarts f pool ds))
         (height (fn2-run-builds-height 0 builds)) (crow (fn2-run-builds-crow 0 builds)))
     (implies (and (fn2-run-overview-promotion-ready-p level builds writers) (posp height) (<= height *fn2-run-max-levels*)
                   (fn2-run-higher-writers-available-p (1- height) (1+ level) writers)
                   (fn2-run-writerp level writers restarts f) (< crow (fn2-fc-rows fc)) (< crow (fn2-fc-context-rows ctx))
                   (member-eq (car promote) '(:ok :more)))
              (equal (fn2-run-run-onestep layout entries src sg at unit pages builds curs paths cache writers restarts f pool fc ctx b3 ds)
                     (list nil :more entries at unit pages (mv-nth 1 promote) curs paths cache (mv-nth 2 promote)
                           (mv-nth 3 promote) (mv-nth 4 promote) (mv-nth 5 promote) fc ctx b3 (mv-nth 6 promote)))))
   :rule-classes nil
   :hints (("Goal" :do-not '(preprocess) :use (fn2-run-work-schedules-parent-promotion fn2-run-driver-carries-promoted-state)
            :in-theory (theory 'minimal-theory)))))

(defthm fn2-run-driver-promotes-sealed-child
  (fn2-run-promoting-index-row
   (let* ((height (fn2-run-builds-height 0 builds)) (crow (fn2-run-builds-crow 0 builds))
          (step (fn2-run-run-onestep layout entries src sg at unit pages builds curs paths cache writers restarts f pool fc ctx b3 ds)))
     (implies (and (posp height) (<= height *fn2-run-max-levels*)
                   (fn2-run-higher-writers-available-p (1- height) w writers)
                   (fn2-run-writerp level writers restarts f) (< crow (fn2-fc-rows fc)) (< crow (fn2-fc-context-rows ctx)))
              (and (equal step (list nil :more entries at unit pages (mv-nth 1 promote) curs paths cache (mv-nth 2 promote)
                                     (mv-nth 3 promote) (mv-nth 4 promote) (mv-nth 5 promote) fc ctx b3 (mv-nth 6 promote)))
                   (fn2-run-parent-promotion-effects)))))
  :rule-classes nil
  :hints (("Goal" :do-not '(preprocess)
           :use (fn2-run-promoted-parent-continues fn2-run-scheduled-promotion-result)
           :in-theory (theory 'minimal-theory))))

(defthm fn2-range-builder-promotion-step
  (fn2-run-promoting-index-row
   (let* ((height (fn2-run-builds-height 0 builds)) (crow (fn2-run-builds-crow 0 builds))
          (step (fn2-run-run-onestep layout entries src sg at unit pages builds curs paths cache writers restarts f pool fc ctx b3 ds))
          (child (if (zp level) rows (append-lst subtrees)))
          (page (list level (fn2-run-writers-unit level writers) (fn2-run-writers-counter level writers)
                            (fn2-run-writers-slot level writers) (fn2-run-writers-gen level writers)))
          (row (fn2-run-unload-values *fn2-overview-index* ib rf rp)))
     (implies (and (posp height) (<= height *fn2-run-max-levels*)
                   (fn2-run-higher-writers-available-p (1- height) w writers)
                   (fn2-run-writerp level writers restarts f) (< crow (fn2-fc-rows fc)) (< crow (fn2-fc-context-rows ctx))
                   (true-listp rows) (implies (not (zp level)) (fn2-range-indexes-children-p rows subtrees))
                   (fn2-range-indexes-children-p parent-rows children) (fn2-range-index-addresses-p parent-rows child-pages))
              (and (equal step (list nil :more entries at unit pages (mv-nth 1 promote) curs paths cache (mv-nth 2 promote)
                                     (mv-nth 3 promote) (mv-nth 4 promote) (mv-nth 5 promote) fc ctx b3 (mv-nth 6 promote)))
                   (fn2-run-parent-promotion-effects)
                   (implies fits
                     (and (fn2-range-indexes-children-p (append parent-rows (list row)) (append children (list child)))
                          (fn2-range-index-addresses-p (append parent-rows (list row)) (append child-pages (list page)))))))))
  :rule-classes nil
  :hints (("Goal"
           :do-not '(preprocess)
           :use (fn2-run-driver-promotes-sealed-child
                 (:instance fn2-range-promotion-extends-parent-index (w level) (ib *fn2-run-build-index*) (hrow (+ 136 level))
                   (hslot (fn2-run-builds-hslot 0 builds)) (hgen (fn2-run-builds-hgen 0 builds))
                   (index parent-rows) (pages child-pages)))
           :in-theory (theory 'minimal-theory))))
