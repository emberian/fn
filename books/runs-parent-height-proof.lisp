; A sealed top page finishes the run when it is the only root.
; Otherwise the builder extends its height and requests a fresh parent.
(in-package "ACL2")
(include-book "runs-served")

(defun-nx fn2-run-sealed-top-ready-p (level builds writers restarts f fc ctx)
  (let ((p (1+ level)) (row (fn2-run-builds-crow 0 builds)))
    (and (natp level) (< p *fn2-run-max-levels*) (posp (fn2-run-builds-height 0 builds))
         (equal level (1- (fn2-run-builds-height 0 builds)))
         (equal (fn2-run-builds-wbase 0 builds) 0) (equal (fn2-run-builds-fields 0 builds) 0)
         (equal (fn2-run-builds-schema 0 builds) 3) (equal (fn2-run-builds-hbase 0 builds) 136)
         (< p (fn2-run-writers-rows writers)) (equal (fn2-run-writers-phase level writers) *fn2-run-writer-phase-sealed*)
         (equal (fn2-run-writers-phase p writers) *fn2-run-writer-phase-idle*)
         (fn2-run-writerp level writers restarts f) (fn2-run-writerp p writers restarts f)
         (<= (+ *fn2-run-build-index* *fn2-run-entry-rows*) (fn2-fields-rows f))
         (< row (fn2-fc-rows fc)) (< row (fn2-fc-context-rows ctx)))))

(defun-nx fn2-run-top-is-root-p (level builds writers)
  (and (equal (fn2-run-builds-phase 0 builds) *fn2-run-build-phase-finishing*)
       (equal (fn2-run-writers-ordinal level writers) 0) (fn2-run-below-idle level 0 writers)))

(local
 (defthm fn2-run-scan-at-sealed-top
   (let ((fin (equal (fn2-run-builds-phase 0 builds) *fn2-run-build-phase-finishing*)))
     (implies (and (natp level) (equal (fn2-run-builds-height 0 builds) (1+ level))
                   (equal (fn2-run-builds-wbase 0 builds) 0)
                   (equal (fn2-run-writers-phase level writers) *fn2-run-writer-phase-sealed*))
              (equal (fn2-run-scan level 0 fin builds writers)
                     (list (if (fn2-run-top-is-root-p level builds writers) :root :promote) level))))
   :rule-classes nil
   :hints (("Goal" :expand ((:free (fin) (fn2-run-scan level 0 fin builds writers)))
            :in-theory (e/d (fn2-run-top-is-root-p)
                            (fn2-run-below-idle fn2-run-scan fn2-run-writers-ordinal fn2-run-writers-phase
                             fn2-run-builds-wbase fn2-run-builds-height fn2-run-builds-phase))))))

(local
 (defthm fn2-run-work-on-root-or-promotion
   (let* ((height (fn2-run-builds-height 0 builds)) (crow (fn2-run-builds-crow 0 builds))
          (fin (equal (fn2-run-builds-phase 0 builds) *fn2-run-build-phase-finishing*))
          (w (+ (fn2-run-builds-wbase 0 builds) level)))
     (implies (and (<= height *fn2-run-max-levels*)
                   (equal (fn2-run-scan (1- height) 0 fin builds writers) (list (if root :root :promote) level))
                   (natp level) (< w (fn2-run-writers-rows writers)) (fn2-run-writerp w writers restarts f)
                   (< crow (fn2-fc-rows fc)) (< crow (fn2-fc-context-rows ctx))
                   (unsigned-byte-p 32 (+ (fn2-run-builds-hbase 0 builds) level)))
              (equal (fn2-run-build-work 0 4096 builds writers restarts f pool fc ctx b3 ds)
                     (list (if root :root :promote) level
                           (if root (fn2-run-builds-set-phase 0 *fn2-run-build-phase-done* builds) builds)
                           writers restarts f pool fc ctx b3 ds))))
   :rule-classes nil
   :hints (("Goal" :cases (root) :do-not '(preprocess)
            :in-theory (union-theories (theory 'minimal-theory)
                          '(fn2-run-build-work eq eql car-cons cdr-cons mv-nth (:e equal) (:e zp) (:e binary-+) (:e mv-nth)))))))

(local
 (defthm fn2-run-sealed-top-work
   (let* ((root (fn2-run-top-is-root-p level builds writers))
          (work (fn2-run-build-work 0 4096 builds writers restarts f pool fc ctx b3 ds)))
     (implies (fn2-run-sealed-top-ready-p level builds writers restarts f fc ctx)
              (equal work (list (if root :root :promote) level
                                (if root (fn2-run-builds-set-phase 0 *fn2-run-build-phase-done* builds) builds)
                                writers restarts f pool fc ctx b3 ds))))
   :rule-classes nil
   :hints (("Goal" :do-not '(preprocess)
            :use (fn2-run-scan-at-sealed-top
                  (:instance fn2-run-work-on-root-or-promotion (root (fn2-run-top-is-root-p level builds writers))))
            :in-theory (e/d (fn2-run-sealed-top-ready-p)
                      (fn2-run-top-is-root-p fn2-run-build-work fn2-run-scan fn2-run-builds-set-phase
                       fn2-run-builds-height fn2-run-builds-phase fn2-run-builds-wbase fn2-run-builds-hbase
                       fn2-run-builds-crow fn2-run-builds-fields fn2-run-builds-schema fn2-fields-rows
                       fn2-fc-rows fn2-fc-context-rows fn2-run-writers-rows fn2-run-writers-phase fn2-run-writerp))))))

(local
 (defthm fn2-run-sealed-top-grows-parent
   (implies (fn2-run-sealed-top-ready-p level builds writers restarts f fc ctx)
            (equal (fn2-run-build-promote 0 level builds writers restarts f pool ds)
                   (list :need-page (fn2-run-builds-set-height 0 (+ 2 level) builds) writers restarts f pool ds)))
   :rule-classes nil
   :hints (("Goal" :in-theory (e/d (fn2-run-build-promote fn2-run-promote-check fn2-run-sealed-top-ready-p)
                       (fn2-run-builds-height fn2-run-builds-set-height fn2-run-builds-wbase fn2-run-builds-fields
                        fn2-run-builds-phase fn2-run-builds-schema fn2-run-builds-hbase fn2-run-builds-crow
                        fn2-run-writers-phase fn2-run-writers-rows fn2-run-writerp fn2-fields-rows fn2-fc-rows
                        fn2-fc-context-rows fn2-run-layout-decode fn2-run-child-ref fn2-run-add fn2-run-promote-commit))))))

(defthmd fn2-run-driver-finishes-root-or-grows-parent
  (let* ((root (fn2-run-top-is-root-p level builds writers))
         (step (fn2-run-run-onestep layout entries src sg off unit pages builds curs paths cache writers restarts f pool fc ctx b3 ds)))
    (implies (fn2-run-sealed-top-ready-p level builds writers restarts f fc ctx)
             (equal step (list (if root t nil) (if root :root :more) entries off unit pages
                             (if root (fn2-run-builds-set-phase 0 *fn2-run-build-phase-done* builds)
                               (fn2-run-builds-set-height 0 (+ 2 level) builds))
                             curs paths cache writers restarts f pool fc ctx b3 ds))))
  :hints (("Goal" :do-not '(preprocess) :cases ((fn2-run-top-is-root-p level builds writers))
           :use (fn2-run-sealed-top-work fn2-run-sealed-top-grows-parent)
           :in-theory (union-theories (theory 'minimal-theory)
                      '(fn2-run-run-onestep eq eql member-equal mv-nth car-cons cdr-cons (:e equal) (:e zp)
                        (:e binary-+) (:e mv-nth) (:e member-equal))))))

(defthmd fn2-run-grown-parent-requests-its-page
  (let* ((grown (fn2-run-builds-set-height 0 (+ 2 level) builds)) (p (1+ level))
         (work (fn2-run-build-work 0 4096 grown writers restarts f pool fc ctx b3 ds)))
    (implies (fn2-run-sealed-top-ready-p level builds writers restarts f fc ctx)
             (equal work (list :need-page p grown writers restarts f pool fc ctx b3 ds))))
  :hints (("Goal" :expand ((:free (fin b) (fn2-run-scan (+ 1 level) 0 fin b writers)))
           :in-theory (e/d (fn2-run-sealed-top-ready-p fn2-run-build-work fn2-run-builds-set-height update-fn2-run-builds-height$ai
                            fn2-run-builds-height fn2-run-builds-wbase fn2-run-builds-hbase fn2-run-builds-crow fn2-run-builds-phase nth-update-nth)
                        (fn2-run-scan fn2-run-below-idle fn2-run-writers-phase fn2-run-writers-rows fn2-run-writers-ordinal
                         fn2-run-writerp fn2-fields-rows fn2-fc-rows fn2-fc-context-rows fn2-run-builds-fields fn2-run-builds-schema
                         fn2-run-head fn2-run-close fn2-run-close-step fn2-run-seal-step fn2-run-seal-context nth update-nth)))))
