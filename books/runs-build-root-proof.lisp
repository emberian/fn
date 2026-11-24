; A sealed top writer with all lower writers idle finishes the real
; adapter loop immediately. Its complete list of page addresses and the
; underlying bytes are exactly those handed off to installation.
(in-package "ACL2")
(include-book "runs-served")

(defun-nx fn2-run-finished-root-p (builds writers restarts f fc ctx)
  (let* ((height (fn2-run-builds-height 0 builds)) (l (1- height))
         (wbase (fn2-run-builds-wbase 0 builds)) (w (+ wbase l))
         (crow (fn2-run-builds-crow 0 builds)) (hrow (+ l (fn2-run-builds-hbase 0 builds))))
    (and (posp height) (<= height *fn2-run-max-levels*)
         (equal (fn2-run-builds-phase 0 builds) *fn2-run-build-phase-finishing*)
         (equal (fn2-run-writers-phase w writers) *fn2-run-writer-phase-sealed*)
         (equal (fn2-run-writers-ordinal w writers) 0) (fn2-run-below-idle l wbase writers)
         (< w (fn2-run-writers-rows writers)) (fn2-run-writerp w writers restarts f)
         (< crow (fn2-fc-rows fc)) (< crow (fn2-fc-context-rows ctx)) (unsigned-byte-p 32 hrow))))

(local
 (defthm fn2-run-finished-top-is-root
   (let ((l (1- (fn2-run-builds-height 0 builds))))
     (implies (fn2-run-finished-root-p builds writers restarts f fc ctx)
              (equal (fn2-run-scan l 0 t builds writers) (list :root l))))
   :rule-classes nil
   :hints (("Goal" :expand ((fn2-run-scan (1- (fn2-run-builds-height 0 builds)) 0 t builds writers))
            :in-theory (e/d (fn2-run-finished-root-p)
                        (fn2-run-scan fn2-run-below-idle fn2-run-writers-phase fn2-run-writers-ordinal
                         fn2-run-builds-height fn2-run-builds-wbase fn2-run-writerp fn2-run-writers-rows
                         fn2-run-builds-phase fn2-run-builds-crow fn2-run-builds-hbase fn2-fc-rows fn2-fc-context-rows))))))

(local
 (defthm fn2-run-work-completes-root
   (implies (fn2-run-finished-root-p builds writers restarts f fc ctx)
            (equal (fn2-run-build-work 0 4096 builds writers restarts f pool fc ctx b3 ds)
                   (list :root (1- (fn2-run-builds-height 0 builds))
                         (fn2-run-builds-set-phase 0 *fn2-run-build-phase-done* builds)
                         writers restarts f pool fc ctx b3 ds)))
   :rule-classes nil
   :hints (("Goal" :use fn2-run-finished-top-is-root
            :in-theory (e/d (fn2-run-build-work fn2-run-finished-root-p)
                        (fn2-run-scan fn2-run-below-idle fn2-run-writers-phase fn2-run-writers-ordinal
                         fn2-run-builds-height fn2-run-builds-wbase fn2-run-writerp fn2-run-writers-rows
                         fn2-run-builds-phase fn2-run-builds-crow fn2-run-builds-hbase fn2-fc-rows fn2-fc-context-rows
                         fn2-run-builds-set-phase fn2-run-close-step fn2-run-head fn2-run-seal-step
                         fn2-run-close fn2-run-seal-context))))))

(defthmd fn2-run-build-returns-completed-pages
  (implies (and (posp fuel) (fn2-run-finished-root-p builds writers restarts f fc ctx))
           (equal (fn2-run-run-loop fuel layout entries src sg off unit pages builds curs paths cache writers restarts
                                    f pool fc ctx b3 ds)
                  (list :root pages (fn2-run-builds-set-phase 0 *fn2-run-build-phase-done* builds)
                        curs paths cache writers restarts f pool fc ctx b3 ds)))
  :hints (("Goal" :use fn2-run-work-completes-root
           :expand ((fn2-run-run-loop fuel layout entries src sg off unit pages builds curs paths cache writers restarts
                                      f pool fc ctx b3 ds))
           :in-theory (union-theories (theory 'minimal-theory)
                    '(fn2-run-run-onestep posp zp eq eql mv-nth car-cons cdr-cons
                      (:e equal) (:e zp) (:e consp) (:e binary-+) (:e mv-nth))))))
