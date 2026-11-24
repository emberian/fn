; Connect the physical header and contents to the scheduled adapter step.
(in-package "ACL2")
(include-book "runs-headed-page-contents-proof")
(include-book "runs-served")

(defun-nx fn2-run-build-heading-at-p (l builds writers restarts f fc ctx)
  (let* ((height (fn2-run-builds-height 0 builds)) (w (+ l (fn2-run-builds-wbase 0 builds)))
         (crow (fn2-run-builds-crow 0 builds)) (hrow (+ l (fn2-run-builds-hbase 0 builds)))
         (finishing (equal (fn2-run-builds-phase 0 builds) *fn2-run-build-phase-finishing*)))
    (and (<= height *fn2-run-max-levels*) (natp l)
         (equal (fn2-run-scan (1- height) 0 finishing builds writers) (list :head l))
         (< w (fn2-run-writers-rows writers)) (fn2-run-writerp w writers restarts f)
         (< crow (fn2-fc-rows fc)) (< crow (fn2-fc-context-rows ctx)) (unsigned-byte-p 32 hrow)
         (< (fn2-digest-slot crow *fn2-fc-previous-seal*) 4294967296))))

(local
 (defthm fn2-run-headers-enter-sealing
   (let* ((w (+ l (fn2-run-builds-wbase 0 builds))) (head (fn2-run-head w writers restarts f pool))
          (crow (fn2-run-builds-crow 0 builds)) (hrow (+ l (fn2-run-builds-hbase 0 builds))))
     (implies (and (fn2-run-build-heading-at-p l builds writers restarts f fc ctx) (equal (car head) :ok))
              (equal (fn2-run-build-work 0 4096 builds writers restarts f pool fc ctx b3 ds)
                     (list :more l builds (mv-nth 1 head) restarts (mv-nth 2 head) (mv-nth 3 head) fc
                           (fn2-run-seal-context w crow hrow (mv-nth 1 head) ctx) b3 ds))))
   :rule-classes nil
   :hints (("Goal" :in-theory (e/d (fn2-run-build-work fn2-run-build-heading-at-p)
                              (fn2-run-scan fn2-run-writerp fn2-run-writers-rows fn2-run-builds-height
                               fn2-run-builds-wbase fn2-run-builds-crow fn2-run-builds-hbase fn2-run-builds-phase
                               fn2-fc-rows fn2-fc-context-rows fn2-digest-slot fn2-run-close-step fn2-run-close
                               fn2-run-seal-context fn2-run-seal-step fn2-run-head unsigned-byte-p))))))

(local
 (defthm fn2-run-adapter-retains-headed-page
   (let* ((w (+ l (fn2-run-builds-wbase 0 builds))) (head (fn2-run-head w writers restarts f pool))
          (step (fn2-run-run-onestep layout entries src sg off unit pages builds curs paths cache writers restarts f pool fc ctx b3 ds)))
     (implies (and (fn2-run-build-heading-at-p l builds writers restarts f fc ctx) (equal (car head) :ok))
              (and (equal (car step) nil) (equal (mv-nth 1 step) :more)
                   (equal (mv-nth 2 step) entries) (equal (mv-nth 5 step) pages) (equal (mv-nth 10 step) (mv-nth 1 head))
                   (equal (mv-nth 13 step) (mv-nth 3 head)))))
   :rule-classes nil
   :hints (("Goal" :use fn2-run-headers-enter-sealing
            :in-theory (union-theories (theory 'minimal-theory)
                        '(fn2-run-run-onestep mv-nth car-cons cdr-cons eq eql member-equal
                          (:e equal) (:e zp) (:e consp) (:e binary-+) (:e mv-nth) (:e member-equal)))))))

(defthmd fn2-run-adapter-writes-encoded-overview-page
  (let* ((w (+ l (fn2-run-builds-wbase 0 builds))) (level (fn2-run-writers-level w writers))
         (step (fn2-run-run-onestep layout entries src sg off unit pages builds curs paths cache writers restarts f pool fc ctx b3 ds)))
    (implies (and (fn2-run-build-heading-at-p l builds writers restarts f fc ctx)
                  (fn2-run-heading-page-p w writers f pool) (fn2-run-closed-overview-contents-p rows w writers pool))
             (and (not (car step)) (equal (mv-nth 1 step) :more) (equal (mv-nth 2 step) entries) (equal (mv-nth 5 step) pages)
                  (equal (mv-nth 10 step) (fn2-run-writers-set-phase w *fn2-run-writer-phase-sealing* writers))
                  (fn2-run-encoded-overview-page-p rows level (fn2-run-outer-header-values w writers) (fn2-run-inner-header-values w writers)
                       (fn2-run-writers-slot w writers) (fn2-run-writers-gen w writers) (fn2-run-writers-okind w writers)
                       (fn2-run-writers-oslot w writers) (fn2-run-writers-ogen w writers) (mv-nth 13 step)))))
  :hints (("Goal" :use (fn2-run-adapter-retains-headed-page
                      (:instance fn2-run-writer-produces-encoded-overview-page (w (+ l (fn2-run-builds-wbase 0 builds))))
                      (:instance fn2-run-heading-writes-readable-headers (w (+ l (fn2-run-builds-wbase 0 builds)))))
           :in-theory (union-theories (theory 'minimal-theory) '(not (:e equal))))))
