; The actual run loop has written zeros throughout the page tail when the
; closing writer reaches the header. Charge its existing count of close steps.
(in-package "ACL2")
(include-book "runs-page-zero-padding-proof")

(local
 (defthm fn2-run-zero-padding-window
   (implies (fn2-run-page-padding-zero-p w start slot gen writers restarts pool)
            (fn2-run-padding-window-p w slot gen 9 0 1 0 0 writers restarts pool))
   :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory) '(fn2-run-page-padding-zero-p))))))

(local
 (defthm fn2-run-window-has-closing-phase
   (implies (fn2-run-padding-window-p w slot gen pk ps pg at size writers restarts pool)
            (equal (fn2-run-writers-phase w writers) *fn2-run-writer-phase-closing*))
   :rule-classes nil
   :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
                          '(fn2-run-padding-window-p fn2-run-closing-page-ready-p))))))

(local
 (defthm fn2-run-padding-status-changes-phase
   (let* ((close (fn2-run-close-step w 4096 writers restarts f pool)) (after (mv-nth 1 close)))
     (implies (fn2-run-padding-window-p w slot gen 9 0 1 0 0 writers restarts pool)
              (equal (fn2-run-writers-phase w after)
                     (if (equal (car close) :ok) *fn2-run-writer-phase-heading* *fn2-run-writer-phase-closing*))))
   :rule-classes nil
   :hints (("Goal" :do-not '(preprocess)
            :use ((:instance fn2-run-padding-preserves-window (pk 9) (ps 0) (pg 1) (at 0) (size 0))
                  (:instance fn2-run-window-has-closing-phase (pk 9) (ps 0) (pg 1) (at 0) (size 0)
                    (writers (mv-nth 1 (fn2-run-close-step w 4096 writers restarts f pool)))
                    (pool (mv-nth 3 (fn2-run-close-step w 4096 writers restarts f pool)))))
            :in-theory (union-theories (theory 'minimal-theory) '(fn2-run-heading-phase-after-close (:e equal)))))))

(local
 (defthm fn2-run-counted-close-extends-zero-padding
   (let* ((w (+ l (fn2-run-builds-wbase 0 builds))) (count (fn2-run-writer-close-steps w writers))
          (close (fn2-run-close-step w 4096 writers restarts f pool))
          (after (mv-nth 1 close)) (pool2 (mv-nth 3 close)))
     (implies (and (fn2-run-build-closing-at-p l builds writers restarts f fc ctx)
                   (fn2-run-page-padding-zero-p w start slot gen writers restarts pool))
              (and (posp count) (<= count 18)
                   (equal (fn2-run-writer-close-steps w after) (1- count))
                   (if (equal count 1)
                       (fn2-ribbon-zero-region-p (- 65536 start) start slot gen pool2)
                     (and (fn2-run-build-closing-at-p l builds after restarts f fc ctx)
                          (fn2-run-page-padding-zero-p w start slot gen after restarts pool2))))))
   :rule-classes nil
   :hints (("Goal" :do-not '(preprocess)
            :use ((:instance fn2-run-padding-step-continues-or-heads (pk 9) (ps 0) (pg 1) (at 0) (size 0))
                  (:instance fn2-run-closing-page-extends-zero-padding (w (+ l (fn2-run-builds-wbase 0 builds))))
                  (:instance fn2-run-padding-status-changes-phase (w (+ l (fn2-run-builds-wbase 0 builds))))
                  (:instance fn2-run-window-has-closing-phase (pk 9) (ps 0) (pg 1) (at 0) (size 0)
                    (w (+ l (fn2-run-builds-wbase 0 builds)))
                    (writers (mv-nth 1 (fn2-run-close-step (+ l (fn2-run-builds-wbase 0 builds)) 4096 writers restarts f pool)))
                    (pool (mv-nth 3 (fn2-run-close-step (+ l (fn2-run-builds-wbase 0 builds)) 4096 writers restarts f pool)))))
            :in-theory (union-theories (theory 'minimal-theory) '(fn2-run-zero-padding-window (:e equal)))))))

(defthm fn2-run-builder-finishes-zero-padding
  (let* ((w (+ l (fn2-run-builds-wbase 0 builds)))
         (result (fn2-run-run-loop fuel layout entries src sg off unit pages builds curs paths cache
                                   writers restarts f pool fc ctx b3 ds)))
    (implies (and (equal fuel (fn2-run-writer-close-steps w writers))
                  (fn2-run-build-closing-at-p l builds writers restarts f fc ctx)
                  (fn2-run-page-padding-zero-p w start slot gen writers restarts pool))
             (fn2-ribbon-zero-region-p (- 65536 start) start slot gen (mv-nth 9 result))))
  :rule-classes nil
  :hints (("Goal" :induct (fn2-run-padding-induct fuel l builds writers restarts f pool)
           :do-not '(preprocess)
           :in-theory (union-theories (theory 'minimal-theory)
                       '((:induction fn2-run-padding-induct) fn2-run-zero-padding-window posp zp not (:e equal) (:e zp))))
          ("Subgoal *1/1" :use (fn2-run-counted-close-extends-zero-padding
                                (:instance fn2-run-padding-loop-takes-close-step (pk 9) (ps 0) (pg 1) (at 0) (size 0)))
           :expand ((:free (ww pp) (fn2-run-run-loop 0 layout entries src sg off unit pages builds curs paths cache
                                                      ww restarts f pp fc ctx b3 ds)))
           :in-theory (union-theories (theory 'minimal-theory) '(fn2-run-zero-padding-window posp zp not mv-nth car-cons cdr-cons
                              (:t fn2-run-run-loop) (:e mv-nth) (:e zp) (:e equal) (:e binary-+) (:e unary--) (:e consp))))
          ("Subgoal *1/2" :use (fn2-run-counted-close-extends-zero-padding
                                (:instance fn2-run-padding-loop-takes-close-step (pk 9) (ps 0) (pg 1) (at 0) (size 0))))))
