; The range builder completes page padding with the pending rows intact.
; Charge the exact number of calls and resume the same loop at header encoding.
(in-package "ACL2")
(include-book "runs-close-step-count-proof")
(local (include-book "columns-observation-frames"))

(local (defcolumns-observation-frame fn2-run-phase-after-close-position fn2-run-writers phase pos))
(local (defcolumns-observation-frame fn2-run-ordinal-after-close-position fn2-run-writers ordinal pos))
(local (defcolumns-observation-frame fn2-run-fields-after-close-position fn2-run-writers fields pos))

(local
 (defthm fn2-run-close-position-keeps-idle-levels
   (equal (fn2-run-below-idle l base (fn2-run-writers-set-pos w n writers))
          (fn2-run-below-idle l base writers))
   :hints (("Goal" :induct (fn2-run-below-idle l base writers)
            :in-theory (e/d (fn2-run-below-idle) (fn2-run-writers-phase fn2-run-writers-set-pos))))))

(defthmd fn2-run-close-position-keeps-scheduled-action
  (equal (fn2-run-scan l b finishing builds (fn2-run-writers-set-pos w n writers))
         (fn2-run-scan l b finishing builds writers))
  :hints (("Goal" :induct (fn2-run-scan l b finishing builds writers)
           :in-theory (e/d (fn2-run-scan)
                    (fn2-run-below-idle fn2-run-builds-wbase fn2-run-builds-height fn2-run-writers-phase
                     fn2-run-writers-ordinal fn2-run-writers-set-pos)))))

(defthmd fn2-run-advancing-close-position-keeps-workspace
  (let ((w (+ l (fn2-run-builds-wbase 0 builds))))
    (implies (and (fn2-run-build-closing-at-p l builds writers restarts f fc ctx)
                  (unsigned-byte-p 32 n) (fn2-fields-wfp f2)
                  (equal (fn2-fields-rows f2) (fn2-fields-rows f)))
             (fn2-run-build-closing-at-p l builds (fn2-run-writers-set-pos w n writers) restarts f2 fc ctx)))
  :hints (("Goal" :in-theory (e/d (fn2-run-build-closing-at-p fn2-run-writerp
                                      fn2-run-close-position-keeps-scheduled-action)
                      (fn2-run-scan fn2-run-writers-set-pos fn2-run-builds-height fn2-run-builds-wbase
                       fn2-run-builds-hbase fn2-run-builds-crow fn2-run-builds-phase fn2-fc-rows fn2-fc-context-rows
                       fn2-run-writers-fields fn2-run-writers-rows fn2-run-writers-wfp fn2-run-restarts-wfp
                       fn2-run-restarts-rows fn2-fields-wfp fn2-fields-rows unsigned-byte-p)))))

(defun-nx fn2-run-padding-window-p (w slot gen pk ps pg at size writers restarts pool)
  (let* ((pos (fn2-run-writers-pos w writers)) (cursor (fn2-run-writers-cursor w writers)))
    (and (fn2-run-closing-page-ready-p w writers restarts pool)
         (<= (* 4 (fn2-run-writers-restarts w writers)) pos)
         (equal slot (fn2-run-writers-slot w writers)) (equal gen (fn2-run-writers-gen w writers))
         (equal pk (fn2-run-writers-okind w writers)) (equal ps (fn2-run-writers-oslot w writers))
         (equal pg (fn2-run-writers-ogen w writers))
         (natp at) (natp size) (<= (+ at size) (+ cursor pos)))))

(local
 (defthm fn2-run-padding-offset-keeps-page
   (let ((after (fn2-run-writers-set-pos w n writers)))
     (and (equal (fn2-run-writers-pos w after) n)
          (equal (fn2-run-writers-phase w after) (fn2-run-writers-phase w writers))
          (equal (fn2-run-writers-slot w after) (fn2-run-writers-slot w writers))
          (equal (fn2-run-writers-gen w after) (fn2-run-writers-gen w writers))
          (equal (fn2-run-writers-okind w after) (fn2-run-writers-okind w writers))
          (equal (fn2-run-writers-oslot w after) (fn2-run-writers-oslot w writers))
          (equal (fn2-run-writers-ogen w after) (fn2-run-writers-ogen w writers))
          (equal (fn2-run-writers-cursor w after) (fn2-run-writers-cursor w writers))
          (equal (fn2-run-writers-restarts w after) (fn2-run-writers-restarts w writers))))
   :hints (("Goal" :in-theory (e/d (fn2-run-writers-set-pos update-fn2-run-writers-pos$ai
                         fn2-run-writers-pos fn2-run-writers-phase fn2-run-writers-slot fn2-run-writers-gen
                         fn2-run-writers-okind fn2-run-writers-oslot fn2-run-writers-ogen
                         fn2-run-writers-cursor fn2-run-writers-restarts nth-update-nth) (nth update-nth))))))

(local
 (defmacro fn2-run-padding-room-theory (&rest rules)
   `(e/d (fn2-run-padding-window-p fn2-run-closing-page-ready-p ,@rules)
     (fn2-run-close-step fn2-run-writers-slot fn2-run-writers-gen fn2-run-writers-okind fn2-run-writers-oslot
      fn2-run-writers-ogen fn2-run-writers-phase fn2-run-writers-fields fn2-run-writers-cursor
      fn2-run-writers-restarts fn2-run-writers-pos fn2-run-writers-set-pos fn2-run-writers-set-phase
      fn2-run-restarts-rows fn2-run-restartsp fn2-run-restarts-wfp
      fn2-run-read-bytes fn2-pool-base fn2-layout-range-code))))

(defthm fn2-run-padding-preserves-window
  (let* ((cursor (fn2-run-writers-cursor w writers)) (pos (fn2-run-writers-pos w writers))
         (left (- *fn2-run-page-size* (+ cursor pos)))
         (close (fn2-run-close-step w 4096 writers restarts f pool))
         (after (mv-nth 1 close)) (pool2 (mv-nth 3 close)))
    (implies (fn2-run-padding-window-p w slot gen pk ps pg at size writers restarts pool)
             (and (natp left)
                  (equal (car close) (if (zp left) :ok :more)) (equal (mv-nth 2 close) f)
                  (equal (fn2-run-read-bytes size slot gen at pk ps pg pool2)
                         (fn2-run-read-bytes size slot gen at pk ps pg pool))
                  (if (zp left)
                      (equal after (fn2-run-writers-set-phase w *fn2-run-writer-phase-heading* writers))
                    (and (equal after (fn2-run-writers-set-pos w (+ pos (min 4096 left)) writers))
                         (unsigned-byte-p 32 (+ pos (min 4096 left)))
                         (fn2-run-padding-window-p w slot gen pk ps pg at size after restarts pool2))))))
  :rule-classes nil
  :hints (("Goal" :use (fn2-run-close-pads-stored-page)
           :in-theory (fn2-run-padding-room-theory))))

(local
 (defthm fn2-run-scheduled-close-has-fields
   (implies (fn2-run-build-closing-at-p l builds writers restarts f fc ctx) (fn2-fields-wfp f))
   :rule-classes nil
   :hints (("Goal" :in-theory (e/d (fn2-run-build-closing-at-p fn2-run-writerp)
                        (fn2-run-scan fn2-fields-wfp fn2-run-writers-wfp fn2-run-restarts-wfp))))))

(defthm fn2-run-heading-phase-after-close
  (equal (fn2-run-writers-phase w (fn2-run-writers-set-phase w *fn2-run-writer-phase-heading* writers))
         *fn2-run-writer-phase-heading*)
  :hints (("Goal" :in-theory (e/d (fn2-run-writers-phase fn2-run-writers-set-phase
                                   update-fn2-run-writers-phase$ai nth-update-nth) (nth update-nth)))))

(local
 (defthm fn2-run-padding-move-keeps-schedule
   (let* ((w (+ l (fn2-run-builds-wbase 0 builds)))
          (close (fn2-run-close-step w 4096 writers restarts f pool))
          (after (mv-nth 1 close)))
     (implies (and (fn2-run-build-closing-at-p l builds writers restarts f fc ctx)
                   (fn2-run-padding-window-p w slot gen pk ps pg at size writers restarts pool))
              (and (member-eq (car close) '(:ok :more))
                   (equal (mv-nth 2 close) f)
                   (equal (fn2-run-read-bytes size slot gen at pk ps pg (mv-nth 3 close))
                          (fn2-run-read-bytes size slot gen at pk ps pg pool))
                   (or (equal (fn2-run-writers-phase w after) *fn2-run-writer-phase-heading*)
                       (and (fn2-run-build-closing-at-p l builds after restarts f fc ctx)
                            (fn2-run-padding-window-p w slot gen pk ps pg at size after restarts (mv-nth 3 close)))))))
   :rule-classes nil
   :hints (("Goal" :do-not '(preprocess)
            :use (fn2-run-scheduled-close-has-fields
                  (:instance fn2-run-padding-preserves-window (w (+ l (fn2-run-builds-wbase 0 builds))))
                  (:instance fn2-run-advancing-close-position-keeps-workspace (f2 f)
                    (n (+ (fn2-run-writers-pos (+ l (fn2-run-builds-wbase 0 builds)) writers)
                          (min 4096 (- *fn2-run-page-size* (+ (fn2-run-writers-cursor (+ l (fn2-run-builds-wbase 0 builds)) writers)
                                                            (fn2-run-writers-pos (+ l (fn2-run-builds-wbase 0 builds)) writers))))))))
            :in-theory (union-theories (theory 'minimal-theory)
                         '(fn2-run-heading-phase-after-close member-equal (:e member-equal) (:e equal)
                           (:e car) (:e cdr) (:e consp)))))))

(defthm fn2-run-builder-preserves-padding-window
  (let* ((w (+ l (fn2-run-builds-wbase 0 builds)))
         (step (fn2-run-run-onestep layout entries src sg inoff unit pages builds curs paths cache
                                    writers restarts f pool fc ctx b3 ds))
         (after (mv-nth 10 step)) (pool2 (mv-nth 13 step)))
    (implies (and (fn2-run-build-closing-at-p l builds writers restarts f fc ctx)
                  (fn2-run-padding-window-p w slot gen pk ps pg at size writers restarts pool))
             (and (equal step (list nil :more entries inoff unit pages builds curs paths cache
                                    after restarts f pool2 fc ctx b3 ds))
                  (equal (fn2-run-read-bytes size slot gen at pk ps pg pool2)
                         (fn2-run-read-bytes size slot gen at pk ps pg pool))
                  (or (equal (fn2-run-writers-phase w after) *fn2-run-writer-phase-heading*)
                      (and (fn2-run-build-closing-at-p l builds after restarts f fc ctx)
                           (fn2-run-padding-window-p w slot gen pk ps pg at size after restarts pool2))))))
  :rule-classes nil
  :hints (("Goal" :do-not '(preprocess)
           :use (fn2-run-padding-move-keeps-schedule (:instance fn2-run-adapter-performs-close-step (off inoff)))
           :in-theory (union-theories (theory 'minimal-theory)
                        '(mv-nth car-cons cdr-cons (:e mv-nth) (:e zp) (:e binary-+) (:e equal) (:e consp))))))

(defmacro fn2-run-padding-close ()
  '(fn2-run-close-step (+ l (fn2-run-builds-wbase 0 builds)) 4096 writers restarts f pool))

(defmacro fn2-run-padding-loop (fuel writers pool)
  `(fn2-run-run-loop ,fuel layout entries src sg off unit pages builds curs paths cache
                    ,writers restarts f ,pool fc ctx b3 ds))

(local
 (defthm fn2-run-padding-includes-close-readiness
   (implies (fn2-run-padding-window-p w slot gen pk ps pg at size writers restarts pool)
            (fn2-run-closing-page-ready-p w writers restarts pool))
   :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory) '(fn2-run-padding-window-p))))))

(defthm fn2-run-padding-step-continues-or-heads
  (let* ((w (+ l (fn2-run-builds-wbase 0 builds)))
         (count (fn2-run-writer-close-steps w writers))
         (close (fn2-run-padding-close)) (after (mv-nth 1 close)) (pool2 (mv-nth 3 close)))
    (implies (and (fn2-run-build-closing-at-p l builds writers restarts f fc ctx)
                  (fn2-run-padding-window-p w slot gen pk ps pg at size writers restarts pool))
             (and (posp count) (<= count 18)
                  (equal (fn2-run-writer-close-steps w after) (1- count))
                  (equal (fn2-run-read-bytes size slot gen at pk ps pg pool2)
                         (fn2-run-read-bytes size slot gen at pk ps pg pool))
                  (if (equal count 1) (equal (fn2-run-writers-phase w after) *fn2-run-writer-phase-heading*)
                    (and (fn2-run-build-closing-at-p l builds after restarts f fc ctx)
                         (fn2-run-padding-window-p w slot gen pk ps pg at size after restarts pool2))))))
  :rule-classes nil
  :hints (("Goal" :do-not '(preprocess)
           :use ((:instance fn2-run-builder-decreases-close-count (inoff off))
                 (:instance fn2-run-builder-preserves-padding-window (inoff off))
                 (:instance fn2-run-padding-preserves-window (w (+ l (fn2-run-builds-wbase 0 builds))))
                 fn2-run-adapter-performs-close-step)
           :in-theory (union-theories (theory 'minimal-theory)
             '(fn2-run-padding-includes-close-readiness mv-nth car-cons cdr-cons (:e member-equal)
               (:e mv-nth) (:e zp) (:e binary-+) (:e equal) (:e consp))))))

(defthm fn2-run-padding-loop-takes-close-step
  (let* ((w (+ l (fn2-run-builds-wbase 0 builds))) (close (fn2-run-padding-close)))
    (implies (and (posp fuel) (fn2-run-build-closing-at-p l builds writers restarts f fc ctx)
                  (fn2-run-padding-window-p w slot gen pk ps pg at size writers restarts pool))
             (equal (fn2-run-padding-loop fuel writers pool)
                    (fn2-run-padding-loop (1- fuel) (mv-nth 1 close) (mv-nth 3 close)))))
  :rule-classes nil
  :hints (("Goal" :do-not '(preprocess)
           :expand ((fn2-run-padding-loop fuel writers pool))
           :use ((:instance fn2-run-padding-preserves-window (w (+ l (fn2-run-builds-wbase 0 builds))))
                 fn2-run-adapter-performs-close-step)
           :in-theory (union-theories (theory 'minimal-theory)
             '(posp zp not mv-nth car-cons cdr-cons (:e member-equal) (:e mv-nth) (:e zp)
               (:e binary-+) (:e equal) (:e consp))))))

(defun-nx fn2-run-padding-induct (fuel l builds writers restarts f pool)
  (declare (xargs :measure (nfix fuel)))
  (if (or (zp fuel) (equal fuel 1)) (list writers pool)
    (let ((close (fn2-run-padding-close)))
      (fn2-run-padding-induct (1- fuel) l builds (mv-nth 1 close) restarts f (mv-nth 3 close)))))

(defun-nx fn2-run-headed-padding-result-p (result w pages builds curs paths cache restarts f fc ctx b3 ds
                                               slot gen pk ps pg at size bytes)
  (let ((after (mv-nth 6 result)) (pool2 (mv-nth 9 result)))
    (and (equal result (list :fuel pages builds curs paths cache after restarts f pool2 fc ctx b3 ds))
         (equal (fn2-run-writers-phase w after) *fn2-run-writer-phase-heading*)
         (equal (fn2-run-read-bytes size slot gen at pk ps pg pool2) bytes))))

(local
 (defthm fn2-run-heading-padding-result
   (equal (fn2-run-headed-padding-result-p (list :fuel pages builds curs paths cache after restarts f pool2 fc ctx b3 ds)
                      w pages builds curs paths cache restarts f fc ctx b3 ds slot gen pk ps pg at size bytes)
          (and (equal (fn2-run-writers-phase w after) *fn2-run-writer-phase-heading*)
               (equal (fn2-run-read-bytes size slot gen at pk ps pg pool2) bytes)))
   :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
                          '(fn2-run-headed-padding-result-p mv-nth car-cons cdr-cons (:e mv-nth)
                            (:e zp) (:e binary-+) (:e equal) (:e consp)))))))

(defthm fn2-run-builder-finishes-page-padding
  (let* ((w (+ l (fn2-run-builds-wbase 0 builds)))
         (result (fn2-run-run-loop fuel layout entries src sg off unit pages builds curs paths cache
                                   writers restarts f pool fc ctx b3 ds))
         (bytes (fn2-run-read-bytes size slot gen at pk ps pg pool)))
    (implies (and (equal fuel (fn2-run-writer-close-steps w writers))
                  (fn2-run-build-closing-at-p l builds writers restarts f fc ctx)
                  (fn2-run-padding-window-p w slot gen pk ps pg at size writers restarts pool))
             (and (posp fuel) (<= fuel 18)
                  (fn2-run-headed-padding-result-p result w pages builds curs paths cache restarts f fc ctx b3 ds
                                                 slot gen pk ps pg at size bytes))))
  :rule-classes nil
  :hints (("Goal" :induct (fn2-run-padding-induct fuel l builds writers restarts f pool)
           :do-not '(preprocess)
           :in-theory (union-theories (theory 'minimal-theory)
                        '((:induction fn2-run-padding-induct) posp zp not (:e equal) (:e zp))))
          ("Subgoal *1/1" :use (fn2-run-padding-step-continues-or-heads fn2-run-padding-loop-takes-close-step)
           :expand ((:free (after pool2) (fn2-run-padding-loop 0 after pool2)))
           :in-theory (union-theories (theory 'minimal-theory) '(fn2-run-heading-padding-result posp zp not mv-nth car-cons cdr-cons (:t fn2-run-run-loop) (:e mv-nth) (:e zp) (:e equal) (:e binary-+) (:e unary--) (:e consp))))
          ("Subgoal *1/2" :use (fn2-run-padding-step-continues-or-heads fn2-run-padding-loop-takes-close-step))))

(local
 (defthm fn2-run-one-less-padding-step
   (implies (natp extra) (equal (+ -1 (+ 1 extra)) extra))))

(local
 (defthm fn2-run-padding-step-from-total
   (equal (+ -1 (+ fuel extra)) (+ (+ -1 fuel) extra))))

(local
 (defthm fn2-run-single-padding-result-fields
   (let* ((w (+ l (fn2-run-builds-wbase 0 builds))) (close (fn2-run-padding-close))
          (r (fn2-run-padding-loop 1 writers pool)))
     (implies (and (fn2-run-build-closing-at-p l builds writers restarts f fc ctx)
                   (fn2-run-padding-window-p w slot gen pk ps pg at size writers restarts pool))
              (and (equal (mv-nth 6 r) (mv-nth 1 close)) (equal (mv-nth 9 r) (mv-nth 3 close)))))
   :rule-classes nil
   :hints (("Goal" :use ((:instance fn2-run-padding-loop-takes-close-step (fuel 1)))
            :expand ((:free (after pool2) (fn2-run-padding-loop 0 after pool2)))
            :in-theory (union-theories (theory 'minimal-theory)
                     '(posp natp mv-nth car-cons cdr-cons (:e <) (:e integerp) (:e mv-nth)
                       (:e binary-+) (:e unary--) (:e equal) (:e consp) (:e zp)))))))

(defthm fn2-run-builder-continues-after-padding
  (let* ((w (+ l (fn2-run-builds-wbase 0 builds)))
         (result (fn2-run-run-loop fuel layout entries src sg off unit pages builds curs paths cache
                                   writers restarts f pool fc ctx b3 ds))
         (after (mv-nth 6 result)) (pool2 (mv-nth 9 result)))
    (implies (and (equal fuel (fn2-run-writer-close-steps w writers)) (natp extra)
                  (fn2-run-build-closing-at-p l builds writers restarts f fc ctx)
                  (fn2-run-padding-window-p w slot gen pk ps pg at size writers restarts pool))
             (equal (fn2-run-run-loop (+ fuel extra) layout entries src sg off unit pages builds curs paths cache
                                      writers restarts f pool fc ctx b3 ds)
                    (fn2-run-run-loop extra layout entries src sg off unit pages builds curs paths cache
                                      after restarts f pool2 fc ctx b3 ds))))
  :rule-classes nil
  :hints (("Goal" :induct (fn2-run-padding-induct fuel l builds writers restarts f pool)
           :do-not '(preprocess)
           :in-theory (union-theories (theory 'minimal-theory)
                       '((:induction fn2-run-padding-induct) posp natp zp not fn2-run-padding-step-from-total
                         unicity-of-0 fix (:e equal) (:e zp) (:e binary-+))))
          ("Subgoal *1/1" :use (fn2-run-padding-step-continues-or-heads fn2-run-single-padding-result-fields
                                (:instance fn2-run-padding-loop-takes-close-step (fuel (+ fuel extra))))
           :expand ((:free (after pool2) (fn2-run-padding-loop 0 after pool2)))
           :in-theory (union-theories (theory 'minimal-theory)
                '(posp natp zp not fn2-run-one-less-padding-step unicity-of-0 fix
                  mv-nth car-cons cdr-cons (:t fn2-run-run-loop) (:e mv-nth) (:e zp)
                  (:e equal) (:e binary-+) (:e unary--) (:e consp))))
          ("Subgoal *1/2" :use (fn2-run-padding-step-continues-or-heads fn2-run-padding-loop-takes-close-step
                                (:instance fn2-run-padding-loop-takes-close-step (fuel (+ fuel extra)))))))
