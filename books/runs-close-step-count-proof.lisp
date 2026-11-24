; Count one directory write, bounded padding writes, and the transition
; to header encoding. The range adapter closes a 64 KiB page in at most 18 calls.
(in-package "ACL2")
(include-book "runs-build-close-proof")
(defun fn2-run-page-padding-steps (left)
  (declare (xargs :guard (integerp left) :measure (nfix left)))
  (if (<= (ifix left) 0) 0 (1+ (fn2-run-page-padding-steps (- left 4096)))))

(local
 (defun fn2-run-count-padding-slices (left slices)
   (declare (xargs :verify-guards nil :measure (nfix slices)))
   (if (zp slices) left (fn2-run-count-padding-slices (- left 4096) (1- slices)))))

(local
 (defthm fn2-run-padding-fits-slices
   (implies (and (integerp left) (natp slices) (<= left (* 4096 slices)))
            (<= (fn2-run-page-padding-steps left) slices))
   :rule-classes nil
   :hints (("Goal" :induct (fn2-run-count-padding-slices left slices)
            :expand ((fn2-run-page-padding-steps left))))))

(defun fn2-run-close-steps-left (cursor dir pos)
  (declare (xargs :guard (and (natp cursor) (natp dir) (natp pos))))
  (+ (if (< pos dir) 1 0) 1 (fn2-run-page-padding-steps (- *fn2-run-page-size* (+ cursor (max dir pos))))))

(local
 (defthm fn2-run-padding-count-decreases
   (implies (and (natp left) (posp left))
            (equal (fn2-run-page-padding-steps (- left (min left 4096))) (1- (fn2-run-page-padding-steps left))))
   :hints (("Goal" :cases ((<= left 4096)) :expand ((fn2-run-page-padding-steps left) (fn2-run-page-padding-steps (- left 4096)))))))

(defthmd fn2-run-close-count-bounded
  (implies (and (natp cursor) (natp dir) (natp pos))
           (and (posp (fn2-run-close-steps-left cursor dir pos))
                (<= (fn2-run-close-steps-left cursor dir pos) 18)))
  :hints (("Goal" :use ((:instance fn2-run-padding-fits-slices (left (- *fn2-run-page-size* (+ cursor (max dir pos)))) (slices 16)))
           :in-theory (e/d (fn2-run-close-steps-left) (fn2-run-page-padding-steps)))))

(local
 (defthm fn2-run-close-rank-transition
   (implies (and (natp cursor) (natp pos) (natp dir) (<= (+ cursor pos) *fn2-run-page-size*)
                 (<= (+ cursor dir) *fn2-run-page-size*))
            (equal (cond ((< pos dir) (fn2-run-close-steps-left cursor dir dir))
                         ((equal (+ cursor pos) *fn2-run-page-size*) 0)
                         (t (fn2-run-close-steps-left cursor dir (+ pos (min 4096 (- *fn2-run-page-size* (+ cursor pos)))))))
                   (1- (fn2-run-close-steps-left cursor dir pos))))
   :hints (("Goal" :cases ((< pos dir) (equal (+ cursor pos) *fn2-run-page-size*))
            :use ((:instance fn2-run-padding-count-decreases (left (- *fn2-run-page-size* (+ cursor pos)))))
            :in-theory (e/d (fn2-run-close-steps-left) (fn2-run-page-padding-steps))))))

(local
 (defthm fn2-run-no-padding-left
   (equal (equal (fn2-run-page-padding-steps left) 0) (<= (ifix left) 0))
   :hints (("Goal" :expand ((fn2-run-page-padding-steps left))
            :in-theory (disable fn2-run-page-padding-steps)))))

(local
 (defthm fn2-run-last-close-step
   (implies (and (natp cursor) (natp dir) (natp pos) (<= (+ cursor pos) *fn2-run-page-size*))
            (equal (equal (fn2-run-close-steps-left cursor dir pos) 1)
                   (and (<= dir pos) (equal (+ cursor pos) *fn2-run-page-size*))))
   :rule-classes nil
   :hints (("Goal" :in-theory (e/d (fn2-run-close-steps-left) (fn2-run-page-padding-steps))))))

(local
 (defthm fn2-run-closing-writer-updates
   (let ((moved (fn2-run-writers-set-pos w n writers))
         (headed (fn2-run-writers-set-phase w *fn2-run-writer-phase-heading* writers)))
     (and (equal (fn2-run-writers-pos w moved) n)
          (equal (fn2-run-writers-cursor w moved) (fn2-run-writers-cursor w writers))
          (equal (fn2-run-writers-restarts w moved) (fn2-run-writers-restarts w writers))
          (equal (fn2-run-writers-phase w moved) (fn2-run-writers-phase w writers))
          (equal (fn2-run-writers-phase w headed) *fn2-run-writer-phase-heading*)))
   :hints (("Goal" :in-theory (e/d (fn2-run-writers-set-pos fn2-run-writers-set-phase fn2-run-writers-pos
                                   fn2-run-writers-phase fn2-run-writers-cursor fn2-run-writers-restarts
                                   update-fn2-run-writers-pos$ai update-fn2-run-writers-phase$ai nth-update-nth)
                                  (nth update-nth unsigned-byte-p))))))

(defun-nx fn2-run-writer-close-steps (w writers)
  (if (equal (fn2-run-writers-phase w writers) *fn2-run-writer-phase-closing*)
      (fn2-run-close-steps-left (fn2-run-writers-cursor w writers) (* 4 (fn2-run-writers-restarts w writers))
                                (fn2-run-writers-pos w writers))
    0))

(defthm fn2-run-builder-decreases-close-count
  (let* ((w (+ l (fn2-run-builds-wbase 0 builds)))
         (step (fn2-run-run-onestep layout entries src sg inoff unit pages builds curs paths cache
                                    writers restarts f pool fc ctx b3 ds))
         (after (mv-nth 10 step)) (count (fn2-run-writer-close-steps w writers)))
    (implies (and (fn2-run-build-closing-at-p l builds writers restarts f fc ctx)
                  (fn2-run-closing-page-ready-p w writers restarts pool))
             (and (posp count) (<= count 18) (not (car step)) (equal (mv-nth 1 step) :more)
                  (equal (fn2-run-writer-close-steps w after) (1- count))
                  (equal (fn2-run-writers-phase w after)
                         (if (equal count 1) *fn2-run-writer-phase-heading* *fn2-run-writer-phase-closing*)))))
  :rule-classes nil
  :hints (("Goal" :do-not '(preprocess)
           :use ((:instance fn2-run-adapter-close-preserves-page-prefix (at 0) (size 0))
                 (:instance fn2-run-close-rank-transition (cursor (fn2-run-writers-cursor (+ l (fn2-run-builds-wbase 0 builds)) writers))
                   (dir (* 4 (fn2-run-writers-restarts (+ l (fn2-run-builds-wbase 0 builds)) writers)))
                   (pos (fn2-run-writers-pos (+ l (fn2-run-builds-wbase 0 builds)) writers)))
                 (:instance fn2-run-last-close-step (cursor (fn2-run-writers-cursor (+ l (fn2-run-builds-wbase 0 builds)) writers))
                   (dir (* 4 (fn2-run-writers-restarts (+ l (fn2-run-builds-wbase 0 builds)) writers)))
                   (pos (fn2-run-writers-pos (+ l (fn2-run-builds-wbase 0 builds)) writers)))
                 (:instance fn2-run-close-count-bounded (cursor (fn2-run-writers-cursor (+ l (fn2-run-builds-wbase 0 builds)) writers))
                   (dir (* 4 (fn2-run-writers-restarts (+ l (fn2-run-builds-wbase 0 builds)) writers)))
                   (pos (fn2-run-writers-pos (+ l (fn2-run-builds-wbase 0 builds)) writers))))
           :in-theory (e/d (fn2-run-writer-close-steps fn2-run-closing-page-ready-p)
                (fn2-run-close-steps-left fn2-run-build-closing-at-p fn2-run-run-onestep fn2-run-builds-wbase
                 fn2-run-writers-cursor fn2-run-writers-phase fn2-run-writers-restarts fn2-run-writers-pos
                 fn2-run-writers-set-pos fn2-run-writers-set-phase fn2-run-writers-fields fn2-run-writers-slot
                 fn2-run-writers-gen fn2-run-writers-okind fn2-run-writers-oslot fn2-run-writers-ogen
                 fn2-pool-base fn2-run-restarts-rows fn2-run-restartsp fn2-run-restarts-wfp fn2-layout-range-code)))))
