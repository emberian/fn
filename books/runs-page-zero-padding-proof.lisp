; At the end of the restart directory, padding starts with an empty
; zero region. Each real close step extends it up to the next position.
(in-package "ACL2")
(include-book "runs-padding-completion-proof")
(include-book "ribbon-false-neg-finish-proof")

(defun-nx fn2-run-page-padding-zero-p (w start slot gen writers restarts pool)
  (let* ((cursor (fn2-run-writers-cursor w writers)) (pos (fn2-run-writers-pos w writers)))
    (and (fn2-run-padding-window-p w slot gen 9 0 1 0 0 writers restarts pool)
         (natp start) (equal start (+ cursor (* 4 (fn2-run-writers-restarts w writers))))
         (fn2-ribbon-zero-region-p (- (+ cursor pos) start) start slot gen pool))))

(defthmd fn2-run-page-padding-starts-at-directory-end
  (implies (and (fn2-run-padding-window-p w slot gen 9 0 1 0 0 writers restarts pool)
                (natp start) (equal start (+ (fn2-run-writers-cursor w writers) (fn2-run-writers-pos w writers)))
                (equal (fn2-run-writers-pos w writers) (* 4 (fn2-run-writers-restarts w writers))))
           (fn2-run-page-padding-zero-p w start slot gen writers restarts pool))
  :hints (("Goal" :in-theory (e/d (fn2-run-page-padding-zero-p)
                                 (fn2-run-padding-window-p fn2-run-writers-cursor fn2-run-writers-restarts fn2-run-writers-pos))
           :expand ((:free (n) (fn2-ribbon-zero-region-p n start slot gen pool))))))

(local
 (defthm fn2-run-padding-position-offsets
   (let ((moved (fn2-run-writers-set-pos w n writers)))
     (and (equal (fn2-run-writers-pos w moved) n)
          (equal (fn2-run-writers-cursor w moved) (fn2-run-writers-cursor w writers))
          (equal (fn2-run-writers-restarts w moved) (fn2-run-writers-restarts w writers))))
   :hints (("Goal" :in-theory (e/d (fn2-run-writers-set-pos update-fn2-run-writers-pos$ai fn2-run-writers-pos
                                    fn2-run-writers-cursor fn2-run-writers-restarts nth-update-nth)
                                  (nth update-nth))))))

(local
 (defthmd fn2-run-close-step-writes-padding
   (let* ((pos (+ (fn2-run-writers-cursor w writers) (fn2-run-writers-pos w writers)))
          (size (min 4096 (- 65536 pos))) (write (fn2-run-zero size slot gen pos 9 0 1 pool))
          (close (fn2-run-close-step w 4096 writers restarts f pool)))
     (implies (fn2-run-padding-window-p w slot gen 9 0 1 0 0 writers restarts pool)
              (and (natp pos) (<= pos 65536)
                   (equal (mv-nth 3 close) (if (equal pos 65536) pool (mv-nth 1 write)))
                   (implies (< pos 65536) (equal (car write) :ok)))))
   :hints (("Goal" :do-not '(preprocess)
            :use ((:instance fn2-run-padding-keeps-page-prefix (n (min 4096 (- 65536 (+ (fn2-run-writers-cursor w writers)
                                                     (fn2-run-writers-pos w writers))))) (cap 65536)
                     (off (+ (fn2-run-writers-cursor w writers) (fn2-run-writers-pos w writers))) (at 0) (size 0)
                     (pk 9) (ps 0) (pg 1)))
            :in-theory (e/d (fn2-run-padding-window-p fn2-run-closing-page-ready-p fn2-run-close-step)
                     (fn2-run-zero fn2-run-read-bytes fn2-layout-range-code fn2-pool-base fn2-run-write-restarts
                      fn2-run-writers-slot fn2-run-writers-gen fn2-run-writers-okind fn2-run-writers-oslot fn2-run-writers-ogen
                      fn2-run-writers-phase fn2-run-writers-cursor fn2-run-writers-pos fn2-run-writers-restarts
                      fn2-run-writers-fields fn2-run-writers-set-phase fn2-run-writers-set-pos unsigned-byte-p))))))

(local (defthm fn2-run-padding-result-status
         (equal (mv-nth 0 x) (car x))
         :hints (("Goal" :in-theory (enable mv-nth)))))

(local
 (defthmd fn2-run-next-zero-padding-span
   (let* ((pos (+ (fn2-run-writers-cursor w writers) (fn2-run-writers-pos w writers)))
          (size (min 4096 (- 65536 pos))) (close (fn2-run-close-step w 4096 writers restarts f pool)))
     (implies (fn2-run-page-padding-zero-p w start slot gen writers restarts pool)
              (fn2-ribbon-zero-region-p (- (+ pos size) start) start slot gen (mv-nth 3 close))))
   :hints (("Goal" :cases ((equal (+ (fn2-run-writers-cursor w writers) (fn2-run-writers-pos w writers)) 65536))
            :use (fn2-run-close-step-writes-padding
                  (:instance fn2-ribbon-padding-extends-zero-region (fn2-pool pool)
                    (pos (+ (fn2-run-writers-cursor w writers) (fn2-run-writers-pos w writers)))
                    (k (min 4096 (- 65536 (+ (fn2-run-writers-cursor w writers) (fn2-run-writers-pos w writers)))))
                    (count (- (+ (fn2-run-writers-cursor w writers) (fn2-run-writers-pos w writers)
                           (min 4096 (- 65536 (+ (fn2-run-writers-cursor w writers) (fn2-run-writers-pos w writers))))) start))))
            :in-theory (e/d (fn2-run-page-padding-zero-p fn2-run-padding-window-p fn2-run-closing-page-ready-p nfix)
                       (fn2-run-close-step fn2-run-zero fn2-ribbon-zero-region-p fn2-layout-range-code fn2-pool-base
                        fn2-run-writers-gen fn2-run-writers-slot fn2-run-writers-okind fn2-run-writers-oslot fn2-run-writers-ogen
                        fn2-run-writers-phase fn2-run-writers-cursor fn2-run-writers-pos fn2-run-writers-restarts
                        fn2-run-writers-fields fn2-run-restarts-rows fn2-run-restartsp fn2-run-restarts-wfp))))))

(defthmd fn2-run-closing-page-extends-zero-padding
  (let* ((close (fn2-run-close-step w 4096 writers restarts f pool))
         (after (mv-nth 1 close)) (p2 (mv-nth 3 close)))
    (implies (fn2-run-page-padding-zero-p w start slot gen writers restarts pool)
             (if (eq (car close) :ok)
                 (fn2-ribbon-zero-region-p (- 65536 start) start slot gen p2)
               (and (equal (car close) :more)
                    (fn2-run-page-padding-zero-p w start slot gen after restarts p2)))))
  :hints (("Goal" :do-not '(preprocess) :use (fn2-run-next-zero-padding-span fn2-run-close-step-writes-padding
                        (:instance fn2-run-padding-preserves-window (pk 9) (ps 0) (pg 1) (at 0) (size 0)))
           :in-theory (e/d (fn2-run-page-padding-zero-p)
                          (fn2-run-close-step fn2-run-padding-window-p fn2-run-zero fn2-ribbon-zero-region-p
                           fn2-run-writers-set-pos fn2-run-writers-set-phase fn2-run-writers-cursor fn2-run-writers-pos
                           fn2-run-writers-restarts fn2-run-writers-phase fn2-run-read-bytes unsigned-byte-p)))))
