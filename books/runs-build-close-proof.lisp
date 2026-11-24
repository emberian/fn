; Closing work in the range adapter advances the selected page writer. The
; pending input, assigned page addresses and installed cache stay available.
(in-package "ACL2")
(include-book "runs-close-directory-proof")
(include-book "runs-close-padding-proof")
(include-book "runs-served")

(defun-nx fn2-run-build-closing-at-p (l builds writers restarts f fc ctx)
  (let* ((height (fn2-run-builds-height 0 builds)) (w (+ l (fn2-run-builds-wbase 0 builds)))
         (crow (fn2-run-builds-crow 0 builds)) (hrow (+ l (fn2-run-builds-hbase 0 builds)))
         (finishing (equal (fn2-run-builds-phase 0 builds) *fn2-run-build-phase-finishing*)))
    (and (<= height *fn2-run-max-levels*) (natp l)
         (equal (fn2-run-scan (1- height) 0 finishing builds writers) (list :close-step l))
         (< w (fn2-run-writers-rows writers)) (fn2-run-writerp w writers restarts f)
         (< crow (fn2-fc-rows fc)) (< crow (fn2-fc-context-rows ctx)) (unsigned-byte-p 32 hrow))))

(defthmd fn2-run-build-performs-close-step
  (let* ((w (+ l (fn2-run-builds-wbase 0 builds)))
         (close (fn2-run-close-step w 4096 writers restarts f pool))
         (work (fn2-run-build-work 0 4096 builds writers restarts f pool fc ctx b3 ds)))
    (implies (fn2-run-build-closing-at-p l builds writers restarts f fc ctx)
             (equal work
                    (list (if (member-eq (car close) '(:ok :more)) :more (car close))
                          l builds (mv-nth 1 close) restarts (mv-nth 2 close) (mv-nth 3 close)
                          fc ctx b3 ds))))
  :hints (("Goal" :in-theory (e/d (fn2-run-build-work)
                       (fn2-run-scan fn2-run-close-step fn2-run-writerp fn2-run-writers-rows
                        fn2-run-builds-height fn2-run-builds-wbase fn2-run-builds-crow fn2-run-builds-hbase
                        fn2-run-builds-phase fn2-fc-rows fn2-fc-context-rows
                        fn2-run-head fn2-run-seal-context fn2-run-seal-step fn2-run-close)))))

(defthmd fn2-run-adapter-performs-close-step
  (let* ((w (+ l (fn2-run-builds-wbase 0 builds)))
         (close (fn2-run-close-step w 4096 writers restarts f pool))
         (step (fn2-run-run-onestep layout entries src sg off unit pages builds curs paths cache
                                    writers restarts f pool fc ctx b3 ds)))
    (implies (and (fn2-run-build-closing-at-p l builds writers restarts f fc ctx)
                  (member-eq (car close) '(:ok :more)))
             (equal step (list nil :more entries off unit pages builds curs paths cache
                               (mv-nth 1 close) restarts (mv-nth 2 close) (mv-nth 3 close) fc ctx b3 ds))))
  :hints (("Goal" :use fn2-run-build-performs-close-step
           :in-theory (union-theories (theory 'minimal-theory)
                      '(fn2-run-run-onestep mv-nth car-cons cdr-cons eq eql member-equal
                        (:e equal) (:e zp) (:e consp) (:e binary-+) (:e mv-nth) (:e member-equal))))))

; OFF is the first byte this step may change. Before the first directory
; write it is the end of the last entry; while padding it includes the directory.
(defun-nx fn2-run-closing-page-ready-p (w writers restarts pool)
  (let* ((cursor (fn2-run-writers-cursor w writers)) (k (fn2-run-writers-restarts w writers))
         (pos (fn2-run-writers-pos w writers)) (off (+ cursor pos))
         (slot (fn2-run-writers-slot w writers)) (gen (fn2-run-writers-gen w writers))
         (pk (fn2-run-writers-okind w writers)) (ps (fn2-run-writers-oslot w writers))
         (pg (fn2-run-writers-ogen w writers)))
    (and (natp w) (equal (fn2-run-writers-phase w writers) *fn2-run-writer-phase-closing*)
         (natp cursor) (natp k) (natp pos) (natp slot) (natp (fn2-pool-base slot pool))
         (<= off *fn2-run-page-size*)
         (if (< pos (* 4 k))
             (and (equal pos 0) (<= k 1024) (<= (+ cursor (* 4 k)) *fn2-run-page-size*)
                  (natp (+ *fn2-run-scratch-fields* (fn2-run-writers-fields w writers)))
                  (<= (+ (* *fn2-run-restart-capacity* w) k) (fn2-run-restarts-rows restarts))
                  (fn2-run-restartsp restarts) (fn2-run-restarts-wfp restarts)
                  (equal (fn2-layout-range-code slot gen cursor (+ cursor (* 4 k)) t pk ps pg pool) :ok))
           (equal (fn2-layout-range-code slot gen off *fn2-run-page-size* t pk ps pg pool) :ok)))))

(local
 (defthm fn2-run-closing-page-prefix
  (let* ((cursor (fn2-run-writers-cursor w writers)) (pos (fn2-run-writers-pos w writers))
         (off (+ cursor pos)) (dir (* 4 (fn2-run-writers-restarts w writers)))
         (slot (fn2-run-writers-slot w writers)) (gen (fn2-run-writers-gen w writers))
         (pk (fn2-run-writers-okind w writers)) (ps (fn2-run-writers-oslot w writers))
         (pg (fn2-run-writers-ogen w writers))
         (close (fn2-run-close-step w 4096 writers restarts f pool)))
    (implies (and (fn2-run-closing-page-ready-p w writers restarts pool)
                  (natp at) (natp size) (<= (+ at size) off))
             (and (member-eq (car close) '(:ok :more))
                  (equal (mv-nth 1 close)
                         (cond ((< pos dir) (fn2-run-writers-set-pos w dir writers))
                               ((equal off *fn2-run-page-size*)
                                (fn2-run-writers-set-phase w *fn2-run-writer-phase-heading* writers))
                               (t (fn2-run-writers-set-pos w (+ pos (min 4096 (- *fn2-run-page-size* off))) writers))))
                  (equal (fn2-run-read-bytes size slot gen at pk ps pg (mv-nth 3 close))
                         (fn2-run-read-bytes size slot gen at pk ps pg pool)))))
  :rule-classes nil
  :hints (("Goal" :do-not '(preprocess)
           :cases ((< (fn2-run-writers-pos w writers) (* 4 (fn2-run-writers-restarts w writers))))
           :in-theory (disable fn2-run-writers-cursor fn2-run-writers-slot fn2-run-writers-gen fn2-run-writers-okind
                 fn2-run-writers-oslot fn2-run-writers-ogen fn2-run-writers-phase fn2-run-writers-fields
                 fn2-run-writers-restarts fn2-run-writers-pos fn2-run-writers-set-pos fn2-run-writers-set-phase
                 fn2-run-close-step fn2-run-read-bytes fn2-layout-range-code fn2-pool-base fn2-run-restarts-rows
                 fn2-run-restartsp fn2-run-restarts-wfp fn2-run-write-restarts fn2-run-load-bytes
                 fn2-run-directory-octets fn2-run-saved-offsets))
          ("Subgoal 1" :use (fn2-run-close-writes-directory (:instance fn2-run-close-keeps-entry-bytes (n size))))
          ("Subgoal 2" :use fn2-run-close-pads-stored-page))))

(defthm fn2-run-adapter-close-preserves-page-prefix
  (let* ((w (+ l (fn2-run-builds-wbase 0 builds)))
         (cursor (fn2-run-writers-cursor w writers)) (pos (fn2-run-writers-pos w writers))
         (off (+ cursor pos)) (dir (* 4 (fn2-run-writers-restarts w writers)))
         (slot (fn2-run-writers-slot w writers)) (gen (fn2-run-writers-gen w writers))
         (pk (fn2-run-writers-okind w writers)) (ps (fn2-run-writers-oslot w writers))
         (pg (fn2-run-writers-ogen w writers))
         (step (fn2-run-run-onestep layout entries src sg inoff unit pages builds curs paths cache
                                    writers restarts f pool fc ctx b3 ds)))
    (implies (and (fn2-run-build-closing-at-p l builds writers restarts f fc ctx)
                  (fn2-run-closing-page-ready-p w writers restarts pool)
                  (natp at) (natp size) (<= (+ at size) off))
             (and (not (car step)) (equal (mv-nth 1 step) :more)
                  (equal (mv-nth 2 step) entries) (equal (mv-nth 5 step) pages)
                  (equal (mv-nth 10 step)
                         (cond ((< pos dir) (fn2-run-writers-set-pos w dir writers))
                               ((equal off *fn2-run-page-size*)
                                (fn2-run-writers-set-phase w *fn2-run-writer-phase-heading* writers))
                               (t (fn2-run-writers-set-pos w (+ pos (min 4096 (- *fn2-run-page-size* off))) writers))))
                  (equal (fn2-run-read-bytes size slot gen at pk ps pg (mv-nth 13 step))
                         (fn2-run-read-bytes size slot gen at pk ps pg pool)))))
  :rule-classes nil
  :hints (("Goal" :use ((:instance fn2-run-adapter-performs-close-step (off inoff))
                        (:instance fn2-run-closing-page-prefix (w (+ l (fn2-run-builds-wbase 0 builds)))))
           :in-theory (union-theories (theory 'minimal-theory)
                    '(mv-nth car-cons cdr-cons member-equal (:e mv-nth) (:e equal)
                      (:e consp) (:e zp) (:e binary-+))))))
