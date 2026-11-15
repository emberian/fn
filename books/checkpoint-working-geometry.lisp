; Shared C working-window geometry. B future-window geometry remains in its
; existing B book; no root1 state or reserve worker belongs in this leaf.
(in-package "ACL2")
(include-book "pool-credit")
(include-book "run-geometry")
(include-book "checkpoint-future-working")
(fn2-book-layer :c)

(defconst *fn2-checkpoint-source-page-window* 19)

(defconst *fn2-checkpoint-source-read-window* (+ 1 *fn2-checkpoint-source-page-window*))

; A key survives the complete source rescan while window14 holds the best
; entry and window16 may be handed to the canonical page/semantic worker.
; This is the physical page representation bound, not a stored-data limit.
(defconst *fn2-checkpoint-compaction-key-window* (+ 1 *fn2-checkpoint-source-read-window*))
(defconst *fn2-checkpoint-window-count* (+ 1 *fn2-checkpoint-compaction-key-window*))

(defconst *fn2-checkpoint-working-window-count*
 (+ *fn2-checkpoint-window-count* *fn2-checkpoint-future-window-count*))

(defun fn2-checkpoint-window-length (i)
 (declare (xargs :guard t))
 (cond ((or (< (nfix i) 12) (equal i 14) (equal i 16) (equal i *fn2-checkpoint-source-page-window*) (equal i *fn2-checkpoint-compaction-key-window*)) *fn2-run-page-size*)
       ((or (equal i 12) (equal i 13)) (* 32 *fn2-run-max-levels*))
       ((equal i 15) 64) (t 4096)))

(defun fn2-checkpoint-window-class-demand (i class fn2-pool)
 (declare (xargs :stobjs fn2-pool :guard (and (natp i) (<= i *fn2-checkpoint-window-count*))
                 :measure (nfix (- *fn2-checkpoint-window-count* (nfix i)))))
 (if (not (and (natp i) (< i *fn2-checkpoint-window-count*))) 0
  (+ (if (equal class (fn2-pool-class-for (fn2-checkpoint-window-length i) fn2-pool)) 1 0)
     (fn2-checkpoint-window-class-demand (+ i 1) class fn2-pool))))

(defun fn2-checkpoint-admission-roomp (i fn2-pool)
 (declare (xargs :stobjs fn2-pool :guard (and (natp i) (<= i *fn2-checkpoint-working-window-count*)) :measure (nfix (- *fn2-checkpoint-working-window-count* (nfix i)))))
 (if (not (and (natp i) (< i *fn2-checkpoint-working-window-count*))) t
  (let ((class (fn2-pool-class-for
                (if (< i *fn2-checkpoint-window-count*) (fn2-checkpoint-window-length i)
                 (fn2-checkpoint-future-window-length (- i *fn2-checkpoint-window-count*))) fn2-pool)))
   (and (natp class) (< class (fn2-pool-nclasses fn2-pool))
        (<= (+ (fn2-checkpoint-window-class-demand 0 class fn2-pool)
               (fn2-checkpoint-future-class-demand 0 class fn2-pool)) (fn2-pool-free-count class fn2-pool))
        (fn2-checkpoint-admission-roomp (+ i 1) fn2-pool)))))
