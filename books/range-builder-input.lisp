; A run is built from low levels up. Read the represented rows back in
; the opposite order and append the input still waiting for the leaf.
(in-package "ACL2")
(include-book "runs-page-format")

(defun-nx fn2-range-child-entry-lists (children records)
  (if (atom children) nil
    (cons (nth 4 (assoc-equal (car children) records))
          (fn2-range-child-entry-lists (cdr children) records))))

(defun-nx fn2-range-writer-page-address (level w writers)
  (list level (fn2-run-writers-unit w writers) (fn2-run-writers-counter w writers)
        (fn2-run-writers-slot w writers) (fn2-run-writers-gen w writers)))

(defun-nx fn2-range-writer-covered-rows (level w leaves children records writers)
  (let ((phase (fn2-run-writers-phase w writers)))
    (cond ((equal phase *fn2-run-writer-phase-idle*) nil)
          ((equal phase *fn2-run-writer-phase-sealed*)
           (nth 4 (assoc-equal (fn2-range-writer-page-address level w writers) records)))
          ((zp level) leaves)
          (t (append-lst (fn2-range-child-entry-lists (nth level children) records))))))

(defun-nx fn2-range-builder-input (height base leaves children records writers pending)
  (if (zp height) pending
    (let ((level (1- height)))
      (append (fn2-range-writer-covered-rows level (+ base level) leaves children records writers)
              (fn2-range-builder-input level base leaves children records writers pending)))))

(defthmd fn2-range-empty-builder-keeps-entire-input
  (equal (fn2-range-builder-input height base nil nil nil writers pending) pending)
  :hints (("Goal" :induct (fn2-range-builder-input height base nil nil nil writers pending)
           :in-theory (e/d (fn2-range-builder-input fn2-range-writer-covered-rows)
                           (fn2-run-writers-phase fn2-range-writer-page-address)))))
