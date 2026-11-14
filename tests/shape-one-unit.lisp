(in-package "ACL2")
(include-book "../books/machines")

(defcolumns fn2-shape-source ((value :u32)) :rows-bound 8)
(defcolumns fn2-shape-target ((value :u32)) :rows-bound 8)

;; The scalar comes from a read-only child absent from the output claims.
(defun fn2-shape-copy (n i fn2-shape-source fn2-shape-target)
  (declare (xargs :stobjs (fn2-shape-source fn2-shape-target) :measure (nfix n)
                  :guard (and (natp n) (natp i)
                              (fn2-shape-source-wfp fn2-shape-source)
                              (fn2-shape-target-wfp fn2-shape-target))))
  (if (or (zp n) (not (natp i))
          (>= i (fn2-shape-source-rows fn2-shape-source))
          (>= i (fn2-shape-target-rows fn2-shape-target)))
      (mv :done fn2-shape-target)
    (let ((fn2-shape-target
           (fn2-shape-target-set-value i (fn2-shape-source-value i fn2-shape-source) fn2-shape-target)))
      (fn2-shape-copy (- n 1) (+ 1 i) fn2-shape-source fn2-shape-target))))

(defmacro fn2-shape-copy-events (&optional enables)
  `(make-event
    (let* ((events
            (fn2-shape-one-events
             'fn2-shape-copy-preserves 'fn2-shape-copy
             '(n i fn2-shape-source fn2-shape-target)
             '((fn2-shape-sourcep fn2-shape-source) (fn2-shape-source-wfp fn2-shape-source)
               (fn2-shape-targetp fn2-shape-target) (fn2-shape-target-wfp fn2-shape-target))
             '((fn2-shape-targetp (mv-nth 1 fn2-shape-r))
               (fn2-shape-target-wfp (mv-nth 1 fn2-shape-r))
               (equal (fn2-shape-target-rows (mv-nth 1 fn2-shape-r))
                      (fn2-shape-target-rows fn2-shape-target)))
             '(fn2-shape-target) '(fn2-shape-copy ,@enables)
             '(fn2-shape-source-rows fn2-shape-target-rows) (w state)))
           (hints (fn2-decl-get :hints (cdddr (nth 4 events))))
           (theory (fn2-decl-get :in-theory (cdar hints)))
           (closed (caddr theory)))
      ,(if enables
           ;; An explicit opening is honored without changing any claims.
           '(if (and (member-eq 'nth closed)
                     (not (member-eq 'fn2-shape-source-value closed)))
                (value '(value-triple :explicit-reader-opening))
              (er soft 'fn2-shape-copy-events "Explicit reader opening lost."))
         ;; Output-only inference would omit SOURCE-VALUE and fail this control.
         '(if (and (member-eq 'nth closed)
                   (member-eq 'fn2-shape-source-value closed)
                   (member-eq 'fn2-shape-target-value closed))
              (value (cons 'progn events))
            (er soft 'fn2-shape-copy-events "Read-only input reader left open."))))))

(fn2-shape-copy-events)
(fn2-shape-copy-events (fn2-shape-source-value))
