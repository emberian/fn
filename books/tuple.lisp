; Shared names for logic/test tuples. This extends the crash model's existing
; reader generator; these lists are never a served representation.
(in-package "ACL2")

; Resolve the index at expansion time. Cons checks preserve the model readers'
; total behavior on malformed evidence, which the consuming predicate rejects.
(defun fn2-cm-reader-body (index term)
  (declare (xargs :guard (natp index) :measure (nfix index)))
  (if (zp index) `(if (consp ,term) (car ,term) nil)
    `(if (consp ,term)
         ,(fn2-cm-reader-body (- index 1) `(cdr ,term)) nil)))

(defun fn2-cm-readers (names index)
  (declare (xargs :mode :logic :guard (and (symbol-listp names) (natp index))))
  (if (endp names) nil
    (let ((reader (car names))
          (updater (intern-in-package-of-symbol
                    (concatenate 'string "UPDATE-" (symbol-name (car names)))
                    (car names))))
      (cons `(defun ,reader (x)
               (declare (xargs :guard t))
               ,(fn2-cm-reader-body index 'x))
            (cons `(defun ,updater (value x)
                     (declare (xargs :guard (true-listp x)))
                     (update-nth ,index value x))
                  (fn2-cm-readers (cdr names) (+ 1 index)))))))

(defmacro fn2-cm-defreaders (&rest names)
  `(progn ,@(fn2-cm-readers names 0)))
