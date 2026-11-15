; Opt-in extra-array frames from the canonical defcolumns registry. Primary
; column resizers change table geometry and are deliberately outside this API.
(in-package "ACL2")
(include-book "columns")

(defun fn2-columns-extra-resize-frame-events (table extras)
 (declare (xargs :verify-guards nil))
 (if (atom extras) nil
  (let* ((field (car extras))
         (resize (fn2-columns-pre "RESIZE-" (car field)))
         (rows (fn2-columns-sym table "-ROWS"))
         (preserves (fn2-columns-sym table "-PRESERVES")))
   (append
    (and (fn2-columns-numeric-fieldp field)
         (fn2-columns-arrayp field)
         (cadr (member-eq :resizable field))
         `((,preserves ,resize (n ,table)
             :specs (("-ROWS" ,rows nil :frame ,table)) :disable nil
             :hints (("Goal" :in-theory (enable ,rows ,resize))))))
    (fn2-columns-extra-resize-frame-events table (cdr extras))))))

(defmacro fn2-columns-extra-resize-frames (table)
 `(make-event
   (let ((schema (fn2-decl-row (list :columns ',table) (w state))))
    (if (not schema)
        (er hard 'fn2-columns-extra-resize-frames "No columns schema for ~x0." ',table)
      (cons 'progn (fn2-columns-extra-resize-frame-events ',table
                    (fn2-decl-get :extra-fields schema)))))))
