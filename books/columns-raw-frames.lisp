; Raw row frames reuse the canonical preservation statement. Keep the actual
; function opaque while converting its public row accessor to the raw slot.
(in-package "ACL2")
(include-book "columns")
(defun fn2-columns-raw-row-frame-event (table name args position prefix)
 (declare (xargs :verify-guards nil))
 (let* ((rows (fn2-columns-sym table "-ROWS"))
        (public (fn2-columns-sym name (concatenate 'string prefix "-ROWS")))
        (events (fn2-columns-preserves table name args position nil
                 `((,(concatenate 'string prefix "-ROWS") ,rows ,position :frame ,table))
                 prefix t nil nil t t nil nil nil))
        ; DISABLE=NIL leaves the generated raw frame last. Retain its exact
        ; name/formula and replace only the proof hint, not its hypotheses.
        (raw (car (last (cdr events)))))
  (append (take 3 raw)
   `(:hints (("Goal" :use ,public
              :in-theory (e/d (,rows) (,name ,public))))))))
(defmacro fn2-columns-raw-row-frame (table name args &key position (prefix '"-PRESERVES"))
 `(make-event
   (if (fn2-decl-row (list :columns ',table) (w state))
       (value (fn2-columns-raw-row-frame-event ',table ',name ',args ',position ',prefix))
     (er hard 'fn2-columns-raw-row-frame "No columns schema for ~x0." ',table))))
