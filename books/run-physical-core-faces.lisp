; The shared loader is called by C maintenance/transactions as well as D
; readers. Materialize its core faces once, before those machine wrappers.
(in-package "ACL2")
(include-book "machine-arms")
(fn2-book-layer :c)
(defun fn2-run-loader-core-face-events (ops world)
 (declare (xargs :verify-guards nil))
 (if (atom ops) (mv nil nil)
  (let* ((op (car ops)) (row (fn2-arms-op-row op world)) (child (fn2-decl-get :child row)))
   (if (not (and row child (function-symbolp child world)))
    (mv (msg "Physical loader operation ~x0 has no actual admitted child." op) nil)
    (mv-let (err rest) (fn2-run-loader-core-face-events (cdr ops) world)
     (mv err (append (and (not (function-symbolp op world)) (fn2-arms-op-face-events op child world)) rest)))))))
(defconst *fn2-run-page-core-operations*
 '(fn2-run-page-reserve fn2-run-page-bind fn2-run-page-step fn2-run-page-read fn2-run-page-release))
(defmacro fn2-run-page-core-faces ()
 '(make-event
   (mv-let (err events) (fn2-run-loader-core-face-events *fn2-run-page-core-operations* (w state))
    (if err (er soft 'fn2-run-page-core-faces "~@0" err) (value (cons 'progn events))))))
