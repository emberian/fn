; The query cursor's arms (D6, books/cursor.lisp): the core faces of its
; own operations (each one stobj-let around the child the arms call), the
; arms' core faces and derived contracts over the child-form arms generated
; in its own book, then its run entry, after the transaction kind's section.
(in-package "ACL2")
(include-book "assembly-callbacks-d")
(include-book "cursor")

(fn2-read-loader-core-faces)
(make-event
 (mv-let (err events) (fn2-run-loader-core-face-events '(fn2-cursor-query-article-page fn2-cursor-lease-reserve fn2-cursor-lease-release fn2-cursor-lease-class fn2-cursor-physical-sources) (w state))
  (if err (er soft 'fn2-cursor-query-article-page "~@0" err) (value (cons 'progn events)))))
(defmachine-arms fn2-cursor :wrappers)
(defmachine-run fn2-cursor)
