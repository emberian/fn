; The query cursor's arms (D6, books/cursor.lisp): the core faces of its
; own operations (each one stobj-let around the child the arms call), the
; arms' core faces and derived contracts over the child-form arms generated
; in its own book, then its run entry, after the transaction kind's section.
(in-package "ACL2")
(include-book "assembly-callbacks-d")
(include-book "cursor")

(defmachine-arms fn2-cursor :wrappers)
(defmachine-run fn2-cursor)
