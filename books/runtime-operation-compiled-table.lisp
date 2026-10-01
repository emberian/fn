; Image-build selected operation producer results. Rebuilt by the ACL2 source
; compiler, never installed through a host setter. No complete protocol family
; has yet supplied its actual phase/PRS producer at this source coordinate.
(in-package "ACL2")
(include-book "runtime-operation-source-assembly")
(defconst *fn-runtime-operation-compiled-table* nil)
(defconst *fn-runtime-operation-compiled-binding*
 (fn-roc-compiled-binding *fn-runtime-operation-compiled-table*))

(defun fn-roc-selected-body-cost (kind request cached)
 (declare (ignore kind request cached) (xargs :guard t))
 (mv :runtime-operation-unavailable nil))
(in-theory (disable fn-roc-selected-body-cost))

(defconst *fn-runtime-operation-compiled-executor-rows* nil)
(defconst *fn-runtime-operation-compiled-kinds*
 (if *fn-runtime-operation-compiled-binding*
     (fn-roc-executor-kinds *fn-runtime-operation-compiled-executor-rows*) nil))
(defconst *fn-runtime-operation-compiled-slots*
 (fn-roc-operation-slots *fn-runtime-operation-compiled-executor-rows*
  (fn-roc-slot-rows *fn-runtime-operation-compiled-kinds* 0)))
