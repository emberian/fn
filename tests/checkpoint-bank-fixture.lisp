; Shared explicit typed empty-obligation premise for callback/packing units.
; This helper does NOT witness the real boot scan/create/Fence binder.
(in-package "ACL2")
(include-book "../books/checkpoint-bank-obligations-state")
(defun fn2-checkpoint-test-empty-publication (fn2-checkpoint-publication)
 (declare (xargs :stobjs fn2-checkpoint-publication :verify-guards nil))
 (let ((fn2-checkpoint-publication (fn2-checkpoint-publication-init 1 fn2-checkpoint-publication)))
  (fn2-checkpoint-publication-put 0 (cold-bind-phase *fn2-checkpoint-cold-bind-phase-complete*)
   (cold-bind-cursor 4) (cold-selected 4) (cold-empty-mask 15))))
