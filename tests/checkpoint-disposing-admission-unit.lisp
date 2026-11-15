; Actual candidate claim predicate, with an explicit complete retained owner
; tuple. Disposing closes fresh builder consumers while preserving identity.
(in-package "ACL2")
(include-book "std/util/bstar" :dir :system)
(include-book "../books/checkpoint")
(defun fn2-cdau-body (fn2-checkpoints)
 (declare (xargs :stobjs fn2-checkpoints :verify-guards nil))
 (b* ((fn2-checkpoints (fn2-checkpoints-init 2 fn2-checkpoints))
      (fn2-checkpoints (fn2-checkpoints-put 1 (state *fn2-checkpoint-state-building*)
       (checkpoint 71) (history 101) (incarnation 103)
       (builder-token 17) (builder-owner-kind 9) (builder-owner-slot 3) (builder-owner-gen 23)))
      (before (and (fn2-checkpoint-builder-claimp 1 17 9 3 23 fn2-checkpoints)
                   (fn2-checkpoint-builder-ownerp 1 17 9 3 23 fn2-checkpoints)))
      (fn2-checkpoints (fn2-checkpoints-set-state 1 *fn2-checkpoint-state-disposing* fn2-checkpoints)))
  (mv (and before
           (not (fn2-checkpoint-builder-claimp 1 17 9 3 23 fn2-checkpoints))
           (not (fn2-checkpoint-builder-ownerp 1 17 9 3 23 fn2-checkpoints))
           (= (fn2-checkpoints-builder-token 1 fn2-checkpoints) 17)
           (= (fn2-checkpoints-checkpoint 1 fn2-checkpoints) 71)
           (= (fn2-checkpoints-state 0 fn2-checkpoints) *fn2-checkpoint-state-free*))
      fn2-checkpoints)))
(assert-event
 (with-local-stobj fn2-checkpoints
  (mv-let (answer fn2-checkpoints) (fn2-cdau-body fn2-checkpoints) answer)))
