; Materialized after the actual core and B machine table exist. The executor
; invokes this only for image startup before any engine/foreground genesis.
; A refused configuration is a startup failure, never an unprotected fallback.
(in-package "ACL2")
(include-book "checkpoint-working-credit")
(fn2-book-layer :c)
(defmacro fn2-checkpoint-working-credit-init-events ()
 '(progn
  (defun fn2-checkpoint-working-credit-init (profile fn2-core)
   (declare (xargs :stobjs fn2-core :guard (and (fn2-profilep profile) (fn2-core-wfp fn2-core))))
   (stobj-let ((fn2-commit (fn2-commit-table fn2-core))
               (fn2-commit-io (fn2-core-commit-io fn2-core))
               (fn2-pool (fn2-core-pool fn2-core)))
    (code fn2-pool)
    (fn2-checkpoint-working-credit-configure
     profile (fn2-commit-rows fn2-commit) (fn2-commit-io-rows fn2-commit-io) fn2-pool)
    (mv code fn2-core)))
  (fn2-core-preserves fn2-checkpoint-working-credit-init (profile fn2-core)
   :position 1 :rows nil :hyps ((fn2-profilep profile)))))
