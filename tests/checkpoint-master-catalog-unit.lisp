; UNEXECUTED narrow scalar catalog control, not an authenticated recovery or
; whole checkpoint actor witness. Candidate rows are synthetic typed fixtures.
(in-package "ACL2")
(include-book "../books/checkpoint-master-control")
(defun fn2-checkpoint-master-catalog-control (fn2-checkpoints)
 (declare (xargs :stobjs fn2-checkpoints :verify-guards nil))
 (b* ((fn2-checkpoints (fn2-checkpoints-init 3 fn2-checkpoints))
      (fn2-checkpoints (fn2-checkpoints-put 0 (state *fn2-checkpoint-state-building*) (checkpoint 999)))
      (fn2-checkpoints (fn2-checkpoints-put 1 (state *fn2-checkpoint-state-installed*)
                        (checkpoint 7) (installation-commit 11)))
      ((mv a s h c f &) (fn2-checkpoint-catalog-step 0 0 0 nil fn2-checkpoints))
      ((mv b s h c f &) (fn2-checkpoint-catalog-step s h c f fn2-checkpoints))
      ((mv d s h c f &) (fn2-checkpoint-catalog-step s h c f fn2-checkpoints))
      ((mv e & & chosen & identity) (fn2-checkpoint-catalog-step s h c f fn2-checkpoints))
      ((mv full & & & & &) (fn2-checkpoint-catalog-step 3 h c nil fn2-checkpoints))
      ((mv exhausted & & & & &) (fn2-checkpoint-catalog-step 3 (- (expt 2 60) 1) c t fn2-checkpoints)))
  (mv (and (equal (list a b d) '(:more :more :more))
           (eq e :ready) (equal chosen 2) (equal identity 8)
           (eq full :no-space) (eq exhausted :exhausted)) fn2-checkpoints)))
(assert-event
 (with-local-stobj fn2-checkpoints
  (mv-let (ok fn2-checkpoints) (fn2-checkpoint-master-catalog-control fn2-checkpoints) ok)))
