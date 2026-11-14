; Local candidate-claim/prepare controls only. Synthetic BUILDING eligibility
; does not witness actual C cut, descriptor BEGIN or physical construction.
(in-package "ACL2")
(include-book "../books/checkpoint")
(defun fn2-checkpoint-builder-claim-test-body (fn2-checkpoints fn2-checkpoint-refs fn2-checkpoint-bytes fn2-digests)
 (declare (xargs :stobjs (fn2-checkpoints fn2-checkpoint-refs fn2-checkpoint-bytes fn2-digests) :verify-guards nil))
 (b* ((fn2-checkpoints (fn2-checkpoints-init 1 fn2-checkpoints))
      (fn2-checkpoint-refs (fn2-checkpoint-refs-init 6 fn2-checkpoint-refs))
      (fn2-checkpoint-bytes (fn2-checkpoint-bytes-init 192 fn2-checkpoint-bytes))
      (fn2-digests (fn2-digests-init 1 fn2-digests))
      (fn2-checkpoints (fn2-checkpoints-put 0 (state *fn2-checkpoint-state-building*)
        (builder-token 9) (builder-owner-kind 1) (builder-owner-slot 2) (builder-owner-gen 3)))
      (fn2-checkpoint-refs (fn2-checkpoint-refs-set-root-build-token 0 88 fn2-checkpoint-refs))
      (antecedent (fn2-checkpoint-builder-ownerp 0 9 1 2 3 fn2-checkpoints))
      ((mv external fn2-checkpoints fn2-checkpoint-refs fn2-checkpoint-bytes)
       (fn2-checkpoint-prepare 0 7 1 1 0 16 1 1 *page-kind-checkpoint-descriptor* 4096 0
        fn2-checkpoints fn2-checkpoint-refs fn2-checkpoint-bytes fn2-digests))
      (unchanged (and (eq external :bounds) (fn2-checkpoint-builder-ownerp 0 9 1 2 3 fn2-checkpoints)
                      (equal (fn2-checkpoint-refs-root-build-token 0 fn2-checkpoint-refs) 88)))
      ((mv wrong fn2-checkpoints fn2-checkpoint-refs fn2-checkpoint-bytes)
       (fn2-checkpoint-prepare-owned 0 9 1 2 4 7 1 1 0 16 1 1 *page-kind-checkpoint-descriptor* 4096 0
        fn2-checkpoints fn2-checkpoint-refs fn2-checkpoint-bytes fn2-digests))
      (wrong-frame (and (eq wrong :owner) (fn2-checkpoint-builder-ownerp 0 9 1 2 3 fn2-checkpoints)
                        (equal (fn2-checkpoint-refs-root-build-token 0 fn2-checkpoint-refs) 88)))
      ((mv owned fn2-checkpoints fn2-checkpoint-refs fn2-checkpoint-bytes)
       (fn2-checkpoint-prepare-owned 0 9 1 2 3 7 1 1 0 16 1 1 *page-kind-checkpoint-descriptor* 4096 0
        fn2-checkpoints fn2-checkpoint-refs fn2-checkpoint-bytes fn2-digests)))
  (mv (and antecedent unchanged wrong-frame (eq owned :ok)
           (equal (fn2-checkpoints-state 0 fn2-checkpoints) *fn2-checkpoint-state-preparing*)
           (fn2-checkpoint-builder-claimp 0 9 1 2 3 fn2-checkpoints)
           (not (fn2-checkpoint-builder-ownerp 0 9 1 2 3 fn2-checkpoints))
           (equal (fn2-checkpoint-refs-root-build-token 0 fn2-checkpoint-refs) 0))
      fn2-checkpoints fn2-checkpoint-refs fn2-checkpoint-bytes fn2-digests)))
(defun fn2-checkpoint-builder-claim-test ()
 (declare (xargs :verify-guards nil))
 (with-local-stobj fn2-checkpoints
 (mv-let (answer fn2-checkpoints)
  (with-local-stobj fn2-checkpoint-refs
 (mv-let (answer fn2-checkpoints fn2-checkpoint-refs)
  (with-local-stobj fn2-checkpoint-bytes
 (mv-let (answer fn2-checkpoints fn2-checkpoint-refs fn2-checkpoint-bytes)
  (with-local-stobj fn2-digests
 (mv-let (answer fn2-checkpoints fn2-checkpoint-refs fn2-checkpoint-bytes fn2-digests)
  (fn2-checkpoint-builder-claim-test-body fn2-checkpoints fn2-checkpoint-refs fn2-checkpoint-bytes fn2-digests)
  (mv answer fn2-checkpoints fn2-checkpoint-refs fn2-checkpoint-bytes)))
  (mv answer fn2-checkpoints fn2-checkpoint-refs)))
  (mv answer fn2-checkpoints)))
  answer)))
(assert-event (fn2-checkpoint-builder-claim-test))
