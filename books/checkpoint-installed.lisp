; Actual installed-chain evidence for the checkpoint publisher.
(in-package "ACL2")
(include-book "machines-b")
(include-book "checkpoint-boot")
(fn2-book-layer :b)

; The writer derives the installation seal from the actual durable commit
; directory, never from a caller-selected digest row. This directory is indexed
; by commit and its digest stripe is the same one fn2-commit-seal-context saves.
(defun fn2-checkpoint-installation-seal-row (c fn2-checkpoints fn2-commit-root fn2-fc fn2-digests)
 (declare (xargs :stobjs (fn2-checkpoints fn2-commit-root fn2-fc fn2-digests)
  :guard (and (fn2-checkpoints-wfp fn2-checkpoints) (fn2-commit-root-wfp fn2-commit-root)
              (fn2-fc-wfp fn2-fc) (fn2-digests-wfp fn2-digests))))
 (if (not (and (natp c) (< c (fn2-checkpoints-rows fn2-checkpoints))
               (< 0 (fn2-commit-root-rows fn2-commit-root))
               (equal (fn2-checkpoints-state c fn2-checkpoints) *fn2-checkpoint-state-installed*)))
     (mv :state 0)
  (let* ((batch (fn2-checkpoints-installation-commit c fn2-checkpoints))
         (row (+ (* *fn2-digest-stride* (fn2-fc-rows fn2-fc)) batch)))
   (cond ((not (and (posp batch) (< batch (fn2-commit-root-rows fn2-commit-root))
                     (<= batch (fn2-commit-root-installed 0 fn2-commit-root))
                     (equal (fn2-commit-root-seal-ready batch fn2-commit-root) 1)
                     (equal (fn2-commit-root-parent batch fn2-commit-root) (- batch 1))))
          (mv :installation 0))
         ((not (fn2-digest-rowp row fn2-digests)) (mv :bounds 0))
         (t (mv :ok row))))))
