; Checkpoint scratch capacity is an admission profile, not a stored-data cap.
(in-package "ACL2")
(include-book "machines-b")
(include-book "checkpoint-boot")
(fn2-book-layer :b)
(defun fn2-checkpoint-capacity (profile)
 (declare (xargs :guard t))
 (fn2-b-checkpoint-capacity profile))
(defcorechild fn2-core-checkpoints fn2-checkpoints
 :init (fn2-checkpoints-init (fn2-checkpoint-capacity profile) fn2-checkpoints)
 :profilep (unsigned-byte-p 32 (+ 96 (* 192 (fn2-checkpoint-capacity profile))))
 :why "Bounded active checkpoint publication and recovery candidates; pressure refuses admission.")
(defcorechild fn2-core-checkpoint-refs fn2-checkpoint-refs
 :init (fn2-checkpoint-refs-init (* 6 (fn2-checkpoint-capacity profile)) fn2-checkpoint-refs)
 :profilep (unsigned-byte-p 32 (+ 96 (* 192 (fn2-checkpoint-capacity profile))))
 :why "Descriptor plus five root references for each active checkpoint candidate.")
(defcorechild fn2-core-checkpoint-bytes fn2-checkpoint-bytes
 :init (fn2-checkpoint-bytes-init (+ 96 (* 192 (fn2-checkpoint-capacity profile))) fn2-checkpoint-bytes)
 :profilep (unsigned-byte-p 32 (+ 96 (* 192 (fn2-checkpoint-capacity profile))))
 :why "Immutable owned digest bytes survive reuse of format checker scratch rows.")

(defcorechild fn2-core-checkpoint-publication fn2-checkpoint-publication
 :init (fn2-checkpoint-publication-init 1 fn2-checkpoint-publication)
 :profilep t
 :harvest (fn2-checkpoint-publication-harvest
           ((fn2-core-checkpoint-publication fn2-checkpoint-publication)))
 :why "One checkpoint bank writer keeps exact operation identities through physical harvest.")

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
