; Leaf operations of the generated checkpoint writer. No alternate journal,
; decoder, hash checker, allocator or host-side geometry decisions.
(in-package "ACL2")
(include-book "checkpoint-installed")
(fn2-book-layer :b)

(defun fn2-checkpoint-writer-phase-children (fn2-checkpoint-publication)
 (declare (xargs :stobjs fn2-checkpoint-publication :guard (fn2-checkpoint-publication-wfp fn2-checkpoint-publication)))
 (if (< 0 (fn2-checkpoint-publication-rows fn2-checkpoint-publication))
     (mv :ok (fn2-checkpoint-publication-phase 0 fn2-checkpoint-publication)) (mv :bounds 0)))
(defun fn2-checkpoint-writer-checker-children (fn2-fc)
 (declare (xargs :stobjs fn2-fc :guard (fn2-fc-wfp fn2-fc)))
 (if (<= 2 (fn2-fc-rows fn2-fc))
  (let* ((row (fn2-b-checkpoint-row (fn2-fc-rows fn2-fc))) (base (* 128 row)))
   (if (and (unsigned-byte-p 32 row) (unsigned-byte-p 32 base)) (mv :ok row base) (mv :bounds 0 0)))
  (mv :bounds 0 0)))

; Current boot has proved all four slots empty; the predecessor checkpoint
; digest is therefore the zero genesis value. A second/selected checkpoint
; requires the real selected-anchor source, never a caller-provided digest.
(defun fn2-checkpoint-writer-begin-children (c slot0 gen0 slot1 gen1 kind owner generation
                                          fn2-checkpoints fn2-commit-root fn2-fc fn2-boot-config
                                          fn2-checkpoint-publication fn2-checkpoint-bytes fn2-digests)
 (declare (xargs :stobjs (fn2-checkpoints fn2-commit-root fn2-fc fn2-boot-config
                          fn2-checkpoint-publication fn2-checkpoint-bytes fn2-digests)
  :guard (and (fn2-checkpoints-wfp fn2-checkpoints) (fn2-commit-root-wfp fn2-commit-root)
              (fn2-fc-wfp fn2-fc) (fn2-boot-config-wfp fn2-boot-config)
              (fn2-checkpoint-publication-wfp fn2-checkpoint-publication)
              (fn2-checkpoint-bytes-wfp fn2-checkpoint-bytes) (fn2-digests-wfp fn2-digests))))
 (b* (((mv code batch-hash) (fn2-checkpoint-installation-seal-row c fn2-checkpoints fn2-commit-root fn2-fc fn2-digests))
      ((unless (eq code :ok)) (mv code fn2-checkpoint-publication fn2-checkpoint-bytes fn2-digests))
      ((mv code row &) (fn2-checkpoint-writer-checker-children fn2-fc))
      ((unless (eq code :ok)) (mv code fn2-checkpoint-publication fn2-checkpoint-bytes fn2-digests))
      (geometry (fn2-digest-slot row *fn2-fc-geometry*))
      (previous (fn2-digest-slot row *fn2-fc-previous-seal*))
      ((unless (and (fn2-digest-rowp geometry fn2-digests) (fn2-digest-rowp previous fn2-digests)
                     (not (equal geometry batch-hash)) (not (equal previous batch-hash))
                     (not (equal geometry previous))))
       (mv :bounds fn2-checkpoint-publication fn2-checkpoint-bytes fn2-digests))
      ((mv code fn2-checkpoint-publication) (fn2-checkpoint-publication-bind-boot fn2-boot-config fn2-checkpoint-publication))
      ((unless (eq code :ok)) (mv code fn2-checkpoint-publication fn2-checkpoint-bytes fn2-digests))
      ((mv code fn2-digests) (fn2-checkpoint-boot-geometry-load geometry fn2-boot-config fn2-digests))
      ((unless (eq code :ok)) (mv code fn2-checkpoint-publication fn2-checkpoint-bytes fn2-digests))
      (fn2-digests (fn2-rec-zero-digest previous fn2-digests))
      ((mv code fn2-checkpoint-publication fn2-checkpoint-bytes)
       (fn2-checkpoint-publication-begin c (fn2-boot-config-image-size fn2-boot-config)
        (fn2-boot-config-extents fn2-boot-config) (fn2-boot-config-count fn2-boot-config)
        kind owner generation slot0 gen0 slot1 gen1 batch-hash previous geometry
        fn2-checkpoints fn2-checkpoint-publication fn2-checkpoint-bytes fn2-digests)))
  (mv code fn2-checkpoint-publication fn2-checkpoint-bytes fn2-digests)))
(fn2-checkpoint-publication-preserves fn2-checkpoint-writer-begin-children
 (c slot0 gen0 slot1 gen1 kind owner generation fn2-checkpoints fn2-commit-root fn2-fc fn2-boot-config
    fn2-checkpoint-publication fn2-checkpoint-bytes fn2-digests)
 :carriers ((fn2-checkpoint-publication 1 :prefix "-PUBLICATION")
            (fn2-checkpoint-bytes 2 :prefix "-BYTES") (fn2-digests 3 :prefix "-DIGESTS")))

; The generated worker is the only publisher of this private checker stripe.
; It cannot change context while a seal/check continuation is live.
(defun fn2-checkpoint-writer-context-children (which fn2-checkpoints fn2-checkpoint-publication
                                            fn2-boot-config fn2-fc fn2-b3 fn2-fc-context fn2-digests)
 (declare (xargs :stobjs (fn2-checkpoints fn2-checkpoint-publication fn2-boot-config
                          fn2-fc fn2-b3 fn2-fc-context fn2-digests)
  :guard (and (fn2-checkpoints-wfp fn2-checkpoints) (fn2-checkpoint-publication-wfp fn2-checkpoint-publication)
              (fn2-boot-config-wfp fn2-boot-config) (fn2-fc-wfp fn2-fc) (fn2-b3-wfp fn2-b3)
              (fn2-fc-context-wfp fn2-fc-context) (fn2-digests-wfp fn2-digests))))
 (b* (((unless (and (< 0 (fn2-checkpoint-publication-rows fn2-checkpoint-publication))
                     (natp which) (< which 2)
                     (equal (fn2-checkpoint-publication-checker-live 0 fn2-checkpoint-publication) 0)
                     (equal (fn2-checkpoint-publication-phase 0 fn2-checkpoint-publication)
                            *fn2-checkpoint-publication-phase-prepare*)
                     (member-equal (if (equal which 0)
                       (fn2-checkpoint-publication-stage0 0 fn2-checkpoint-publication)
                       (fn2-checkpoint-publication-stage1 0 fn2-checkpoint-publication)) '(1 3))))
       (mv :state fn2-fc-context fn2-digests))
      ((mv code row &) (fn2-checkpoint-writer-checker-children fn2-fc))
      ((unless (and (eq code :ok) (< row (fn2-fc-context-rows fn2-fc-context))
                     (equal (fn2-fc-phase row fn2-fc) *fn2-fc-phase-idle*) (fn2-b3-ready row fn2-b3 fn2-digests)))
       (mv :checker fn2-fc-context fn2-digests))
      (c (fn2-checkpoint-publication-candidate 0 fn2-checkpoint-publication))
      ((unless (and (natp c) (< c (fn2-checkpoints-rows fn2-checkpoints)))) (mv :bounds fn2-fc-context fn2-digests))
      (geometry (fn2-digest-slot row *fn2-fc-geometry*))
      (hash (fn2-digest-slot row *fn2-fc-hash*))
      (previous (fn2-digest-slot row *fn2-fc-previous-seal*))
      ((unless (and (fn2-digest-rowp geometry fn2-digests) (fn2-digest-rowp hash fn2-digests)
                     (fn2-digest-rowp previous fn2-digests))) (mv :bounds fn2-fc-context fn2-digests))
      ((mv code fn2-digests) (fn2-checkpoint-boot-geometry-load geometry fn2-boot-config fn2-digests))
      ((unless (eq code :ok)) (mv code fn2-fc-context fn2-digests))
      (fn2-fc-context (fn2-fc-context-set-location row (+ which (* 2 (fn2-checkpoint-publication-bank 0 fn2-checkpoint-publication))) fn2-fc-context))
      (fn2-fc-context (fn2-fc-context-set-history row (fn2-checkpoints-history c fn2-checkpoints) fn2-fc-context))
      (fn2-fc-context (fn2-fc-context-set-incarnation row (fn2-checkpoints-incarnation c fn2-checkpoints) fn2-fc-context))
      (fn2-fc-context (fn2-fc-context-set-geometry row geometry fn2-fc-context))
      (fn2-fc-context (fn2-fc-context-set-hash row hash fn2-fc-context))
      (fn2-fc-context (fn2-fc-context-set-previous-seal row previous fn2-fc-context)))
  (mv :ok fn2-fc-context fn2-digests)))
(fn2-fc-context-preserves fn2-checkpoint-writer-context-children
 (which fn2-checkpoints fn2-checkpoint-publication fn2-boot-config fn2-fc fn2-b3 fn2-fc-context fn2-digests)
 :carriers ((fn2-fc-context 1 :prefix "-CONTEXT") (fn2-digests 2 :prefix "-DIGESTS")))

; One atomic pool bundle. Do not hold one storage window while waiting for a
; second window of the same D0 rank. Cached class counts preflight all three;
; ordinary exhaustion has no effect. An invariant failure retains any allocated
; prefix by returning every handle, and the generated worker stops with it held.
(defun fn2-checkpoint-writer-reserve-children (kind owner generation fn2-pool fn2-control)
 (declare (xargs :stobjs (fn2-pool fn2-control)
  :guard (and (fn2-pool-wfp fn2-pool) (fn2-control-wfp fn2-control))))
 (b* (((unless (and (unsigned-byte-p 8 kind) (unsigned-byte-p 32 owner) (unsigned-byte-p 60 generation)))
       (mv :bounds 0 0 0 0 0 0 fn2-pool fn2-control))
      (large (fn2-pool-class-for 4096 fn2-pool))
      (scratch (fn2-pool-class-for 160 fn2-pool))
      ((unless (and (natp large) (< large (fn2-pool-nclasses fn2-pool))
                     (natp scratch) (< scratch (fn2-pool-nclasses fn2-pool))))
       (mv :bounds 0 0 0 0 0 0 fn2-pool fn2-control))
      ((unless (and (<= (if (equal large scratch) 3 2) (fn2-pool-class-countsi large fn2-pool))
                     (or (equal large scratch) (<= 1 (fn2-pool-class-countsi scratch fn2-pool)))))
       (mv :exhausted 0 0 0 0 0 0 fn2-pool fn2-control))
      ((mv code s0 g0 fn2-pool) (fn2-pool-reserve large kind owner generation fn2-pool))
      ((unless (eq code :ok)) (mv code 0 0 0 0 0 0 fn2-pool fn2-control))
      ((mv code s1 g1 fn2-pool) (fn2-pool-reserve large kind owner generation fn2-pool))
      ((unless (eq code :ok)) (mv :partial s0 g0 0 0 0 0 fn2-pool fn2-control))
      ((mv code ss gs fn2-pool) (fn2-pool-reserve scratch kind owner generation fn2-pool)))
  (mv (if (eq code :ok) :ok :partial) s0 g0 s1 g1 ss gs fn2-pool fn2-control)))
(fn2-pool-preserves fn2-checkpoint-writer-reserve-children
 (kind owner generation fn2-pool fn2-control)
 :carriers ((fn2-pool 7 :prefix "-POOL") (fn2-control 8 :prefix "-CONTROL")))

(defun fn2-checkpoint-writer-release-children (s0 g0 s1 g1 ss gs kind owner generation fn2-pool fn2-control)
 (declare (xargs :stobjs (fn2-pool fn2-control)
  :guard (and (fn2-pool-wfp fn2-pool) (fn2-control-wfp fn2-control))))
 (b* (((mv code fn2-pool fn2-control) (fn2-core-release-children s0 g0 kind owner generation fn2-pool fn2-control))
      ((unless (member-eq code '(:ok :retired))) (mv code fn2-pool fn2-control))
      ((mv code fn2-pool fn2-control) (fn2-core-release-children s1 g1 kind owner generation fn2-pool fn2-control))
      ((unless (member-eq code '(:ok :retired))) (mv code fn2-pool fn2-control))
      ((mv code fn2-pool fn2-control) (fn2-core-release-children ss gs kind owner generation fn2-pool fn2-control)))
  (mv (if (member-eq code '(:ok :retired)) :ok code) fn2-pool fn2-control)))
(fn2-pool-preserves fn2-checkpoint-writer-release-children
 (s0 g0 s1 g1 ss gs kind owner generation fn2-pool fn2-control)
 :carriers ((fn2-pool 1 :prefix "-POOL") (fn2-control 2 :prefix "-CONTROL")))
