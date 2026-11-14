; The live publisher consumes actual checked boot state, never a caller's
; assertion of image geometry. Current boot admits only an empty anchor bank;
; nonempty selection/restore must replace that explicit startup restriction.
(in-package "ACL2")
(include-book "boot-kind")
(include-book "checkpoint-publication")
(fn2-book-layer :b)

(defun fn2-checkpoint-publication-bind-boot (fn2-boot-config fn2-checkpoint-publication)
 (declare (xargs :stobjs (fn2-boot-config fn2-checkpoint-publication)
  :guard (and (fn2-boot-config-wfp fn2-boot-config)
              (fn2-checkpoint-publication-wfp fn2-checkpoint-publication))))
 (if (not (and (< 0 (fn2-checkpoint-publication-rows fn2-checkpoint-publication))
               (equal (fn2-checkpoint-publication-phase 0 fn2-checkpoint-publication)
                      *fn2-checkpoint-publication-phase-idle*)
               (equal (fn2-boot-config-checkpoint-layout-ready fn2-boot-config) 1)
               (fn2-checkpoint-image-sizep (fn2-boot-config-image-size fn2-boot-config)
                 (fn2-boot-config-extents fn2-boot-config) (fn2-boot-config-count fn2-boot-config))))
     (mv :layout-unbound fn2-checkpoint-publication)
  (let ((fn2-checkpoint-publication (fn2-checkpoint-publication-put 0
          (layout-ready 1) (image-size (fn2-boot-config-image-size fn2-boot-config))
          (extents (fn2-boot-config-extents fn2-boot-config)) (groups (fn2-boot-config-count fn2-boot-config))
          (has-base 0) (active-bank 0))))
   (mv :ok fn2-checkpoint-publication))))
(fn2-checkpoint-publication-preserves fn2-checkpoint-publication-bind-boot
 (fn2-boot-config fn2-checkpoint-publication) :position 1)

(defun fn2-checkpoint-boot-geometry-word (i fn2-boot-config)
 (declare (xargs :stobjs fn2-boot-config
  :guard (and (fn2-boot-config-wfp fn2-boot-config) (natp i) (< i 8))))
 (let ((at (* 4 i)))
  (fn-b3-word (+ (fn2-boot-config-geometryi at fn2-boot-config)
                (* 256 (fn2-boot-config-geometryi (+ at 1) fn2-boot-config))
                (* 65536 (fn2-boot-config-geometryi (+ at 2) fn2-boot-config))
                (* 16777216 (fn2-boot-config-geometryi (+ at 3) fn2-boot-config))))))
(defthm fn2-checkpoint-boot-geometry-word-type
 (unsigned-byte-p 32 (fn2-checkpoint-boot-geometry-word i fn2-boot-config)))
(in-theory (disable fn2-checkpoint-boot-geometry-word))

(defun fn2-checkpoint-boot-geometry-copy (i row fn2-boot-config fn2-digests)
 (declare (xargs :stobjs (fn2-boot-config fn2-digests) :measure (nfix (- 8 (nfix i)))
  :guard (and (fn2-boot-config-wfp fn2-boot-config) (fn2-digest-rowp row fn2-digests)
              (natp i) (<= i 8))))
 (if (or (not (natp i)) (>= i 8)) fn2-digests
  (let ((fn2-digests (fn2-digest-set-word row i (fn2-checkpoint-boot-geometry-word i fn2-boot-config) fn2-digests)))
   (fn2-checkpoint-boot-geometry-copy (+ 1 i) row fn2-boot-config fn2-digests))))

(defun fn2-checkpoint-boot-geometry-load (row fn2-boot-config fn2-digests)
 (declare (xargs :stobjs (fn2-boot-config fn2-digests)
  :guard (and (fn2-boot-config-wfp fn2-boot-config) (fn2-digests-wfp fn2-digests))))
 (if (not (and (equal (fn2-boot-config-checkpoint-layout-ready fn2-boot-config) 1)
               (fn2-digest-rowp row fn2-digests)))
     (mv :layout-unbound fn2-digests)
  (let ((fn2-digests (fn2-checkpoint-boot-geometry-copy 0 row fn2-boot-config fn2-digests)))
   (mv :ok fn2-digests))))
(fn2-digests-preserves fn2-checkpoint-boot-geometry-load
 (row fn2-boot-config fn2-digests) :position 1)
