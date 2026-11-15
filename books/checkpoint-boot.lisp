; The live publisher consumes actual checked boot state, never a caller's
; assertion of image geometry. Current boot admits only an empty anchor bank;
; nonempty selection/restore must replace that explicit startup restriction.
(in-package "ACL2")
(include-book "boot-kind")
(include-book "checkpoint-publication")
(include-book "boot-geometry-state")
(fn2-book-layer :b)

(defun fn2-checkpoint-publication-bind-boot (fn2-boot-config fn2-checkpoint-publication)
 (declare (xargs :stobjs (fn2-boot-config fn2-checkpoint-publication)
  :guard (and (fn2-boot-config-wfp fn2-boot-config)
              (fn2-checkpoint-publication-wfp fn2-checkpoint-publication))))
 (if (not (and (< 0 (fn2-checkpoint-publication-rows fn2-checkpoint-publication))
               (equal (fn2-checkpoint-publication-phase 0 fn2-checkpoint-publication)
                      *fn2-checkpoint-publication-phase-idle*)
               (equal (fn2-boot-config-checkpoint-layout-ready fn2-boot-config) 1)
               ; Rebinding geometry must not erase a same-process live bank,
               ; or silently associate its retained predecessor with an image.
               (or (equal (fn2-checkpoint-publication-layout-ready 0 fn2-checkpoint-publication) 0)
                   (and (equal (fn2-checkpoint-publication-image-size 0 fn2-checkpoint-publication) (fn2-boot-config-image-size fn2-boot-config))
                        (equal (fn2-checkpoint-publication-extents 0 fn2-checkpoint-publication) (fn2-boot-config-extents fn2-boot-config))
                        (equal (fn2-checkpoint-publication-groups 0 fn2-checkpoint-publication) (fn2-boot-config-count fn2-boot-config))))
               (fn2-checkpoint-image-sizep (fn2-boot-config-image-size fn2-boot-config)
                 (fn2-boot-config-extents fn2-boot-config) (fn2-boot-config-count fn2-boot-config))))
     (mv :layout-unbound fn2-checkpoint-publication)
  (let ((fn2-checkpoint-publication (fn2-checkpoint-publication-put 0
          (layout-ready 1) (image-size (fn2-boot-config-image-size fn2-boot-config))
          (extents (fn2-boot-config-extents fn2-boot-config)) (groups (fn2-boot-config-count fn2-boot-config)))))
   (mv :ok fn2-checkpoint-publication))))
(fn2-checkpoint-publication-preserves fn2-checkpoint-publication-bind-boot
 (fn2-boot-config fn2-checkpoint-publication)
 :hyps ((fn2-boot-configp fn2-boot-config) (fn2-checkpoint-publicationp fn2-checkpoint-publication) (fn2-boot-config-wfp fn2-boot-config) (fn2-checkpoint-publication-wfp fn2-checkpoint-publication))
 :specs (("-CHECKPOINT-PUBLICATION-TYPE" fn2-checkpoint-publicationp 1)
         ("-CHECKPOINT-PUBLICATION-WFP" fn2-checkpoint-publication-wfp 1)
         ("-CHECKPOINT-PUBLICATION-ROWS" fn2-checkpoint-publication-rows 1 :frame fn2-checkpoint-publication)))
