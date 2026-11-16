; Connected BOOT callbacks. Scalar authority comes only from the live actor.
; Expected-byte construction never mints a receipt; completed physical reads do.
(in-package "ACL2")
(include-book "boot-bootstrap-verify")
(include-book "boot-anchor-admission")
(fn2-book-layer :b)

; Descriptor CHECK costing is deliberately unresolved: its FORMAT grant does
; not include terminal decode/reference capture. Do not activate these faces
; until the lower reader owner supplies the complete callback bound.
(defcost fn2-boot-checkpoint-descriptor-target :answers t)
(defcost fn2-boot-bootstrap-offset :answers (:ok :bounds :state))
(defcost fn2-boot-checkpoint-anchor-offset :answers (:ok :bounds :source :state))
(defcost fn2-boot-bootstrap-pack :answers t :bytes 16384
 :tables (fn2-core-fields fn2-core-digests fn2-core-b3 fn2-core-pool))
(defcost fn2-boot-bootstrap-verify :answers t :bytes 24576
 :tables (fn2-core-boot-config fn2-core-fields fn2-core-digests fn2-core-b3 fn2-core-pool))
(defcost fn2-boot-checkpoint-anchor-zero :answers t :bytes 4096 :tables (fn2-core-pool))
(defcost fn2-boot-checkpoint-anchor-step :answers t :bytes 8192
 :tables (fn2-core-boot-config fn2-core-checkpoints fn2-core-checkpoint-refs fn2-core-checkpoint-bytes
          fn2-core-fc fn2-core-fc-context fn2-core-b3 fn2-core-fields fn2-core-pool fn2-core-digests))

(defmacro fn2-boot-checkpoint-core-operations ()
 '(progn
  (defun fn2-boot-checkpoint-owner-p (id ogen fn2-core)
   (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
   (if (not (and (unsigned-byte-p 32 id) (eq (fn2-boot-snapshot-read-code id fn2-core) :ok))) nil
    (let* ((row-kind (fn2-machine-kind id fn2-core)) (row-generation (fn2-machine-generation id fn2-core)) (row-pending (fn2-machine-pending id fn2-core)) (row-stage (fn2-machine-stage id fn2-core)) (row-index (fn2-machine-index id fn2-core)) (row-total (fn2-machine-total id fn2-core)))
(and (unsigned-byte-p 32 id) (posp ogen) (unsigned-byte-p 60 ogen)
        (eq (fn2-boot-snapshot-read-code id fn2-core) :ok)
        (equal row-kind *fn2-boot-kind*)
        (equal row-generation ogen)
        (equal row-pending 0)
        (equal row-stage 0)
        (stobj-let ((fn2-boot-config (fn2-core-boot-config fn2-core))) (valid)
         (and (equal row-index (fn2-boot-config-count fn2-boot-config))
              (equal row-total (fn2-boot-config-count fn2-boot-config))
              (null (fn2-boot-config-groups fn2-boot-config))) valid)))))

  (defun fn2-boot-checkpoint-read-complete-p (id offset fn2-core)
   (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
   (if (not (and (unsigned-byte-p 32 id) (eq (fn2-boot-snapshot-read-code id fn2-core) :ok))) nil
    (let* ((row-offset (fn2-machine-offset id fn2-core)) (row-pending (fn2-machine-pending id fn2-core)) (row-event-ready (fn2-machine-event-ready id fn2-core)) (row-outcome (fn2-machine-outcome id fn2-core)) (row-count (fn2-machine-count id fn2-core)))
(and (equal row-offset offset)
        (equal row-pending 0)
        (equal row-event-ready 1)
        (equal row-outcome *fn2-outcome-done*)
        (equal row-count *fn2-format-sector-size*)))))

  ; Receipt binds every namespace component, not merely generation or history.
  ; For parser phases it also binds the actual saved read address/completion.
  (defun fn2-boot-bootstrap-current-p (id ogen fn2-core)
   (declare (xargs :stobjs fn2-core :verify-guards nil :guard (fn2-core-wfp fn2-core)))
   (if (not (and (unsigned-byte-p 32 id) (eq (fn2-boot-snapshot-read-code id fn2-core) :ok))) nil
    (let* ((row-image-size (fn2-machine-image-size id fn2-core)) (row-phase (fn2-machine-phase id fn2-core)) (row-checkpoint-index (fn2-machine-checkpoint-index id fn2-core)) (row-offset (fn2-machine-offset id fn2-core)) (completed (fn2-boot-checkpoint-read-complete-p id row-offset fn2-core)))
(and (fn2-boot-checkpoint-owner-p id ogen fn2-core)
    (stobj-let ((fn2-boot-config (fn2-core-boot-config fn2-core))
                (fn2-origin (fn2-core-origin fn2-core))
                (fn2-checkpoints (fn2-core-checkpoints fn2-core))
                (fn2-checkpoint-refs (fn2-core-checkpoint-refs fn2-core))
                (fn2-checkpoint-bytes (fn2-core-checkpoint-bytes fn2-core))) (valid)
     (and (fn2-boot-bootstrap-receipt-p *fn2-boot-kind* id ogen fn2-boot-config fn2-origin)
          (equal row-image-size (fn2-boot-config-image-size fn2-boot-config))
          (let ((phase row-phase) (c row-checkpoint-index))
           (and (natp c) (< c *fn2-checkpoint-anchor-slots*)
            (cond
             ((or (equal phase *fn2-boot-state-checkpoint-anchor*)
                  (equal phase *fn2-boot-state-checkpoint-anchor-step*))
              (mv-let (code offset) (fn2-checkpoint-anchor-offset c row-image-size
                 (fn2-boot-config-extents fn2-boot-config) (fn2-boot-config-count fn2-boot-config))
               (and (eq code :ok) (equal row-offset offset)
                (or (equal phase *fn2-boot-state-checkpoint-anchor*)
                    (and completed (equal row-offset offset))))))
             ((equal phase *fn2-boot-state-checkpoint-descriptor*) t)
             ((equal phase *fn2-boot-state-checkpoint-descriptor-step*)
              (mv-let (code offset bytes) (fn2-boot-checkpoint-descriptor-target-pool c *fn2-boot-kind* id ogen
                 fn2-boot-config fn2-origin fn2-checkpoints fn2-checkpoint-refs fn2-checkpoint-bytes)
               (and (eq code :read) (equal bytes *fn2-format-sector-size*)
                    (and completed (equal row-offset offset)))))
             (t nil))))) valid)))))

  (defun fn2-boot-bootstrap-offset (id ogen fn2-core)
   (declare (xargs :stobjs fn2-core :verify-guards nil :guard (fn2-core-wfp fn2-core)))
   (if (not (and (fn2-boot-checkpoint-owner-p id ogen fn2-core)
                 (equal (fn2-machine-phase id fn2-core) *fn2-boot-state-bootstrap*))) (mv :state 0)
    (let ((size (fn2-machine-image-size id fn2-core)))
    (stobj-let ((fn2-boot-config (fn2-core-boot-config fn2-core))) (code offset)
     (let ((offset (* *fn2-format-sector-size* (fn2-checkpoint-bootstrap-unit
                    (fn2-boot-config-extents fn2-boot-config) (fn2-boot-config-count fn2-boot-config)))))
      (if (fn2-checkpoint-image-sizep size
             (fn2-boot-config-extents fn2-boot-config) (fn2-boot-config-count fn2-boot-config))
       (mv :ok offset) (mv :bounds 0))) (mv code offset)))))

  (defun fn2-boot-checkpoint-anchor-offset (id ogen fn2-core)
   (declare (xargs :stobjs fn2-core :verify-guards nil :guard (fn2-core-wfp fn2-core)))
   (if (not (and (fn2-boot-checkpoint-owner-p id ogen fn2-core)
                 (equal (fn2-machine-phase id fn2-core) *fn2-boot-state-checkpoint-anchor*))) (mv :state 0)
    (let ((c (fn2-machine-checkpoint-index id fn2-core)) (size (fn2-machine-image-size id fn2-core)))
     (stobj-let ((fn2-boot-config (fn2-core-boot-config fn2-core)) (fn2-origin (fn2-core-origin fn2-core))) (code offset)
      (if (and (fn2-boot-bootstrap-receipt-p *fn2-boot-kind* id ogen fn2-boot-config fn2-origin)
               (equal size (fn2-boot-config-image-size fn2-boot-config)))
       (fn2-checkpoint-anchor-offset c size (fn2-boot-config-extents fn2-boot-config) (fn2-boot-config-count fn2-boot-config))
       (mv :source 0)) (mv code offset)))))

  (defun fn2-boot-bootstrap-pack (id ogen fn2-core)
   (declare (xargs :stobjs fn2-core :verify-guards nil :guard (fn2-core-wfp fn2-core)))
   (if (not (and (unsigned-byte-p 32 id) (eq (fn2-boot-snapshot-read-code id fn2-core) :ok))) (mv :state fn2-core)
    (let* ((row-phase (fn2-machine-phase id fn2-core)) (row-image-size (fn2-machine-image-size id fn2-core)) (row-pool-slot (fn2-machine-pool-slot id fn2-core)) (row-pool-gen (fn2-machine-pool-gen id fn2-core)))
(if (not (and (fn2-boot-checkpoint-owner-p id ogen fn2-core)
                 (equal row-phase *fn2-boot-state-bootstrap*)))
       (mv :state fn2-core)
    (stobj-let ((fn2-boot-config (fn2-core-boot-config fn2-core))
                (fn2-fields (fn2-core-fields fn2-core)) (fn2-digests (fn2-core-digests fn2-core))
                (fn2-b3 (fn2-core-b3 fn2-core)) (fn2-pool (fn2-core-pool fn2-core)))
     (code fn2-fields fn2-digests fn2-b3 fn2-pool)
     (fn2-boot-bootstrap-pack-pool row-image-size
      row-pool-slot row-pool-gen *fn2-boot-kind* id ogen
      fn2-boot-config fn2-fields fn2-digests fn2-b3 fn2-pool)
     (mv code fn2-core))))))

  (defun fn2-boot-bootstrap-verify (id ogen budget fn2-core)
   (declare (xargs :stobjs fn2-core :verify-guards nil :guard (fn2-core-wfp fn2-core)))
   (if (not (and (unsigned-byte-p 32 id) (eq (fn2-boot-snapshot-read-code id fn2-core) :ok))) (mv :state fn2-core)
    (let* ((row-phase (fn2-machine-phase id fn2-core)) (row-image-size (fn2-machine-image-size id fn2-core)) (row-pool-slot (fn2-machine-pool-slot id fn2-core)) (row-pool-gen (fn2-machine-pool-gen id fn2-core)) (row-rx-slot (fn2-machine-rx-slot id fn2-core)) (row-rx-gen (fn2-machine-rx-gen id fn2-core)) (row-offset (fn2-machine-offset id fn2-core)) (completed (fn2-boot-checkpoint-read-complete-p id row-offset fn2-core)))
(if (not (and (fn2-boot-checkpoint-owner-p id ogen fn2-core)
                 (equal row-phase *fn2-boot-state-bootstrap-verify*)))
       (mv :state fn2-core)
    (if (not (and (natp budget) (<= 24576 budget))) (mv :more fn2-core)
     (stobj-let ((fn2-boot-config (fn2-core-boot-config fn2-core)) (fn2-origin (fn2-core-origin fn2-core))
                 (fn2-fields (fn2-core-fields fn2-core)) (fn2-digests (fn2-core-digests fn2-core))
                 (fn2-b3 (fn2-core-b3 fn2-core)) (fn2-pool (fn2-core-pool fn2-core)))
      (code fn2-boot-config fn2-fields fn2-digests fn2-b3 fn2-pool)
      (if (and completed (equal row-offset
           (* *fn2-format-sector-size* (fn2-checkpoint-bootstrap-unit
             (fn2-boot-config-extents fn2-boot-config) (fn2-boot-config-count fn2-boot-config)))))
       (fn2-boot-bootstrap-verify-pool row-image-size
        row-pool-slot row-pool-gen
        row-rx-slot row-rx-gen *fn2-boot-kind* id ogen
        fn2-boot-config fn2-origin fn2-fields fn2-digests fn2-b3 fn2-pool)
       (mv :state fn2-boot-config fn2-fields fn2-digests fn2-b3 fn2-pool))
      (mv code fn2-core)))))))

  (defun fn2-boot-checkpoint-anchor-zero (id ogen fn2-core)
   (declare (xargs :stobjs fn2-core :verify-guards nil :guard (fn2-core-wfp fn2-core)))
   (if (not (and (unsigned-byte-p 32 id) (eq (fn2-boot-snapshot-read-code id fn2-core) :ok))) (mv :state fn2-core)
    (let* ((row-phase (fn2-machine-phase id fn2-core)) (row-create (fn2-machine-create id fn2-core)) (row-pool-slot (fn2-machine-pool-slot id fn2-core)) (row-pool-gen (fn2-machine-pool-gen id fn2-core)))
(if (not (and (fn2-boot-bootstrap-current-p id ogen fn2-core)
                 (equal row-phase *fn2-boot-state-checkpoint-anchor*)
                 (equal row-create 1))) (mv :state fn2-core)
    (stobj-let ((fn2-pool (fn2-core-pool fn2-core))) (code fn2-pool)
     (b* ((slot row-pool-slot) (gen row-pool-gen)
          ((mv code fn2-pool) (fn2-pool-reset slot gen *fn2-boot-kind* id ogen fn2-pool))
          ((unless (eq code :ok)) (mv code fn2-pool)))
      (fn2-boot-pad *fn2-format-sector-size* 0 slot gen *fn2-boot-kind* id ogen fn2-pool))
     (mv code fn2-core))))))

  (defun fn2-boot-checkpoint-anchor-step (id ogen budget fn2-core)
   (declare (xargs :stobjs fn2-core :verify-guards nil :guard (fn2-core-wfp fn2-core)))
   (if (not (and (unsigned-byte-p 32 id) (eq (fn2-boot-snapshot-read-code id fn2-core) :ok))) (mv :state 0 fn2-core)
    (let* ((row-phase (fn2-machine-phase id fn2-core)) (row-checkpoint-index (fn2-machine-checkpoint-index id fn2-core)) (row-checkpoint-length (fn2-machine-checkpoint-length id fn2-core)) (row-rx-slot (fn2-machine-rx-slot id fn2-core)) (row-rx-gen (fn2-machine-rx-gen id fn2-core)))
(if (not (and (fn2-boot-bootstrap-current-p id ogen fn2-core)
                 (equal row-phase *fn2-boot-state-checkpoint-anchor-step*)))
       (mv :state 0 fn2-core)
    (stobj-let ((fn2-boot-config (fn2-core-boot-config fn2-core)) (fn2-origin (fn2-core-origin fn2-core))
                (fn2-checkpoints (fn2-core-checkpoints fn2-core)) (fn2-checkpoint-refs (fn2-core-checkpoint-refs fn2-core))
                (fn2-checkpoint-bytes (fn2-core-checkpoint-bytes fn2-core)) (fn2-fc (fn2-core-fc fn2-core))
                (fn2-fc-context (fn2-core-fc-context fn2-core)) (fn2-b3 (fn2-core-b3 fn2-core))
                (fn2-fields (fn2-core-fields fn2-core)) (fn2-pool (fn2-core-pool fn2-core)) (fn2-digests (fn2-core-digests fn2-core)))
     (code length fn2-boot-config fn2-checkpoints fn2-checkpoint-refs fn2-checkpoint-bytes
      fn2-fc fn2-fc-context fn2-b3 fn2-fields fn2-pool fn2-digests)
     (fn2-boot-anchor-admit-pool row-checkpoint-index
      row-checkpoint-length row-rx-slot row-rx-gen
      *fn2-boot-kind* id ogen budget fn2-boot-config fn2-origin fn2-checkpoints fn2-checkpoint-refs fn2-checkpoint-bytes
      fn2-fc fn2-fc-context fn2-b3 fn2-fields fn2-pool fn2-digests)
     (mv code length fn2-core))))))
  (fn2-core-preserves fn2-boot-bootstrap-pack (id ogen fn2-core) :position 1 :rows nil)
  (fn2-core-preserves fn2-boot-bootstrap-verify (id ogen budget fn2-core) :position 1 :rows nil)
  (fn2-core-preserves fn2-boot-checkpoint-anchor-zero (id ogen fn2-core) :position 1 :rows nil)
  (fn2-core-preserves fn2-boot-checkpoint-anchor-step (id ogen budget fn2-core) :position 2 :rows nil)
  ; Materialize the sole existing descriptor wrappers against CURRENT-P above.
  (fn2-boot-descriptor-operations)))
