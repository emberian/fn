; Actual cold semantic transport/constructor leaves. BOOT supplies its live
; owner and completed ordinary read context; these leaves grant no adoption,
; allocator reconstruction, ready flag, or persistent source-retention promise.
(in-package "ACL2")
(include-book "checkpoint-summary-catalog")
(include-book "checkpoint-restore-semantic-reach")
(include-book "boot-config-state")
(fn2-book-layer :c)

(defun fn2-boot-semantic-start-children (slot gen kind owner generation row base budget
 fn2-checkpoints fn2-checkpoint-refs fn2-checkpoint-bytes fn2-checkpoint-restore-map fn2-checkpoint-restore-map-control
 fn2-checkpoint-restore-reach-control fn2-checkpoint-restore-semantic fn2-checkpoint-summary fn2-fc fn2-fields fn2-pool)
 (declare (xargs :stobjs (fn2-checkpoints fn2-checkpoint-refs fn2-checkpoint-bytes fn2-checkpoint-restore-map fn2-checkpoint-restore-map-control fn2-checkpoint-restore-reach-control fn2-checkpoint-restore-semantic fn2-checkpoint-summary fn2-fc fn2-fields fn2-pool)
 :guard (and (fn2-checkpoints-wfp fn2-checkpoints) (fn2-checkpoint-refs-wfp fn2-checkpoint-refs) (fn2-checkpoint-bytes-wfp fn2-checkpoint-bytes)
 (fn2-checkpoint-restore-map-wfp fn2-checkpoint-restore-map) (fn2-checkpoint-restore-map-control-wfp fn2-checkpoint-restore-map-control)
 (fn2-checkpoint-restore-reach-control-wfp fn2-checkpoint-restore-reach-control) (fn2-checkpoint-restore-semantic-wfp fn2-checkpoint-restore-semantic)
 (fn2-checkpoint-summary-wfp fn2-checkpoint-summary) (fn2-fc-wfp fn2-fc) (fn2-fields-wfp fn2-fields) (fn2-pool-wfp fn2-pool))))
 (b* (((unless (and (natp budget) (<= 128 budget)))
       (mv :more fn2-checkpoint-restore-semantic fn2-checkpoint-summary fn2-fc fn2-pool))
      ((unless (and (< 0 (fn2-checkpoint-restore-semantic-rows fn2-checkpoint-restore-semantic))
                    (equal (fn2-checkpoint-restore-semantic-phase 0 fn2-checkpoint-restore-semantic) *fn2-checkpoint-restore-semantic-phase-idle*)
                    (natp row) (< row (fn2-fc-rows fn2-fc)) (unsigned-byte-p 32 row)
                    (natp base) (unsigned-byte-p 32 base) (fn2-run-readerp base fn2-fields)
                    (fn2-checkpoint-restore-reach-current-p fn2-checkpoints fn2-checkpoint-refs fn2-checkpoint-bytes
                     fn2-checkpoint-restore-map fn2-checkpoint-restore-map-control fn2-checkpoint-restore-reach-control)))
       (mv :source fn2-checkpoint-restore-semantic fn2-checkpoint-summary fn2-fc fn2-pool))
      ((mv code fn2-checkpoint-restore-semantic)
       (fn2-checkpoint-restore-semantic-begin slot gen kind owner generation fn2-checkpoints fn2-checkpoint-refs fn2-checkpoint-bytes
        fn2-checkpoint-restore-map fn2-checkpoint-restore-map-control fn2-pool fn2-checkpoint-restore-semantic))
      ((unless (eq code :read)) (mv code fn2-checkpoint-restore-semantic fn2-checkpoint-summary fn2-fc fn2-pool))
      ((mv code fn2-checkpoint-summary)
       (fn2-checkpoint-summary-begin fn2-checkpoint-summary fn2-checkpoints fn2-checkpoint-refs fn2-checkpoint-bytes
        fn2-checkpoint-restore-map fn2-checkpoint-restore-map-control fn2-checkpoint-restore-semantic))
      ((unless (eq code :ok)) (mv code fn2-checkpoint-restore-semantic fn2-checkpoint-summary fn2-fc fn2-pool))
      ((mv code fn2-pool) (fn2-pool-reset slot gen kind owner generation fn2-pool))
      ((unless (eq code :ok)) (mv code fn2-checkpoint-restore-semantic fn2-checkpoint-summary fn2-fc fn2-pool))
      (fn2-fc (fn2-fc-reset row fn2-fc))
      (fn2-checkpoint-restore-semantic (fn2-checkpoint-restore-semantic-put 0 (checker-row row) (field-base base))))
  (mv :read fn2-checkpoint-restore-semantic fn2-checkpoint-summary fn2-fc fn2-pool)))

(defun fn2-boot-semantic-transport-current-p (fn2-checkpoints fn2-checkpoint-refs fn2-checkpoint-bytes
 fn2-checkpoint-restore-map fn2-checkpoint-restore-map-control fn2-checkpoint-restore-reach-control fn2-checkpoint-restore-semantic fn2-pool)
 (declare (xargs :stobjs (fn2-checkpoints fn2-checkpoint-refs fn2-checkpoint-bytes fn2-checkpoint-restore-map fn2-checkpoint-restore-map-control fn2-checkpoint-restore-reach-control fn2-checkpoint-restore-semantic fn2-pool)
 :guard (and (fn2-checkpoints-wfp fn2-checkpoints) (fn2-checkpoint-refs-wfp fn2-checkpoint-refs) (fn2-checkpoint-bytes-wfp fn2-checkpoint-bytes)
 (fn2-checkpoint-restore-map-wfp fn2-checkpoint-restore-map) (fn2-checkpoint-restore-map-control-wfp fn2-checkpoint-restore-map-control)
 (fn2-checkpoint-restore-reach-control-wfp fn2-checkpoint-restore-reach-control) (fn2-checkpoint-restore-semantic-wfp fn2-checkpoint-restore-semantic) (fn2-pool-wfp fn2-pool))))
 (and (fn2-checkpoint-restore-semantic-current-p fn2-checkpoints fn2-checkpoint-refs fn2-checkpoint-bytes
       fn2-checkpoint-restore-map fn2-checkpoint-restore-map-control fn2-checkpoint-restore-semantic)
      (fn2-checkpoint-restore-reach-current-p fn2-checkpoints fn2-checkpoint-refs fn2-checkpoint-bytes
       fn2-checkpoint-restore-map fn2-checkpoint-restore-map-control fn2-checkpoint-restore-reach-control)
      (equal (fn2-checkpoint-restore-semantic-phase 0 fn2-checkpoint-restore-semantic) *fn2-checkpoint-restore-semantic-phase-read*)
      (let ((slot (fn2-checkpoint-restore-semantic-slot 0 fn2-checkpoint-restore-semantic)))
       (and (eq (fn2-pool-workspace-code slot (fn2-checkpoint-restore-semantic-gen 0 fn2-checkpoint-restore-semantic)
                  (fn2-checkpoint-restore-semantic-owner-kind 0 fn2-checkpoint-restore-semantic)
                  (fn2-checkpoint-restore-semantic-owner-slot 0 fn2-checkpoint-restore-semantic)
                  (fn2-checkpoint-restore-semantic-owner-gen 0 fn2-checkpoint-restore-semantic) fn2-pool) :ok)
            (<= *fn2-format-page-size* (fn2-pool-cap slot fn2-pool))
            (< (fn2-pool-fill slot fn2-pool) *fn2-format-page-size*)
            (equal (mod (fn2-pool-fill slot fn2-pool) *fn2-format-sector-size*) 0)))))

; The physical offset derives from the actual DFS-selected full Ref and actual
; destination fill. A caller cannot skip a sector by proposing another cursor.
(defun fn2-boot-semantic-target-children (fn2-checkpoints fn2-checkpoint-refs fn2-checkpoint-bytes
 fn2-checkpoint-restore-map fn2-checkpoint-restore-map-control fn2-checkpoint-restore-reach-control fn2-checkpoint-restore-semantic fn2-boot-config fn2-pool)
 (declare (xargs :stobjs (fn2-checkpoints fn2-checkpoint-refs fn2-checkpoint-bytes fn2-checkpoint-restore-map fn2-checkpoint-restore-map-control fn2-checkpoint-restore-reach-control fn2-checkpoint-restore-semantic fn2-boot-config fn2-pool)
 :guard (and (fn2-checkpoints-wfp fn2-checkpoints) (fn2-checkpoint-refs-wfp fn2-checkpoint-refs) (fn2-checkpoint-bytes-wfp fn2-checkpoint-bytes)
 (fn2-checkpoint-restore-map-wfp fn2-checkpoint-restore-map) (fn2-checkpoint-restore-map-control-wfp fn2-checkpoint-restore-map-control)
 (fn2-checkpoint-restore-reach-control-wfp fn2-checkpoint-restore-reach-control) (fn2-checkpoint-restore-semantic-wfp fn2-checkpoint-restore-semantic)
 (fn2-boot-config-wfp fn2-boot-config) (fn2-pool-wfp fn2-pool))))
 (b* (((unless (fn2-boot-semantic-transport-current-p fn2-checkpoints fn2-checkpoint-refs fn2-checkpoint-bytes
                    fn2-checkpoint-restore-map fn2-checkpoint-restore-map-control fn2-checkpoint-restore-reach-control fn2-checkpoint-restore-semantic fn2-pool)) (mv :source 0))
      (slot (fn2-checkpoint-restore-semantic-slot 0 fn2-checkpoint-restore-semantic))
      (offset (+ (* *fn2-format-sector-size* (fn2-checkpoint-restore-semantic-unit 0 fn2-checkpoint-restore-semantic)) (fn2-pool-fill slot fn2-pool))))
  (if (and (unsigned-byte-p 60 offset)
           (<= (+ offset *fn2-format-sector-size*) (fn2-boot-config-image-size fn2-boot-config)))
   (mv :read offset) (mv :bounds 0))))

; Parent BOOT checks its exact completed ordinary read before invoking COPY.
; Copied bytes are still untrusted: only canonical PAGE-REACH below can expose
; ENTRIES. This leaf never accepts a completion/verified/ready boolean.
(defun fn2-boot-semantic-copy-children (rxslot rxgen budget fn2-checkpoints fn2-checkpoint-refs fn2-checkpoint-bytes
 fn2-checkpoint-restore-map fn2-checkpoint-restore-map-control fn2-checkpoint-restore-reach-control fn2-checkpoint-restore-semantic fn2-pool)
 (declare (xargs :stobjs (fn2-checkpoints fn2-checkpoint-refs fn2-checkpoint-bytes fn2-checkpoint-restore-map fn2-checkpoint-restore-map-control fn2-checkpoint-restore-reach-control fn2-checkpoint-restore-semantic fn2-pool)
 :guard (and (fn2-checkpoints-wfp fn2-checkpoints) (fn2-checkpoint-refs-wfp fn2-checkpoint-refs) (fn2-checkpoint-bytes-wfp fn2-checkpoint-bytes)
 (fn2-checkpoint-restore-map-wfp fn2-checkpoint-restore-map) (fn2-checkpoint-restore-map-control-wfp fn2-checkpoint-restore-map-control)
 (fn2-checkpoint-restore-reach-control-wfp fn2-checkpoint-restore-reach-control) (fn2-checkpoint-restore-semantic-wfp fn2-checkpoint-restore-semantic) (fn2-pool-wfp fn2-pool))))
 (b* (((unless (and (natp budget) (<= (* 2 *fn2-format-sector-size*) budget))) (mv :more fn2-pool))
      ((unless (fn2-boot-semantic-transport-current-p fn2-checkpoints fn2-checkpoint-refs fn2-checkpoint-bytes
                    fn2-checkpoint-restore-map fn2-checkpoint-restore-map-control fn2-checkpoint-restore-reach-control fn2-checkpoint-restore-semantic fn2-pool)) (mv :source fn2-pool))
      (slot (fn2-checkpoint-restore-semantic-slot 0 fn2-checkpoint-restore-semantic))
      (gen (fn2-checkpoint-restore-semantic-gen 0 fn2-checkpoint-restore-semantic))
      (kind (fn2-checkpoint-restore-semantic-owner-kind 0 fn2-checkpoint-restore-semantic))
      (owner (fn2-checkpoint-restore-semantic-owner-slot 0 fn2-checkpoint-restore-semantic))
      (generation (fn2-checkpoint-restore-semantic-owner-gen 0 fn2-checkpoint-restore-semantic))
      ((unless (and (not (equal slot rxslot)) (eq (fn2-pool-workspace-code rxslot rxgen kind owner generation fn2-pool) :ok)
                    (equal (fn2-pool-fill rxslot fn2-pool) *fn2-format-sector-size*))) (mv :window fn2-pool))
      ((mv code fn2-pool) (fn2-pool-copy-range rxslot rxgen 0 slot gen (fn2-pool-fill slot fn2-pool)
                             *fn2-format-sector-size* kind owner generation fn2-pool)))
  (mv (if (eq code :ok) (if (equal (fn2-pool-fill slot fn2-pool) *fn2-format-page-size*) :check :read) code) fn2-pool)))

(defcost fn2-boot-checkpoint-semantic-begin :child fn2-boot-semantic-start-children :answers t :bytes 128
 :tables (fn2-core-checkpoint-restore-semantic fn2-core-checkpoint-summary fn2-core-fc fn2-core-pool))
(defcost fn2-boot-checkpoint-semantic-target :child fn2-boot-semantic-target-children :answers (:read :bounds :source) :bytes 128)
(defcost fn2-boot-checkpoint-semantic-copy :child fn2-boot-semantic-copy-children :answers t :bytes 8192 :tables (fn2-core-pool))
(defcost fn2-boot-checkpoint-semantic-check :child fn2-checkpoint-restore-semantic-page-reach :answers t :bytes 4096
 :tables (fn2-core-checkpoint-restore-semantic fn2-core-checkpoint-restore-reach fn2-core-fc fn2-core-fc-context fn2-core-b3 fn2-core-fields fn2-core-pool fn2-core-digests))
(defcost fn2-boot-checkpoint-summary-capture :child fn2-checkpoint-summary-capture :answers t :bytes *fn2-checkpoint-restore-semantic-entry-bytes*
 :tables (fn2-core-checkpoint-summary fn2-core-checkpoint-summary-sources fn2-core-fields))
(defcost fn2-boot-checkpoint-semantic-consume :child fn2-checkpoint-restore-semantic-consume :answers t :bytes *fn2-checkpoint-restore-semantic-entry-bytes*
 :tables (fn2-core-checkpoint-restore-semantic fn2-core-checkpoint-restore-semantic-work fn2-core-fields fn2-core-digests))
(defcost fn2-boot-checkpoint-semantic-find :child fn2-checkpoint-restore-semantic-find :answers t :bytes 128
 :tables (fn2-core-checkpoint-restore-semantic fn2-core-checkpoint-restore-semantic-work fn2-core-fc fn2-core-pool))
(defcost fn2-boot-checkpoint-summary-close :child fn2-checkpoint-summary-close :answers t :tables (fn2-core-checkpoint-summary))

; Explicit row/data frames accompany the actual returned carrier subset.
(defun fn2-boot-semantic-frame-hyps (children)
 (declare (xargs :verify-guards nil))
 (if (atom children) nil
  (append (list (list (fn2-columns-sym (car children) "P") (car children))
                (list (fn2-columns-sym (car children) "-WFP") (car children)))
          (fn2-boot-semantic-frame-hyps (cdr children)))))
(defun fn2-boot-semantic-frame-specs (outputs)
 (declare (xargs :verify-guards nil))
 (if (atom outputs) nil
  (let* ((child (caar outputs)) (position (cadar outputs)) (stem (symbol-name child)))
   (append (list (list (concatenate 'string "-" stem "-TYPE") (fn2-columns-sym child "P") position)
                 (list (concatenate 'string "-" stem "-WFP") (fn2-columns-sym child "-WFP") position)
                 (list (concatenate 'string "-" stem "-ROWS") (fn2-columns-sym child "-ROWS") position :frame child))
           (and (eq child 'fn2-pool) (list (list "-POOL-DATA" 'fn2-pool-data-length position :frame child)))
           (fn2-boot-semantic-frame-specs (cdr outputs))))))
(defmacro fn2-boot-semantic-consumer-frames (name args children outputs)
 `(fn2-checkpoint-restore-semantic-preserves ,name ,args
   :hyps ,(fn2-boot-semantic-frame-hyps children)
   :specs ,(fn2-boot-semantic-frame-specs outputs)))
(fn2-boot-semantic-consumer-frames fn2-boot-semantic-start-children
 (slot gen kind owner generation row base budget fn2-checkpoints fn2-checkpoint-refs fn2-checkpoint-bytes
  fn2-checkpoint-restore-map fn2-checkpoint-restore-map-control fn2-checkpoint-restore-reach-control
  fn2-checkpoint-restore-semantic fn2-checkpoint-summary fn2-fc fn2-fields fn2-pool)
 (fn2-checkpoints fn2-checkpoint-refs fn2-checkpoint-bytes fn2-checkpoint-restore-map fn2-checkpoint-restore-map-control
  fn2-checkpoint-restore-reach-control fn2-checkpoint-restore-semantic fn2-checkpoint-summary fn2-fc fn2-fields fn2-pool)
 ((fn2-checkpoint-restore-semantic 1) (fn2-checkpoint-summary 2) (fn2-fc 3) (fn2-pool 4)))
(fn2-boot-semantic-consumer-frames fn2-boot-semantic-copy-children
 (rxslot rxgen budget fn2-checkpoints fn2-checkpoint-refs fn2-checkpoint-bytes fn2-checkpoint-restore-map
  fn2-checkpoint-restore-map-control fn2-checkpoint-restore-reach-control fn2-checkpoint-restore-semantic fn2-pool)
 (fn2-checkpoints fn2-checkpoint-refs fn2-checkpoint-bytes fn2-checkpoint-restore-map fn2-checkpoint-restore-map-control
  fn2-checkpoint-restore-reach-control fn2-checkpoint-restore-semantic fn2-pool)
 ((fn2-pool 1)))
