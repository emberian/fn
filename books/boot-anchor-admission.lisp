; The real bootstrap receipt gates the existing authenticated anchor intake.
(in-package "ACL2")
(include-book "boot-bootstrap-pack")
(include-book "checkpoint-anchor-input")
(include-book "checkpoint-zero-range")
(include-book "checkpoint-boot-descriptor")
(fn2-book-layer :b)

(defmacro fn2-boot-anchor-return (code length)
 `(mv ,code ,length fn2-boot-config fn2-checkpoints fn2-checkpoint-refs fn2-checkpoint-bytes
      fn2-fc fn2-fc-context fn2-b3 fn2-fields fn2-pool fn2-digests))

(defun fn2-boot-save-anchor-evidence (anchor slot gen kind id ogen fn2-fields fn2-pool fn2-boot-config)
 (declare (xargs :stobjs (fn2-fields fn2-pool fn2-boot-config) :verify-guards nil
  :guard (and (fn2-fields-wfp fn2-fields) (fn2-pool-wfp fn2-pool) (fn2-boot-config-wfp fn2-boot-config))))
 (b* (((unless (and (natp anchor) (< anchor 4)
                     (<= (+ 256 *fn2-format-anchor-num-fields*) (fn2-fields-rows fn2-fields))))
       (mv :bounds fn2-boot-config))
      ((mv code fn2-boot-config) (fn2-boot-save-anchor-digest 32 (* 96 anchor)
        (fn2-fields-ref-off (+ 256 *fn2-format-anchor-field-checkpoint-batch*) fn2-fields)
        slot gen kind id ogen fn2-pool fn2-boot-config))
      ((unless (eq code :ok)) (mv code fn2-boot-config))
      ((mv code fn2-boot-config) (fn2-boot-save-anchor-digest 32 (+ 32 (* 96 anchor))
        (fn2-fields-ref-off (+ 256 *fn2-format-anchor-field-previous-checkpoint*) fn2-fields)
        slot gen kind id ogen fn2-pool fn2-boot-config))
      ((unless (eq code :ok)) (mv code fn2-boot-config)))
  (fn2-boot-save-anchor-digest 32 (+ 64 (* 96 anchor))
    (fn2-fields-ref-off (+ 256 *fn2-format-anchor-field-anchor-hash*) fn2-fields)
    slot gen kind id ogen fn2-pool fn2-boot-config)))

; LENGTH=0 is only the actor's initial visit. The returned actual decoded span
; is retained by that same BOOT row while the input lease stays held. It is
; not a caller assertion of successful verification. A positive LENGTH resumes
; the existing FORMAT continuation and never reseeds its expected context.
(defun fn2-boot-anchor-admit-pool (anchor length slot gen kind id ogen budget
                                  fn2-boot-config fn2-origin fn2-checkpoints fn2-checkpoint-refs fn2-checkpoint-bytes
                                  fn2-fc fn2-fc-context fn2-b3 fn2-fields fn2-pool fn2-digests)
 (declare (xargs :stobjs (fn2-boot-config fn2-origin fn2-checkpoints fn2-checkpoint-refs fn2-checkpoint-bytes
                          fn2-fc fn2-fc-context fn2-b3 fn2-fields fn2-pool fn2-digests)
  :verify-guards nil
  :guard (and (fn2-boot-config-wfp fn2-boot-config) (fn2-origin-wfp fn2-origin)
              (fn2-checkpoints-wfp fn2-checkpoints) (fn2-checkpoint-refs-wfp fn2-checkpoint-refs)
              (fn2-checkpoint-bytes-wfp fn2-checkpoint-bytes) (fn2-fc-wfp fn2-fc)
              (fn2-fc-context-wfp fn2-fc-context) (fn2-b3-wfp fn2-b3)
              (fn2-fields-wfp fn2-fields) (fn2-pool-wfp fn2-pool) (fn2-digests-wfp fn2-digests))))
 (b* (((unless (natp budget)) (fn2-boot-anchor-return :bounds length))
      ((when (zp budget)) (fn2-boot-anchor-return :more length))
      ((unless (and (fn2-boot-bootstrap-receipt-p kind id ogen fn2-boot-config fn2-origin)
                     (natp anchor) (< anchor 4) (natp length) (<= length *fn2-format-anchor-max-size*)))
       (fn2-boot-anchor-return :source length))
      (row 2) (base 256) (geometry (fn2-digest-slot row *fn2-fc-geometry*))
      ((unless (and (fn2-checkpoint-slotp anchor fn2-checkpoints fn2-checkpoint-refs fn2-checkpoint-bytes)
                     (equal (fn2-checkpoints-state anchor fn2-checkpoints) *fn2-checkpoint-state-free*)
                     (< row (fn2-fc-rows fn2-fc)) (< row (fn2-fc-context-rows fn2-fc-context))
                     (fn2-b3-ready row fn2-b3 fn2-digests) (fn2-digest-rowp geometry fn2-digests)
                     (<= (+ base *fn2-format-sealed-batch-num-fields*) (fn2-fields-rows fn2-fields))))
       (fn2-boot-anchor-return :bounds length))
      (readable (fn2-layout-range-code slot gen 0 *fn2-format-sector-size* nil kind id ogen fn2-pool))
      ((unless (eq readable :ok)) (fn2-boot-anchor-return readable length))
      (bit (ash 1 anchor))
      ((when (zp length))
       (b* ((empty (fn2-checkpoint-restore-zero-range *fn2-format-sector-size* 0 slot gen kind id ogen fn2-pool))
            ((when (eq empty :ok))
             (let ((fn2-boot-config (update-fn2-boot-config-anchor-empty-mask
                    (logior bit (fn2-boot-config-anchor-empty-mask fn2-boot-config)) fn2-boot-config)))
              (fn2-boot-anchor-return :empty 0)))
            ((unless (eq empty :padding)) (fn2-boot-anchor-return empty 0))
            ((mv decoded span fn2-fields)
             (fn2-format-anchor-decode base slot gen 0 *fn2-format-anchor-max-size* kind id ogen fn2-fields fn2-pool))
            (tail (if (and (eq decoded :ok) (posp span) (<= span *fn2-format-anchor-max-size*))
                   (fn2-checkpoint-restore-zero-range (- *fn2-format-sector-size* span) span slot gen kind id ogen fn2-pool)
                   :format))
            ((unless (eq tail :ok))
             (let ((fn2-boot-config (update-fn2-boot-config-anchor-invalid-mask
                    (logior bit (fn2-boot-config-anchor-invalid-mask fn2-boot-config)) fn2-boot-config)))
              (fn2-boot-anchor-return :invalid 0)))
            (fn2-digests (fn2-checkpoint-boot-geometry-copy 0 geometry fn2-boot-config fn2-digests))
            (fn2-fc (fn2-fc-reset row fn2-fc))
            (fn2-fc-context (fn2-fc-context-put row (location anchor)
              (history (fn2-origin-history fn2-origin)) (incarnation (fn2-origin-history-incarnation fn2-origin))
              (encoded-length span) (hash geometry) (geometry geometry) (previous-seal geometry))))
        ; The fixed initial decode/tail work has already been charged. FORMAT
        ; starts on the next visit rather than spending its quantum again.
        (fn2-boot-anchor-return :more span)))
      ((unless (and (equal (fn2-fc-context-location row fn2-fc-context) anchor)
                     (equal (fn2-fc-context-history row fn2-fc-context) (fn2-origin-history fn2-origin))
                     (equal (fn2-fc-context-incarnation row fn2-fc-context) (fn2-origin-history-incarnation fn2-origin))
                     (equal (fn2-fc-context-encoded-length row fn2-fc-context) length)
                     (equal (fn2-fc-context-hash row fn2-fc-context) geometry)
                     (equal (fn2-fc-context-geometry row fn2-fc-context) geometry)
                     (equal (fn2-fc-context-previous-seal row fn2-fc-context) geometry)
                     (fn2-boot-descriptor-geometry-matches-p 0 geometry fn2-boot-config fn2-digests)))
       (fn2-boot-anchor-return :context length))
      ((mv code fn2-checkpoints fn2-checkpoint-refs fn2-checkpoint-bytes fn2-fc fn2-b3 fn2-fields fn2-pool fn2-digests)
       (fn2-checkpoint-restore-anchor-step anchor anchor row slot gen length base kind id ogen
        (min budget *fn2-format-sector-size*) fn2-checkpoints fn2-checkpoint-refs fn2-checkpoint-bytes
        fn2-fc fn2-fc-context fn2-b3 fn2-fields fn2-pool fn2-digests))
      ((when (eq code :more)) (fn2-boot-anchor-return :more length))
      ((unless (eq code :candidate))
       (let ((fn2-boot-config (update-fn2-boot-config-anchor-invalid-mask
              (logior bit (fn2-boot-config-anchor-invalid-mask fn2-boot-config)) fn2-boot-config)))
        (fn2-boot-anchor-return :invalid length)))
      ((mv evidence fn2-boot-config)
       (fn2-boot-save-anchor-evidence anchor slot gen kind id ogen fn2-fields fn2-pool fn2-boot-config))
      ((unless (eq evidence :ok))
       (let ((fn2-checkpoints (fn2-checkpoints-set-state anchor *fn2-checkpoint-state-uncertain* fn2-checkpoints)))
        (fn2-boot-anchor-return evidence length)))
      (fn2-boot-config (update-fn2-boot-config-anchor-checked-mask
        (logior bit (fn2-boot-config-anchor-checked-mask fn2-boot-config)) fn2-boot-config)))
  (fn2-boot-anchor-return :candidate length)))
