; Actual bootstrap rejection boundary until the selected fixed-image envelope
; is qualified. Raw geometry is observation, never allocation authority.
(in-package "ACL2")
(include-book "page-read-pool-state")
(defun fn-owner-runtime-bootstrap-admit
  (status pages page-octets reservation fn-page-read-pool)
  (declare (xargs :stobjs fn-page-read-pool :guard t))
  (declare (ignore pages page-octets reservation))
  ; The whole fixed-image/first-use/GC/control envelope producer is missing.
  ; No shape, version, constructor subtotal or raw numeric value can replace it.
  (mv (if (or (eq status :qualification-request) (eq status :completed))
          :runtime-qualification-unavailable
        :runtime-observation-uncertain)
      (if (or (eq status :qualification-request) (eq status :completed)) :refused :fenced)
      fn-page-read-pool))
