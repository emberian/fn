; Internal installation transition, called only by the genuine source-owned
; bootstrap evaluator while the native SAMEpool participant barrier is held.
; These arguments are internal results, never a public supplied allowance.
(in-package "ACL2")
(include-book "allocation-epoch")
(include-book "page-read-pool-state")
(defun fn-rbc-virgin-poolp (fn-page-read-pool)
 (declare (xargs :stobjs fn-page-read-pool :guard t))
 (and (not (fn-prp-alloc-installation fn-page-read-pool))
      (eq (fn-prp-alloc-mode fn-page-read-pool) :uninstalled)
      (equal (fn-prp-alloc-epoch fn-page-read-pool) 0)
      (equal (fn-prp-alloc-occupied fn-page-read-pool) 0)
      (equal (fn-prp-alloc-allocated fn-page-read-pool) 0)
      (equal (fn-prp-alloc-active-turns fn-page-read-pool) 0)
      (not (fn-prp-alloc-gc-nonce fn-page-read-pool))))
(defun fn-aec-bootstrap-complete-internal
 (installation pages page-octets reservation suffix fn-page-read-pool)
 (declare (xargs :stobjs fn-page-read-pool :guard t))
 (let* ((domain (fn-aec-at 2 installation))
        (association (fn-aec-at 1 installation)))
  (cond
   ((not (fn-rbc-virgin-poolp fn-page-read-pool))
    (mv :runtime-bootstrap-already-attempted :fenced fn-page-read-pool))
   ((not (and (fn-aec-installationp installation)
              (natp pages) (posp page-octets) (posp reservation)
              (natp suffix) (<= suffix domain)
              (<= pages domain) (<= page-octets domain)
              (<= reservation domain)
              (equal page-octets (fn-aec-at 4 association))
              (equal reservation (fn-aec-at 5 association))
              ; Division before multiplication keeps the primitive immediate.
              (<= pages (floor domain page-octets))))
    (mv :runtime-bootstrap-geometry-refused :refused fn-page-read-pool))
   (t
    (let ((occupied (* pages page-octets)))
     (if (not (fn-aec-statep installation :active 0 occupied suffix 0 nil))
         (mv :runtime-bootstrap-budget-refused :refused fn-page-read-pool)
       (let* ((fn-page-read-pool
               (update-fn-prp-alloc-installation installation fn-page-read-pool))
              (fn-page-read-pool
               (update-fn-prp-alloc-occupied occupied fn-page-read-pool))
              (fn-page-read-pool
               (update-fn-prp-alloc-allocated suffix fn-page-read-pool))
              (fn-page-read-pool
               (update-fn-prp-alloc-mode :active fn-page-read-pool)))
        ; Global BOOT stays closed; genuine ATS construction must consume the
        ; prepaid suffix before any ordinary executor may enter.
        (mv :runtime-bootstrap-installed :accepted fn-page-read-pool))))))))
