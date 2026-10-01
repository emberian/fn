; Actual source-owned qualifier and geometry completion. Raw observations are
; never an allowance; only the matching compiled producer supplies its tariff.
(in-package "ACL2")
(include-book "runtime-bootstrap-compiled-request")
(include-book "runtime-bootstrap-completion")
(defun fn-owner-runtime-bootstrap-admit
 (status pages page-octets reservation fn-page-read-pool)
 (declare (xargs :stobjs fn-page-read-pool :guard t))
 (mv-let (source-word capsule installation suffix) (fn-rbcp-request)
  (declare (ignore capsule))
  (cond
   ((not (fn-rbc-virgin-poolp fn-page-read-pool))
    (mv :runtime-bootstrap-already-attempted :fenced fn-page-read-pool))
   ((not (eq source-word :runtime-bootstrap-source-available))
    (mv :runtime-qualification-unavailable :refused fn-page-read-pool))
   ((eq status :qualification-request)
    ; No sample is taken until the actual source is available. This word
    ; authorizes the fixed masked observation only, not facility startup.
    (mv :runtime-qualification-available :qualified fn-page-read-pool))
   ((eq status :completed)
    (fn-aec-bootstrap-complete-internal installation pages page-octets
                                        reservation suffix fn-page-read-pool))
   (t (mv :runtime-observation-uncertain :fenced fn-page-read-pool)))))
