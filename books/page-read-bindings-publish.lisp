; Binding-changing publication uses the existing runtime source authority.
(in-package "ACL2")
(include-book "page-read-binding-revision")
(include-book "runtime-operation-source")

; Actual existing domain getter is called here, not supplied by a host tuple.
; Its current closed producer keeps this path unavailable before mutation.
; Counter-only callers use the distinct frame-proved publisher above.
(defun fn-owner-page-read-bindings-publish (next captured-revision fn-page-read-pool state)
 (declare (xargs :stobjs (fn-page-read-pool state) :guard t :verify-guards nil))
 (let* ((data (fn-prp-data fn-page-read-pool))
        (mode (fn-prp-mode fn-page-read-pool))
        (epoch-mode (fn-prp-alloc-mode fn-page-read-pool))
        (revision (fn-prb-data-revision data)))
  (cond
   ((not (and data (eq mode :served) (member-eq epoch-mode '(:active :draining))))
    (mv :binding-publication-unavailable fn-page-read-pool))
   ((not (and (natp revision) (equal revision captured-revision)))
    (mv :stale-binding-revision fn-page-read-pool))
   (t
    (mv-let (word domain) (fn-owner-runtime-bootstrap-domain fn-page-read-pool state)
     (if (not (and (eq word :runtime-bootstrap-domain) (integerp domain)
                   (< 1 domain) (< revision (- domain 1))))
      (mv :binding-domain-unavailable fn-page-read-pool)
      (let* ((intent (list :binding-publishing mode epoch-mode data next revision))
             (fn-page-read-pool (update-fn-prp-mode intent fn-page-read-pool))
             (fn-page-read-pool (update-fn-prp-alloc-mode :recovery fn-page-read-pool))
             (fn-page-read-pool (update-fn-prp-data (fn-prb-data6 next data (+ 1 revision)) fn-page-read-pool))
             (fn-page-read-pool (update-fn-prp-alloc-mode epoch-mode fn-page-read-pool))
             (fn-page-read-pool (update-fn-prp-mode mode fn-page-read-pool)))
       (mv :published fn-page-read-pool))))))))

