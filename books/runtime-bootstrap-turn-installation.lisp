; Internal prepaid bootstrap suffix. The original concrete ATS object already
; belongs to the saved image; no served constructor or supplied kind vector.
(in-package "ACL2")
(include-book "allocation-turn-slots")
(include-book "allocation-epoch-pool")
(include-book "runtime-operation-installed-source")
(defun fn-owner-runtime-ats-construct-internal
 (fn-allocation-turn-slots fn-page-read-pool)
 (declare (xargs :stobjs (fn-allocation-turn-slots fn-page-read-pool) :guard t))
 (mv-let (word compiled) (fn-runtime-operation-compiled-coordinate)
  (let ((kinds (fn-runtime-operation-compiled-kinds)))
   (if (not (and (eq word :compiled-operation-source) compiled
                  (consp kinds) (true-listp kinds)
                  (fn-aec-installationp (fn-prp-alloc-installation fn-page-read-pool))
                  (equal (fn-aec-at 4 compiled)
                         (fn-aec-at 1 (fn-prp-alloc-installation fn-page-read-pool)))))
       (mv :runtime-turn-source-unavailable fn-allocation-turn-slots)
     (fn-ats-construct-internal kinds fn-allocation-turn-slots fn-page-read-pool)))))

(defun fn-owner-runtime-bootstrap-fence-internal (fn-page-read-pool)
 (declare (xargs :stobjs fn-page-read-pool :guard t))
 (let ((fn-page-read-pool
         (update-fn-prp-alloc-mode (fn-aec-uncertain) fn-page-read-pool)))
  (mv :fenced fn-page-read-pool)))

(defthm fn-rbt-fence-is-pool-uncertain-by-definition
 (equal (mv-nth 1 (fn-owner-runtime-bootstrap-fence-internal pool))
        (fn-aec-pool-uncertain-internal pool))
 :rule-classes nil
 :hints (("Goal" :in-theory (enable fn-owner-runtime-bootstrap-fence-internal
                                    fn-aec-pool-uncertain-internal))))
