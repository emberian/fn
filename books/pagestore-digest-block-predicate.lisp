; Proof-only exact supplied-block predicate, factored without body changes.
; The whole semantic trajectory remains in cursor-semantics; this leaf only
; exposes its actual named block subject without the unrelated proof ancestry.
(in-package "ACL2")
(include-book "pagestore-digest-cursor-refinement")

(defun-nx pgs-dcs-blockp (block msg pgs-digest-state)
  (declare (xargs :stobjs pgs-digest-state :verify-guards nil))
  (implies (pgs-dc-needs-block pgs-digest-state)
           (equal block (fn-b3-words 16
                          (pgs-dcr-span (pgs-dc-pos pgs-digest-state)
                                         (pgs-dc-end pgs-digest-state) msg)))))
