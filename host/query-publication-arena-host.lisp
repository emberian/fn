; Registered generation capture derives its arena coordinate from actual
; STATE and the bound arena. Caller serialization is owner -> lifecycle.
(in-package "ACL2")
(include-book "../books/index-backing-generations")
(include-book "../books/query-payload-state")
(include-book "../books/payload-arena")
(defun fn-owner-index-publication-arena-capture
  (token fuel fn-mio$c fn-arena state)
  (declare (xargs :stobjs (fn-mio$c fn-arena state) :guard (natp fuel)))
  (cond ((zp fuel) (mv :yield fuel fn-mio$c))
        (t (let ((ledger (fn-owner-query-payload-ledger state)))
             (if (not (fn-pvl-ledgerp ledger))
                 (mv :invalid-payload-ledger (- fuel 1) fn-mio$c)
               (fn-mio-generation-capture-coordinate
                 token (fn-omk-at 0 ledger) (fn-arena-count fn-arena)
                 (- fuel 1) fn-mio$c))))))
(verify-guards fn-owner-index-publication-arena-capture)
