; Internal pre-dispatch reader continuation. The caller holds owner exclusion
; from current source validation through actual RC and once-only completion.
(in-package "ACL2")
(include-book "../books/index-connection-repin-prepare")

(defun fn-owner-index-connection-repin-prepare
 (id old-token new-token fuel fn-mio$c state)
 (declare (xargs :stobjs (fn-mio$c state) :guard t))
 ; Every fn-mca-read-span/fn-orr-read-span uses this reader-view selector,
 ; including reads on connections whose exposure/peer OPEN used working state.
 (let ((kind (if (and (f-boundp-global 'fn-owner-reader-views state)
                      (consp (f-get-global 'fn-owner-reader-views state)))
                 :d :current)))
  (stobj-let ((fn-index-backing (fn-mio$c-provider fn-mio$c)))
   (word pin left fn-index-backing)
   (fn-icr-repin-prepare id old-token new-token kind (nfix fuel) fn-index-backing)
   (mv word pin left fn-mio$c state))))
