; Include at the owner bridge after its actual STATE/source accessors.
; No owner-host include here: owner-host owns the serialized producer caller.
(in-package "ACL2")
(logic)
(include-book "../books/index-reader-request")

; Token-only consumer of the actual registered range control. The callee
; validates the exact active query/payload claim before borrowing its plan.
; FUEL pays all directory traversals; STATE is preserved by this consumer.
(defun fn-owner-index-reader-request-render-install
 (token fuel fn-mio$c fn-render-holder state)
 (declare (xargs :stobjs (fn-mio$c fn-render-holder state)
                 :guard (natp fuel)))
 (mv-let (word left fn-mio$c fn-render-holder)
   (fn-irr-render-install token fuel fn-mio$c fn-render-holder)
   (mv word left fn-mio$c fn-render-holder state)))

; Core-generated response projection from the SAME admitted registered
; request. The owner decides current account/configuration authority; this
; consumer validates retained source/query lifetime, not mutable policy.
(defun fn-owner-index-reader-request-response
 (token fuel fn-mio$c state)
 (declare (xargs :stobjs (fn-mio$c state) :guard (natp fuel)))
 (mv-let (word step left)
   (fn-irr-response-read token fuel fn-mio$c)
   (mv word step left fn-mio$c state)))
