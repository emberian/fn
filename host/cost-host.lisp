; Cost rows checked in the actual image world, after interface declarations.
; Partial means unknown, never an admission tariff or a completed allocation
; claim.  FN-READER-INSTALL-RESULT is itself unaccounted: its installer is
; too large/has unresolved dependencies for this derivation's inliner.
(in-package "ACL2")
(include-book "../books/def-cost")
(include-book "../books/string-line-cursor-cost")

(def-cost fn-reader-chunk
  :visits (+ 1 request-octets)
  :sizes ((request-octets (len octets)))
  :unaccounted (fn-served-step fn-reader-install-result)
  :hints (("Goal" :in-theory
           (union-theories '(fn-reader-chunk-visits fn-reader-chunk-route-visits)
                           (theory 'minimal-theory)))))
(def-cost-check fn-reader-chunk)

; Pin the actual route and unresolved dependency set.  This does not pretend
; to execute a defun-nx cost twin or the constrained unknown leaf costs.
(assert-event
 (let ((row (cdr (assoc-eq 'fn-reader-chunk (table-alist 'fn-cost (w state))))))
   (and (eq (fn-cost-get :route row) :served)
        (equal (fn-cost-get :route-cost row) '(binary-+ '1 (len octets)))
        (equal (fn-cost-get :unaccounted row) '(fn-served-step fn-reader-install-result)))))

; Real owner syncer entry: derive the same function the native actor calls.
; No supplied bound means no qualifying tariff; custody is already enforced
; for the charged worker projection while total entry work remains owed.
(def-cost create-fn-resource-ledger :unaccounted (make-list-ac))
(def-cost fn-ros-install-syncer :unaccounted (fn-ros-install))
(def-cost fn-ros-issue :unaccounted (fn-rl-wfp fn-rl-draw mv-nth))
(def-operation-check fn-ros-issue)
(def-cost fn-ros-physical
  :unaccounted (fn-ros-livep member-eq-exec fn-ros-settle-ready))
(def-cost fn-ros-outcome :unaccounted (fn-ros-livep fn-ros-settle-ready))
(def-cost fn-ros-drainedp :unaccounted (fn-rl-wfp))
