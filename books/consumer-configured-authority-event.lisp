; First complete account E family after the actual bounded node decision.
; Source assembly: the registered node/identity producer, carried-state
; relation, guards, cost/funding and owner installation remain qualification
; obligations. No native caller may supply NEXT or a semantic phase flag.
(in-package "ACL2")
(include-book "consumer-configured-authority-replay")
(include-book "consumer-configured-authority-finish")

; The actual authority node producer preserves committed articles/bindings/
; retention, and the same identity producer emits :none. Consequently this
; family needs no article comparison, control lookup, withdrawal traversal,
; verdict traversal or visibility reconstruction. NEXT is the retained
; configured node from the owner's registered :node-ready decision.
(defun fn-cape-authority-after-node (s produced next base-row-carry)
 (declare (xargs :guard (and (fn-cnode-statep (fn-cp-nth 1 s))
                             (fn-cnode-statep next)
                             (fn-store-event-p (fn-cp-nth 0 (fn-cp-nth 15 s))))
                  :verify-guards nil))
 (fn-cape-authority-finish s produced next
                          (fn-cnode-config (fn-cp-nth 1 s)) base-row-carry))

(in-theory (disable fn-cape-authority-after-node))
