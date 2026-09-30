; Guarded actual operation callbacks. No runtime installation or endpoint
; selection is performed by these declarations.
(in-package "ACL2")
(include-book "../books/connection-operation-start")

(definterface fn-owner-index-connection-prepare :class :common-lisp-compliant
 :raw-with (fn-owner-index-connection-prepare-preserves-carried-pool
            fn-owner-index-connection-prepare-retains-installed-roots))

(definterface fn-owner-index-connection-start :class :common-lisp-compliant
 :keystones (fn-owner-index-connection-reserved-has-registered-receipt))
