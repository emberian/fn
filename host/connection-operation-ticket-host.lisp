; Native declarations over the actual guarded STATE ticket callbacks.
(in-package "ACL2")
(include-book "../books/connection-operation-ticket")

(definterface fn-owner-index-connection-finish :class :common-lisp-compliant
 :raw-with (fn-owner-index-connection-finish-raw-with
            fn-owner-index-connection-finish-retains-installed-roots)
 :keystones (fn-owner-index-connection-finish-consumes-one))

(definterface fn-owner-index-connection-fault :class :common-lisp-compliant
 :raw-with (fn-owner-index-connection-fault-raw-pool
            fn-owner-index-connection-fault-retains-roots)
 :keystones (fn-owner-index-connection-fault-is-idempotent))
