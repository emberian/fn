; Internal compiled callbacks; no public supplied BODY or installation.
(in-package "ACL2")
(include-book "../books/allocation-turn-raw-bridge")
(include-book "../books/definterface")

(definterface fn-ats-enter-internal :class :common-lisp-compliant
 :raw-with (fn-atsh-entry-preserves-carried-pool-state fn-atsh-entry-preserves-installed-roots)
 :keystones (fn-ats-enter-owns-actual-shared-nonce fn-ats-entry-preserves-slot-count-correspondence))
(definterface fn-ats-finish-owned :class :common-lisp-compliant
 :raw-with (fn-atsh-finish-preserves-carried-pool-state fn-atsh-finish-preserves-installed-roots)
 :keystones (fn-ats-finish-matching-consumes-once fn-ats-finish-preserves-slot-count-correspondence
))
(definterface fn-ats-uncertain-internal :class :common-lisp-compliant
 :raw-with (fn-atsh-uncertain-preserves-carried-pool-state fn-ats-raw-uncertainty-retains-receipts))
