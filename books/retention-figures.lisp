; fn: the two retention figures of a Store node (PKT-220, PRF-185).
;
; `store ROOT retention' (host/native/io.lisp fnn-command-retention, through
; host/store-node-host.lisp fn-store-sn-pin-count and fn-store-sn-reserved)
; prints the pin count and the reserved charge of the retention ledger of
; the Store it replayed; `operator CONFIG obligations' prints the same two
; figures of the Store the running owner carries (books/native-live-status
; fn-nls-report :obligations).  Both read them through these functions, and
; books/native-health.lisp `fn-nls-obligations-figures-are-the-retention-
; figures' proves the live report's first line is these two figures of the
; owner's Store node, so the offline verb and the live one cannot differ on
; the same node.  This book is small so that host/store-node-host.lisp, which
; loads before the status report, can include it.
;
; Prefix `fn-rtf-' (docs/prefixes.md).
(in-package "ACL2")
(include-book "store-observed")

(defun fn-rtf-pin-count (s)
  (declare (xargs :guard t :verify-guards nil))
  (len (fn-retain-pins (fn-node-retention (fn-sn-node s)))))

(defun fn-rtf-reserved (s)
  (declare (xargs :guard t :verify-guards nil))
  (fn-retain-reserved (fn-node-retention (fn-sn-node s))))
