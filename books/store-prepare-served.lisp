; fn: the standalone Store's POST prepare decides the served groups itself
; (lane prepare-served, 2026-09-27; PKT-827 (d)).  Before this book
; host/store-node-host.lisp fn-store-sn-prepare tested
; fn-cnode-selection-servedp in host code, then called
; fn-store-prepare-carried-next, which stages a record whatever its groups.
;
; This book shares the prefix `fn-psrv-' (docs/prefixes.md).
(in-package "ACL2")
(include-book "store-prepare-carried")

; THE STANDALONE STORE'S PREPARE (host/store-node-host.lisp
; fn-store-sn-prepare; host/native/io.lisp fnn-bridge-prepare): the wire
; record W is staged by fn-store-prepare-carried-next only when the live
; configuration CONFIG serves its groups.
(defun fn-psrv-store-prepare-next (config s w count)
  (declare (xargs :guard (and (fn-sn-statep s) (natp count))))
  (if (and (fn-record-p w)
           (fn-cnode-selection-servedp config (fn-record-groups w)))
      (fn-store-prepare-carried-next s w count)
    s))

(defthm fn-psrv-store-prepare-next-cases
  (equal (fn-psrv-store-prepare-next config s w count)
         (if (fn-cnode-selection-servedp config (fn-record-groups w))
             (fn-store-prepare-carried-next s w count)
           s))
  :hints (("Goal" :in-theory (enable fn-store-prepare-carried-next))))

(in-theory (disable fn-psrv-store-prepare-next))
