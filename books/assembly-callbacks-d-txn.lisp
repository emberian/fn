; The transaction kind's operations and continuations (D5,
; books/txn.lisp), after the upload's: their own book keeps each layer D section under the one-minute rule.
; After the control connection's section (e-cns): the append check
; (authority.lisp's fn2-authority-allows-events) reads a consumer request's
; connection and the owner's principal through its operations.
(in-package "ACL2")
(include-book "assembly-callbacks-e-cns")
(include-book "txn")
(include-book "authority")
(fn2-txn-op-events)
(fn2-authority-allows-events)
(assert-event (equal *fn2-auth-depend-slot* *fn2-txn-slot-depend*))

(defun fn2-txn-peer-role-grant (conn gen request upload ugen pid account fn2-core)
  (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
  (b* (((mv role principal grant) (fn2-conn-authenticated-peer conn gen fn2-core))
       ((unless (and (eq role :ok) (posp pid) (equal principal pid)
                     (equal (fn2-conn-row-phase conn fn2-core) *fn2-conn-state-article-input*)
                     (equal (fn2-conn-row-request conn fn2-core) request)
                     (equal (fn2-conn-row-upload conn fn2-core) upload)
                     (equal (fn2-conn-row-upload-gen conn fn2-core) ugen)
                     (equal (fn2-conn-row-principal-slot conn fn2-core) account)))
        (mv :access 0)))
    (mv :ok grant)))
(in-theory (disable fn2-txn-peer-role-grant))

(fn2-txn-events)
