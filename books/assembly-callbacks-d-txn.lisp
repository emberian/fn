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
  (b* (((unless (and (eq (fn2-conn-snapshot-read-code conn fn2-core) :ok)
                     (posp gen) (equal (fn2-machine-generation conn fn2-core) gen)
                     (equal (fn2-conn-row-phase conn fn2-core) *fn2-conn-state-article-input*)
                     (equal (fn2-conn-row-request conn fn2-core) request)
                     (equal (fn2-conn-row-upload conn fn2-core) upload)
                     (equal (fn2-conn-row-upload-gen conn fn2-core) ugen)
                     (equal (fn2-conn-row-principal-slot conn fn2-core) account)
                     (posp pid) (equal (fn2-conn-row-login-principal conn fn2-core) pid)))
        (mv :access 0))
       (mask (nfix (fn2-conn-row-mask conn fn2-core)))
       (role-mask (logior *fn2-nntp-state-tls* *fn2-nntp-state-authenticated* *fn2-nntp-state-peer*))
       (grant (fn2-conn-row-peer-role-grant conn fn2-core)))
    (if (and (equal (logand mask role-mask) role-mask)
             (equal (logand mask *fn2-nntp-state-anonymous*) 0)
             (posp grant))
        (mv :ok grant)
      (mv :access 0))))
(in-theory (disable fn2-txn-peer-role-grant))

(fn2-txn-events)
