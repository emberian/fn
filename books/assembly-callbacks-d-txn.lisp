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
;; The upload binding checks generation, request, live account incarnation
;; and the owning socket. Only that socket can carry administrator authority.
(defun fn2-txn-cancel-authorization (tx article conn gen upload ugen request principal budget fn2-core)
  (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
  (b* (((unless (and (posp article) (unsigned-byte-p 60 article))) (mv :access fn2-core))
       ((mv code actor) (fn2-upload-transfer-principal conn gen upload ugen request principal fn2-core))
       ((unless (eq code :ok)) (mv :access fn2-core))
       ((when (and (eq (fn2-cns-snapshot-read-code conn fn2-core) :ok)
                   (let ((ctl (fn2-cns-row-ctl conn fn2-core)))
                     (and (eq (fn2-ctl-snapshot-read-code ctl fn2-core) :ok)
                          (equal (fn2-ctl-row-admin ctl fn2-core) 1)))))
        (mv :ok fn2-core))
       ((mv tc submitter fn2-core)
        (fn2-auth-xl-core tx *fn2-txn-article-sid* 1 article 0 0 0
                          *fn2-article-entry-field-submitter* budget fn2-core)))
    (mv (case tc
          (:ok (if (and (posp actor) (equal actor submitter)) :ok :access))
          (:more :more)
          (:absent :access)
          (otherwise :unavailable))
        fn2-core)))
(fn2-core-preserves fn2-txn-cancel-authorization (tx article conn gen upload ugen request principal budget fn2-core)
  :position 1 :rows nil)
(in-theory (disable fn2-txn-cancel-authorization))
(assert-event (equal *fn2-auth-depend-slot* *fn2-txn-slot-depend*))
(fn2-txn-events)
