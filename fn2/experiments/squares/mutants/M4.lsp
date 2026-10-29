; M4: short-send running summary loses its previous accumulated offset.
; Original: fn2/books/machines-a-run.lisp:41 at 137695dfc.
; Sole semantic edit: (off (+ off count)) -> (off count).
(in-package "ACL2")
; Test-only redefinition in a fresh process. Never include/certify this file.
; REDEF! updates both ACL2 executable counterpart and raw function.
(redef!)
(defun fn2-echo-observe-send (id event outcome reason count aux0 aux1
  row-phase row-generation row-principal-slot row-account-ref row-ready-prev row-ready-next row-wait-reason row-deadline row-cap-index row-cap-nonce row-pool-slot row-pool-gen row-off row-length row-pending row-borrows row-next-free row-stopped row-mode fn2-core)
  (declare (xargs :stobjs fn2-core :verify-guards nil
                  :guard (and (fn2-core-wfp fn2-core)
                    (fn2-echo-valuesp row-phase row-generation row-principal-slot row-account-ref row-ready-prev row-ready-next row-wait-reason row-deadline row-cap-index row-cap-nonce row-pool-slot row-pool-gen row-off row-length row-pending row-borrows row-next-free row-stopped row-mode)))
           (ignorable id event outcome reason count aux0 aux1 row-phase row-generation row-principal-slot row-account-ref row-ready-prev row-ready-next row-wait-reason row-deadline row-cap-index row-cap-nonce row-pool-slot row-pool-gen row-off row-length row-pending row-borrows row-next-free row-stopped row-mode))
  (let* ((off row-off) (len row-length)
         (fn2-core (fn2-echo-put-core id (borrows (fn2-machine-pool-borrows row-pool-slot fn2-core))))
         (fn2-core
          (if (and (or (equal outcome *fn2-outcome-done*) (equal outcome *fn2-outcome-short*))
                   (natp count) (<= (+ off count) len))
              (fn2-echo-put-core id (off count))
            (fn2-echo-put-core id (phase *fn2-echo-state-closing*)))))
    (mv id fn2-core)))
