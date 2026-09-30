; Actual INITIAL entry: source and complete request family are read from
; their internal owners. No supplied demand/receipt/table argument exists.
(in-package "ACL2")
(include-book "../books/snapshot-initial-custody")
(include-book "../books/runtime-operation-source")
(include-book "recovery-initial-source-host")

(defun fn-owner-recovery-initial-admit (source fn-page-read-pool state)
  (declare (xargs :stobjs (fn-page-read-pool state) :mode :program))
  (mv-let (erp descriptor state) (fn-owner-recovery-startup-source source state)
    (if (or erp (not (eq (fn-prl-nth 0 descriptor) :recovery-census)))
        (mv erp descriptor fn-page-read-pool state)
      ; The caller holds the same owner/extent span across both readouts;
      ; there is no yield or caller-supplied installation association.
      (mv-let (word family)
        (fn-owner-runtime-operation-source :initial fn-page-read-pool state)
        (if (not (eq word :available))
            (mv nil '(:unavailable :initial-runtime-family) fn-page-read-pool state)
          (mv-let (word table)
            (fn-owner-runtime-operation-role-table :initial fn-page-read-pool state)
            (if (not (eq word :available))
                (mv nil '(:unavailable :initial-runtime-roles) fn-page-read-pool state)
              (mv-let (answer ledger)
                (fn-sni-issue (fn-owner-page-read-ledger fn-page-read-pool)
                              source descriptor family table)
                (if (eq (fn-prl-nth 0 answer) :admitted)
                    (let ((fn-page-read-pool
                           (fn-owner-page-read-keep-ledger ledger fn-page-read-pool)))
                      (mv nil answer fn-page-read-pool state))
                  (mv nil answer fn-page-read-pool state))))))))))

(defun fn-owner-recovery-initial-livep (source maintenance fn-page-read-pool state)
  (declare (xargs :stobjs (fn-page-read-pool state) :mode :program))
  (and (fn-owner-recovery-source-currentp-value
        (fn-owner-recovery-global 'fn-owner-recovery-source state) source state)
       (fn-sni-livep (fn-owner-page-read-ledger fn-page-read-pool) source maintenance)))

; There is deliberately no public INITIAL settle from a host Boolean.
; Role-specific actual release + allocation-turn/collector epilogue must
; produce the real joined settlement before this receipt can be refunded.
