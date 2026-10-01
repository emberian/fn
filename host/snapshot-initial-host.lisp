; Actual INITIAL entry: source and complete request family are read from
; their internal owners. No supplied demand/receipt/table argument exists.
(in-package "ACL2")
(include-book "../books/snapshot-initial-custody")
(include-book "../books/runtime-operation-source")
(include-book "recovery-initial-source-host")
(include-book "recovery-initial-operation-host")

(defun fn-owner-recovery-initial-admit (source fn-page-read-pool state)
  (declare (xargs :stobjs (fn-page-read-pool state) :mode :program))
  ; NIL requests the genuine already-issued current source readout. It is
  ; never a source token, installation/refresh request or authority. A
  ; supplied nonNIL token, including a stale one, is checked unchanged.
  (mv-let (read-erp source state)
    (if (null source) (fn-owner-recovery-source-token state)
      (mv nil source state))
    (if read-erp (mv read-erp source fn-page-read-pool state)
  (mv-let (erp descriptor state) (fn-owner-recovery-startup-source source state)
    (if (or erp (not (eq (fn-prl-nth 0 descriptor) :recovery-census)))
        (mv erp descriptor fn-page-read-pool state)
      ; The caller holds the same owner/extent span across both readouts;
      ; there is no yield or caller-supplied installation association.
      (mv-let (word family)
        (fn-owner-runtime-operation-source :initial fn-page-read-pool state)
        (if (not (eq word :runtime-operation-available))
            (mv nil '(:unavailable :initial-runtime-family) fn-page-read-pool state)
          (mv-let (word table)
            (fn-owner-runtime-operation-role-table :initial fn-page-read-pool state)
            (if (not (eq word :runtime-operation-available))
                (mv nil '(:unavailable :initial-runtime-roles) fn-page-read-pool state)
              (mv-let (answer ledger)
                (fn-sni-issue (fn-owner-page-read-ledger fn-page-read-pool)
                              source descriptor family table)
                (if (eq (fn-prl-nth 0 answer) :admitted)
                    (let ((fn-page-read-pool
                           (fn-owner-page-read-keep-ledger ledger fn-page-read-pool)))
                      (mv nil answer fn-page-read-pool state))
                  (mv nil answer fn-page-read-pool state))))))))))))

(defun fn-owner-recovery-initial-livep (source maintenance fn-page-read-pool state)
  (declare (xargs :stobjs (fn-page-read-pool state) :mode :program))
  ; Check the ALREADY issued same-pool row before allowing the sealed
  ; operation handoff. This never issues or refreshes an INITIAL token.
  (and (fn-sni-livep (fn-owner-page-read-ledger fn-page-read-pool) source maintenance)
       (fn-owner-recovery-initial-operation-currentp source state)))

; There is deliberately no public INITIAL settle from a host Boolean.
; Role-specific actual release + allocation-turn/collector epilogue must
; produce the real joined settlement before this receipt can be refunded.
