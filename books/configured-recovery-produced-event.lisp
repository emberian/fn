; MV7 retains the produced packet across a yielded/unavailable callback.
; Resume that callback only; never call this intern/append entry again for it.
; Actual per-event assembly: one intern/identity decision, one prefix append,
; one configured/account callback. Unadmitted source; no ready activation.
(in-package "ACL2")
(include-book "statement-recover-produced-row")
(include-book "configured-recovery-prefix")
(include-book "consumer-configured-authority-replay")

(defun fn-crp-produced-event (paired acc fields wire raw position mode dicts
                              snapshot-carry prefix-files base-row-carry cep-cursor
                              fn-arena fn-hist)
 (declare (xargs :stobjs (fn-arena fn-hist) :verify-guards nil
                 :guard (and (fn-ssr-statep acc) (fn-lzr-dictsp dicts)
                             (fn-cnode-statep (fn-cp-nth 1 paired)))))
 (mv-let (next-acc next-fields metadata effect child sizes row fn-arena)
  (fn-ssrp-intern-row acc fields wire raw position mode dicts snapshot-carry fn-arena)
  (if (eq next-acc :bad)
   (mv (list :unavailable paired :identity) next-acc next-fields
       prefix-files nil fn-arena fn-hist)
   (let ((produced
          (list (fn-ssr-at 3 next-acc) next-fields metadata effect child sizes)))
   (mv-let (word next-prefix fn-hist)
    (fn-crp-append prefix-files row fn-hist)
    (if (not (eq word :appended))
     (mv (list :unavailable paired :prefix-index) next-acc next-fields
         next-prefix produced fn-arena fn-hist)
     ; The fixed packet is retained from the SAME lexical decision above.
     ; Its allocation is an explicit open caller-envelope obligation.
     (let ((result
            (fn-capr-event-step paired produced
             next-prefix fn-hist base-row-carry cep-cursor)))
      ; Refusal retains the actual advanced prefix/arena; there is no rollback,
      ; retry, or independent identity/account replay here.
      (mv result next-acc next-fields next-prefix produced fn-arena fn-hist))))))))
