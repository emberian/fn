; PKT497: replay of the accepted durable configuration record.
; Source replay is not evidence about a physical disk or process death.
(in-package "ACL2")
(include-book "peer-invite-retry")

(defthm fn-par-accepted-record-replay-resumes-without-another-record
  (let* ((generation (fn-cfg-generation cfg))
         (value (fn-cfg-value cfg))
         (plan (fn-par-accept-record-plan received observed-ml ed ml snapshots
                                          (fn-cfg-peers value) ident generation))
         (delta (fn-cfg-ag-car (fn-pinv-at 1 plan)))
         (record (fn-cfg-record-make sequence txid (1+ generation)
                                    (list delta) stamp))
         (replayed (fn-config-replay-loop cfg reserved ceiling (list record))))
    (implies (and (equal (list (car plan) (fn-cfg-delta-kind delta))
                         '(:configure :accept-peer))
                  (fn-cfg-record-acceptablep cfg record reserved ceiling))
             (equal (fn-par-accept-record-plan
                     received observed-ml ed ml snapshots
                     (fn-cfg-peers (fn-cfg-value replayed)) ident
                     (fn-cfg-generation replayed))
                    '(:resume))))
  :rule-classes nil
  :hints (("Goal"
           :in-theory (e/d (fn-config-replay-loop fn-cfg-apply-record fn-cfg-apply)
                            (fn-cfg-record-acceptablep fn-cfg-apply-delta
                             fn-par-accept-record-plan))
           :use ((:instance fn-par-current-adoption-fold-resumes-without-another-record
                            (value (fn-cfg-value cfg))
                            (generation (fn-cfg-generation cfg)))))))
