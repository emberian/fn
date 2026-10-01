; Synthetic registration only, testing actual STATE getter/gate, not issuance.
(in-package "ACL2")
(include-book "../../books/history-semantic-writer-state")
(make-event
 (let* ((token '(:admission-grant 2 7 9 9 91 :article))
        (parent '(:history-installed 3 4 5 6 7))
        (state (f-put-global 'fn-owner-canonical-epoch 7 state))
        (state (f-put-global 'fn-owner-canonical-admission-pending
                            (list token nil :reserved nil nil) state))
        (state (f-put-global 'fn-owner-history-semantic-source
                            (list :history-semantic-source token parent nil) state))
        (state (f-put-global 'fn-owner-history-publication parent state))
        (state (f-put-global 'fn-owner-history-completion-fault nil state))
        (current (fn-owner-history-writer-gate token state))
        (blocked (not (fn-owner-history-bootstrap-mutationp state)))
        (state (f-put-global 'fn-owner-history-publication
                            '(:history-installed 8 4 5 6 7) state))
        (changed (fn-owner-history-writer-gate token state))
        (state (f-put-global 'fn-owner-history-completion-fault :published-owner-mismatch state))
        (fenced (fn-owner-history-writer-gate token state)))
  (mv nil (list 'assert-event
                (and (eq current :writer-current) blocked
                     (eq changed :writer-source-changed)
                     (eq fenced :recovery-required))) state)))
