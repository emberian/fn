(defun fn-owner-finish-submission-synced (fn-arena fn-cat fn-hist state)
  (declare (xargs :stobjs (fn-arena fn-cat fn-hist state) :mode :program))
  (let ((oc (fn-owner-ocfg state)))
    (if (fn-ocfg-staged oc)
        (mv nil :fault fn-cat state)
      ; The completion the store is consuming, read before the finish: its
      ; (sequence . txid) pair (fn-sf-completion).  The pending row's token is
      ; (txid . expected) of the record it prepared, so a completion of any
      ; other record is a stale token.
      (let* ((completion (fn-sf-completion
                          (fn-sn-files (fn-own-store (fn-ocfg-owner oc)))))
             ; fn-apc-own-finish-is-own-finish (books/owner-parse-carried.lisp):
             ; fn-ccar-own-finish with the stored octets' Cancel-Lock fields
             ; read from the take's parse and the completion's refresh over the
             ; Store's event index (post-alloc-2).
             ; The configuration is the take's (fn-owner-take-config, PKT-789):
             ; the octets staged are fn-own-sub-stored-octets under it.
             (result (fn-apc-own-finish (fn-ocfg-owner oc) (fn-owner-take-config state)
                                        fn-arena fn-hist (fn-owner-parse-carry state)))
             (state (fn-owner-replace-core (cdr result) state))
             (pending (f-get-global 'fn-owner-cat-pending state)))
        (if (not (and (equal (car result) :durable) pending (consp completion)))
            (mv nil (car result) fn-cat state)
          ; T4 then T2: the article's withdrawal targets the refreshed view no
          ; longer shows, withdrawn at the count with this row as the cause,
          ; THEN the row completed by the completing record's token -- hidden
          ; when the view no longer shows its Message-ID (R1).
          (let ((state (fn-orc-writer-enter state))
                (view (fn-own-view (cdr result))))
            (mv-let (word pending2 fn-cat)
              (fn-sca-finish (cons (nfix (cdr completion)) (fn-pc-expected pending))
                             pending (fn-own-view-index view)
                             (fn-sca-targets-of (fn-record-msgid (fn-pc-held pending))
                                                (fn-own-view-withdrawals view))
                             fn-cat)
              (let* ((state (if (or (equal (car word) :stale-token)
                                      (equal (car word) :expected-mismatch))
                               (fn-orc-writer-fault state)
                             (fn-orc-writer-leave state)))
                     (state (f-put-global 'fn-owner-cat-pending pending2 state)))
                (if (or (equal (car word) :stale-token) (equal (car word) :expected-mismatch))
                    ; the catalog refused the completion the store made durable:
                    ; a recovery event, never a silent divergence (the catalog
                    ; is rebuilt from the store's rows at the next open).
                    (mv nil :fault fn-cat state)
                  (mv nil (car result) fn-cat state))))))))))

(defun fn-owner-finish-identity (fn-arena fn-cat fn-hist state)
  (declare (xargs :stobjs (fn-arena fn-cat fn-hist state) :mode :program)
           (ignorable fn-arena))
  (let ((completion (fn-sf-completion (fn-sn-files (fn-owner-store state)))))
    (mv-let (erp word fn-hist state)
      (fn-owner-finish fn-hist state)
      (declare (ignore erp))
      (let ((pending (f-get-global 'fn-owner-cat-pending state)))
        (if (not (and (equal word :durable) pending (consp completion)))
            (mv nil word fn-cat fn-hist state)
          (let ((state (fn-orc-writer-enter state))
                (view (fn-own-view (fn-owner-core state))))
            (mv-let (cword pending2 fn-cat)
              (fn-sca-finish (cons (nfix (cdr completion)) (fn-pc-expected pending))
                             pending (fn-own-view-index view)
                             (fn-sca-targets-of (fn-record-msgid (fn-pc-held pending))
                                                (fn-own-view-withdrawals view))
                             fn-cat)
              (let* ((state (if (or (equal (car cword) :stale-token)
                                      (equal (car cword) :expected-mismatch))
                               (fn-orc-writer-fault state)
                             (fn-orc-writer-leave state)))
                     (state (f-put-global 'fn-owner-cat-pending pending2 state)))
                (if (or (equal (car cword) :stale-token) (equal (car cword) :expected-mismatch))
                    (mv nil :fault fn-cat fn-hist state)
                  (mv nil word fn-cat fn-hist state))))))))))
