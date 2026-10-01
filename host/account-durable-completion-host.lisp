; INTERNAL successor to the genuine dense E completion. This entry is called
; only after SF completion, backing publication and current-shell installation
; succeeded in FnOwnerHistoryCompleteCurrent, before its durable return.
; No native export accepts a supplied receipt or semantic result.
(in-package "ACL2")
(include-book "owner-host")
(include-book "account-adoption-turn-host")
(include-book "../books/consumer-account-operation-state")
(include-book "../books/consumer-account-transaction-driver")
(include-book "../books/consumer-account-durable-outcome-state")

; RECEIPT is the local value produced by that actual completion, not an input
; from the socket/native caller. The old ready/capture aliases remain retained
; through publication; the prepublication CURRENT getter is not called after
; installing the successor Store, because its old writer gate has advanced.
(defun fn-owner-account-durable-complete-internal (receipt state)
 (declare (xargs :stobjs state :mode :program :guard t))
 (let* ((holder (fn-owner-account-adoption-operation state))
        (saved (and (boundp-global 'fn-owner-history-account-state state)
                    (f-get-global 'fn-owner-history-account-state state)))
        (capture (and (boundp-global 'fn-owner-history-account-capture state)
                      (f-get-global 'fn-owner-history-account-capture state)))
        (prior (fn-owner-account-durable-outcome state))
        (selection (fn-prl-nth 3 holder)) (event (fn-cp-nth 1 selection))
        (full (fn-prl-nth 3 saved)) (token (fn-prl-nth 1 receipt))
        (turn-token (fn-prl-nth 13 holder))
        (turn (fn-owner-account-turn-current state)))
  (cond
   ; An unrelated E completion never invents an account decision.
   ((null holder) (mv :account-unrelated state))
   ; Never recompute an outcome after a raw escape or replay this callback.
   (prior (mv :recovery-required state))
   ((not
     (and (fn-apr-widthp 14 holder)
          (eq (fn-prl-nth 0 holder) :account-adoption-operation)
          (eq (fn-cp-nth 0 selection) :publish)
          (or (fn-cac-eventp event) (fn-cab-eventp event))
          (fn-apr-widthp 3 receipt)
          (eq (fn-prl-nth 0 receipt) :history-completion)
          (fn-apr-tokenp token)
          (equal (fn-prl-nth 2 receipt) (fn-prl-nth 5 token))
          (equal (fn-prl-nth 7 holder) (fn-prl-nth 3 token))
          (equal (fn-prl-nth 8 holder) (fn-prl-nth 4 token))
          (equal (fn-prl-nth 9 holder) (fn-prl-nth 5 token))
          (equal (fn-cp-nth 1 event) (fn-prl-nth 4 token))
          (equal (fn-cp-nth 2 event) (fn-prl-nth 5 token))
          (fn-apr-widthp 5 saved)
          (eq (fn-prl-nth 0 saved) :history-account-ready)
          (fn-apr-tokenp (fn-prl-nth 1 saved))
          (equal token (fn-prl-nth 1 saved))
          (fn-apr-widthp 5 capture)
          (eq (fn-prl-nth 0 capture) :history-account-capture)
          (fn-apr-tokenp (fn-prl-nth 1 capture))
          (equal token (fn-prl-nth 1 capture))
          (eq (fn-cp-nth 0 full) :ok)
          (fn-act-livep turn-token turn)
          (eq (fn-cp-nth 2 turn) :reserved)
          (eq (fn-cp-nth 4 turn) :operation-select)
          (fn-cado-source-keyp (fn-prl-nth 2 holder))
          (fn-cado-source-keyp (fn-cp-nth 5 turn))
          (equal (fn-prl-nth 2 holder) (fn-cp-nth 5 turn))
          (equal (fn-owner-canonical-epoch state) (fn-prl-nth 5 holder))
          (equal (fn-cfg-generation (fn-owner-config state))
                 (fn-prl-nth 6 holder))
          (eq (fn-sf-phase (fn-sn-files (fn-owner-store state))) :ready)
          (equal (fn-sf-records-count (fn-sn-files (fn-owner-store state)))
                 (+ 1 (fn-prl-nth 7 holder)))))
    (mv :recovery-required state))
   (t
    (let* ((request (fn-prl-nth 12 holder))
           ; Keep every original before the once-called allocating collector.
           (state (f-put-global 'fn-owner-account-durable-outcome
                    (list :account-durable-intent turn-token receipt holder saved request)
                    state))
           (one (fn-catd-published (fn-prl-nth 4 holder) selection full
                                  (fn-prl-nth 7 holder))))
     (if (not (and (eq (fn-cp-nth 0 one) :yield)
                    (eq (fn-cp-nth 1 (fn-cp-nth 1 one)) :ready)))
         (mv :recovery-required state)
      (let* ((next-job (fn-cp-nth 1 one))
             (output (list request next-job one))
             (state (f-put-global 'fn-owner-account-durable-outcome
                      (list :account-durable-outcome turn-token receipt holder saved output request)
                      state))
             (state (fn-owner-account-adoption-job-install next-job state)))
       ; Keep the selected holder/ready/capture until genuine typed promotion
       ; and last-alias cleanup; this call never releases a pool claim.
       (mv :account-durable-produced state))))))))

; Bounded readout for the pooled actual same-turn promoter. This is not a
; native :durable atom, and it does not reconstruct any semantic result.
(defun fn-owner-account-adoption-durable-output (state)
 (declare (xargs :stobjs state :mode :program :guard t))
 (let* ((outcome (fn-owner-account-durable-outcome state))
        (holder (fn-owner-account-adoption-operation state))
        (turn-token (fn-prl-nth 1 outcome))
        (saved-holder (fn-prl-nth 3 outcome))
        (turn (fn-owner-account-turn-current state)))
  (if (and (fn-apr-widthp 7 outcome)
           (eq (fn-prl-nth 0 outcome) :account-durable-outcome)
           (fn-apr-widthp 14 holder) (fn-apr-widthp 14 saved-holder)
           (fn-cado-receipt-coordinatep turn-token)
           (fn-cado-receipt-coordinatep (fn-prl-nth 13 holder))
           (fn-cado-receipt-coordinatep (fn-prl-nth 13 saved-holder))
           (equal turn-token (fn-prl-nth 13 holder))
           (equal turn-token (fn-prl-nth 13 saved-holder))
           (equal (fn-prl-nth 8 holder) (fn-prl-nth 8 saved-holder))
           (equal (fn-prl-nth 9 holder) (fn-prl-nth 9 saved-holder))
           (fn-act-livep turn-token turn)
           (eq (fn-cp-nth 2 turn) :reserved)
           (eq (fn-cp-nth 4 turn) :operation-select))
      (mv :account-durable-produced turn-token (fn-prl-nth 5 outcome))
    (mv :unavailable nil nil))))
