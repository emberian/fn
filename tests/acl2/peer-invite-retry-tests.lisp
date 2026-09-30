(in-package "ACL2")
(include-book "peer-invite-tests")
(include-book "../../books/peer-invite-retry")
(include-book "../../books/peer-adoption-invalidation")
(include-book "../../books/peer-carriage-rows")

(defconst *par-ident* (list (make-list 32 :initial-element 19) 7))
(defmacro par-plan ()
  '(fn-par-accept-record-plan (pit-inv) *pit-a-ml* :verified :verified
                              (pit-a-snapshots) nil *par-ident* 0))
(defmacro par-delta () '(car (fn-pinv-at 1 (par-plan))))
(defmacro par-rows () '(fn-cfg-delta-rows (par-delta)))
(defmacro par-config-value ()
  '(fn-cfg-value-make-full nil 0 nil nil nil (par-rows) nil nil nil nil nil))

; Complete positive witness over the entry the native owner now calls.
(assert-event
 (and (fn-pinv-bound-document-p (pit-inv) *pit-a-ml* :verified :verified
                                 *fn-pinv-invitation-kind* (pit-a-snapshots))
      (fn-par-local-contextp *par-ident* 1)
      (equal (car (par-plan)) :configure)
      (equal (fn-cfg-delta-kind (par-delta)) :accept-peer)
      (fn-cfg-deltap (par-delta))
      (fn-cfg-accept-peer-receiptp (par-rows) 1)
      (fn-par-retry-authorizedp (pit-inv) *pit-a-ml* :verified :verified
                                (pit-a-snapshots) (par-rows) *par-ident* 1)
      (equal (fn-par-accept-record-plan (pit-inv) *pit-a-ml* :verified :verified
                                       (pit-a-snapshots) (par-rows) *par-ident* 1)
             '(:resume))))

; Unrelated configuration generations do not strand a committed retry.
(assert-event
 (equal (fn-par-accept-record-plan (pit-inv) *pit-a-ml* :verified :verified
                                  (pit-a-snapshots) (par-rows) *par-ident* 23)
        '(:resume)))

; Local incarnation mismatch cannot reuse another store's adoption.
(assert-event
 (let ((foreign (list (make-list 32 :initial-element 20) 7)))
   (and (fn-par-local-contextp foreign 1)
        (not (fn-par-retry-authorizedp (pit-inv) *pit-a-ml* :verified :verified
                                       (pit-a-snapshots) (par-rows) foreign 1))
        (equal (fn-par-accept-record-plan (pit-inv) *pit-a-ml* :verified :verified
                                          (pit-a-snapshots) (par-rows) foreign 1)
               '(:refused :stale-invitation-receipt)))))

; A generic edit cannot copy adoption evidence into a recreated peer.
(assert-event
 (let ((next (fn-cfg-apply-delta (par-config-value) 2 nil
                                (fn-cfg-set-peer "a.example" (par-rows)))))
   (and (fn-par-receipt-freep (fn-cfg-peers next))
        (equal (fn-cfg-peers next) (fn-par-without-receipts (par-rows)))
        (not (fn-par-retry-authorizedp (pit-inv) *pit-a-ml* :verified :verified
                                       (pit-a-snapshots) (fn-cfg-peers next) *par-ident* 2)))))

; Unrelated delta preserves the exact receipt and authority tuple.
(assert-event
 (let ((next (fn-cfg-apply-delta (par-config-value) 2 nil (fn-cfg-set-capacity 4096))))
   (and (equal (fn-cfg-peers next) (par-rows))
        (equal (fn-par-accept-record-plan (pit-inv) *pit-a-ml* :verified :verified
                                          (pit-a-snapshots) (fn-cfg-peers next) *par-ident* 2)
               '(:resume)))))

; Hypothesis-removal witness for the resume keystone: no retained hypotheses,
; omitted resume antecedent false and its complete conclusion false.
(assert-event
 (and (not (equal (car (fn-par-accept-record-plan (pit-inv) *pit-a-ml* :verified :verified
                                                 (pit-a-snapshots) nil *par-ident* 0)) :resume))
      (not (and (fn-par-retry-authorizedp (pit-inv) *pit-a-ml* :verified :verified
                                          (pit-a-snapshots) nil *par-ident* 0)
                (fn-pinv-bound-document-p (pit-inv) *pit-a-ml* :verified :verified
                                          *fn-pinv-invitation-kind* (pit-a-snapshots))))))

; All five generic mutation kinds invalidate the affected adoption.  These
; literal witnesses name each delta rather than hiding them in a test loop.
(assert-event
 (let ((delta (fn-cfg-add-peer-rows "a.example" '(("a.example" "pull-interval" "" 1000)))))
   (and (equal (fn-cfg-delta-kind delta) :add-peer-rows)
        (fn-par-receipt-freep
         (fn-cfg-rows-with-key (fn-cfg-peers (fn-cfg-apply-delta (par-config-value) 2 nil delta))
                               (fn-cfg-delta-a delta))))))
(assert-event
 (let ((delta (fn-cfg-remove-peer-rows "a.example" (list (car (fn-par-only-receipts (par-rows)))))))
   (and (equal (fn-cfg-delta-kind delta) :remove-peer-rows)
        (fn-par-receipt-freep
         (fn-cfg-rows-with-key (fn-cfg-peers (fn-cfg-apply-delta (par-config-value) 2 nil delta))
                               (fn-cfg-delta-a delta))))))
(assert-event
 (let ((delta (fn-cfg-remove-peer "a.example")))
   (and (equal (fn-cfg-delta-kind delta) :remove-peer)
        (fn-par-receipt-freep
         (fn-cfg-rows-with-key (fn-cfg-peers (fn-cfg-apply-delta (par-config-value) 2 nil delta))
                               (fn-cfg-delta-a delta))))))
(assert-event
 (let ((delta (fn-cfg-set-peers (par-rows))))
   (and (equal (fn-cfg-delta-kind delta) :set-peers)
        (fn-par-receipt-freep (fn-cfg-peers (fn-cfg-apply-delta (par-config-value) 2 nil delta))))))
; An unrelated peer adoption/edit retains the first peer's committed tuple.
(assert-event
 (let ((next (fn-cfg-apply-delta (par-config-value) 2 nil
                                (fn-cfg-set-peer "other" '(("other" "path-identity" "other" 0))))))
   (and (equal (fn-cfg-rows-with-key (fn-cfg-peers next) "a.example") (par-rows))
        (equal (fn-par-accept-record-plan (pit-inv) *pit-a-ml* :verified :verified
                                          (pit-a-snapshots) (fn-cfg-peers next) *par-ident* 2)
               '(:resume)))))

; Internal adoption is the separating case for the generic-mutation kind
; hypothesis: it preserves a nonempty receipt, rather than stripping it.
(assert-event
 (and (not (member-equal (fn-cfg-delta-kind (par-delta))
                        '(:set-peer :remove-peer :add-peer-rows :remove-peer-rows :set-peers)))
      (not (fn-par-receipt-freep
            (fn-cfg-rows-with-key
             (fn-cfg-peers (fn-cfg-apply-delta
                            (fn-cfg-value-make-full nil 0 nil nil nil nil nil nil nil nil nil)
                            1 nil (par-delta)))
             (fn-cfg-delta-a (par-delta)))))))

; Missing and malformed internal receipt tuples are refused at admission.
(assert-event
 (let ((missing (fn-cfg-delta-make :accept-peer "a.example" "" 1
                                  (fn-par-without-receipts (par-rows)))))
   (and (fn-cfg-deltap missing)
        (equal (fn-cfg-delta-reason
                (fn-cfg-value-make-full nil 0 nil nil nil nil nil nil nil nil nil)
                1 nil 0 512 missing)
               :adoption-receipt-malformed))))

; Actual producer, actual configuration fold, then resumed actual entry.
(assert-event
 (let* ((value (fn-cfg-value-make-full nil 0 nil nil nil nil nil nil nil nil nil))
        (plan (fn-par-accept-record-plan (pit-inv) *pit-a-ml* :verified :verified
                                       (pit-a-snapshots) (fn-cfg-peers value) *par-ident* 0))
        (delta (fn-cfg-ag-car (fn-pinv-at 1 plan)))
        (next (fn-cfg-apply-delta value 1 nil delta)))
   (and (equal (car plan) :configure)
        (equal (fn-cfg-delta-kind delta) :accept-peer)
        (equal (fn-par-accept-record-plan (pit-inv) *pit-a-ml* :verified :verified
                                         (pit-a-snapshots) (fn-cfg-peers next) *par-ident* 1)
               '(:resume)))))

; A different, independently verified signed invitation cannot reuse receipt.
(assert-event
 (let ((other (pit-sign (pit-invitation-source *pit-nonce2* (pit-a) *pit-a-token* *pit-a-keys*)
                        (pit-a) *pit-a-keys*)))
   (and (fn-pinv-bound-document-p other *pit-a-ml* :verified :verified
                                  *fn-pinv-invitation-kind* (pit-a-snapshots))
        (not (fn-par-retry-authorizedp other *pit-a-ml* :verified :verified
                                      (pit-a-snapshots) (par-rows) *par-ident* 1))
        (equal (fn-par-accept-record-plan other *pit-a-ml* :verified :verified
                                         (pit-a-snapshots) (par-rows) *par-ident* 1)
               '(:refused :stale-invitation-receipt)))))

; Primitive signature refusal and absent current authority both forbid retry.
(assert-event
 (and (equal (fn-par-accept-record-plan (pit-inv) *pit-a-ml* :verified :refused
                                       (pit-a-snapshots) (par-rows) *par-ident* 1)
              '(:refused :stale-invitation-receipt))
      (equal (fn-par-accept-record-plan (pit-inv) *pit-a-ml* :verified :verified
                                       nil (par-rows) *par-ident* 1)
              '(:refused :stale-invitation-receipt))))

; Positive anchor: an ordinary nonempty peer contains no adoption evidence.
(assert-event
 (fn-par-receipt-freep '(("ordinary" "path-identity" "ordinary" 0))))

; Substantive unconditional filtered-group successor: reachable receipt state.
(assert-event
 (let* ((rows '(("a.example" "carried-budget-charge" "" 100)))
        (next (fn-cfg-apply-delta (par-config-value) 2 nil
                                  (fn-cfg-add-peer-rows "a.example" rows))))
   (and (true-listp rows) (fn-cfg-rows-keyed-p rows "a.example")
        (equal (fn-cfg-rows-with-key (fn-cfg-peers next) "a.example")
               (fn-par-without-receipts
                (append (fn-cfg-rows-without-members
                         (fn-cfg-rows-with-key (par-rows) "a.example") rows) rows)))
        (fn-par-receipt-freep (fn-cfg-rows-with-key (fn-cfg-peers next) "a.example")))))

; Removing the internal-adoption trigger fails the complete conclusion.
(assert-event
 (let* ((plan (fn-par-accept-record-plan nil nil nil nil nil nil *par-ident* 0))
        (delta (fn-cfg-ag-car (fn-pinv-at 1 plan))))
   (and (not (equal (list (car plan) (fn-cfg-delta-kind delta))
                    '(:configure :accept-peer)))
        (not (and (fn-pinv-bound-document-p nil nil nil nil *fn-pinv-invitation-kind* nil)
                  (fn-pinv-enrolled-withp (fn-pinv-received-principal nil)
                                          (fn-pinv-received-keys nil) nil)
                  (fn-par-local-contextp *par-ident* 0)
                  (equal (fn-cfg-delta-n delta) 1))))))

; Fold trigger removal: the refused plan cannot produce a resumed adoption.
(assert-event
 (let* ((value (fn-cfg-value-make-full nil 0 nil nil nil nil nil nil nil nil nil))
        (plan (fn-par-accept-record-plan nil nil nil nil nil nil *par-ident* 0))
        (delta (fn-cfg-ag-car (fn-pinv-at 1 plan)))
        (next (fn-cfg-apply-delta value 1 nil delta)))
   (and (not (equal (list (car plan) (fn-cfg-delta-kind delta))
                    '(:configure :accept-peer)))
        (not (equal (fn-par-accept-record-plan nil nil nil nil nil
                                              (fn-cfg-peers next) *par-ident* 1)
                    '(:resume))))))

; A recreated store with the same node spelling and another history salt refuses.
(assert-event
 (let ((other (list (car *par-ident*) 8)))
   (and (fn-par-local-contextp other 1)
        (equal (fn-par-accept-record-plan (pit-inv) *pit-a-ml* :verified :verified
                                          (pit-a-snapshots) (par-rows) other 1)
               '(:refused :stale-invitation-receipt)))))
; A changed peer-specific key generation cannot revive an older receipt.
(assert-event
 (let ((snapshots (list (fn-hl-enroll-event 4 5 6 2 (pit-a) *pit-a-keys* (pit-a-snapshots)))))
   (and (fn-pinv-enrolled-withp (pit-a) *pit-a-keys* snapshots)
        (equal (fn-par-accept-record-plan (pit-inv) *pit-a-ml* :verified :verified
                                          snapshots (par-rows) *par-ident* 2)
               '(:refused :stale-invitation-receipt)))))
; Either primitive refusal independently prevents resumption.
(assert-event
 (equal (fn-par-accept-record-plan (pit-inv) *pit-a-ml* :refused :verified
                                   (pit-a-snapshots) (par-rows) *par-ident* 1)
        '(:refused :stale-invitation-receipt)))

; Keyed-row hypothesis removal: a foreign row is not that peer's group.
(assert-event
 (let* ((rows '(("foreign" "carried-budget-charge" "" 100)))
        (next (fn-cfg-apply-delta (par-config-value) 2 nil
                                  (fn-cfg-add-peer-rows "a.example" rows))))
   (and (not (fn-cfg-rows-keyed-p rows "a.example"))
        (not (equal (fn-cfg-rows-with-key (fn-cfg-peers next) "a.example")
                    (fn-par-without-receipts
                     (append (fn-cfg-rows-without-members
                              (fn-cfg-rows-with-key (par-rows) "a.example") rows)
                             rows)))))))
