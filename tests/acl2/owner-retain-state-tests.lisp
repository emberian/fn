; PRF-1067: exact live ACL2 state effects, with a nonempty carried value.
; The value is deliberately opaque here: these theorems describe state
; effects, not validity of the ledger/index contents.
(in-package "ACL2")
(include-book "../../books/owner-retain-state")

(defun fn-orst-live-effects-witness (state)
  (declare (xargs :stobjs state :mode :program))
  (let* ((original (fn-owner-retain-carry state))
         (carry '("nonempty-ledger" . "nonempty-index"))
         (state (fn-owner-retain-carry-put carry state))
         ; Complete unconditional conclusion of the writer theorem.
         (put-conclusion (equal (fn-owner-retain-carry state) carry))
         (key 'fn-orst-witness-other)
         (old-other (if (boundp-global 'fn-orst-witness-other state)
                        (f-get-global 'fn-orst-witness-other state) nil))
         (before (fn-owner-retain-carry state))
         (state (f-put-global 'fn-orst-witness-other :unrelated-value state))
         ; Entire antecedent and conclusion of the frame theorem.
         (other-hypothesis (not (equal key 'fn-owner-retain-carry)))
         (other-conclusion (equal (fn-owner-retain-carry state) before))
         ; Hypothesis removal witness: same key, changed value, false conclusion.
         (key 'fn-owner-retain-carry)
         (state (f-put-global 'fn-owner-retain-carry
                              '("changed-ledger" . "changed-index") state))
         (removed-hypothesis (equal key 'fn-owner-retain-carry))
         (failed-conclusion (not (equal (fn-owner-retain-carry state) before)))
         (state (f-put-global 'fn-orst-witness-other old-other state))
         (state (fn-owner-retain-carry-put original state)))
    (mv (and (consp carry) put-conclusion other-hypothesis other-conclusion
             removed-hypothesis failed-conclusion)
        state)))

(make-event
 (mv-let (ok state) (fn-orst-live-effects-witness state)
   (value (list 'assert-event ok))))
