; Literal positives and hypothesis removals for all three actual boundaries.
; Retired cases are generic typed-protocol witnesses, not fresh-service
; response-serial reachability or physical heap/receipt authenticity claims.
(in-package "ACL2")

(include-book "../../books/resource-output-chain")

(defthm rct-issue-positive
 (let* ((ledger (mv-nth 1 (fn-rl-install '(16777216 0 0 0 0 0 0 0 0)
                                      '(8192 0 0 0 0 0 0 0 0)
                                      '(1048576 0 0 0 0 0 0 0 0) 4
                                      (create-fn-resource-ledger))))
        (ledger (fn-rlo-free-init 2 ledger))
        (ledger (update-fn-rl-next 2 ledger))
        (ledger (update-fn-rl-file-limit 1048576 ledger))
        (ledger (update-fn-rl-mode 2 ledger))
        (result (fn-rlo-issue 7 11 8 :issued ledger)))
  (and (fn-rlo-free-chainp '(2 3) ledger)
       (eq (car result) :drawn)
       (fn-rlo-free-chainp '(3) (mv-nth 2 result))))
 :rule-classes nil)

(defthm rct-issue-without-chain
 (let* ((ledger (mv-nth 1 (fn-rl-install '(16777216 0 0 0 0 0 0 0 0)
                                      '(8192 0 0 0 0 0 0 0 0)
                                      '(1048576 0 0 0 0 0 0 0 0) 4
                                      (create-fn-resource-ledger))))
        (ledger (fn-rlo-free-init 2 ledger))
        (ledger (update-fn-rl-next 2 ledger))
        (ledger (update-fn-rl-file-limit 1048576 ledger))
        (ledger (update-fn-rl-mode 2 ledger))
        (ledger (update-fn-rl-idsi 3 2 ledger))
        (result (fn-rlo-issue 7 11 8 :issued ledger)))
  (and (not (fn-rlo-free-chainp '(2 3) ledger))
       (eq (car result) :drawn)
       (not (fn-rlo-free-chainp '(3) (mv-nth 2 result)))))
 :rule-classes nil)

(defthm rct-issue-without-drawn
 (let* ((ledger (mv-nth 1 (fn-rl-install '(16777216 0 0 0 0 0 0 0 0)
                                      '(8192 0 0 0 0 0 0 0 0)
                                      '(1048576 0 0 0 0 0 0 0 0) 4
                                      (create-fn-resource-ledger))))
        (ledger (fn-rlo-free-init 2 ledger))
        (ledger (update-fn-rl-next 2 ledger))
        (ledger (update-fn-rl-file-limit 1048576 ledger))
        (ledger (update-fn-rl-mode 2 ledger))
        (result (fn-rlo-issue -1 11 8 :issued ledger)))
  (and (fn-rlo-free-chainp '(2 3) ledger)
       (not (eq (car result) :drawn))
       (not (fn-rlo-free-chainp '(3) (mv-nth 2 result)))))
 :rule-classes nil)

(defthm rct-output-positive
 (let* ((ledger (mv-nth 1 (fn-rl-install '(16777216 0 0 0 0 0 0 0 0)
                                      '(8192 0 0 0 0 0 0 0 0)
                                      '(1048576 0 0 0 0 0 0 0 0) 4
                                      (create-fn-resource-ledger))))
        (ledger (fn-rlo-free-init 2 ledger))
        (ledger (update-fn-rl-next 2 ledger))
        (ledger (update-fn-rl-file-limit 1048576 ledger))
        (ledger (update-fn-rl-mode 2 ledger))
        (issue (fn-rlo-issue 7 11 8 :issued ledger))
        (token (cadr issue))
        (ledger (mv-nth 2 issue))
        (ledger (mv-nth 1 (fn-rlo-physical token 8 :terminal ledger)))
        (result (fn-rlo-output token 8 :discarded ledger)))
  (and (fn-rlo-free-chainp '(3) ledger)
       (eq (car result) :settled)
       (fn-rlo-free-chainp
        (if (< (fn-rl-gensi (caddr token) ledger) *fn-rl-word-max*)
            (cons (caddr token) '(3)) '(3)) (mv-nth 1 result))))
 :rule-classes nil)

(defthm rct-output-without-chain
 (let* ((ledger (mv-nth 1 (fn-rl-install '(16777216 0 0 0 0 0 0 0 0)
                                      '(8192 0 0 0 0 0 0 0 0)
                                      '(1048576 0 0 0 0 0 0 0 0) 4
                                      (create-fn-resource-ledger))))
        (ledger (fn-rlo-free-init 2 ledger))
        (ledger (update-fn-rl-next 2 ledger))
        (ledger (update-fn-rl-file-limit 1048576 ledger))
        (ledger (update-fn-rl-mode 2 ledger))
        (issue (fn-rlo-issue 7 11 8 :issued ledger))
        (token (cadr issue))
        (ledger (mv-nth 2 issue))
        (ledger (mv-nth 1 (fn-rlo-physical token 8 :terminal ledger)))
        (ledger (update-fn-rl-idsi 3 2 ledger))
        (result (fn-rlo-output token 8 :discarded ledger)))
  (and (not (fn-rlo-free-chainp '(3) ledger))
       (eq (car result) :settled)
       (not (fn-rlo-free-chainp
        (if (< (fn-rl-gensi (caddr token) ledger) *fn-rl-word-max*)
            (cons (caddr token) '(3)) '(3)) (mv-nth 1 result)))))
 :rule-classes nil)

(defthm rct-output-without-settled
 (let* ((ledger (mv-nth 1 (fn-rl-install '(16777216 0 0 0 0 0 0 0 0)
                                      '(8192 0 0 0 0 0 0 0 0)
                                      '(1048576 0 0 0 0 0 0 0 0) 4
                                      (create-fn-resource-ledger))))
        (ledger (fn-rlo-free-init 2 ledger))
        (ledger (update-fn-rl-next 2 ledger))
        (ledger (update-fn-rl-file-limit 1048576 ledger))
        (ledger (update-fn-rl-mode 2 ledger))
        (issue (fn-rlo-issue 7 11 8 :issued ledger))
        (token (cadr issue))
        (ledger (mv-nth 2 issue))
        (result (fn-rlo-output token 8 :discarded ledger)))
  (and (fn-rlo-free-chainp '(3) ledger)
       (not (eq (car result) :settled))
       (not (fn-rlo-free-chainp
        (if (< (fn-rl-gensi (caddr token) ledger) *fn-rl-word-max*)
            (cons (caddr token) '(3)) '(3)) (mv-nth 1 result)))))
 :rule-classes nil)

(defthm rct-output-retired-positive
 (let* ((ledger (mv-nth 1 (fn-rl-install '(16777216 0 0 0 0 0 0 0 0)
                                      '(8192 0 0 0 0 0 0 0 0)
                                      '(1048576 0 0 0 0 0 0 0 0) 4
                                      (create-fn-resource-ledger))))
        (ledger (fn-rlo-free-init 2 ledger))
        (ledger (update-fn-rl-next 2 ledger))
        (ledger (update-fn-rl-file-limit 1048576 ledger))
        (ledger (update-fn-rl-mode 2 ledger))
        (ledger (update-fn-rl-gensi 2 (1- *fn-rl-word-max*) ledger))
        (issue (fn-rlo-issue 7 11 8 :issued ledger))
        (token (cadr issue))
        (ledger (mv-nth 2 issue))
        (ledger (mv-nth 1 (fn-rlo-physical token 8 :terminal ledger)))
        (result (fn-rlo-output token 8 :discarded ledger)))
  (and (fn-rlo-free-chainp '(3) ledger)
       (eq (car result) :settled)
       (fn-rlo-free-chainp
        (if (< (fn-rl-gensi (caddr token) ledger) *fn-rl-word-max*)
            (cons (caddr token) '(3)) '(3)) (mv-nth 1 result))))
 :rule-classes nil)

(defthm rct-physical-positive
 (let* ((ledger (mv-nth 1 (fn-rl-install '(16777216 0 0 0 0 0 0 0 0)
                                      '(8192 0 0 0 0 0 0 0 0)
                                      '(1048576 0 0 0 0 0 0 0 0) 4
                                      (create-fn-resource-ledger))))
        (ledger (fn-rlo-free-init 2 ledger))
        (ledger (update-fn-rl-next 2 ledger))
        (ledger (update-fn-rl-file-limit 1048576 ledger))
        (ledger (update-fn-rl-mode 2 ledger))
        (issue (fn-rlo-issue 7 11 8 :issued ledger))
        (token (cadr issue))
        (ledger (mv-nth 2 issue))
        (ledger (mv-nth 1 (fn-rlo-output token 8 :discarded ledger)))
        (result (fn-rlo-physical token 8 :terminal ledger)))
  (and (fn-rlo-free-chainp '(3) ledger)
       (eq (car result) :settled)
       (fn-rlo-free-chainp
        (if (< (fn-rl-gensi (caddr token) ledger) *fn-rl-word-max*)
            (cons (caddr token) '(3)) '(3)) (mv-nth 1 result))))
 :rule-classes nil)

(defthm rct-physical-without-chain
 (let* ((ledger (mv-nth 1 (fn-rl-install '(16777216 0 0 0 0 0 0 0 0)
                                      '(8192 0 0 0 0 0 0 0 0)
                                      '(1048576 0 0 0 0 0 0 0 0) 4
                                      (create-fn-resource-ledger))))
        (ledger (fn-rlo-free-init 2 ledger))
        (ledger (update-fn-rl-next 2 ledger))
        (ledger (update-fn-rl-file-limit 1048576 ledger))
        (ledger (update-fn-rl-mode 2 ledger))
        (issue (fn-rlo-issue 7 11 8 :issued ledger))
        (token (cadr issue))
        (ledger (mv-nth 2 issue))
        (ledger (mv-nth 1 (fn-rlo-output token 8 :discarded ledger)))
        (ledger (update-fn-rl-idsi 3 2 ledger))
        (result (fn-rlo-physical token 8 :terminal ledger)))
  (and (not (fn-rlo-free-chainp '(3) ledger))
       (eq (car result) :settled)
       (not (fn-rlo-free-chainp
        (if (< (fn-rl-gensi (caddr token) ledger) *fn-rl-word-max*)
            (cons (caddr token) '(3)) '(3)) (mv-nth 1 result)))))
 :rule-classes nil)

(defthm rct-physical-without-settled
 (let* ((ledger (mv-nth 1 (fn-rl-install '(16777216 0 0 0 0 0 0 0 0)
                                      '(8192 0 0 0 0 0 0 0 0)
                                      '(1048576 0 0 0 0 0 0 0 0) 4
                                      (create-fn-resource-ledger))))
        (ledger (fn-rlo-free-init 2 ledger))
        (ledger (update-fn-rl-next 2 ledger))
        (ledger (update-fn-rl-file-limit 1048576 ledger))
        (ledger (update-fn-rl-mode 2 ledger))
        (issue (fn-rlo-issue 7 11 8 :issued ledger))
        (token (cadr issue))
        (ledger (mv-nth 2 issue))
        (result (fn-rlo-physical token 8 :terminal ledger)))
  (and (fn-rlo-free-chainp '(3) ledger)
       (not (eq (car result) :settled))
       (not (fn-rlo-free-chainp
        (if (< (fn-rl-gensi (caddr token) ledger) *fn-rl-word-max*)
            (cons (caddr token) '(3)) '(3)) (mv-nth 1 result)))))
 :rule-classes nil)

(defthm rct-physical-retired-positive
 (let* ((ledger (mv-nth 1 (fn-rl-install '(16777216 0 0 0 0 0 0 0 0)
                                      '(8192 0 0 0 0 0 0 0 0)
                                      '(1048576 0 0 0 0 0 0 0 0) 4
                                      (create-fn-resource-ledger))))
        (ledger (fn-rlo-free-init 2 ledger))
        (ledger (update-fn-rl-next 2 ledger))
        (ledger (update-fn-rl-file-limit 1048576 ledger))
        (ledger (update-fn-rl-mode 2 ledger))
        (ledger (update-fn-rl-gensi 2 (1- *fn-rl-word-max*) ledger))
        (issue (fn-rlo-issue 7 11 8 :issued ledger))
        (token (cadr issue))
        (ledger (mv-nth 2 issue))
        (ledger (mv-nth 1 (fn-rlo-output token 8 :discarded ledger)))
        (result (fn-rlo-physical token 8 :terminal ledger)))
  (and (fn-rlo-free-chainp '(3) ledger)
       (eq (car result) :settled)
       (fn-rlo-free-chainp
        (if (< (fn-rl-gensi (caddr token) ledger) *fn-rl-word-max*)
            (cons (caddr token) '(3)) '(3)) (mv-nth 1 result))))
 :rule-classes nil)
