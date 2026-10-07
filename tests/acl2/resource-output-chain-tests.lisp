; Literal positives and hypothesis removals for all three actual boundaries.
; Retired cases are generic typed-protocol witnesses, not fresh-service
; response-serial reachability or physical heap/receipt authenticity claims.
(in-package "ACL2")

(include-book "../../books/resource-output-chain")
(include-book "../../books/defkeystone")

; The book closes over its proof-only chain predicate (in-theory disable at its
; end, 0ff71d35a); these ground witnesses open it to evaluate the chain.
(local (in-theory (enable fn-rlo-free-chainp)))

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

(defthm rct-install-positive
 (let* ((result (fn-rlo-install 268435456 67108864 nil '(16777216 1048576) 4 (create-fn-resource-ledger)))
        (after (mv-nth 1 result)))
  (and (eq (car result) :installed)
       (fn-rlo-free-chainp (fn-rlo-free-range 2 4) after))) :rule-classes nil)
(defthm rct-install-without-installed
 (let* ((result (fn-rlo-install 268435456 67108864 nil nil 4 (create-fn-resource-ledger)))
        (after (mv-nth 1 result)))
  (and (not (eq (car result) :installed))
       (not (fn-rlo-free-chainp (fn-rlo-free-range 2 4) after)))) :rule-classes nil)
; Separately labeled corrupted-state regression: typed/WFP zero count with
; padded active rows previously survived resize and could enter the free chain.
(defthm rct-install-padded-zero-count-refused
 (let* ((ledger (fn-rl-resize-all 4 (create-fn-resource-ledger)))
        (ledger (update-fn-rl-count 0 ledger))
        (ledger (update-fn-rl-phasesi 2 1 ledger))
        (result (fn-rlo-install 268435456 67108864 nil '(16777216 1048576) 4 ledger)))
  (and (fn-resource-ledgerp ledger) (fn-rl-wfp ledger)
       (not (fn-rl-freshp ledger))
       (eq (car result) :invalid-output-install-state)
       (equal (mv-nth 1 result) ledger))) :rule-classes nil)
(defthm rct-install-repeat-preserves-refusal
 (let* ((result (fn-rlo-install 268435456 67108864 nil '(16777216 1048576) 4 (create-fn-resource-ledger)))
        (ledger (mv-nth 1 result))
        (repeat (fn-rlo-install 268435456 67108864 nil '(16777216 1048576) 4 ledger)))
  (and (eq (car result) :installed)
       (eq (car repeat) :already-installed)
       (equal (mv-nth 1 repeat) ledger))) :rule-classes nil)

; ---------------------------------------------------------------------------
; The fn-rlo-* keystones with their teeth (TEETH CONTRACT v1).  The ledger is
; a stobj, so the executable witnesses cannot bind it, and the operations
; return several values, so (mv-nth K (F ..)) does not evaluate in an
; assert-event: every witness is a ground theorem (:witness-lemma, :lemma)
; whose formula is the conjunction the entry would assert, at the entry's
; bindings, proved by evaluation over the ledger's logical value (the
; defun-nx fixtures below: the setup of rct-issue-positive, then one issue,
; one output or physical receipt, and the pair).  They are lemma debt
; (TEETH-OWED-MV-CLAIM, TEETH-OWED-STOBJ-WITNESS), not executed witnesses.
(defun-nx rcx-l0 () (create-fn-resource-ledger))
(defun-nx rcx-l1 ()
  (let* ((ledger (mv-nth 1 (fn-rl-install '(16777216 0 0 0 0 0 0 0 0)
                                          '(8192 0 0 0 0 0 0 0 0)
                                          '(1048576 0 0 0 0 0 0 0 0) 4
                                          (create-fn-resource-ledger))))
         (ledger (fn-rlo-free-init 2 ledger))
         (ledger (update-fn-rl-next 2 ledger))
         (ledger (update-fn-rl-file-limit 1048576 ledger))
         (ledger (update-fn-rl-mode 2 ledger)))
    ledger))
(defun-nx rcx-l2 () (mv-nth 2 (fn-rlo-issue 7 11 8 :issued (rcx-l1))))
(defun-nx rcx-tok () (cadr (fn-rlo-issue 7 11 8 :issued (rcx-l1))))
(defun-nx rcx-l3 () (mv-nth 1 (fn-rlo-physical (rcx-tok) 8 :terminal (rcx-l2))))
(defun-nx rcx-l4 () (mv-nth 1 (fn-rlo-output (rcx-tok) 8 :discarded (rcx-l2))))
(defun-nx rcx-l5 () (update-fn-rl-elensi 2 1 (rcx-l3)))
(defun-nx rcx-l5 () (update-fn-rl-elensi 2 1 (rcx-l3)))

(defthm rcx-fn-rlo-install-keeps-representation-witness
  (and (fn-resource-ledgerp (rcx-l1)) (fn-rl-wfp (rcx-l1)) (let ((after (mv-nth 1 (fn-rlo-install 1073741824 536870912 nil '(16777216 1048576) 4 (rcx-l1))))) (and (fn-resource-ledgerp after) (fn-rl-wfp after)))))
(defthm rcx-fn-rlo-install-keeps-representation-without-rep
  (and (fn-rl-wfp nil) (not (fn-resource-ledgerp nil)) (not (let ((after (mv-nth 1 (fn-rlo-install 1073741824 536870912 nil '(16777216 1048576) 4 nil)))) (and (fn-resource-ledgerp after) (fn-rl-wfp after))))))
(defthm rcx-fn-rlo-install-keeps-representation-without-wf
  (and (fn-resource-ledgerp (update-fn-rl-count 99 (rcx-l1))) (not (fn-rl-wfp (update-fn-rl-count 99 (rcx-l1)))) (not (let ((after (mv-nth 1 (fn-rlo-install 1073741824 536870912 nil '(16777216 1048576) 4 (update-fn-rl-count 99 (rcx-l1)))))) (and (fn-resource-ledgerp after) (fn-rl-wfp after))))))
(defthm rcx-fn-rlo-install-keeps-representation-mutant-not-wellformed
  (and (fn-resource-ledgerp (rcx-l1)) (fn-rl-wfp (rcx-l1)) (let ((after (mv-nth 1 (fn-rlo-install 1073741824 536870912 nil '(16777216 1048576) 4 (rcx-l1))))) (and (fn-resource-ledgerp after) (fn-rl-wfp after))) (not (let ((after (mv-nth 1 (fn-rlo-install 1073741824 536870912 nil '(16777216 1048576) 4 (rcx-l1))))) (not (fn-rl-wfp after))))))
(defteeth fn-rlo-install-keeps-representation
  :claim (((rep (fn-resource-ledgerp ledger)) (wf (fn-rl-wfp ledger))) (let ((after (mv-nth 1 (fn-rlo-install dynamic store-need cold policy slots ledger)))) (and (fn-resource-ledgerp after) (fn-rl-wfp after))))
  :subject fn-rlo-install
  :witness-lemma rcx-fn-rlo-install-keeps-representation-witness
  :witness ((dynamic 1073741824) (store-need 536870912) (cold nil) (policy '(16777216 1048576)) (slots 4) (ledger (rcx-l1)))
  :breaks ((rep ((ledger nil)) :lemma rcx-fn-rlo-install-keeps-representation-without-rep)
          (wf ((ledger (update-fn-rl-count 99 (rcx-l1)))) :lemma rcx-fn-rlo-install-keeps-representation-without-wf))
  :mutations ((not-wellformed (:conclusion (let ((after (mv-nth 1 (fn-rlo-install dynamic store-need cold policy slots ledger)))) (not (fn-rl-wfp after)))) ((dynamic 1073741824) (store-need 536870912) (cold nil) (policy '(16777216 1048576)) (slots 4) (ledger (rcx-l1))) :fault "an operation that leaves the ledger ill-formed" :lemma rcx-fn-rlo-install-keeps-representation-mutant-not-wellformed)))


(defthm rcx-fn-rlo-issue-keeps-representation-witness
  (and (fn-resource-ledgerp (rcx-l1)) (fn-rl-wfp (rcx-l1)) (let ((after (mv-nth 2 (fn-rlo-issue 7 11 8 :issued (rcx-l1))))) (and (fn-resource-ledgerp after) (fn-rl-wfp after)))))
(defthm rcx-fn-rlo-issue-keeps-representation-without-rep
  (and (fn-rl-wfp nil) (not (fn-resource-ledgerp nil)) (not (let ((after (mv-nth 2 (fn-rlo-issue 7 11 8 :issued nil)))) (and (fn-resource-ledgerp after) (fn-rl-wfp after))))))
(defthm rcx-fn-rlo-issue-keeps-representation-without-wf
  (and (fn-resource-ledgerp (update-fn-rl-count 99 (rcx-l1))) (not (fn-rl-wfp (update-fn-rl-count 99 (rcx-l1)))) (not (let ((after (mv-nth 2 (fn-rlo-issue 7 11 8 :issued (update-fn-rl-count 99 (rcx-l1)))))) (and (fn-resource-ledgerp after) (fn-rl-wfp after))))))
(defthm rcx-fn-rlo-issue-keeps-representation-mutant-not-wellformed
  (and (fn-resource-ledgerp (rcx-l1)) (fn-rl-wfp (rcx-l1)) (let ((after (mv-nth 2 (fn-rlo-issue 7 11 8 :issued (rcx-l1))))) (and (fn-resource-ledgerp after) (fn-rl-wfp after))) (not (let ((after (mv-nth 2 (fn-rlo-issue 7 11 8 :issued (rcx-l1))))) (not (fn-rl-wfp after))))))
(defteeth fn-rlo-issue-keeps-representation
  :claim (((rep (fn-resource-ledgerp ledger)) (wf (fn-rl-wfp ledger))) (let ((after (mv-nth 2 (fn-rlo-issue cid connection-gen operation-gen dependency ledger)))) (and (fn-resource-ledgerp after) (fn-rl-wfp after))))
  :subject fn-rlo-issue
  :witness-lemma rcx-fn-rlo-issue-keeps-representation-witness
  :witness ((cid 7) (connection-gen 11) (operation-gen 8) (dependency :issued) (ledger (rcx-l1)))
  :breaks ((rep ((ledger nil)) :lemma rcx-fn-rlo-issue-keeps-representation-without-rep)
          (wf ((ledger (update-fn-rl-count 99 (rcx-l1)))) :lemma rcx-fn-rlo-issue-keeps-representation-without-wf))
  :mutations ((not-wellformed (:conclusion (let ((after (mv-nth 2 (fn-rlo-issue cid connection-gen operation-gen dependency ledger)))) (not (fn-rl-wfp after)))) ((cid 7) (connection-gen 11) (operation-gen 8) (dependency :issued) (ledger (rcx-l1))) :fault "an operation that leaves the ledger ill-formed" :lemma rcx-fn-rlo-issue-keeps-representation-mutant-not-wellformed)))


(defthm rcx-fn-rlo-output-keeps-representation-witness
  (and (fn-resource-ledgerp (rcx-l2)) (fn-rl-wfp (rcx-l2)) (let ((after (mv-nth 1 (fn-rlo-output (rcx-tok) 8 :discarded (rcx-l2))))) (and (fn-resource-ledgerp after) (fn-rl-wfp after)))))
(defthm rcx-fn-rlo-output-keeps-representation-without-rep
  (and (fn-rl-wfp nil) (not (fn-resource-ledgerp nil)) (not (let ((after (mv-nth 1 (fn-rlo-output (rcx-tok) 8 :discarded nil)))) (and (fn-resource-ledgerp after) (fn-rl-wfp after))))))
(defthm rcx-fn-rlo-output-keeps-representation-without-wf
  (and (fn-resource-ledgerp (update-fn-rl-count 99 (rcx-l2))) (not (fn-rl-wfp (update-fn-rl-count 99 (rcx-l2)))) (not (let ((after (mv-nth 1 (fn-rlo-output (rcx-tok) 8 :discarded (update-fn-rl-count 99 (rcx-l2)))))) (and (fn-resource-ledgerp after) (fn-rl-wfp after))))))
(defthm rcx-fn-rlo-output-keeps-representation-mutant-not-wellformed
  (and (fn-resource-ledgerp (rcx-l2)) (fn-rl-wfp (rcx-l2)) (let ((after (mv-nth 1 (fn-rlo-output (rcx-tok) 8 :discarded (rcx-l2))))) (and (fn-resource-ledgerp after) (fn-rl-wfp after))) (not (let ((after (mv-nth 1 (fn-rlo-output (rcx-tok) 8 :discarded (rcx-l2))))) (not (fn-rl-wfp after))))))
(defteeth fn-rlo-output-keeps-representation
  :claim (((rep (fn-resource-ledgerp ledger)) (wf (fn-rl-wfp ledger))) (let ((after (mv-nth 1 (fn-rlo-output token operation-gen receipt ledger)))) (and (fn-resource-ledgerp after) (fn-rl-wfp after))))
  :subject fn-rlo-output
  :witness-lemma rcx-fn-rlo-output-keeps-representation-witness
  :witness ((token (rcx-tok)) (operation-gen 8) (receipt :discarded) (ledger (rcx-l2)))
  :breaks ((rep ((ledger nil)) :lemma rcx-fn-rlo-output-keeps-representation-without-rep)
          (wf ((ledger (update-fn-rl-count 99 (rcx-l2)))) :lemma rcx-fn-rlo-output-keeps-representation-without-wf))
  :mutations ((not-wellformed (:conclusion (let ((after (mv-nth 1 (fn-rlo-output token operation-gen receipt ledger)))) (not (fn-rl-wfp after)))) ((token (rcx-tok)) (operation-gen 8) (receipt :discarded) (ledger (rcx-l2))) :fault "an operation that leaves the ledger ill-formed" :lemma rcx-fn-rlo-output-keeps-representation-mutant-not-wellformed)))

