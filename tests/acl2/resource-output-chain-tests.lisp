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


(defthm rcx-fn-rlo-physical-keeps-representation-witness
  (and (fn-resource-ledgerp (rcx-l2)) (fn-rl-wfp (rcx-l2)) (let ((after (mv-nth 1 (fn-rlo-physical (rcx-tok) 8 :terminal (rcx-l2))))) (and (fn-resource-ledgerp after) (fn-rl-wfp after)))))
(defthm rcx-fn-rlo-physical-keeps-representation-without-rep
  (and (fn-rl-wfp nil) (not (fn-resource-ledgerp nil)) (not (let ((after (mv-nth 1 (fn-rlo-physical (rcx-tok) 8 :terminal nil)))) (and (fn-resource-ledgerp after) (fn-rl-wfp after))))))
(defthm rcx-fn-rlo-physical-keeps-representation-without-wf
  (and (fn-resource-ledgerp (update-fn-rl-count 99 (rcx-l2))) (not (fn-rl-wfp (update-fn-rl-count 99 (rcx-l2)))) (not (let ((after (mv-nth 1 (fn-rlo-physical (rcx-tok) 8 :terminal (update-fn-rl-count 99 (rcx-l2)))))) (and (fn-resource-ledgerp after) (fn-rl-wfp after))))))
(defthm rcx-fn-rlo-physical-keeps-representation-mutant-not-wellformed
  (and (fn-resource-ledgerp (rcx-l2)) (fn-rl-wfp (rcx-l2)) (let ((after (mv-nth 1 (fn-rlo-physical (rcx-tok) 8 :terminal (rcx-l2))))) (and (fn-resource-ledgerp after) (fn-rl-wfp after))) (not (let ((after (mv-nth 1 (fn-rlo-physical (rcx-tok) 8 :terminal (rcx-l2))))) (not (fn-rl-wfp after))))))
(defteeth fn-rlo-physical-keeps-representation
  :claim (((rep (fn-resource-ledgerp ledger)) (wf (fn-rl-wfp ledger))) (let ((after (mv-nth 1 (fn-rlo-physical token operation-gen receipt ledger)))) (and (fn-resource-ledgerp after) (fn-rl-wfp after))))
  :subject fn-rlo-physical
  :witness-lemma rcx-fn-rlo-physical-keeps-representation-witness
  :witness ((token (rcx-tok)) (operation-gen 8) (receipt :terminal) (ledger (rcx-l2)))
  :breaks ((rep ((ledger nil)) :lemma rcx-fn-rlo-physical-keeps-representation-without-rep)
          (wf ((ledger (update-fn-rl-count 99 (rcx-l2)))) :lemma rcx-fn-rlo-physical-keeps-representation-without-wf))
  :mutations ((not-wellformed (:conclusion (let ((after (mv-nth 1 (fn-rlo-physical token operation-gen receipt ledger)))) (not (fn-rl-wfp after)))) ((token (rcx-tok)) (operation-gen 8) (receipt :terminal) (ledger (rcx-l2))) :fault "an operation that leaves the ledger ill-formed" :lemma rcx-fn-rlo-physical-keeps-representation-mutant-not-wellformed)))


(defthm rcx-fn-rlo-exhausted-settlement-keeps-free-head-witness
  (and (<= *fn-rl-word-max* (fn-rl-gensi 2 (update-fn-rl-gensi 2 *fn-rl-word-max* (rcx-l5)))) (let ((after (mv-nth 1 (fn-rlo-settle-ready 2 (update-fn-rl-gensi 2 *fn-rl-word-max* (rcx-l5))))) (slot 2) (ledger (update-fn-rl-gensi 2 *fn-rl-word-max* (rcx-l5)))) (and (equal (fn-rl-next after) (fn-rl-next ledger)) (equal (fn-rl-gensi slot after) (fn-rl-gensi slot ledger))))))
(defthm rcx-fn-rlo-exhausted-settlement-keeps-free-head-without-exhausted
  (and (not (<= *fn-rl-word-max* (fn-rl-gensi 2 (rcx-l5)))) (not (let ((after (mv-nth 1 (fn-rlo-settle-ready 2 (rcx-l5)))) (slot 2) (ledger (rcx-l5))) (and (equal (fn-rl-next after) (fn-rl-next ledger)) (equal (fn-rl-gensi slot after) (fn-rl-gensi slot ledger)))))))
(defthm rcx-fn-rlo-exhausted-settlement-keeps-free-head-mutant-head-moves
  (and (<= *fn-rl-word-max* (fn-rl-gensi 2 (update-fn-rl-gensi 2 *fn-rl-word-max* (rcx-l5)))) (let ((after (mv-nth 1 (fn-rlo-settle-ready 2 (update-fn-rl-gensi 2 *fn-rl-word-max* (rcx-l5))))) (slot 2) (ledger (update-fn-rl-gensi 2 *fn-rl-word-max* (rcx-l5)))) (and (equal (fn-rl-next after) (fn-rl-next ledger)) (equal (fn-rl-gensi slot after) (fn-rl-gensi slot ledger)))) (not (let ((after (mv-nth 1 (fn-rlo-settle-ready 2 (update-fn-rl-gensi 2 *fn-rl-word-max* (rcx-l5))))) (ledger (update-fn-rl-gensi 2 *fn-rl-word-max* (rcx-l5)))) (not (equal (fn-rl-next after) (fn-rl-next ledger)))))))
(defteeth fn-rlo-exhausted-settlement-keeps-free-head
  :claim (((exhausted (<= *fn-rl-word-max* (fn-rl-gensi slot ledger)))) (let ((after (mv-nth 1 (fn-rlo-settle-ready slot ledger)))) (and (equal (fn-rl-next after) (fn-rl-next ledger)) (equal (fn-rl-gensi slot after) (fn-rl-gensi slot ledger)))))
  :subject fn-rlo-settle-ready
  :witness-lemma rcx-fn-rlo-exhausted-settlement-keeps-free-head-witness
  :witness ((slot 2) (ledger (update-fn-rl-gensi 2 *fn-rl-word-max* (rcx-l5))))
  :breaks ((exhausted ((ledger (rcx-l5))) :lemma rcx-fn-rlo-exhausted-settlement-keeps-free-head-without-exhausted))
  :mutations ((head-moves (:conclusion (let ((after (mv-nth 1 (fn-rlo-settle-ready slot ledger)))) (not (equal (fn-rl-next after) (fn-rl-next ledger))))) ((slot 2) (ledger (update-fn-rl-gensi 2 *fn-rl-word-max* (rcx-l5)))) :fault "a settlement of an exhausted slot that pushes it back on the free head" :lemma rcx-fn-rlo-exhausted-settlement-keeps-free-head-mutant-head-moves)))


(defthm rcx-fn-rlo-install-bank-correspondence-witness
  (and (eq (mv-nth 0 (fn-rlo-install 1073741824 536870912 nil '(16777216 1048576) 4 (rcx-l0))) :installed) (let ((grant (fn-orv-startup-grant 1073741824 536870912 nil '(16777216 1048576) 4)) (ledger (rcx-l0)) (slots 4) (policy '(16777216 1048576)) (cold nil) (store-need 536870912) (dynamic 1073741824)) (equal (fn-rl-bank (mv-nth 1 (fn-rlo-install dynamic store-need cold policy slots ledger))) (fn-rl-bank (mv-nth 1 (fn-rl-install (fn-rlo-resident-vector (nth 1 grant)) (fn-rlo-resident-vector (nth 3 grant)) (fn-rlo-resident-vector (nth 2 grant)) slots ledger)))))))
(defthm rcx-fn-rlo-install-bank-correspondence-without-installed
  (and (not (eq (mv-nth 0 (fn-rlo-install 1073741824 536870912 nil nil 4 (rcx-l0))) :installed)) (not (let ((grant (fn-orv-startup-grant 1073741824 536870912 nil nil 4)) (ledger (rcx-l0)) (slots 4) (policy nil) (cold nil) (store-need 536870912) (dynamic 1073741824)) (equal (fn-rl-bank (mv-nth 1 (fn-rlo-install dynamic store-need cold policy slots ledger))) (fn-rl-bank (mv-nth 1 (fn-rl-install (fn-rlo-resident-vector (nth 1 grant)) (fn-rlo-resident-vector (nth 3 grant)) (fn-rlo-resident-vector (nth 2 grant)) slots ledger))))))))
(defthm rcx-fn-rlo-install-bank-correspondence-mutant-grant-parts-swapped
  (and (eq (mv-nth 0 (fn-rlo-install 1073741824 536870912 nil '(16777216 1048576) 4 (rcx-l0))) :installed) (let ((grant (fn-orv-startup-grant 1073741824 536870912 nil '(16777216 1048576) 4)) (ledger (rcx-l0)) (slots 4) (policy '(16777216 1048576)) (cold nil) (store-need 536870912) (dynamic 1073741824)) (equal (fn-rl-bank (mv-nth 1 (fn-rlo-install dynamic store-need cold policy slots ledger))) (fn-rl-bank (mv-nth 1 (fn-rl-install (fn-rlo-resident-vector (nth 1 grant)) (fn-rlo-resident-vector (nth 3 grant)) (fn-rlo-resident-vector (nth 2 grant)) slots ledger))))) (not (let ((grant (fn-orv-startup-grant 1073741824 536870912 nil '(16777216 1048576) 4)) (ledger (rcx-l0)) (slots 4) (policy '(16777216 1048576)) (cold nil) (store-need 536870912) (dynamic 1073741824)) (equal (fn-rl-bank (mv-nth 1 (fn-rlo-install dynamic store-need cold policy slots ledger))) (fn-rl-bank (mv-nth 1 (fn-rl-install (fn-rlo-resident-vector (nth 3 grant)) (fn-rlo-resident-vector (nth 1 grant)) (fn-rlo-resident-vector (nth 2 grant)) slots ledger))))))))
(defteeth fn-rlo-install-bank-correspondence
  :claim (((installed (eq (mv-nth 0 (fn-rlo-install dynamic store-need cold policy slots ledger)) :installed))) (let ((grant (fn-orv-startup-grant dynamic store-need cold policy slots))) (equal (fn-rl-bank (mv-nth 1 (fn-rlo-install dynamic store-need cold policy slots ledger))) (fn-rl-bank (mv-nth 1 (fn-rl-install (fn-rlo-resident-vector (nth 1 grant)) (fn-rlo-resident-vector (nth 3 grant)) (fn-rlo-resident-vector (nth 2 grant)) slots ledger))))))
  :subject fn-rlo-install
  :witness-lemma rcx-fn-rlo-install-bank-correspondence-witness
  :witness ((dynamic 1073741824) (store-need 536870912) (cold nil) (policy '(16777216 1048576)) (slots 4) (ledger (rcx-l0)))
  :breaks ((installed ((policy nil)) :lemma rcx-fn-rlo-install-bank-correspondence-without-installed))
  :mutations ((grant-parts-swapped (:conclusion (let ((grant (fn-orv-startup-grant dynamic store-need cold policy slots))) (equal (fn-rl-bank (mv-nth 1 (fn-rlo-install dynamic store-need cold policy slots ledger))) (fn-rl-bank (mv-nth 1 (fn-rl-install (fn-rlo-resident-vector (nth 3 grant)) (fn-rlo-resident-vector (nth 1 grant)) (fn-rlo-resident-vector (nth 2 grant)) slots ledger)))))) ((dynamic 1073741824) (store-need 536870912) (cold nil) (policy '(16777216 1048576)) (slots 4) (ledger (rcx-l0))) :fault "an install that charges the store and dynamic grants the wrong way round" :lemma rcx-fn-rlo-install-bank-correspondence-mutant-grant-parts-swapped)))


(defthm rcx-fn-rlo-issue-drawn-bank-correspondence-witness
  (and (eq (mv-nth 0 (fn-rlo-issue 7 11 8 :issued (rcx-l1))) :drawn) (equal (fn-rl-bank (mv-nth 2 (fn-rlo-issue 7 11 8 :issued (rcx-l1)))) (fn-rl-bank (mv-nth 2 (fn-rl-draw (fn-rl-next (rcx-l1)) (fn-rlo-resident-vector (fn-rl-file-limit (rcx-l1))) (rcx-l1)))))))
(defthm rcx-fn-rlo-issue-drawn-bank-correspondence-without-drawn
  (and (not (eq (mv-nth 0 (fn-rlo-issue -1 11 8 :issued (rcx-l1))) :drawn)) (not (equal (fn-rl-bank (mv-nth 2 (fn-rlo-issue -1 11 8 :issued (rcx-l1)))) (fn-rl-bank (mv-nth 2 (fn-rl-draw (fn-rl-next (rcx-l1)) (fn-rlo-resident-vector (fn-rl-file-limit (rcx-l1))) (rcx-l1))))))))
(defthm rcx-fn-rlo-issue-drawn-bank-correspondence-mutant-bank-unchanged
  (and (eq (mv-nth 0 (fn-rlo-issue 7 11 8 :issued (rcx-l1))) :drawn) (equal (fn-rl-bank (mv-nth 2 (fn-rlo-issue 7 11 8 :issued (rcx-l1)))) (fn-rl-bank (mv-nth 2 (fn-rl-draw (fn-rl-next (rcx-l1)) (fn-rlo-resident-vector (fn-rl-file-limit (rcx-l1))) (rcx-l1))))) (not (equal (fn-rl-bank (mv-nth 2 (fn-rlo-issue 7 11 8 :issued (rcx-l1)))) (fn-rl-bank (rcx-l1))))))
(defteeth fn-rlo-issue-drawn-bank-correspondence
  :claim (((drawn (eq (mv-nth 0 (fn-rlo-issue cid connection-gen operation-gen dependency ledger)) :drawn))) (equal (fn-rl-bank (mv-nth 2 (fn-rlo-issue cid connection-gen operation-gen dependency ledger))) (fn-rl-bank (mv-nth 2 (fn-rl-draw (fn-rl-next ledger) (fn-rlo-resident-vector (fn-rl-file-limit ledger)) ledger)))))
  :subject fn-rlo-issue
  :witness-lemma rcx-fn-rlo-issue-drawn-bank-correspondence-witness
  :witness ((cid 7) (connection-gen 11) (operation-gen 8) (dependency :issued) (ledger (rcx-l1)))
  :breaks ((drawn ((cid -1)) :lemma rcx-fn-rlo-issue-drawn-bank-correspondence-without-drawn))
  :mutations ((bank-unchanged (:conclusion (equal (fn-rl-bank (mv-nth 2 (fn-rlo-issue cid connection-gen operation-gen dependency ledger))) (fn-rl-bank ledger))) ((cid 7) (connection-gen 11) (operation-gen 8) (dependency :issued) (ledger (rcx-l1))) :fault "an issue that draws a slot without charging the bank" :lemma rcx-fn-rlo-issue-drawn-bank-correspondence-mutant-bank-unchanged)))


(defthm rcx-fn-rlo-issued-token-is-live-witness
  (implies (and (fn-resource-ledgerp (rcx-l1)) (eq (mv-nth 0 (fn-rlo-issue 7 11 8 :issued (rcx-l1))) :drawn)) (fn-rlo-livep (mv-nth 1 (fn-rlo-issue 7 11 8 :issued (rcx-l1))) 8 (mv-nth 2 (fn-rlo-issue 7 11 8 :issued (rcx-l1))))))
(defthm rcx-fn-rlo-issued-token-is-live-mutant-live-at-the-next-operation
  (and (implies (and (fn-resource-ledgerp (rcx-l1)) (eq (mv-nth 0 (fn-rlo-issue 7 11 8 :issued (rcx-l1))) :drawn)) (fn-rlo-livep (mv-nth 1 (fn-rlo-issue 7 11 8 :issued (rcx-l1))) 8 (mv-nth 2 (fn-rlo-issue 7 11 8 :issued (rcx-l1))))) (not (implies (and (fn-resource-ledgerp (rcx-l1)) (eq (mv-nth 0 (fn-rlo-issue 7 11 8 :issued (rcx-l1))) :drawn)) (fn-rlo-livep (mv-nth 1 (fn-rlo-issue 7 11 8 :issued (rcx-l1))) (+ 1 8) (mv-nth 2 (fn-rlo-issue 7 11 8 :issued (rcx-l1))))))))
(defteeth fn-rlo-issued-token-is-live
  :claim (() (implies (and (fn-resource-ledgerp ledger) (eq (mv-nth 0 (fn-rlo-issue cid connection-gen operation-gen dependency ledger)) :drawn)) (fn-rlo-livep (mv-nth 1 (fn-rlo-issue cid connection-gen operation-gen dependency ledger)) operation-gen (mv-nth 2 (fn-rlo-issue cid connection-gen operation-gen dependency ledger)))))
  :subject fn-rlo-issue
  :witness-lemma rcx-fn-rlo-issued-token-is-live-witness
  :witness ((cid 7) (connection-gen 11) (operation-gen 8) (dependency :issued) (ledger (rcx-l1)))
  :mutations ((live-at-the-next-operation (:conclusion (implies (and (fn-resource-ledgerp ledger) (eq (mv-nth 0 (fn-rlo-issue cid connection-gen operation-gen dependency ledger)) :drawn)) (fn-rlo-livep (mv-nth 1 (fn-rlo-issue cid connection-gen operation-gen dependency ledger)) (+ 1 operation-gen) (mv-nth 2 (fn-rlo-issue cid connection-gen operation-gen dependency ledger))))) ((cid 7) (connection-gen 11) (operation-gen 8) (dependency :issued) (ledger (rcx-l1))) :fault "a token live for an operation generation other than the one it was issued for" :lemma rcx-fn-rlo-issued-token-is-live-mutant-live-at-the-next-operation)))


(defthm rcx-fn-rlo-output-bank-correspondence-witness
  (equal (fn-rl-bank (mv-nth 1 (fn-rlo-output (rcx-tok) 8 :discarded (rcx-l3)))) (if (and (fn-rlo-livep (rcx-tok) 8 (rcx-l3)) (member-eq :discarded '(:drained :discarded)) (equal (fn-rl-trailersi (caddr (rcx-tok)) (rcx-l3)) 1)) (fn-rl-bank (mv-nth 1 (fn-rl-settle (caddr (rcx-tok)) (fn-rl-gensi (caddr (rcx-tok)) (rcx-l3)) (rcx-l3)))) (fn-rl-bank (rcx-l3)))))
(defthm rcx-fn-rlo-output-bank-correspondence-mutant-bank-unchanged
  (and (equal (fn-rl-bank (mv-nth 1 (fn-rlo-output (rcx-tok) 8 :discarded (rcx-l3)))) (if (and (fn-rlo-livep (rcx-tok) 8 (rcx-l3)) (member-eq :discarded '(:drained :discarded)) (equal (fn-rl-trailersi (caddr (rcx-tok)) (rcx-l3)) 1)) (fn-rl-bank (mv-nth 1 (fn-rl-settle (caddr (rcx-tok)) (fn-rl-gensi (caddr (rcx-tok)) (rcx-l3)) (rcx-l3)))) (fn-rl-bank (rcx-l3)))) (not (equal (fn-rl-bank (mv-nth 1 (fn-rlo-output (rcx-tok) 8 :discarded (rcx-l3)))) (fn-rl-bank (rcx-l3))))))
(defteeth fn-rlo-output-bank-correspondence
  :claim (() (equal (fn-rl-bank (mv-nth 1 (fn-rlo-output token operation-gen receipt ledger))) (if (and (fn-rlo-livep token operation-gen ledger) (member-eq receipt '(:drained :discarded)) (equal (fn-rl-trailersi (caddr token) ledger) 1)) (fn-rl-bank (mv-nth 1 (fn-rl-settle (caddr token) (fn-rl-gensi (caddr token) ledger) ledger))) (fn-rl-bank ledger))))
  :subject fn-rlo-output
  :witness-lemma rcx-fn-rlo-output-bank-correspondence-witness
  :witness ((token (rcx-tok)) (operation-gen 8) (receipt :discarded) (ledger (rcx-l3)))
  :mutations ((bank-unchanged (:conclusion (equal (fn-rl-bank (mv-nth 1 (fn-rlo-output token operation-gen receipt ledger))) (fn-rl-bank ledger))) ((token (rcx-tok)) (operation-gen 8) (receipt :discarded) (ledger (rcx-l3))) :fault "a settling receipt that leaves the bank charged" :lemma rcx-fn-rlo-output-bank-correspondence-mutant-bank-unchanged)))

