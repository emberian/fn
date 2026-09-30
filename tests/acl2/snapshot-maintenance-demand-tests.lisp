; PRF-1142 / SCN-1048: actual ledger growth, exact identities and refusals.
(in-package "ACL2")
(include-book "../../books/snapshot-maintenance-demand")

(defun-nx osjdt-probe (disk-budget fd-demand source stage mutate)
 (let* ((ledger (fn-prl-make (list 10000 disk-budget 10 1 100)))
        (admit (fn-pmn-admit ledger 1 0 (list 1000 16384 fd-demand 1 1)))
        (maintenance (mv-nth 1 admit))
        (issued (mv-nth 2 admit))
        (request (list :checkpoint-growth source stage maintenance
                       6 1 1 163840 192 32))
        (request (if mutate (update-nth 8 191 request) request))
        (result (fn-osj-grow issued maintenance source stage request))
        (grant (mv-nth 0 result)) (next (mv-nth 1 result)))
  (list (equal (car grant) :checkpoint-funded)
        (fn-osj-growth-requestp request source stage maintenance)
        (equal grant (cons :checkpoint-funded (cdr request)))
        (fn-prs-fundedp (fn-prl-nth 0 issued) (fn-prl-baseline issued)
                        '(0 0 0 0 0) (fn-prl-nth 1 next))
        (fn-osj-grant-livep grant next)
        (equal issued next)
        (fn-prl-nth 1 next))))

(defthm osjdt-all-grown-keystones-literal-positive
 (equal (osjdt-probe 164064 4 '(1 (5 6) 0 0) 0 nil)
        '(t t t t t nil (1000 164064 4 1 1)))
 :rule-classes nil)

; Only theorem antecedent: actual success. Each removed-antecedent witness
; affirms its failure and failure of the exact literal conclusion.
(defthm osjdt-remove-grown-result-for-request-theorem
 (let ((r (osjdt-probe 164063 4 '(1 (5 6) 0 0) 0 nil)))
  (and (not (car r)) (nth 1 r) (not (nth 2 r))))
 :rule-classes nil)
(defthm osjdt-remove-grown-result-for-live-theorem
 (let ((r (osjdt-probe 164063 4 '(1 (5 6) 0 0) 0 nil)))
  (and (not (car r)) (not (nth 4 r))))
 :rule-classes nil)
; Pool funding can remain true on refused growth; its success antecedent
; is redundant only if an initial carried funding premise replaces it.
; The literal malformed prior ledger below negates that conclusion too.
(defthm osjdt-remove-grown-result-for-funding-theorem
 (let* ((ledger '((0 0 0 0 0) (1 0 0 0 0) 0 nil))
        (r (fn-osj-grow ledger '(:maintenance 0 1 0)
                       '(1 (5 6) 0 0) 0 nil)))
  (and (not (equal (car (mv-nth 0 r)) :checkpoint-funded))
       (not (fn-prs-fundedp (fn-prl-nth 0 ledger) (fn-prl-baseline ledger)
                           '(0 0 0 0 0) (fn-prl-nth 1 (mv-nth 1 r))))))
 :rule-classes nil)

(defthm osjdt-source-epoch-mutant-refused
 (equal (osjdt-probe 164064 4 '(2 (5 6) 0 0) 0 nil)
        '(nil nil nil t nil t (1000 16384 4 1 1)))
 :rule-classes nil)
(defthm osjdt-stage-counter-mutant-refused
 (equal (osjdt-probe 164064 4 '(1 (5 6) 0 0) 1 nil)
        '(nil nil nil t nil t (1000 16384 4 1 1)))
 :rule-classes nil)
(defthm osjdt-short-spool-mutant-refused
 (equal (osjdt-probe 164064 4 '(1 (5 6) 0 0) 0 t)
        '(nil nil nil t nil t (1000 16384 4 1 1)))
 :rule-classes nil)
(defthm osjdt-missing-spool-descriptor-credit-refused
 (equal (osjdt-probe 164064 2 '(1 (5 6) 0 0) 0 nil)
        '(nil t nil t nil t (1000 16384 2 1 1)))
 :rule-classes nil)

(defun-nx osjdt-returned-grant-probe ()
 (let* ((admit (fn-pmn-admit (fn-prl-make '(10000 164064 10 1 100))
                             1 0 '(1000 16384 4 1 1)))
        (maintenance (mv-nth 1 admit))
        (r (fn-osj-grow (mv-nth 2 admit) maintenance '(1 (5 6) 0 0) 0
             (list :checkpoint-growth '(1 (5 6) 0 0) 0 maintenance
                    6 1 1 163840 192 32)))
        (grant (mv-nth 0 r)) (ledger (mv-nth 1 r))
        ; fn-pmn-release is called only at actual joined/definite cleanup by
        ; the producer. This tests authority invalidation, not host fidelity.
        (released (fn-pmn-release ledger maintenance)))
  (list (fn-osj-grant-livep grant ledger)
        (fn-osj-grant-livep grant (mv-nth 1 released))
        (mv-nth 0 released) (fn-prl-nth 1 (mv-nth 1 released))
        (fn-osj-grant-livep (update-nth 3 '(:maintenance 99 1 0) grant) ledger)
        (fn-osj-grant-livep (update-nth 2 99 grant) ledger)
        (fn-osj-grant-livep (update-nth 1 '(1 (5 6) 1 0) grant) ledger)
        (fn-osj-grant-livep (update-nth 4 5 grant) ledger))))

(defthm osjdt-old-grant-invalid-after-actual-release
 (equal (osjdt-returned-grant-probe)
        '(t nil :released (0 0 0 0 1) nil nil nil nil))
 :rule-classes nil)
