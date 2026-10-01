; Internal supplied-demand algebra fixture; no installed runtime permission.
(in-package "ACL2")
(include-book "../../books/decoded-worker-resolved-admission")
(defconst *dwa-empty* (mv-nth 1 (fn-prl-make-baseline '(10000 0 2 1 20) '(1000 0 0 0 0))))
(defconst *dwa-ledger* (mv-nth 1 (fn-prl-register *dwa-empty* 7 '(64 0 1 0 0))))
(defconst *dwa-desc* '(7 100 320 120 40 200 99 250 0))
(defconst *dwa-scan* (fn-dwb-one (fn-dwb-start 7 9 (fn-prl-nth 3 *dwa-ledger*) '(:test-source))))
; Full literal complete-MV refinement positive and actual issued nonce.
(assert-event
 (and (eq (fn-dwb-word *dwa-scan*) :binding-resolved)
      (equal (fn-prl-nth 1 *dwa-scan*) (fn-pwz-nth 0 *dwa-desc*))
      (equal (fn-prl-nth 5 *dwa-scan*)
             (fn-prl-binding (list :incarnation (fn-pwz-nth 0 *dwa-desc*)) (fn-prl-nth 3 *dwa-ledger*)))
      (equal (fn-dwb-admit-resolved *dwa-ledger* *dwa-desc* '(256 0 0 1 1) *dwa-scan*)
             (fn-pwz-admit *dwa-ledger* *dwa-desc* '(256 0 0 1 1)))
      (eq (mv-nth 0 (fn-dwb-admit-resolved *dwa-ledger* *dwa-desc* '(256 0 0 1 1) *dwa-scan*)) :admitted)))
; Corrupted-state removal: wrong retained binding cannot authorize CURRENT.
(assert-event
 (and (eq (fn-dwb-word *dwa-scan*) :binding-resolved)
      (equal (fn-prl-nth 1 *dwa-scan*) (fn-pwz-nth 0 *dwa-desc*))
      (not (equal (fn-prl-nth 5 *dwa-scan*)
                  (fn-prl-binding (list :incarnation (fn-pwz-nth 0 *dwa-desc*)) (fn-prl-nth 3 *dwa-empty*))))
      (not (equal (fn-dwb-admit-resolved *dwa-empty* *dwa-desc* '(256 0 0 1 1) *dwa-scan*)
                  (fn-pwz-admit *dwa-empty* *dwa-desc* '(256 0 0 1 1))))))
