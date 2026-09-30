; Actual host-called stobj representation boundary, not native activation.
(in-package "ACL2")
(include-book "../../host/snapshot-maintenance-host")
(include-book "snapshot-maintenance-demand-tests")
(include-book "snapshot-maintenance-profile-tests")

(defun-nx osjht-probe ()
 (let* ((install (fn-owner-page-read-install-baseline
                 '(10000 164064 10 1 100) '(0 0 0 0 0) 0 0 100
                 (create-fn-page-read-pool)))
        (pool (mv-nth 1 install))
        (admit (fn-owner-maintenance-admit 1 0 '(1000 16384 4 1 1) pool))
        (token (mv-nth 1 admit)) (issued (mv-nth 2 admit))
        (source '(1 (5 6) 0 0))
        (request (list :checkpoint-growth source 0 token 6 1 1 163840 192 32))
        (r (fn-owner-snapshot-growth token source 0 request issued))
        (model (fn-osj-native-grow (fn-owner-page-read-ledger issued) token source 0 request)))
  (list (mv-nth 0 install) (mv-nth 0 admit)
        (equal (fn-owner-page-read-direct-mode issued) :funded-pool)
        (equal (mv-nth 0 r) (mv-nth 0 model))
        (equal (fn-owner-page-read-ledger (mv-nth 1 r)) (mv-nth 1 model))
        (fn-owner-snapshot-grant-livep (mv-nth 0 r) (mv-nth 1 r)))))

(defthm osjht-complete-actual-boundary-positive
 (equal (osjht-probe) '(:installed :admitted t t t t))
 :rule-classes nil)

; Remove the only carried funded-mode premise. Actual unfunded branch
; explicitly refuses; the algebraic model can still differ on that input.
(defthm osjht-remove-funded-mode
 (let* ((pool (create-fn-page-read-pool))
        (r (fn-owner-snapshot-growth nil nil 0 nil pool))
        (model (fn-osj-native-grow (fn-owner-page-read-ledger pool) nil nil 0 nil)))
  (and (not (equal (fn-owner-page-read-direct-mode pool) :funded-pool))
       (not (equal (mv-nth 0 r) (mv-nth 0 model)))
       (not (fn-owner-snapshot-grant-livep (mv-nth 0 r) (mv-nth 1 r)))))
 :rule-classes nil)


(defun-nx osjht-profile-refusal-probe ()
 (let* ((n (expt 2 50)) (source '(1 (5 6) 0 0))
        (end (+ 16384 (* 16384 (+ 1 1 n 1))))
        (disk (+ end (* 32 n) 32))
        (install (fn-owner-page-read-install-baseline
                   (list 10000 disk 10 1 100) '(0 0 0 0 0) 0 0 100
                   (create-fn-page-read-pool)))
        (admit (fn-owner-maintenance-admit 1 0 '(1000 16384 4 1 1)
                                          (mv-nth 1 install)))
        (token (mv-nth 1 admit)) (issued (mv-nth 2 admit))
        (request (list :checkpoint-growth source 0 token n 1 1 end (* 32 n) 32))
        (r (fn-owner-snapshot-growth token source 0 request issued))
        (model (fn-osj-native-grow (fn-owner-page-read-ledger issued)
                                    token source 0 request)))
  (list (mv-nth 0 install) (mv-nth 0 admit)
        (equal (fn-owner-page-read-direct-mode issued) :funded-pool)
        (not (fn-osj-native-backingp request))
        (equal (mv-nth 0 r) '(:refused :checkpoint-offset-profile))
        (equal (mv-nth 0 r) (mv-nth 0 model))
        (equal (fn-owner-page-read-ledger (mv-nth 1 r)) (mv-nth 1 model))
        (equal (fn-owner-page-read-ledger (mv-nth 1 r))
               (fn-owner-page-read-ledger issued))
        (not (fn-owner-snapshot-grant-livep (mv-nth 0 r) (mv-nth 1 r))))))

(defthm osjht-actual-funded-offset-profile-refusal
 (equal (osjht-profile-refusal-probe) '(:installed :admitted t t t t t t t))
 :rule-classes nil)
