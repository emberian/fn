; Complete literal profile/grant/unchanged-ledger teeth. Source evidence only.
(in-package "ACL2")
(include-book "../../books/snapshot-maintenance-profile")

(defun-nx osjpt-probe (n)
 (let* ((source '(1 (5 6) 0 0))
        (end (+ 16384 (* 16384 (+ 1 1 n 1))))
        (disk (+ end (* 32 n) 32))
        (admit (fn-pmn-admit (fn-prl-make (list 10000 disk 10 1 100))
                              1 0 '(1000 16384 4 1 1)))
        (token (mv-nth 1 admit)) (ledger (mv-nth 2 admit))
        (request (list :checkpoint-growth source 0 token n 1 1 end (* 32 n) 32))
        (r (fn-osj-native-grow ledger token source 0 request))
        (ungated (fn-osj-grow ledger token source 0 request)))
  (list (equal (car (mv-nth 0 r)) :checkpoint-funded)
        (fn-osj-native-backingp request)
        (fn-osj-native-grant-livep (mv-nth 0 r) (mv-nth 1 r))
        (fn-prs-fundedp (fn-prl-nth 0 ledger) (fn-prl-baseline ledger)
                        '(0 0 0 0 0) (fn-prl-nth 1 (mv-nth 1 r)))
        (equal r (list '(:refused :checkpoint-offset-profile) ledger))
        (equal (mv-nth 1 r) ledger)
        (fn-osj-grant-livep (mv-nth 0 ungated) (mv-nth 1 ungated))
        (fn-osj-native-grant-livep (mv-nth 0 ungated) (mv-nth 1 ungated)))))

(defthm osjpt-grown-live-and-funding-complete-positive
 (equal (osjpt-probe 6) '(t t t t nil nil t t))
 :rule-classes nil)

(defthm osjpt-refusal-complete-positive-and-remove-live-success
 (let ((r (osjpt-probe (expt 2 50))))
  (and (not (nth 0 r)) (not (nth 1 r)) (not (nth 2 r))
       (nth 4 r) (nth 5 r) (nth 6 r) (not (nth 7 r))))
 :rule-classes nil)

(defthm osjpt-remove-grown-success-for-funding-corrupted-ledger
 (let* ((ledger '((0 0 0 0 0) (1 0 0 0 0) 0 nil))
        (r (fn-osj-native-grow ledger '(:maintenance 0 1 0)
                               '(1 (5 6) 0 0) 0 nil)))
  (and (not (equal (car (mv-nth 0 r)) :checkpoint-funded))
       (not (fn-prs-fundedp (fn-prl-nth 0 ledger) (fn-prl-baseline ledger)
                            '(0 0 0 0 0) (fn-prl-nth 1 (mv-nth 1 r))))))
 :rule-classes nil)

(defthm osjpt-remove-profile-refusal-premise
 (let ((r (osjpt-probe 6)))
  (and (nth 1 r) (not (nth 4 r))))
 :rule-classes nil)

(defthm osjpt-slice-complete-positive
 (and (fn-osj-native-slicep 163840 163776 64)
      (natp 163776) (natp 64) (natp (+ 163776 64))
      (<= 163776 (fn-osj-native-offset-max))
      (<= 64 (fn-osj-native-offset-max))
      (<= (+ 163776 64) (fn-osj-native-offset-max)))
 :rule-classes nil)

(defthm osjpt-remove-slice-corrupted-offset
 (let ((offset (expt 2 63)))
  (and (not (fn-osj-native-slicep 163840 offset 64))
       (not (and (natp offset) (natp 64) (natp (+ offset 64))
                 (<= offset (fn-osj-native-offset-max))
                 (<= 64 (fn-osj-native-offset-max))
                 (<= (+ offset 64) (fn-osj-native-offset-max))))))
 :rule-classes nil)

; Each backing component is independently validated, even if an invalid
; request has not reached the exact-layout predicate yet.
(defthm osjpt-spool-overflow-mutants
 (let ((request '(:checkpoint-growth (1 (5 6) 0 0) 0
                   (:maintenance 0 1 0) 6 1 1 163840 192 32)))
  (and (fn-osj-native-backingp request)
       (not (fn-osj-native-backingp (update-nth 7 (expt 2 63) request)))
       (not (fn-osj-native-backingp (update-nth 8 (expt 2 63) request)))
       (not (fn-osj-native-backingp (update-nth 9 (expt 2 63) request)))))
 :rule-classes nil)
