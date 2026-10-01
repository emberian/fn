; Ghost producer relation to the EXACT old semantic enrollment function.
; Never used by a runtime guard or served metadata setter. The actual
; parser/public canonical bridge must establish each entry at creation.
(in-package "ACL2")
(include-book "replay-enrollment-lookup")

(defun fn-rse-public-ledger-correspondsp (snapshots evidence)
 (declare (xargs :guard t :verify-guards nil))
 (if (consp snapshots)
  (and (consp evidence)
       (equal (fn-rsc-at 0 (car evidence)) (car snapshots))
       (equal (fn-rse-evidence-value (car evidence))
              (fn-hsig-keyring-snapshot-value (car snapshots)))
       (fn-rse-public-ledger-correspondsp (cdr snapshots) (cdr evidence)))
  (and (null snapshots) (null evidence))))
(local (defthm fn-rse-evidence-value-is-nil-or-exact-pair
 (or (not (fn-rse-evidence-value entry))
     (and (true-listp (fn-rse-evidence-value entry))
          (equal (len (fn-rse-evidence-value entry)) 2)))
 :hints (("Goal" :in-theory (enable fn-rse-evidence-value fn-rse-enrollment-model)))))
(local (defthm fn-rse-actual-public-value-head-comparison
 (equal
  (and (true-listp (fn-hsig-keyring-snapshot-value snapshot))
       (equal (len (fn-hsig-keyring-snapshot-value snapshot)) 2)
       (equal (car (fn-hsig-keyring-snapshot-value snapshot)) principal)
       (equal (cadr (fn-hsig-keyring-snapshot-value snapshot)) keys))
  (equal (list principal keys) (fn-hsig-keyring-snapshot-value snapshot)))
 :hints (("Goal" :in-theory
  (e/d (fn-hsig-keyring-snapshot-value)
       (fn-stxk-p fn-stxk-snapshot fn-stxk-profile
        fn-stmt-decode-items fn-stmt-okp fn-stmt-value
        fn-stxe-encode-items fn-stmt-bytes-item-p fn-stmt-uint-item-p
        fn-hsig-subject-p))))))
(local (defthm fn-rse-actual-public-value-reconstructs-by-definition
 (implies (consp (fn-hsig-keyring-snapshot-value snapshot))
  (equal (list (car (fn-hsig-keyring-snapshot-value snapshot))
               (cadr (fn-hsig-keyring-snapshot-value snapshot)))
         (fn-hsig-keyring-snapshot-value snapshot)))
 :hints (("Goal" :in-theory
  (e/d (fn-hsig-keyring-snapshot-value)
       (fn-stxk-p fn-stxk-snapshot fn-stxk-profile
        fn-stmt-decode-items fn-stmt-okp fn-stmt-value
        fn-stxe-encode-items fn-stmt-bytes-item-p fn-stmt-uint-item-p
        fn-hsig-subject-p))))))
(defthm fn-rse-retained-enrollment-model-is-actual-public-enrollment
 (implies (fn-rse-public-ledger-correspondsp snapshots evidence)
  (equal (fn-rse-enrolled-model principal keys evidence)
         (fn-hsig-enrolled-keys-of-principalp principal keys snapshots)))
 :rule-classes nil
 :hints (("Goal" :induct (fn-rse-public-ledger-correspondsp snapshots evidence)
  :in-theory (e/d (fn-rse-public-ledger-correspondsp fn-rse-enrolled-model
                  fn-hsig-enrolled-keys-of-principalp)
                 (fn-rse-evidence-value fn-rse-enrollment-model
                  fn-hsig-keyring-snapshot-value)))))
