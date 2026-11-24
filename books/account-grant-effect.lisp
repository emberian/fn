; A successful reservation writes the chosen principal's holding cell.
(in-package "ACL2")
(include-book "accounts")

(defthm fn2-account-acquire-adds-holding
  (implies (and (fn2-account-guard)
                (equal (mv-nth 0 (fn2-account-acquire p d a fn2-accounts)) :ok))
           (equal (fn2-account-hold p d (mv-nth 1 (fn2-account-acquire p d a fn2-accounts)))
                  (+ a (fn2-account-hold p d fn2-accounts))))
  :hints (("Goal" :in-theory
           (e/d (fn2-account-hold fn2-account-acquire fn2-account-holdv fn2-accounts-rows)
                (fn2-accountsp fn2-accounts-wfp fn2-accounts-shapep
                 fn2-account-reservev fn2-account-limitv fn2-account-capacityv
                 fn2-account-committedv)))))
