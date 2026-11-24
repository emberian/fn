; D7 request grants on the served core.
(in-package "ACL2")
(include-book "owed-accounts")
(include-book "account-once-proof")
(include-book "account-exact-proof")
(include-book "owed-discharge")

(defthm fn2-account-grant-exact-proved
  (fn2-account-grant-exact$owed fn2-core)
  :rule-classes nil
  :hints (("Goal" :use (fn2-account-ready-grant-exact fn2-account-returned-row-clears-wait
                         fn2-account-grant-take-live)
           :in-theory '(fn2-account-grant-exact$owed))))
(fn2-owed-discharge fn2-account-grant-exact fn2-account-grant-exact-proved)

(defthm fn2-account-request-once-proved
  (fn2-account-request-once$owed fn2-core)
  :rule-classes nil
  :hints (("Goal" :use (fn2-account-no-consecutive-grants fn2-account-grant-take-live)
           :in-theory '(fn2-account-request-once$owed))))
(fn2-owed-discharge fn2-account-request-once fn2-account-request-once-proved)
