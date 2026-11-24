; Project the fresh control and ledger through the registered initialization sequence.
(in-package "ACL2")
(include-book "owed-accounts")
(include-book "account-fifo-init")

(defthm fn2-account-stop-columns-of-put-path
  (implies (member-equal k (list *fn2-control-stop* *fn2-control-stop-reason*))
           (equal (nth k (fn2-control-put-path i path ctrl)) (nth k ctrl)))
  :hints (("Goal" :induct (fn2-control-put-path i path ctrl)
           :in-theory (enable fn2-control-put-path))))
(defthm fn2-account-control-initial-stop
  (and (equal (fn2-control-stop (fn2-control-init profile ctrl)) 0)
       (equal (fn2-control-stop-reason (fn2-control-init profile ctrl)) *fn2-stop-reason-none*))
  :hints (("Goal" :in-theory (e/d (fn2-control-init fn2-control-stop fn2-control-stop-reason)
                                  (fn2-control-put-path fn2-control-columns-init
                                   fn2-profile-owner-account fn2-profile-path-identity fn2-profile-get)))))
(make-event
 (value
  `(defthm fn2-account-core-initial-children
     (let ((c (fn2-core-init profile old)))
       (and (equal (fn2-core-accounts c) (fn2-accounts-init profile (fn2-core-accounts old)))
            (equal (fn2-core-control c) (fn2-control-init profile (fn2-core-control old)))))
     :hints (("Goal" :in-theory (e/d (fn2-core-init ,@(fn2-core-init-child-names *fn2-core-children*))
                                    (fn2-control-init fn2-accounts-init)))))))
(defthm fn2-account-initial-row-count-natural
  (natp (fn2-accounts-rows (fn2-accounts-init profile acts)))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (e/d (fn2-accounts-init fn2-accounts-rows)
                                  (fn2-accounts-alloc fn2-account-set-capacities fn2-account-default-rows
                                   fn2-account-configure fn2-account-set-committed fn2-profile-p)))))
(defthm fn2-account-core-initial-invariant
  (implies (fn2-corep old) (fn2-account-core-invariantp (fn2-core-init profile old)))
  :hints (("Goal" :in-theory (e/d (fn2-account-core-invariantp fn2-core-stop-reason fn2-core-stopped-p)
                                  (fn2-core-init fn2-control-init fn2-accounts-init fn2-control-stop
                                   fn2-control-stop-reason fn2-account-fifos-visit fn2-accounts-rows
                                   fn2-accounts-shapep fn2-accountsp fn2-corep)))))
