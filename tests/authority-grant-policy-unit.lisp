(in-package "ACL2")
(include-book "../books/authority-grant-policy")

(assert-event
 (and (fn2-grant-scope-admissible-p 3 2 0)
      (fn2-grant-scope-admissible-p 4 1 7)
      (fn2-grant-scope-admissible-p 5 1 7)
      (not (fn2-grant-scope-admissible-p 3 1 7))
      (not (fn2-grant-scope-admissible-p 4 2 0))
      (not (fn2-grant-scope-admissible-p 7 1 7))
      (not (fn2-grant-scope-admissible-p 5 1 (expt 2 60)))))

(assert-event
 (and (equal (fn2-peer-role-at-decision :ok 21 12 0 1) 12)
      (equal (fn2-peer-role-at-decision :ok 24 12 12 0) 12)
      (equal (fn2-peer-role-at-decision :access 25 12 12 0) 0)
      (equal (fn2-peer-role-at-decision :ok 26 26 12 0) 0)
      (equal (fn2-peer-role-at-decision :ok 26 26 0 0) 0)
      (equal (fn2-peer-role-at-decision :ok 26 26 0 1) 26)
      (equal (fn2-peer-role-at-decision :more 24 12 12 0) 0)))
