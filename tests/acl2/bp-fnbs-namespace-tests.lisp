; Mixed legacy and received FNBS final-name recovery in one directory.
(in-package "ACL2")
(include-book "../../books/bp-fnbs-namespace")
(include-book "std/testing/must-fail" :dir :system)

(defun bpnfn-mixed-names ()
  (list ".record-leftover"
        (fn-bpnf-stored-record-name 0 0)
        (fn-bpn-lifecycle-record-name 0)
        (fn-bpn-lifecycle-record-name 1)
        (fn-bpnf-stored-record-name 9 1)))

(assert-event (equal (fn-bpnf-namespace-max-entries) 12304))
(assert-event (fn-bpnf-legacy-name-candidatep
               (fn-bpn-lifecycle-record-name 0)))
(assert-event (fn-bpnf-kind-five-name-candidatep
               (fn-bpnf-stored-record-name 9 1)))
(assert-event
 (equal (fn-bpnf-namespace-plan (bpnfn-mixed-names))
        (list :ready
              (list (fn-bpn-lifecycle-record-name 0)
                    (fn-bpn-lifecycle-record-name 1))
              (list (fn-bpnf-stored-record-name 0 0)
                    (fn-bpnf-stored-record-name 9 1))
              (list ".record-leftover"))))
(assert-event
 (fn-bpn-lifecycle-namespace-planp
  (fn-bpn-lifecycle-namespace-plan
   (fn-bpnf-namespace-legacy
    (fn-bpnf-namespace-plan (bpnfn-mixed-names))))))
(assert-event
 (equal (fn-bpnf-mixed-recovery-plan (bpnfn-mixed-names))
        (list :ready
              (list (fn-bpn-lifecycle-record-name 0)
                    (fn-bpn-lifecycle-record-name 1))
              (list (fn-bpnf-stored-record-name 0 0)
                    (fn-bpnf-stored-record-name 9 1))
              (list ".record-leftover") 2)))
(assert-event
 (fn-bpnf-mixed-recovery-planp
  (fn-bpnf-mixed-recovery-plan (bpnfn-mixed-names))))
(assert-event
 (equal (fn-bpnf-mixed-legacy-observed
         (fn-bpnf-mixed-recovery-plan (bpnfn-mixed-names)))
        (list (fn-bpn-lifecycle-record-name 0)
              (fn-bpn-lifecycle-record-name 1)
              ".record-leftover")))
(assert-event
 (equal (fn-bpnf-mixed-recovery-plan
         (list (fn-bpnf-stored-record-name 0 0)))
        (list :ready nil (list (fn-bpnf-stored-record-name 0 0)) nil 0)))
(assert-event
 (equal (fn-bpnf-mixed-recovery-plan
         (list (fn-bpn-lifecycle-record-name 1)))
        '(:fault :legacy-namespace)))
(assert-event
 (equal (fn-bpnf-namespace-plan (list "stray.fnb"))
        '(:fault :fnbs-namespace)))
(assert-event
 (equal (fn-bpnf-namespace-plan
         (list (fn-bpnf-stored-record-name 9 1) "9-1.fnb"))
        '(:fault :fnbs-namespace)))
(must-fail
 (assert-event
  (fn-bpnf-namespace-planp (fn-bpnf-namespace-plan (list "stray.fnb")))))
