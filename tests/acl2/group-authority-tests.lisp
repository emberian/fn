; Explicit authority config publication, replay, and hypothesis-removal teeth.
(in-package "ACL2")
(include-book "../../books/config-invariants")
(include-book "../../books/config-records")
(include-book "../../books/native-admin")
(include-book "must-fail-checked")
(include-book "../../books/codec-attach")
(defconst *gat-hex-a* "5555555555555555555555555555555555555555555555555555555555555555")
(defconst *gat-hex-b* "6666666666666666666666666666666666666666666666666666666666666666")
(defconst *gat-r1* (fn-cfg-record-make 0 0 1
  (list (fn-cfg-create-group "fn.test" "post-policy") (fn-cfg-set-capacity 65536))
  *fn-cfg-default-stamp*))
(defconst *gat-r2* (fn-cfg-record-make 1 1 2
  (list (fn-cfg-set-group-authority "fn.test" *gat-hex-a*)) *fn-cfg-default-stamp*))
(defconst *gat-r3* (fn-cfg-record-make 2 2 3
  (list (fn-cfg-set-group-authority "fn.test" *gat-hex-b*)) *fn-cfg-default-stamp*))
(defconst *gat-r4* (fn-cfg-record-make 3 3 4
  (list (fn-cfg-set-group-authority "fn.test" "")) *fn-cfg-default-stamp*))
(defconst *gat-c1* (fn-config-replay 0 510 (list *gat-r1*)))
(defconst *gat-c2* (fn-config-replay 0 510 (list *gat-r1* *gat-r2*)))
(defconst *gat-c3* (fn-config-replay 0 510 (list *gat-r1* *gat-r2* *gat-r3*)))
(defconst *gat-c4* (fn-config-replay 0 510 (list *gat-r1* *gat-r2* *gat-r3* *gat-r4*)))
(defun fn-gat-entry (cfg)
  (declare (xargs :guard t))
  (fn-cfg-group-find (fn-cfg-groups (fn-cfg-value cfg)) "fn.test"))
(assert-event (and (fn-cfgp *gat-c1*) (fn-cfgp *gat-c2*) (fn-cfgp *gat-c3*) (fn-cfgp *gat-c4*)
  (equal (fn-cfg-group-authority (fn-gat-entry *gat-c1*)) "")
  (equal (fn-cfg-group-authority (fn-gat-entry *gat-c2*)) *gat-hex-a*)
  (equal (fn-cfg-group-authority-gen (fn-gat-entry *gat-c2*)) 2)
  (equal (fn-cfg-group-authority (fn-gat-entry *gat-c3*)) *gat-hex-b*)
  (equal (fn-cfg-group-authority-gen (fn-gat-entry *gat-c3*)) 3)
  (equal (fn-cfg-group-authority (fn-gat-entry *gat-c4*)) "")
  (equal (fn-cfg-group-authority-gen (fn-gat-entry *gat-c4*)) 4)
  (equal (fn-cfg-group-policy-id (fn-gat-entry *gat-c4*)) "post-policy")))
; Literal PRF-1061 antecedent and every conjunct of the conclusion.
(assert-event
 (let* ((v (fn-cfg-value *gat-c1*))
        (old (fn-cfg-group-find (fn-cfg-groups v) "fn.test"))
        (new (fn-cfg-group-find (fn-cfg-groups (fn-cfg-apply-delta v 2 *fn-cfg-default-stamp*
                                 (fn-cfg-set-group-authority "fn.test" *gat-hex-a*))) "fn.test")))
  (and (consp old)
       (equal (fn-cfg-group-authority new) *gat-hex-a*)
       (equal (fn-cfg-group-authority-gen new) 2)
       (equal (fn-cfg-group-name new) (fn-cfg-group-name old))
       (equal (fn-cfg-group-created-gen new) (fn-cfg-group-created-gen old))
       (equal (fn-cfg-group-created-stamp new) (fn-cfg-group-created-stamp old))
       (equal (fn-cfg-group-retired-gen new) (fn-cfg-group-retired-gen old))
       (equal (fn-cfg-group-policy-id new) (fn-cfg-group-policy-id old))
       (equal (fn-cfg-group-next new) (fn-cfg-group-next old)))))
; The sole hypothesis removed: no group means no installed authority.
(assert-event
 (let* ((v (fn-cfg-empty-value))
        (old (fn-cfg-group-find (fn-cfg-groups v) "fn.test"))
        (new (fn-cfg-group-find (fn-cfg-groups (fn-cfg-apply-delta v 2 *fn-cfg-default-stamp*
                                 (fn-cfg-set-group-authority "fn.test" *gat-hex-a*))) "fn.test")))
  (and (not (consp old))
       (not (equal (fn-cfg-group-authority new) *gat-hex-a*)))))
(assert-event (and (equal (fn-cfg-kind-code :set-group-authority) 29)
                   (equal (fn-cfg-code-kind 29) :set-group-authority)
                   (equal (fn-cfg-decode-exact (fn-cfg-encode *gat-r2*))
                          (fn-record-parse-ok *gat-r2* nil))))
(defconst *gat-plan* (fn-native-admin-plan
 (list (fn-record-string-octets "group") (fn-record-string-octets "authority")
       (fn-record-string-octets "fn.test") (fn-record-string-octets *gat-hex-a*))))
(assert-event (equal (fn-native-admin-result-status *gat-plan*) :accepted))
(assert-event (equal (fn-native-admin-plan-deltas *gat-plan*)
                    (list (fn-cfg-set-group-authority "fn.test" *gat-hex-a*))))
(assert-event (equal (fn-native-admin-plan-deltas (fn-native-admin-plan
 (list (fn-record-string-octets "group") (fn-record-string-octets "authority")
       (fn-record-string-octets "fn.test") (fn-record-string-octets "ungoverned"))))
                    (list (fn-cfg-set-group-authority "fn.test" ""))))
(assert-event (equal (fn-cfg-delta-reason (fn-cfg-value *gat-c1*) 2 *fn-cfg-default-stamp* 0 510
  (fn-cfg-set-group-authority "fn.test" "bad")) :principal))
(assert-event (equal (fn-cfg-delta-reason (fn-cfg-value *gat-c1*) 2 *fn-cfg-default-stamp* 0 510
  (fn-cfg-set-group-authority "fn.missing" *gat-hex-a*)) :no-such-group))
(must-fail-checked (assert-event (equal (fn-cfg-group-authority (fn-gat-entry *gat-c3*)) *gat-hex-a*)))
