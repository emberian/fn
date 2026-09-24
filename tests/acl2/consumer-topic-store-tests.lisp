; Reachable E2 consumer progress through P3 topic admission and observed reopen.
; The two Store event families share one dense journal, but topic records must
; not advance a consumer's declared ACK or lose its carried projection.
(in-package "ACL2")
(include-book "../../books/consumer-store-invariants")
(include-book "consumer-store-node-tests")
(include-book "topic-history-store-node-tests")

(defconst *cts-initial* (fn-sn-initial '("fn.test") 32))
(defconst *cts-booted* (csnt-commit *cts-initial* *csnt-boot*))
(defconst *cts-registered* (csnt-commit *cts-booted* *csnt-reg*))
(assert-event (fn-csi-livep *cts-registered*))
(assert-event (equal (fn-sf-records (fn-sn-files *cts-registered*))
                     (list *csnt-boot* *csnt-reg*)))

; T10 enrollment and two accepted sources are constructed with the existing
; verified-carrier fixture, at the next actual Store coordinates.
(make-event `(defconst *cts-snapshot*
               ',(fn-hsig-keyring-event 2 2 2 1 *tha-principal* *tha-keys*)))
(make-event `(defconst *cts-enrolled*
               ',(thsn-identity-commit *cts-registered* *cts-snapshot*)))
(make-event `(defconst *cts-root-event*
               ',(fn-hsig-authorized-carried-submission-event
                  3 3 3 1 *tha-snapshot-octets*
                  "<topic-binding@example.invalid>" *tha-root-source*
                  *tha-received* '("fn.test") *tha-obligation*
                  *tha-received-subject* "release"
                  (fn-charge-for-payload (len *tha-received*))
                  *tha-principal* *tha-keys* *tha-signatures* *tha-ml-key*
                  :verified :verified
                  (fn-clock-observation 1 841000000000 0 t))))
(make-event `(defconst *cts-root-accepted*
               ',(thsn-identity-commit *cts-enrolled* *cts-root-event*)))
(assert-event (equal (fn-sf-phase (fn-sn-files *cts-root-accepted*)) :ready))

; The missing general-proof branch is a valid topic admin proposal at the
; actual decoded dispatcher, stopped before and after the durable finish.
(defconst *cts-install-result*
  (fn-th-local-admin-install 4 4 4 501 *thla-id* nil))
(assert-event (fn-stmt-okp *cts-install-result*))
(defconst *cts-install* (fn-stmt-value *cts-install-result*))
(defconst *cts-admin-reserved* (thsn-reserve *cts-root-accepted*))
(assert-event (and (fn-csi-livep *cts-admin-reserved*)
                   (equal (fn-sf-phase (fn-sn-files *cts-admin-reserved*))
                          :reserved)))
(defconst *cts-admin-staged*
  (fn-snrt-step *cts-admin-reserved* (list :prepare-topic *cts-install*)))
(assert-event (equal (fn-sf-phase (fn-sn-files *cts-admin-staged*))
                     :record-staged))
(assert-event (fn-csi-livep *cts-admin-staged*))
(assert-event (equal (fn-sn-consumer *cts-admin-staged*)
                     (fn-sn-consumer *cts-registered*)))
(make-event `(defconst *cts-installed*
               ',(fn-sn-finish (thsn-publish *cts-admin-staged*))))
(assert-event (and (fn-csi-livep *cts-installed*)
                   (fn-csi-full-relationp *cts-installed*)
                   (equal (fn-th-at 5 (fn-sn-topic *cts-installed*))
                          *cts-install*)))

(make-event `(defconst *cts-anchor-result*
               ',(fn-th-prepare-anchor-local
                  5 5 5 *cts-root-event* *cts-snapshot* 501 2
                  *cts-install* nil)))
(assert-event (fn-stmt-okp *cts-anchor-result*))
(defconst *cts-anchor* (fn-stmt-value *cts-anchor-result*))
(make-event `(defconst *cts-anchored*
               ',(thsn-topic-commit *cts-installed* *cts-anchor*)))
(make-event `(defconst *cts-report-event*
               ',(fn-hsig-authorized-carried-submission-event
                  6 6 6 1 *tha-snapshot-octets*
                  "<report-binding@example.invalid>" *thad-report-source*
                  *thad-received* '("fn.test") *thad-obligation*
                  *thad-subject* "release"
                  (fn-charge-for-payload (len *thad-received*))
                  *tha-principal* *tha-keys* *tha-signatures* *tha-ml-key*
                  :verified :verified
                  (fn-clock-observation 1 841000000000 0 t))))
(make-event `(defconst *cts-report-accepted*
               ',(thsn-identity-commit *cts-anchored* *cts-report-event*)))
(make-event `(defconst *cts-admit-result*
               ',(fn-th-prepare-report
                  7 7 7 *cts-report-event* *cts-snapshot*
                  (fn-th-at 4 (fn-sn-topic *cts-report-accepted*)))))
(assert-event (fn-stmt-okp *cts-admit-result*))
(defconst *cts-admit* (fn-stmt-value *cts-admit-result*))
(make-event `(defconst *cts-admitted*
               ',(thsn-topic-commit *cts-report-accepted* *cts-admit*)))

; Topic records, including two accepted T10 articles, consume Store sequence
; places but never declare application processing for this consumer.
(assert-event (and (fn-csi-livep *cts-admitted*)
                   (fn-csi-full-relationp *cts-admitted*)
                   (equal (len (fn-sf-records (fn-sn-files *cts-admitted*))) 8)
                   (equal (len (fn-stx-store (fn-sn-node *cts-admitted*))) 2)
                   (equal (fn-cp-nth 3 (fn-sn-consumer *cts-admitted*)) 8)
                   (equal (fn-cp-nth 7
                            (fn-cp-find '(3)
                             (fn-cp-nth 5 (fn-sn-consumer *cts-admitted*)))) 0)))
(assert-event
 (equal (fn-cpe-projection-replay
         nil (fn-sf-records (fn-sn-files *cts-admitted*)) 0)
        (list :ok (fn-sn-consumer *cts-admitted*))))

(defconst *cts-open*
  (fn-sn-open-observed '("fn.test") 32 8
                       (fn-sf-records (fn-sn-files *cts-admitted*))))
(assert-event (fn-sn-open-okp *cts-open*))
(defconst *cts-reopened* (fn-sn-open-state *cts-open*))
(assert-event (and (fn-csi-full-relationp *cts-reopened*)
                   (equal (fn-sn-consumer *cts-reopened*)
                          (fn-sn-consumer *cts-admitted*))
                   (equal (fn-cp-nth 7
                            (fn-cp-find '(3)
                             (fn-cp-nth 5 (fn-sn-consumer *cts-reopened*)))) 0)))
