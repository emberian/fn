; Experimental topic root and report admission through the actual Store
; reserve/publish/finish path and exact T10 accepted-source events.
(in-package "ACL2")
(include-book "../../books/store-node")
(include-book "topic-history-local-admin-tests")
(include-book "topic-history-admission-tests")
(include-book "std/testing/must-fail" :dir :system)

(defun thsn-reserve (s)
  (fn-sn-io (fn-sn-io (fn-sn-io (fn-sn-io s :start-frontier nil)
                                :frontier-file :ok)
                      :frontier-replace :ok)
            :frontier-directory :ok))
(defun thsn-publish (s)
  (fn-sn-io (fn-sn-io (fn-sn-io s :record-file :ok)
                      :record-link :ok)
            :record-directory :ok))
(defun thsn-topic-commit (s event)
  (fn-sn-finish (thsn-publish (fn-sn-prepare-topic (thsn-reserve s) event))))
(defun thsn-identity-commit (s event)
  (fn-sn-finish (thsn-publish (fn-sn-prepare-identity (thsn-reserve s) event))))

(defconst *thsn-initial* (fn-sn-initial '("fn.test") 32))
(make-event `(defconst *thsn-snapshot*
               ',(fn-hsig-keyring-event 0 0 0 1 *tha-principal* *tha-keys*)))
(make-event `(defconst *thsn-enrolled*
               ',(thsn-identity-commit *thsn-initial* *thsn-snapshot*)))
(assert-event (equal (fn-th-at 1 (fn-sn-topic *thsn-enrolled*)) 1))
(make-event `(defconst *thsn-root-event*
               ',(fn-hsig-authorized-carried-submission-event
                  1 1 1 1 *tha-snapshot-octets*
                  "<topic-binding@example.invalid>" *tha-root-source*
                  *tha-received* '("fn.test") *tha-obligation*
                  *tha-received-subject* "release"
                  (fn-charge-for-payload (len *tha-received*))
                  *tha-principal* *tha-keys* *tha-signatures* *tha-ml-key*
                  :verified :verified
                  (fn-clock-observation 1 841000000000 0 t))))
(assert-event (fn-stxa-p *thsn-root-event*))
(make-event `(defconst *thsn-root-accepted*
               ',(thsn-identity-commit *thsn-enrolled* *thsn-root-event*)))
(assert-event (equal (fn-th-at 1 (fn-sn-topic *thsn-root-accepted*)) 2))
(assert-event (equal (len (fn-th-at 3 (fn-sn-topic *thsn-root-accepted*))) 1))

(defconst *thsn-install-result*
  (fn-th-local-admin-install 2 2 2 501 *thla-id* nil))
(assert-event (fn-stmt-okp *thsn-install-result*))
(defconst *thsn-install* (fn-stmt-value *thsn-install-result*))
(make-event `(defconst *thsn-installed*
               ',(thsn-topic-commit *thsn-root-accepted* *thsn-install*)))
(assert-event (equal (fn-th-at 5 (fn-sn-topic *thsn-installed*))
                     *thsn-install*))
(assert-event (equal (fn-sf-successes (fn-sn-files *thsn-installed*))
                     '((0 . 0) (1 . 1) (2 . 2))))
(assert-event (equal (len (fn-stx-store (fn-sn-node *thsn-installed*))) 1))
(assert-event (equal (fn-sn-prepare-topic
                      (thsn-reserve *thsn-installed*)
                      (list :topic-admin-install 3 3 3 501 *thla-id*))
                     (thsn-reserve *thsn-installed*)))

(make-event `(defconst *thsn-anchor-result*
               ',(fn-th-prepare-anchor-local
                  3 3 3 *thsn-root-event* *thsn-snapshot* 501 2
                  *thsn-install* nil)))
(assert-event (fn-stmt-okp *thsn-anchor-result*))
(defconst *thsn-anchor* (fn-stmt-value *thsn-anchor-result*))
(assert-event (equal (fn-th-at 8 *thsn-anchor*) 2))
(assert-event
 (equal (fn-sn-prepare-topic
         (thsn-reserve *thsn-installed*)
         (fn-th-anchor-v1-fields *thsn-anchor*))
        (thsn-reserve *thsn-installed*)))
(make-event `(defconst *thsn-anchored*
               ',(thsn-topic-commit *thsn-installed* *thsn-anchor*)))
(assert-event (equal (fn-th-at 0 (fn-sn-topic *thsn-anchored*)) :ok))
(assert-event (equal (len (fn-th-at 4 (fn-sn-topic *thsn-anchored*))) 1))
(assert-event (equal (fn-th-at 8 (fn-th-find-anchor *thad-topic*
                                                   (fn-th-at 4 (fn-sn-topic *thsn-anchored*))))
                     2))
(assert-event (equal (len (fn-stx-store (fn-sn-node *thsn-anchored*))) 1))
(assert-event (equal (fn-sf-successes (fn-sn-files *thsn-anchored*))
                     '((0 . 0) (1 . 1) (2 . 2) (3 . 3))))

; A second exact authored source is accepted by T10 before its report can be
; admitted. Relay headers and report metadata cannot fill this history slot.
(make-event `(defconst *thsn-report-event*
               ',(fn-hsig-authorized-carried-submission-event
                  4 4 4 1 *tha-snapshot-octets*
                  "<report-binding@example.invalid>" *thad-report-source*
                  *thad-received* '("fn.test") *thad-obligation*
                  *thad-subject* "release"
                  (fn-charge-for-payload (len *thad-received*))
                  *tha-principal* *tha-keys* *tha-signatures* *tha-ml-key*
                  :verified :verified
                  (fn-clock-observation 1 841000000000 0 t))))
(assert-event (fn-stxa-p *thsn-report-event*))
(make-event `(defconst *thsn-report-accepted*
               ',(thsn-identity-commit *thsn-anchored* *thsn-report-event*)))
(assert-event (equal (fn-th-at 1 (fn-sn-topic *thsn-report-accepted*)) 5))
(make-event `(defconst *thsn-admit-result*
               ',(fn-th-prepare-report
                  5 5 5 *thsn-report-event* *thsn-snapshot*
                  (fn-th-at 4 (fn-sn-topic *thsn-report-accepted*)))))
(assert-event (fn-stmt-okp *thsn-admit-result*))
(defconst *thsn-admit* (fn-stmt-value *thsn-admit-result*))
(make-event `(defconst *thsn-admitted*
               ',(thsn-topic-commit *thsn-report-accepted* *thsn-admit*)))
(assert-event (equal (fn-th-at 0 (fn-sn-topic *thsn-admitted*)) :ok))
(assert-event (equal (fn-th-at 1 (fn-sn-topic *thsn-admitted*)) 6))
(assert-event (equal (fn-th-at 8 (fn-th-find-anchor *thad-topic*
                                                   (fn-th-at 4 (fn-sn-topic *thsn-admitted*))))
                     1))
(assert-event (equal (len (fn-stx-store (fn-sn-node *thsn-admitted*))) 2))
(assert-event (equal (fn-sf-successes (fn-sn-files *thsn-admitted*))
                     '((0 . 0) (1 . 1) (2 . 2) (3 . 3) (4 . 4) (5 . 5))))
; The same root with a different local UID cannot obtain an anchor event.
(assert-event (equal (fn-th-prepare-anchor-local
                      6 6 6 *thsn-root-event* *thsn-snapshot* 502 2
                      *thsn-install* nil)
                     (fn-stmt-error :administrator)))
; A malformed topic envelope cannot enter the reserved Store publication.
(assert-event (equal (fn-sn-prepare-topic
                      (thsn-reserve *thsn-admitted*)
                      (list :topic-admit 6 6 6 *thad-topic*))
                     (thsn-reserve *thsn-admitted*)))
(must-fail
 (assert-event
  (equal (fn-th-at 1
                   (fn-sn-topic
                    (thsn-topic-commit *thsn-admitted*
                     (list :topic-admit 6 6 6 *thad-topic*))))
         7)))
