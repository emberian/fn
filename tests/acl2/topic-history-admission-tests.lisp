(in-package "ACL2")
(include-book "../../books/topic-history-admission")
(include-book "topic-history-authorship-tests")
(include-book "std/testing/must-fail" :dir :system)

(defconst *thad-topic* (fn-stxa-authored-id *tha-event*))
(defconst *thad-report* (list :report *thad-topic* *thad-topic* nil))
(defun thad-source (metadata msgid)
  (declare (xargs :guard t))
  (append (tha-line "From: impersonator@example.invalid")
          (tha-line "Date: Wed, 23 Sep 2026 12:01:00 +0000")
          (tha-line "Newsgroups: fn.test")
          (tha-line "Subject: report")
          (tha-line msgid)
          (fn-th-field-wire metadata) '(13 10 98 111 100 121 13 10)))
; Test-only ACL2 constructor: the source, received carrier, identities and
; T10 accepted event all come from the executable model, not a host twin.
(defun thad-accepted (source principal sequence txid)
  (declare (xargs :guard t :verify-guards nil))
  (let* ((received (fn-hc-render-at-most
                    *fn-article-max-octets* source principal
                    *tha-keys* *tha-signatures*))
         (subject-id (fn-id-subject-of-payload received))
         (subject (fn-record-octets-string (fn-id-text subject-id)))
         (fields (fn-hsig-authored-source-fields source))
         (msgid (car fields))
         (groups (cadr fields))
         (obligation (fn-record-octets-string
                      (fn-id-text
                       (fn-id-obligation-of
                        (fn-record-string-octets msgid) subject-id)))))
    (fn-hsig-authorized-carried-submission-event
     sequence txid 7 4
     (fn-hsig-keyring-snapshot principal *tha-keys*)
     msgid source received groups obligation subject "release"
     (fn-charge-for-payload (len received))
     principal *tha-keys* *tha-signatures* *tha-ml-key*
     :verified :verified (fn-clock-observation 1 841000000000 0 t))))
(make-event `(defconst *thad-report-source*
               ',(thad-source *thad-report*
                              "Message-ID: <report-binding@example.invalid>")))
(make-event `(defconst *thad-received*
               ',(fn-hc-render-at-most *fn-article-max-octets*
                                       *thad-report-source* *tha-principal*
                                       *tha-keys* *tha-signatures*)))
(make-event `(defconst *thad-received-id*
               ',(fn-id-subject-of-payload *thad-received*)))
(defconst *thad-subject*
  (fn-record-octets-string (fn-id-text *thad-received-id*)))
(make-event `(defconst *thad-obligation*
               ',(fn-record-octets-string
                  (fn-id-text
                   (fn-id-obligation-of
                    (fn-record-string-octets "<report-binding@example.invalid>")
                    *thad-received-id*)))))
(make-event `(defconst *thad-event*
               ',(fn-hsig-authorized-carried-submission-event
                  5 6 7 4 *tha-snapshot-octets*
                  "<report-binding@example.invalid>" *thad-report-source*
                  *thad-received* '("fn.test") *thad-obligation*
                  *thad-subject* "release"
                  (fn-charge-for-payload (len *thad-received*))
                  *tha-principal* *tha-keys* *tha-signatures* *tha-ml-key*
                  :verified :verified
                  (fn-clock-observation 1 841000000000 0 t))))
(assert-event (fn-stxa-p *thad-event*))
(assert-event (fn-hsig-article-event-snapshot-bindsp-v1
               *thad-event* *tha-snapshot*))

(make-event `(defconst *thad-anchor-prepared*
               ',(fn-th-prepare-anchor 8 9 10 *tha-event* *tha-snapshot*
                                        *tha-principal* *tha-principal* 2 nil)))
(assert-event (fn-stmt-okp *thad-anchor-prepared*))
(defconst *thad-anchor-event* (fn-stmt-value *thad-anchor-prepared*))
(make-event `(defconst *thad-anchored*
               ',(fn-th-commit-anchor *thad-anchor-event* *tha-event*
                                      *tha-snapshot* *tha-principal* nil)))
(assert-event (fn-stmt-okp *thad-anchored*))
(assert-event (equal (fn-th-at 8
                      (fn-th-find-anchor *thad-topic*
                                         (fn-stmt-value *thad-anchored*)))
                     2))
(assert-event
 (equal (fn-th-prepare-anchor 8 9 10 *tha-event* *tha-snapshot*
                              *tha-other-principal* *tha-principal* 2 nil)
        (fn-stmt-error :administrator)))
(assert-event
 (equal (fn-th-prepare-anchor 8 9 10 *tha-event* *tha-snapshot*
                              *tha-principal* *tha-principal* 0 nil)
        (fn-stmt-error :quota)))
(assert-event
 (equal (fn-th-prepare-anchor 8 9 10 *tha-event* *tha-snapshot*
                              *tha-principal* *tha-principal* 2
                              (fn-stmt-value *thad-anchored*))
        (fn-stmt-error :already-anchored)))
(assert-event
 (equal (fn-th-commit-anchor
         *thad-anchor-event* *tha-event*
         (fn-hsig-keyring-event 1 2 3 4 *tha-other-principal* *tha-keys*)
         *tha-principal* nil)
        (fn-stmt-error :anchor-event)))

(make-event `(defconst *thad-report-prepared*
               ',(fn-th-prepare-report 11 12 13 *thad-event* *tha-snapshot*
                                        (fn-stmt-value *thad-anchored*))))
(assert-event (fn-stmt-okp *thad-report-prepared*))
(defconst *thad-report-event* (fn-stmt-value *thad-report-prepared*))
(make-event `(defconst *thad-admitted*
               ',(fn-th-commit-report *thad-report-event* *thad-event*
                                      *tha-snapshot*
                                      (fn-stmt-value *thad-anchored*))))
(assert-event (fn-stmt-okp *thad-admitted*))
(assert-event
 (let ((anchor (fn-th-find-anchor *thad-topic* (fn-stmt-value *thad-admitted*))))
   (and (equal (fn-th-at 8 anchor) 1)
        (equal (fn-th-at 2 (car (fn-th-anchor-reports anchor)))
               (fn-stxa-authored-id *thad-event*))
        (equal (fn-th-at 3 (car (fn-th-anchor-reports anchor)))
               *thad-topic*))))
; An exact retry returns the old admission without a new event or charge.
(assert-event
 (equal (car (fn-th-prepare-report 99 100 101 *thad-event*
                                      *tha-snapshot*
                                      (fn-stmt-value *thad-admitted*)))
        :replayed-historical))
(assert-event
 (equal (fn-th-prepare-report 11 12 13 *thad-event* *tha-snapshot* nil)
        (fn-stmt-error :unanchored)))
(assert-event
 (equal (fn-th-prepare-report
         11 12 13 *thad-event*
         (fn-hsig-keyring-event 1 2 3 4 *tha-other-principal* *tha-keys*)
         (fn-stmt-value *thad-anchored*))
        (fn-stmt-error :authorship)))
; A distinct verified signer with the same ML key is not on this root roster.
(make-event `(defconst *thad-stranger-source*
               ',(thad-source *thad-report*
                              "Message-ID: <stranger@example.invalid>")))
(make-event `(defconst *thad-stranger-event*
               ',(thad-accepted *thad-stranger-source*
                                *tha-other-principal* 14 15)))
(make-event `(defconst *thad-stranger-snapshot*
               ',(fn-hsig-keyring-event 1 2 3 4
                                       *tha-other-principal* *tha-keys*)))
(assert-event (fn-stxa-p *thad-stranger-event*))
(assert-event
 (equal (fn-th-prepare-report 16 17 18 *thad-stranger-event*
                              *thad-stranger-snapshot*
                              (fn-stmt-value *thad-anchored*))
        (fn-stmt-error :not-author)))
; A syntactically valid parent must have an earlier admission in this topic.
(defconst *thad-parent-report*
  (list :report *thad-topic* *thad-topic* (list *thad-topic*)))
(make-event `(defconst *thad-parent-source*
               ',(thad-source *thad-parent-report*
                              "Message-ID: <missing-parent@example.invalid>")))
(make-event `(defconst *thad-parent-event*
               ',(thad-accepted *thad-parent-source* *tha-principal* 19 20)))
(assert-event (fn-stxa-p *thad-parent-event*))
(assert-event
 (equal (fn-th-prepare-report 21 22 23 *thad-parent-event*
                              *tha-snapshot* (fn-stmt-value *thad-anchored*))
        (fn-stmt-error :parents)))
; A finite one-report reservation is consumed only by committed admission.
(make-event `(defconst *thad-one-anchor-prepared*
               ',(fn-th-prepare-anchor 8 9 10 *tha-event* *tha-snapshot*
                                        *tha-principal* *tha-principal* 1 nil)))
(make-event `(defconst *thad-one-anchored*
               ',(fn-th-commit-anchor
                  (fn-stmt-value *thad-one-anchor-prepared*)
                  *tha-event* *tha-snapshot* *tha-principal* nil)))
(make-event `(defconst *thad-one-admitted*
               ',(fn-th-commit-report
                  (fn-stmt-value
                   (fn-th-prepare-report 11 12 13 *thad-event* *tha-snapshot*
                                         (fn-stmt-value *thad-one-anchored*)))
                  *thad-event* *tha-snapshot*
                  (fn-stmt-value *thad-one-anchored*))))
(assert-event (fn-stmt-okp *thad-one-admitted*))
(make-event `(defconst *thad-second-source*
               ',(thad-source *thad-report*
                              "Message-ID: <second-report@example.invalid>")))
(make-event `(defconst *thad-second-event*
               ',(thad-accepted *thad-second-source* *tha-principal* 24 25)))
(assert-event (fn-stxa-p *thad-second-event*))
(assert-event
 (equal (fn-th-prepare-report 26 27 28 *thad-second-event*
                              *tha-snapshot* (fn-stmt-value *thad-one-admitted*))
        (fn-stmt-error :quota)))
(assert-event
 (equal (car (fn-th-prepare-report 26 27 28 *thad-event* *tha-snapshot*
                                      (fn-stmt-value *thad-one-admitted*)))
        :replayed-historical))
; A prepared event alone leaves both quota and admissions unchanged.
(assert-event
 (let ((anchor (fn-th-find-anchor *thad-topic*
                                  (fn-stmt-value *thad-anchored*))))
   (and (equal (fn-th-at 8 anchor) 2)
        (null (fn-th-anchor-reports anchor)))))
(must-fail
 (defthm thad-anchor-without-admin
   (fn-stmt-okp
    (fn-th-prepare-anchor 8 9 10 *tha-event* *tha-snapshot*
                          *tha-other-principal* *tha-principal* 2 nil))))
(must-fail
 (defthm thad-report-without-anchor
   (fn-stmt-okp
    (fn-th-prepare-report 11 12 13 *thad-event* *tha-snapshot* nil))))
(must-fail
 (defthm thad-report-without-roster-membership
   (fn-stmt-okp
    (fn-th-prepare-report 16 17 18 *thad-stranger-event*
                          *thad-stranger-snapshot*
                          (fn-stmt-value *thad-anchored*)))))
(must-fail
 (defthm thad-report-without-parent-admission
   (fn-stmt-okp
    (fn-th-prepare-report 21 22 23 *thad-parent-event*
                          *tha-snapshot* (fn-stmt-value *thad-anchored*)))))
(must-fail
 (defthm thad-report-without-quota
   (fn-stmt-okp
    (fn-th-prepare-report 26 27 28 *thad-second-event*
                          *tha-snapshot* (fn-stmt-value *thad-one-admitted*)))))
