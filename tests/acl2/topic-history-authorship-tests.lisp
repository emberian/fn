(in-package "ACL2")
(include-book "../../books/topic-history-authorship")
(include-book "../../books/codec-attach")
(include-book "../../books/crypto-attach")
(include-book "std/testing/must-fail" :dir :system)

(defconst *tha-principal* (make-list 32 :initial-element 7))
(defconst *tha-other-principal* (make-list 32 :initial-element 8))
(defconst *tha-ed-key* (make-list 32 :initial-element 11))
(defconst *tha-ml-key* (make-list 1952 :initial-element 13))
(defconst *tha-keys* (list (cons :ed25519 *tha-ed-key*)
                          (cons :ml-dsa-65 *tha-ml-key*)))
(defconst *tha-other-keys*
  (list (cons :ed25519 (make-list 32 :initial-element 12))
        (cons :ml-dsa-65 *tha-ml-key*)))
(defconst *tha-signatures*
  (list (cons :ed25519 (make-list 64 :initial-element 17))
        (cons :ml-dsa-65 (make-list 3309 :initial-element 19))))
(make-event `(defconst *tha-author*
               ',(fn-th-verified-author-ref *tha-principal* *tha-keys*)))
(assert-event (fn-th-author-p *tha-author*))
(defconst *tha-root*
  (list :root (make-list 32 :initial-element 1)
        (first *tha-author*) (second *tha-author*)
        '(109 105 110 105) (list *tha-author*)))
(defconst *tha-report*
  (list :report (second *tha-author*) (second *tha-author*) nil))
(defun tha-line (text)
  (declare (xargs :guard t))
  (append (fn-record-string-octets text) '(13 10)))
(defun tha-source (metadata from)
  (declare (xargs :guard t))
  (append (tha-line from)
          (tha-line "Date: Wed, 23 Sep 2026 12:00:00 +0000")
          (tha-line "Newsgroups: fn.test")
          (tha-line "Subject: topic")
          (tha-line "Message-ID: <topic-binding@example.invalid>")
          (fn-th-field-wire metadata) '(13 10 98 111 100 121 13 10)))
(make-event `(defconst *tha-root-source*
               ',(tha-source *tha-root* "From: claimed@example.invalid")))
(make-event `(defconst *tha-report-source*
               ',(tha-source *tha-report* "From: false@example.invalid")))
(assert-event (fn-th-value-p *tha-root*))
(assert-event
 (equal (fn-th-select-verified-source *tha-root-source*
                                      *tha-principal* *tha-keys*)
        (fn-stmt-ok (list *tha-root* *tha-author* :controller-matched))))
(assert-event
 (equal (fn-th-select-verified-source *tha-root-source*
                                      *tha-other-principal* *tha-keys*)
        (fn-stmt-ok
         (list *tha-root*
               (fn-th-verified-author-ref *tha-other-principal* *tha-keys*)
               :controller-mismatch))))
(assert-event
 (equal (fn-th-at 2 (fn-stmt-value
                       (fn-th-select-verified-source
                        *tha-root-source* *tha-principal* *tha-other-keys*)))
        :controller-mismatch))
; A report's author is the verified context despite a contradictory From.
(assert-event
 (equal (fn-th-select-verified-source *tha-report-source*
                                      *tha-principal* *tha-keys*)
        (fn-stmt-ok (list *tha-report* *tha-author* :not-root))))
(assert-event
 (equal (fn-th-at 1 (fn-stmt-value
                       (fn-th-select-verified-source
                        (tha-source *tha-report* "From: other@example.invalid")
                        *tha-principal* *tha-keys*)))
        *tha-author*))
; Relay-authored-looking fields cannot change the selector's exact source.
(assert-event
 (let ((received (append (tha-line "Path: relay.example!fn")
                         (tha-line "FN-Topic: v1 AAAA")
                         *tha-report-source*)))
   (and (equal (fn-th-at 1 (fn-stmt-value
                           (fn-th-select-verified-source
                            *tha-report-source* *tha-principal* *tha-keys*)))
               *tha-author*)
        (not (fn-stmt-okp
              (fn-th-select-verified-source received *tha-principal*
                                            *tha-keys*))))))

(make-event `(defconst *tha-snapshot-octets*
               ',(fn-hsig-keyring-snapshot *tha-principal* *tha-keys*)))
(make-event `(defconst *tha-received*
               ',(fn-hc-render-at-most *fn-article-max-octets*
                                       *tha-root-source* *tha-principal*
                                       *tha-keys* *tha-signatures*)))
(make-event `(defconst *tha-received-id*
               ',(fn-id-subject-of-payload *tha-received*)))
(defconst *tha-received-subject*
  (fn-record-octets-string (fn-id-text *tha-received-id*)))
(make-event `(defconst *tha-obligation*
               ',(fn-record-octets-string
                  (fn-id-text
                   (fn-id-obligation-of
                    (fn-record-string-octets "<topic-binding@example.invalid>")
                    *tha-received-id*)))))
(make-event `(defconst *tha-event*
               ',(fn-hsig-authorized-carried-submission-event
                  2 3 4 4 *tha-snapshot-octets*
                  "<topic-binding@example.invalid>" *tha-root-source*
                  *tha-received* '("fn.test") *tha-obligation*
                  *tha-received-subject* "release"
                  (fn-charge-for-payload (len *tha-received*))
                  *tha-principal* *tha-keys* *tha-signatures* *tha-ml-key*
                  :verified :verified
                  (fn-clock-observation 1 841000000000 0 t))))
(make-event `(defconst *tha-snapshot*
               ',(fn-hsig-keyring-event 1 2 3 4 *tha-principal* *tha-keys*)))
(assert-event (fn-stxa-p *tha-event*))
(assert-event (fn-hsig-article-event-snapshot-bindsp-v1
               *tha-event* *tha-snapshot*))
(assert-event
 (equal (fn-th-select-accepted-event *tha-event* *tha-snapshot*)
        (fn-stmt-ok (list *tha-root* *tha-author* :controller-matched))))
(assert-event
 (equal (fn-th-select-accepted-event
         *tha-event*
         (fn-hsig-keyring-event 1 2 3 4 *tha-other-principal* *tha-keys*))
        (fn-stmt-error :unbound-event)))
(assert-event
 (equal (fn-th-select-accepted-event
         (fn-stxa-make-carried
          2 3 4 4 *fn-hsig-profile-tag*
          (fn-stxa-content-subject *tha-event*)
          (fn-stxa-article-record *tha-event*)
          (fn-stxa-verdict-event *tha-event*)
          *tha-report-source* (fn-hsig-authored-source-id *tha-report-source*))
         *tha-snapshot*)
        (fn-stmt-error :unbound-event)))
; If the verified principal or exact key set hypothesis is removed, the
; matching-root conclusion has executable counterexamples above.
(must-fail
 (defthm tha-root-match-ignores-principal
   (equal (fn-th-at 2 (fn-stmt-value
                       (fn-th-select-verified-source
                        *tha-root-source* *tha-other-principal* *tha-keys*)))
          :controller-matched)))
(must-fail
 (defthm tha-root-match-ignores-keys
   (equal (fn-th-at 2 (fn-stmt-value
                       (fn-th-select-verified-source
                        *tha-root-source* *tha-principal* *tha-other-keys*)))
          :controller-matched)))
(must-fail
 (defthm tha-accepted-ignores-snapshot
   (fn-stmt-okp
    (fn-th-select-accepted-event
     *tha-event*
     (fn-hsig-keyring-event 1 2 3 4 *tha-other-principal* *tha-keys*)))))
