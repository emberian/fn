(in-package "ACL2")
(include-book "../../books/hybrid-store")
(include-book "../../books/codec-attach")
(include-book "../../books/crypto-attach")
(include-book "std/testing/assert-equal" :dir :system)

(defconst *hst-principal* (make-list 32 :initial-element 7))
(defconst *hst-ed-key* (make-list 32 :initial-element 11))
(defconst *hst-ml-key* (make-list 1952 :initial-element 13))
(defconst *hst-keys* (list (cons :ed25519 *hst-ed-key*)
                           (cons :ml-dsa-65 *hst-ml-key*)))
(defconst *hst-signatures* (list (cons :ed25519 (make-list 64 :initial-element 17))
                                 (cons :ml-dsa-65 (make-list 3309 :initial-element 19))))
(defconst *hst-source* '(65 13 10))
(defconst *hst-record*
  (fn-record-make 2 3 4 "<hybrid@example.invalid>" *hst-source* '("example")
                  "obligation" "subject" "release" 3 841000000))
(defconst *hst-record-octets* (fn-record-encode-impl *hst-record*))
(make-event `(defconst *hst-snapshot* ',(fn-hsig-keyring-snapshot *hst-principal* *hst-keys*)))

(defun hst-line (text)
  (append (fn-record-string-octets text) '(13 10)))

(defconst *hst-authored-source*
  (append (hst-line "From: author@example.invalid")
          (hst-line "Date: Wed, 23 Sep 2026 12:00:00 +0000")
          (hst-line "Newsgroups: example")
          (hst-line "Subject: exact source")
          (hst-line "Message-ID: <hybrid@example.invalid>")
          '(13 10 98 111 100 121 13 10)))

(assert-equal
 (fn-hsig-authored-source-fields *hst-authored-source*)
 (list "<hybrid@example.invalid>" (list "example")))
(assert-equal
 (fn-hsig-authored-source-fields
  (append (hst-line "From: author@example.invalid")
          (hst-line "Newsgroups: example")
          (hst-line "Subject: missing id") '(13 10)))
 nil)

; Version 1 retains exact signed source separately from the received wire
; projection.  The latter is the Store article payload and charge subject.
(make-event `(defconst *hst-carried-received*
               ',(fn-hc-render-at-most *fn-article-max-octets*
                                       *hst-authored-source* *hst-principal*
                                       *hst-keys* *hst-signatures*)))
(assert! *hst-carried-received*)
(assert! (not (equal *hst-carried-received* *hst-authored-source*)))
(make-event `(defconst *hst-carried-event*
               ',(fn-hsig-authorized-carried-submission-event
                  2 3 4 4 *hst-snapshot* "<hybrid@example.invalid>"
                  *hst-authored-source* *hst-carried-received* '("example")
                  "obligation" "subject" "release"
                  (fn-charge-for-payload (len *hst-carried-received*))
                  *hst-principal* *hst-keys* *hst-signatures* *hst-ml-key*
                  :verified :verified
                  (fn-clock-observation 1 841000000000 0 t))))
(assert! (fn-stxa-p *hst-carried-event*))
(assert-equal (fn-stxa-schema *hst-carried-event*) 1)
(assert-equal (fn-stxa-authored-source *hst-carried-event*)
              *hst-authored-source*)
(assert-equal (fn-stxa-authored-id *hst-carried-event*)
              (fn-hsig-authored-source-id *hst-authored-source*))
(assert! (fn-hsig-article-event-snapshot-bindsp
          *hst-carried-event*
          (fn-hsig-keyring-event 1 2 3 4 *hst-principal* *hst-keys*)))
(make-event `(defconst *hst-carried-wrong-id*
               ',(fn-stxa-make-carried
                  (fn-stxa-sequence *hst-carried-event*)
                  (fn-stxa-txid *hst-carried-event*)
                  (fn-stxa-generation *hst-carried-event*)
                  (fn-stxa-keyring-generation *hst-carried-event*)
                  (fn-stxa-profile *hst-carried-event*)
                  (fn-stxa-content-subject *hst-carried-event*)
                  (fn-stxa-article-record *hst-carried-event*)
                  (fn-stxa-verdict-event *hst-carried-event*)
                  (fn-stxa-authored-source *hst-carried-event*)
                  (make-list 32 :initial-element 0))))
(assert! (fn-stxa-bindsp *hst-carried-wrong-id*))
(assert-equal
 (fn-hsig-article-event-snapshot-bindsp
  *hst-carried-wrong-id*
  (fn-hsig-keyring-event 1 2 3 4 *hst-principal* *hst-keys*))
 nil)
(assert-equal
 (fn-hsig-article-event-snapshot-bindsp
  *hst-carried-event*
  (fn-hsig-keyring-event
   1 2 3 4 *hst-principal*
   (list (cons :ed25519 (make-list 32 :initial-element 23))
         (cons :ml-dsa-65 *hst-ml-key*))))
 nil)
(assert-equal
 (fn-hsig-authorized-carried-submission-event
  2 3 4 4 *hst-snapshot* "<hybrid@example.invalid>"
  (append *hst-authored-source* '(32)) *hst-carried-received* '("example")
  "obligation" "subject" "release"
  (fn-charge-for-payload (len *hst-carried-received*))
  *hst-principal* *hst-keys* *hst-signatures* *hst-ml-key*
  :verified :verified (fn-clock-observation 1 841000000000 0 t))
 nil)
(assert-equal
 (fn-hsig-authorized-carried-submission-event
  2 3 4 4 *hst-snapshot* "<hybrid@example.invalid>"
  *hst-authored-source* *hst-carried-received* '("example")
  "obligation" "subject" "release"
  (fn-charge-for-payload (len *hst-carried-received*))
  *hst-principal* *hst-keys* *hst-signatures* *hst-ml-key*
  :verified :invalid (fn-clock-observation 1 841000000000 0 t))
 nil)

(assert!
 (fn-stxa-p
  (fn-hsig-authorized-submission-event
   2 3 4 4 *hst-snapshot* "<hybrid@example.invalid>"
   *hst-authored-source* '("example") "obligation" "subject" "release"
   (fn-charge-for-payload (len *hst-authored-source*))
   *hst-principal* *hst-keys* *hst-signatures* *hst-ml-key*
   :verified :verified (fn-clock-observation 1 841000000000 0 t))))
(assert-equal
 (fn-record-stamp
  (fn-record-result-record
   (fn-record-decode-exact
    (fn-stxa-article-record
     (fn-hsig-authorized-submission-event
      2 3 4 4 *hst-snapshot* "<hybrid@example.invalid>"
      *hst-authored-source* '("example") "obligation" "subject" "release"
      (fn-charge-for-payload (len *hst-authored-source*))
      *hst-principal* *hst-keys* *hst-signatures* *hst-ml-key*
      :verified :verified (fn-clock-observation 1 841000000000 0 t))))))
 841000000)
(assert-equal
 (fn-hsig-authorized-submission-event
  2 3 4 4 *hst-snapshot* "<hybrid@example.invalid>"
  *hst-authored-source* '("example") "obligation" "subject" "release"
  (fn-charge-for-payload (len *hst-authored-source*))
  *hst-principal* *hst-keys* *hst-signatures* *hst-ml-key*
  :verified :verified (fn-clock-observation 1 0 0 nil))
 nil)
(assert-equal
 (fn-hsig-authorized-submission-event
  2 3 4 4 *hst-snapshot* "<conflict@example.invalid>"
  *hst-authored-source* '("example") "obligation" "subject" "release"
  (fn-charge-for-payload (len *hst-authored-source*))
  *hst-principal* *hst-keys* *hst-signatures* *hst-ml-key*
  :verified :verified (fn-clock-observation 1 841000000000 0 t))
 nil)
(assert-equal
 (fn-hsig-authorized-submission-event
  2 3 4 4 *hst-snapshot* "<hybrid@example.invalid>"
  *hst-authored-source* '("example") "obligation" "subject" "release" 1
  *hst-principal* *hst-keys* *hst-signatures* *hst-ml-key*
  :verified :verified (fn-clock-observation 1 841000000000 0 t))
 nil)

(assert! (fn-stxk-p
          (fn-hsig-keyring-event 1 2 3 4 *hst-principal* *hst-keys*)))

(make-event `(defconst *hst-event* ',(fn-hsig-authorized-article-event
   2 3 4 4 *hst-snapshot* "<hybrid@example.invalid>"
   (fn-record-string-octets "subject") *hst-record-octets*
   *hst-principal* *hst-keys* *hst-source* *hst-signatures* *hst-ml-key*
   :verified :verified)))

(assert! (fn-stxa-bindsp *hst-event*))
(assert! (fn-hsig-article-event-snapshot-bindsp
          *hst-event*
          (fn-hsig-keyring-event 1 2 3 4 *hst-principal* *hst-keys*)))
(assert-equal
 (fn-hsig-article-event-snapshot-bindsp
  *hst-event*
  (fn-hsig-keyring-event
   1 2 3 4 *hst-principal*
   (list (cons :ed25519 (make-list 32 :initial-element 23))
         (cons :ml-dsa-65 (make-list 1952 :initial-element 29)))))
 nil)
(assert-equal
 (fn-hsig-authorized-article-event
  2 3 4 4 *hst-snapshot* "<hybrid@example.invalid>"
  (fn-record-string-octets "subject") *hst-record-octets*
  *hst-principal* *hst-keys* *hst-source* *hst-signatures* *hst-ml-key*
  :verified :invalid)
 nil)
(assert-equal
 (fn-hsig-authorized-article-event
  2 3 4 4 *hst-snapshot* "<hybrid@example.invalid>"
  (fn-record-string-octets "subject") *hst-record-octets*
  *hst-principal* *hst-keys* '(65 13 10 0) *hst-signatures* *hst-ml-key*
  :verified :verified)
 nil)

(assert-equal
 (fn-hsig-authorized-article-event
  2 3 4 4 (append *hst-snapshot* '(0)) "<hybrid@example.invalid>"
  (fn-record-string-octets "subject") *hst-record-octets*
  *hst-principal* *hst-keys* *hst-source* *hst-signatures* *hst-ml-key*
  :verified :verified)
 nil)
