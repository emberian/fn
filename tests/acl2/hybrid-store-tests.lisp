(in-package "ACL2")
(include-book "../../books/hybrid-store-invariants")
(include-book "../../books/codec-attach")
(include-book "../../books/crypto-attach")
(include-book "std/testing/assert-equal" :dir :system)
(include-book "std/testing/must-fail" :dir :system)

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

; Native local authorship injects the portable carrier through the same
; ACL2 news agent as POST.  The signed source remains an exact suffix, while
; Path and the two injection trace fields precede the carrier.
(defconst *hst-injection-config*
  (fn-inj-make-config
   t (fn-record-string-octets "author.example.invalid")
   (list (fn-record-string-octets "example")) *fn-article-max-octets*))
(defconst *hst-injection-observation*
  (fn-clock-observation 1 841000000000 0 t))
(make-event `(defconst *hst-injected-received*
               ',(fn-hsig-injected-carrier-octets
                  *hst-authored-source* *hst-principal* *hst-keys*
                  *hst-signatures* *hst-injection-config*
                  *hst-injection-observation*)))
(assert! *hst-injected-received*)
(assert! (fn-inj-suffixp *hst-authored-source* *hst-injected-received*))
(assert! (not (equal (fn-inj-strip
                     (fn-inj-path-line
                      (fn-record-string-octets "author.example.invalid"))
                     *hst-injected-received*)
                    :no)))
(assert! (fn-hc-okp (fn-hc-received-plan *hst-injected-received*)))
(assert-equal (car (fn-hc-value (fn-hc-received-plan *hst-injected-received*)))
              *hst-authored-source*)
(assert! (equal (fn-hc-render-at-most *fn-article-max-octets*
                                      *hst-authored-source* *hst-principal*
                                      *hst-keys* *hst-signatures*)
                *hst-carried-received*))
(assert-equal
 (fn-hsig-injected-carrier-octets
  *hst-authored-source* *hst-principal* *hst-keys* *hst-signatures*
  (fn-inj-make-config nil (fn-record-string-octets "author.example.invalid")
                      (list (fn-record-string-octets "example"))
                      *fn-article-max-octets*)
  *hst-injection-observation*)
 nil)
(must-fail
 (assert! (fn-inj-suffixp
           *hst-authored-source*
           (fn-hsig-injected-carrier-octets
            *hst-authored-source* *hst-principal* *hst-keys*
            *hst-signatures*
            (fn-inj-make-config
             nil (fn-record-string-octets "author.example.invalid")
             (list (fn-record-string-octets "example"))
             *fn-article-max-octets*)
            *hst-injection-observation*))))
(must-fail
 (assert! (fn-inj-reinjectionp
           (fn-hsig-injected-carrier-octets
            *hst-authored-source* *hst-principal* *hst-keys*
            *hst-signatures*
            (fn-inj-make-config
             nil (fn-record-string-octets "author.example.invalid")
             (list (fn-record-string-octets "example"))
             *fn-article-max-octets*)
            *hst-injection-observation*)
           *hst-carried-received*
           (fn-record-string-octets "author.example.invalid")
           (fn-record-string-octets "<hybrid@example.invalid>"))))
(must-fail
 (assert! (fn-inj-reinjectionp
           *hst-carried-received* *hst-carried-received*
           (fn-record-string-octets "author.example.invalid")
           (fn-record-string-octets "<hybrid@example.invalid>"))))
(make-event `(defconst *hst-carried-subject-id*
               ',(fn-id-subject-of-payload *hst-carried-received*)))
(defconst *hst-carried-subject*
  (fn-record-octets-string (fn-id-text *hst-carried-subject-id*)))
(make-event `(defconst *hst-carried-obligation*
               ',(fn-record-octets-string
                  (fn-id-text
                   (fn-id-obligation-of
                    (fn-record-string-octets "<hybrid@example.invalid>")
                    *hst-carried-subject-id*)))))
(make-event `(defconst *hst-carried-event*
               ',(fn-hsig-authorized-carried-submission-event
                  2 3 4 4 *hst-snapshot* "<hybrid@example.invalid>"
                  *hst-authored-source* *hst-carried-received* '("example")
                  *hst-carried-obligation* *hst-carried-subject* "release"
                  (fn-charge-for-payload (len *hst-carried-received*))
                  *hst-principal* *hst-keys* *hst-signatures* *hst-ml-key*
                  :verified :verified
                  (fn-clock-observation 1 841000000000 0 t))))
(assert! (fn-stxa-p *hst-carried-event*))

; The actual native constructor binds all Store metadata to the injected
; received bytes, while the old pathless record above still replays.
(make-event `(defconst *hst-injected-subject-id*
               ',(fn-id-subject-of-payload *hst-injected-received*)))
(defconst *hst-injected-subject*
  (fn-record-octets-string (fn-id-text *hst-injected-subject-id*)))
(make-event `(defconst *hst-injected-obligation*
               ',(fn-record-octets-string
                  (fn-id-text
                   (fn-id-obligation-of
                    (fn-record-string-octets "<hybrid@example.invalid>")
                    *hst-injected-subject-id*)))))
(make-event `(defconst *hst-injected-event*
               ',(fn-hsig-authorized-injected-carried-submission-event
                  2 3 4 4 *hst-snapshot* "<hybrid@example.invalid>"
                  *hst-authored-source* *hst-injected-received* '("example")
                  *hst-injected-obligation* *hst-injected-subject* "release"
                  (fn-charge-for-payload (len *hst-injected-received*))
                  *hst-principal* *hst-keys* *hst-signatures* *hst-ml-key*
                  :verified :verified *hst-injection-config*
                  *hst-injection-observation*)))
(assert! (fn-stxa-p *hst-injected-event*))
(assert! (fn-hsig-article-event-snapshot-bindsp
          *hst-injected-event*
          (fn-hsig-keyring-event 1 2 3 4 *hst-principal* *hst-keys*)))
(assert-equal (fn-stxa-authored-source *hst-injected-event*)
              *hst-authored-source*)
(assert-equal
 (fn-hsig-authorized-injected-carried-submission-event
  2 3 4 4 *hst-snapshot* "<hybrid@example.invalid>"
  *hst-authored-source* *hst-carried-received* '("example")
  *hst-carried-obligation* *hst-carried-subject* "release"
  (fn-charge-for-payload (len *hst-carried-received*))
  *hst-principal* *hst-keys* *hst-signatures* *hst-ml-key*
  :verified :verified *hst-injection-config* *hst-injection-observation*)
 nil)
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
(make-event
 `(defconst *hst-carried-wrong-charge*
    ',(let* ((old (fn-record-result-record
                   (fn-record-decode-exact
                    (fn-stxa-article-record *hst-carried-event*))))
             (record
              (fn-record-make
               (fn-record-sequence old) (fn-record-txid old)
               (fn-record-generation old) (fn-record-msgid old)
               (fn-record-payload old) (fn-record-groups old)
               (fn-record-obligation-id old) (fn-record-content-subject old)
               (fn-record-release-evidence old) (1+ (fn-record-charge old))
               (fn-record-stamp old))))
        (fn-stxa-make-carried
         (fn-stxa-sequence *hst-carried-event*)
         (fn-stxa-txid *hst-carried-event*)
         (fn-stxa-generation *hst-carried-event*)
         (fn-stxa-keyring-generation *hst-carried-event*)
         (fn-stxa-profile *hst-carried-event*)
         (fn-stxa-content-subject *hst-carried-event*)
         (fn-record-encode record)
         (fn-stxa-verdict-event *hst-carried-event*)
         (fn-stxa-authored-source *hst-carried-event*)
         (fn-stxa-authored-id *hst-carried-event*)))))
(assert! (fn-stxa-bindsp *hst-carried-wrong-charge*))
(assert-equal
 (fn-hsig-article-event-snapshot-bindsp
  *hst-carried-wrong-charge*
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
  *hst-carried-obligation* *hst-carried-subject* "release"
  (fn-charge-for-payload (len *hst-carried-received*))
  *hst-principal* *hst-keys* *hst-signatures* *hst-ml-key*
  :verified :verified (fn-clock-observation 1 841000000000 0 t))
 nil)
(assert-equal
 (fn-hsig-authorized-carried-submission-event
  2 3 4 4 *hst-snapshot* "<hybrid@example.invalid>"
  *hst-authored-source* *hst-carried-received* '("example")
  *hst-carried-obligation* *hst-carried-subject* "release"
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

; Carrier v2 (bounds P4): the evidence tag follows the source's version, and
; both tags replay against the one D09 keyring profile.
(assert-event
 (and (equal (fn-hsig-evidence-tag (make-list 65535 :initial-element 42))
             *fn-hsig-profile-tag*)
      (equal (fn-hsig-evidence-tag (make-list 65536 :initial-element 42))
             *fn-stxe-profile-hybrid-v2*)
      (equal (fn-stxe-keyring-profile
              (fn-hsig-evidence-tag (make-list 65536 :initial-element 42)))
             *fn-hsig-profile-tag*)))

; D27 (signed-path): the composite holds every source a carrier signs
; (fn-stxa-holds-every-signable-source).  A 70,000-octet source is v2 and
; past the old 32,768 composite cap; without the subject hypothesis the bound
; is not a theorem (a list may be longer than any carrier admits).
(assert-event (equal (fn-hsig-source-version (make-list 70000 :initial-element 65))
                     *fn-hsig-v2-version*))
(assert-event (and (< 32768 70000) (< 70000 *fn-stxa-max-authored-source*)))
(must-fail
 (defthm hst-source-bound-without-a-subject
   (<= (len source) *fn-stxa-max-authored-source*)))
(assert-event
 (let ((keys (list (cons :ed25519 (make-list 32 :initial-element 1))
                   (cons :ml-dsa-65 (make-list 1952 :initial-element 2))))
       (source (make-list 70000 :initial-element 65)))
   (and (fn-hsig-subject-at-p 2 (make-list 32 :initial-element 3) keys source)
        (<= (len source) *fn-stxa-max-authored-source*))))

; D32: a served POST of a signed carrier with a supplied Path.  The node
; injects it (recipe v3, "author.example.invalid!" inserted in the Path) and
; the authored-source projection of the stored article is still exactly the
; poster's signed source: fn-hc-authored-source drops the Path the poster
; wrote, before and after the prefix, so the carrier projection is unchanged.
(defconst *hst-path-carrier*
  (append (fn-record-string-octets "Path: not-for-mail") '(13 10)
          *hst-carried-received*))
(make-event `(defconst *hst-path-injected*
               ',(fn-inj-decision-octets
                  (fn-inj-decide *hst-path-carrier* *hst-injection-config*
                                 *hst-injection-observation*))))
(assert! (consp *hst-path-injected*))
(assert! (fn-inj-supplies-pathp *hst-path-carrier*))
(assert! (not (fn-inj-suffixp *hst-path-carrier* *hst-path-injected*)))
(assert! (fn-hc-okp (fn-hc-received-plan *hst-path-injected*)))
(assert-equal (car (fn-hc-value (fn-hc-received-plan *hst-path-injected*)))
              *hst-authored-source*)
(assert-equal (car (fn-hc-value (fn-hc-received-plan *hst-path-carrier*)))
              *hst-authored-source*)
