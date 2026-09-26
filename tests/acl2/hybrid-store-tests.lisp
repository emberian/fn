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

; -----------------------------------------------------------------------------
; C3 prerequisite (2026-09-25): the signed record binding names the filing
; group.  fn-hsig-signed-control-record-lists-its-filing-group,
; fn-hsig-malformed-control-binds-no-record.

(defconst *hst-cancel-source*
  (append (hst-line "From: author@example.invalid")
          (hst-line "Date: Wed, 23 Sep 2026 12:00:00 +0000")
          (hst-line "Newsgroups: example")
          (hst-line "Subject: cmsg cancel <hybrid@example.invalid>")
          (hst-line "Control: cancel <hybrid@example.invalid>")
          (hst-line "Message-ID: <cancel@example.invalid>")
          '(13 10 98 111 100 121 13 10)))
(defconst *hst-malformed-source*
  (append (hst-line "From: author@example.invalid")
          (hst-line "Date: Wed, 23 Sep 2026 12:00:00 +0000")
          (hst-line "Newsgroups: example")
          (hst-line "Subject: two controls")
          (hst-line "Control: cancel <a@example.invalid>")
          (hst-line "Control: cancel <b@example.invalid>")
          (hst-line "Message-ID: <cancel@example.invalid>")
          '(13 10 98 111 100 121 13 10)))
(assert-equal (car (fn-ctl-classify-octets *hst-cancel-source*)) :control)
(assert-equal (car (fn-ctl-classify-octets *hst-malformed-source*)) :malformed)
(assert-equal (fn-ctl-classify-octets *hst-authored-source*) :ordinary)
(make-event `(defconst *hst-cancel-received*
               ',(fn-hc-render-at-most *fn-article-max-octets*
                                       *hst-cancel-source* *hst-principal*
                                       *hst-keys* *hst-signatures*)))
(assert! *hst-cancel-received*)
(make-event `(defconst *hst-cancel-subject-id*
               ',(fn-id-subject-of-payload *hst-cancel-received*)))
(make-event `(defconst *hst-cancel-obligation*
               ',(fn-record-octets-string
                  (fn-id-text
                   (fn-id-obligation-of
                    (fn-record-string-octets "<cancel@example.invalid>")
                    *hst-cancel-subject-id*)))))
(defun hst-cancel-record (groups)
  (fn-record-make 2 3 4 "<cancel@example.invalid>" *hst-cancel-received*
                  groups *hst-cancel-obligation*
                  (fn-record-octets-string (fn-id-text *hst-cancel-subject-id*))
                  "release" (fn-charge-for-payload (len *hst-cancel-received*))
                  (fn-record-stamp-of-observation
                   (fn-clock-observation 1 841000000000 0 t))))
(defun hst-cancel-event (groups)
  (fn-hsig-authorized-carried-submission-event
   2 3 4 4 *hst-snapshot* "<cancel@example.invalid>"
   *hst-cancel-source* *hst-cancel-received* groups
   *hst-cancel-obligation*
   (fn-record-octets-string (fn-id-text *hst-cancel-subject-id*)) "release"
   (fn-charge-for-payload (len *hst-cancel-received*))
   *hst-principal* *hst-keys* *hst-signatures* *hst-ml-key*
   :verified :verified (fn-clock-observation 1 841000000000 0 t)))

; Reachable witness: the signed cancel's record in control.cancel binds, the
; native constructor builds its composite, replay's schema-1 binding admits
; it against the enrolled snapshot, and its record lists control.cancel.
(assert! (fn-hsig-carried-record-metadatap
          *hst-cancel-source* *hst-cancel-received*
          (hst-cancel-record '("control.cancel"))))
(assert! (fn-stxa-p (hst-cancel-event '("control.cancel"))))
(assert! (fn-hsig-article-event-snapshot-bindsp
          (hst-cancel-event '("control.cancel"))
          (fn-hsig-keyring-event 1 2 3 4 *hst-principal* *hst-keys*)))
(assert-equal (fn-record-groups
               (fn-record-result-record
                (fn-record-decode-exact
                 (fn-stxa-article-record (hst-cancel-event '("control.cancel"))))))
              '("control.cancel"))
; Teeth, the binding hypothesis: a record of the same signed cancel listing
; its Newsgroups (the pre-C3 binding) is not admitted, and the constructor
; builds no composite for it; the conclusion fails for that record.
(assert! (not (fn-hsig-carried-record-metadatap
               *hst-cancel-source* *hst-cancel-received*
               (hst-cancel-record '("example")))))
(assert-equal (hst-cancel-event '("example")) nil)
(must-fail
 (assert! (equal (fn-record-groups (hst-cancel-record '("example")))
                 (list (fn-ctl-filing-group
                        (cadr (fn-ctl-classify-octets *hst-cancel-source*)))))))
; Teeth, the classification hypothesis: an ordinary signed article binds
; under its Newsgroups, which is not a filing group.
(assert! (fn-hsig-article-event-snapshot-bindsp
          *hst-carried-event*
          (fn-hsig-keyring-event 1 2 3 4 *hst-principal* *hst-keys*)))
(must-fail
 (assert! (equal (fn-record-groups
                  (fn-record-result-record
                   (fn-record-decode-exact
                    (fn-stxa-article-record *hst-carried-event*))))
                 (list (fn-ctl-filing-group
                        (cadr (fn-ctl-classify-octets *hst-authored-source*)))))))
; fn-hsig-malformed-control-binds-no-record.  Witness: two Control fields
; bind under neither group list.  Teeth (the malformed hypothesis): the
; ordinary source binds (the witness above).
(assert! (not (fn-hsig-carried-record-metadatap
               *hst-malformed-source* *hst-cancel-received*
               (hst-cancel-record '("example")))))
(assert! (not (fn-hsig-carried-record-metadatap
               *hst-malformed-source* *hst-cancel-received*
               (hst-cancel-record '("control.cancel")))))

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

; -----------------------------------------------------------------------------
; PKT-147 (control-across-peers, PRF-170): teeth for
; fn-hsig-injected-carrier-unserved-group-is-refused-by-name.  G1 serves
; "example", the group the source names; G2 is this node's list.
(defconst *hst-g1* (list (fn-record-string-octets "example")))
(defconst *hst-g2-unserved* (list (fn-record-string-octets "other")))
(defconst *hst-g2-served* (list (fn-record-string-octets "other")
                                (fn-record-string-octets "example")))
(defun hst-cfg (allow groups)
  (fn-inj-make-config allow (fn-record-string-octets "author.example.invalid")
                      groups *fn-article-max-octets*))
(defun hst-octets (allow groups)
  (fn-hsig-injected-carrier-octets
   *hst-authored-source* *hst-principal* *hst-keys* *hst-signatures*
   (hst-cfg allow groups) *hst-injection-observation*))
(defun hst-reason (allow groups)
  (fn-hsig-injected-carrier-reason
   *hst-authored-source* *hst-principal* *hst-keys* *hst-signatures*
   (hst-cfg allow groups) *hst-injection-observation*))

; Reachable positive witness, the unserved branch: both hypotheses hold, the
; named group is not in G2, and the carrier is refused :unknown-group.
(assert! (and (hst-octets t *hst-g1*)
              (fn-inj-group-namesp *hst-g2-unserved*)
              (not (fn-inj-groups-admissiblep
                    (fn-inj-decision-groups
                     (fn-hsig-injected-carrier-plan
                      *hst-authored-source* *hst-principal* *hst-keys*
                      *hst-signatures* (hst-cfg t *hst-g1*)
                      *hst-injection-observation*))
                    *hst-g2-unserved*))
              (equal (hst-octets t *hst-g2-unserved*) nil)
              (equal (hst-reason t *hst-g2-unserved*) :unknown-group)))
; Reachable positive witness, the served branch: the same octets, no reason.
(assert! (and (hst-octets t *hst-g1*)
              (fn-inj-group-namesp *hst-g2-served*)
              (equal (hst-octets t *hst-g2-served*) (hst-octets t *hst-g1*))
              (equal (hst-reason t *hst-g2-served*) nil)))
; Without the first hypothesis (the source is admitted under some served
; list): posting disallowed, G2 still a list of names, and the refusal is
; not :unknown-group.
(assert! (and (not (hst-octets nil *hst-g1*))
              (fn-inj-group-namesp *hst-g2-unserved*)
              (equal (hst-reason nil *hst-g2-unserved*) :posting-disallowed)))
(must-fail (assert! (equal (hst-reason nil *hst-g2-unserved*) :unknown-group)))
; Without the second (G2 names groups): the first holds, the configuration
; is invalid and the refusal is not :unknown-group.
(defconst *hst-g2-not-names* (list '(32)))
(assert! (and (hst-octets t *hst-g1*)
              (not (fn-inj-group-namesp *hst-g2-not-names*))
              (equal (hst-reason t *hst-g2-not-names*) :config-invalid)))
(must-fail (assert! (equal (hst-reason t *hst-g2-not-names*) :unknown-group)))
