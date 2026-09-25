; Teeth for books/key-statements.lisp (PRF-098).  A reachable succession and
; revocation over the topic-history fixture (principal of 7s enrolled at
; keyring generation 4 with *tha-keys*), and one must-fail per keystone
; hypothesis.
(in-package "ACL2")
(include-book "../../books/key-statements")
(include-book "topic-history-authorship-tests")
(include-book "std/testing/must-fail" :dir :system)

(defun kst-hex (octets)
  (declare (xargs :mode :program))
  (fn-record-octets-string (fn-stx-hex-octets octets)))

; A long value is split over lines of the same name, 64 hex characters each.
(defun kst-chunks (name chars)
  (declare (xargs :mode :program))
  (if (<= (len chars) 64)
      (tha-line (concatenate 'string name ": " (coerce chars 'string)))
    (append (tha-line (concatenate 'string name ": "
                                   (coerce (take 64 chars) 'string)))
            (kst-chunks name (nthcdr 64 chars)))))

(defun kst-field (name octets)
  (declare (xargs :mode :program))
  (kst-chunks name (coerce (kst-hex octets) 'list)))

(defconst *kst-new-keys* *tha-other-keys*)
(defconst *kst-pop-sigs*
  (list (cons :ed25519 (make-list 64 :initial-element 21))
        (cons :ml-dsa-65 (make-list 3309 :initial-element 23))))
(defconst *kst-msgid* "<succession-1@fn-keys.invalid>")

(defun kst-source (kind msgid old-ed)
  (declare (xargs :mode :program))
  (append (tha-line "From: statement@example.invalid")
          (tha-line "Date: Fri, 25 Sep 2026 12:00:00 +0000")
          (tha-line "Newsgroups: fn.keys")
          (tha-line "Subject: fn-key-statement")
          (tha-line (concatenate 'string "Message-ID: " msgid))
          '(13 10)
          (tha-line (concatenate 'string "FN-Key-Statement: " kind))
          (kst-field "FN-Key-Principal" *tha-principal*)
          (kst-field "FN-Key-Old-Ed25519" old-ed)
          (kst-field "FN-Key-New-Ed25519" (cdr (first *kst-new-keys*)))
          (kst-field "FN-Key-New-ML-DSA-65" (cdr (second *kst-new-keys*)))
          (kst-field "FN-Key-PoP-Ed25519" (cdr (first *kst-pop-sigs*)))
          (kst-field "FN-Key-PoP-ML-DSA-65" (cdr (second *kst-pop-sigs*)))))

(make-event `(defconst *kst-source*
               ',(kst-source "succession-v1" *kst-msgid* *tha-ed-key*)))
(assert-event
 (equal (fn-ks-statement *kst-source*)
        (list :succession *tha-principal* *tha-ed-key* *kst-new-keys*
              *kst-pop-sigs*)))

; The kind-4 composite the owner commits for the statement: verified under
; the principal's current enrollment (generation 4).
(defun kst-event (source msgid principal keys snapshot-octets generation)
  (declare (xargs :mode :program))
  (let* ((received (fn-hc-render-at-most *fn-article-max-octets* source
                                         principal keys *tha-signatures*))
         (id (fn-id-subject-of-payload received))
         (subject (fn-record-octets-string (fn-id-text id)))
         (obligation (fn-record-octets-string
                      (fn-id-text (fn-id-obligation-of
                                   (fn-record-string-octets msgid) id)))))
    (fn-hsig-authorized-carried-submission-event
     2 3 4 generation snapshot-octets msgid source received '("fn.keys")
     obligation subject "release" (fn-charge-for-payload (len received))
     principal keys *tha-signatures* (cdr (second keys)) :verified :verified
     (fn-clock-observation 1 841000000000 0 t))))

(make-event `(defconst *kst-event*
               ',(kst-event *kst-source* *kst-msgid* *tha-principal* *tha-keys*
                            *tha-snapshot-octets* 4)))
(assert-event (fn-stxa-p *kst-event*))
(assert-event (equal (fn-ks-verdict *kst-event*)
                     (fn-stx-make-verdict :verified *tha-principal* 4)))
(assert-event (equal (fn-ks-msgid *kst-event*) *kst-msgid*))

(defconst *kst-snapshots* (list *tha-snapshot*))
(make-event `(defconst *kst-rows*
               ',(list (fn-cfg-row-make "fn.keys" (kst-hex *tha-principal*)
                                        "keys" 0))))

; The PoP request names the new keys and the statement's own Message-ID.
(assert-event
 (equal (fn-ks-pop-request *kst-event*)
        (list *tha-principal* *kst-new-keys*
              (fn-ks-pop-source *kst-msgid* *tha-ed-key*) *kst-pop-sigs*)))

; Witness (the succession acts): verified, granted, current, PoP observed.
(assert-event
 (equal (fn-ks-plan *kst-event* *kst-snapshots* *kst-rows*
                    (cdr (second *kst-new-keys*)) :verified :verified)
        (list :enroll *tha-principal* *kst-new-keys*)))
(make-event `(defconst *kst-successor*
               ',(fn-ks-execute *kst-event* *kst-snapshots* *kst-rows*
                                (cdr (second *kst-new-keys*)) :verified :verified
                                5 6 7)))
(assert-event (fn-stxk-p *kst-successor*))
(assert-event (equal (fn-stxk-keyring-generation *kst-successor*) 5))
; fn-ks-succession-selects-the-new-keys, reached.
(assert-event
 (equal (fn-hl-current-enrollment 5 (cons *kst-successor* *kst-snapshots*))
        (list *kst-successor* *tha-principal* *kst-new-keys*)))
; fn-ks-succession-refuses-the-old-keys, reached: the old-key carrier that
; was :ok before is refused after, on every path.
(defconst *kst-relayed* (append (tha-line "Path: gateway.example!fn") *tha-received*))
(assert-event (equal (car (fn-pa-current-plan *kst-relayed* *kst-snapshots* nil nil))
                     :ok))
(assert-event
 (equal (fn-pa-current-plan *kst-relayed* (cons *kst-successor* *kst-snapshots*)
                            nil t)
        (list :refused :local-enrollment)))
; Tooth (fn-ks-succession-refuses-other-keys, the keys differ): a carrier
; under the NEW keys is not refused, it is :ok.
(make-event `(defconst *kst-new-relayed*
               ',(fn-hc-render-at-most *fn-article-max-octets* *tha-root-source*
                                       *tha-principal* *kst-new-keys*
                                       *tha-signatures*)))
(must-fail
 (assert-event
  (equal (fn-pa-current-plan *kst-new-relayed*
                             (cons *kst-successor* *kst-snapshots*) nil t)
         (list :refused :local-enrollment))))

; Teeth for the decision's hypotheses, each alone.
; (a) The PoP: a refused observation declines.
(assert-event
 (equal (fn-ks-plan *kst-event* *kst-snapshots* *kst-rows*
                    (cdr (second *kst-new-keys*)) :refused :verified)
        (list :decline :proof-of-possession)))
(must-fail
 (assert-event
  (fn-ks-execute *kst-event* *kst-snapshots* *kst-rows*
                 (cdr (second *kst-new-keys*)) :verified :refused 5 6 7)))
; (b) The PoP names this Message-ID: a statement whose Message-ID differs has
; a different PoP source, so an observation made for one is not the other's.
(assert-event
 (not (equal (fn-ks-pop-source *kst-msgid* *tha-ed-key*)
             (fn-ks-pop-source "<succession-2@fn-keys.invalid>" *tha-ed-key*))))
; (c) The grant: no "keys" row, or a row over another namespace, declines.
(assert-event
 (equal (fn-ks-plan *kst-event* *kst-snapshots* nil
                    (cdr (second *kst-new-keys*)) :verified :verified)
        (list :decline :no-grant)))
(assert-event
 (equal (car (fn-ks-plan *kst-event* *kst-snapshots*
                         (list (fn-cfg-row-make "fn.other" (kst-hex *tha-principal*)
                                                "keys" 0))
                         (cdr (second *kst-new-keys*)) :verified :verified))
        :decline))
(must-fail
 (assert-event
  (fn-ks-execute *kst-event* *kst-snapshots* nil
                 (cdr (second *kst-new-keys*)) :verified :verified 5 6 7)))
; (d) The old key was current: after the succession the same statement (a
; replay) declines :not-current.
(assert-event
 (equal (fn-ks-plan *kst-event* (cons *kst-successor* *kst-snapshots*) *kst-rows*
                    (cdr (second *kst-new-keys*)) :verified :verified)
        (list :decline :not-current)))
; (e) The old key named is the enrollment's: a statement naming another old
; key declines.
(make-event `(defconst *kst-wrong-old*
               ',(kst-event (kst-source "succession-v1" *kst-msgid*
                                        (make-list 32 :initial-element 99))
                            *kst-msgid* *tha-principal* *tha-keys*
                            *tha-snapshot-octets* 4)))
(assert-event
 (equal (fn-ks-plan *kst-wrong-old* *kst-snapshots* *kst-rows*
                    (cdr (second *kst-new-keys*)) :verified :verified)
        (list :decline :old-key)))

; fn-ks-carried-or-revoked-statement-never-changes-a-keyring: the carried
; composite of the same statement (verdict :carried, no enrollment here)
; never acts, and neither does a :revoked one.
(make-event `(defconst *kst-carried*
               ',(let* ((received (fn-hc-render-at-most
                                   *fn-article-max-octets* *kst-source*
                                   *tha-principal* *tha-keys* *tha-signatures*))
                        (id (fn-id-subject-of-payload received)))
                   (fn-pa-carried-event
                    2 3 4 *kst-msgid* received '("fn.keys")
                    (fn-record-octets-string
                     (fn-id-text (fn-id-obligation-of
                                  (fn-record-string-octets *kst-msgid*) id)))
                    (fn-record-octets-string (fn-id-text id)) "release"
                    (fn-charge-for-payload (len received)) nil
                    (list (fn-record-string-octets (kst-hex *tha-principal*)))
                    (fn-clock-observation 1 841000000000 0 t)))))
(assert-event (fn-stxa-p *kst-carried*))
(assert-event (equal (fn-stx-verdict-token (fn-ks-verdict *kst-carried*)) :carried))
(assert-event
 (equal (fn-ks-plan *kst-carried* *kst-snapshots* *kst-rows*
                    (cdr (second *kst-new-keys*)) :verified :verified)
        (list :decline :carried)))
(must-fail
 (assert-event
  (fn-ks-execute *kst-carried* *kst-snapshots* *kst-rows*
                 (cdr (second *kst-new-keys*)) :verified :verified 5 6 7)))

; Revocation: the statement revokes its own principal at the next
; generation, and no plan for it is :ok after.
(make-event `(defconst *kst-revocation-event*
               ',(kst-event (kst-source "revocation-v1"
                                        "<revocation-1@fn-keys.invalid>"
                                        *tha-ed-key*)
                            "<revocation-1@fn-keys.invalid>" *tha-principal*
                            *tha-keys* *tha-snapshot-octets* 4)))
(assert-event
 (equal (fn-ks-plan *kst-revocation-event* *kst-snapshots* *kst-rows*
                    nil nil nil)
        (list :revoke *tha-principal*)))
(make-event `(defconst *kst-tombstone*
               ',(fn-ks-execute *kst-revocation-event* *kst-snapshots* *kst-rows*
                                nil nil nil 5 6 7)))
(assert-event (fn-stxk-p *kst-tombstone*))
(assert-event
 (equal (fn-pa-current-plan *kst-relayed* (cons *kst-tombstone* *kst-snapshots*)
                            nil nil)
        (list :refused :local-enrollment)))
(assert-event
 (equal (car (fn-pa-current-plan *kst-relayed*
                                 (cons *kst-tombstone* *kst-snapshots*) nil t))
        :revoked))
; Tooth (fn-ks-revocation-leaves-no-ok-plan, the tombstone): without it the
; same carrier is :ok.
(must-fail
 (assert-event
  (not (equal (car (fn-pa-current-plan *kst-relayed* *kst-snapshots* nil t))
              :ok))))

; The next-generation request (books/native-hybrid-control via
; books/hybrid-lifecycle): ACL2's, one past the newest snapshot.
(assert-event (equal (fn-hl-next-generation nil) 1))
(assert-event (equal (fn-hl-next-generation *kst-snapshots*) 5))
(assert-event (equal (fn-ks-log-line (list :decline :carried) nil nil)
                     (fn-record-string-octets "key-statement declined carried")))
(assert-event (equal (fn-ks-log-line (list :enroll *tha-principal* *kst-new-keys*)
                                     :refused nil)
                     (fn-record-string-octets
                      "key-statement enrol-successor refused")))
(assert-event (equal (fn-ks-log-line (list :revoke *tha-principal*) :committed t)
                     (fn-record-string-octets
                      "key-statement revoke committed at-open")))

; -----------------------------------------------------------------------------
; The crash cut (fn-ks-cut) and the open's recovery (fn-ks-recover).

(defconst *kst-ml* (cdr (second *kst-new-keys*)))

; fn-ks-execute-is-idempotent, reached for both kinds: the executed
; statement, run again against its own change newest, changes nothing, also
; under other rows and observations.
(assert-event *kst-successor*)
(assert-event
 (null (fn-ks-execute *kst-event* (cons *kst-successor* *kst-snapshots*)
                      *kst-rows* *kst-ml* :verified :verified 8 9 10)))
(assert-event
 (equal (car (fn-ks-plan *kst-event* (cons *kst-successor* *kst-snapshots*)
                         *kst-rows* *kst-ml* :verified :verified))
        :decline))
(assert-event *kst-tombstone*)
(assert-event
 (null (fn-ks-execute *kst-revocation-event*
                      (cons *kst-tombstone* *kst-snapshots*)
                      *kst-rows* nil nil nil 8 9 10)))
; Tooth (the hypothesis: the first execution acted).  A statement that
; declined (the PoP observation refused) acts on a re-run whose observation
; verified, against the same snapshots behind a non-snapshot head.
(assert-event
 (null (fn-ks-execute *kst-event* *kst-snapshots* *kst-rows* *kst-ml*
                      :refused :verified 5 6 7)))
(assert-event
 (fn-ks-execute *kst-event* (cons nil *kst-snapshots*) *kst-rows* *kst-ml*
                :verified :verified 5 6 7))
(must-fail
 (assert-event
  (null (fn-ks-execute *kst-event* (cons nil *kst-snapshots*) *kst-rows* *kst-ml*
                       :verified :verified 5 6 7))))

; fn-ks-recover-completes-the-cut, reached: the statement committed, the
; process died, the open's recovery made exactly the uninterrupted change.
(defconst *kst-prior* (list :prior-record))
(assert-event (equal (fn-ks-pending *kst-event*) *kst-event*))
(assert-event
 (equal (fn-ks-recover (fn-ks-cut *kst-prior* *kst-snapshots* *kst-event*)
                       *kst-rows* *kst-ml* :verified :verified 5 6 7)
        (fn-ks-accept *kst-prior* *kst-snapshots* *kst-event*
                      *kst-rows* *kst-ml* :verified :verified 5 6 7)))
(assert-event
 (equal (fn-ks-accept *kst-prior* *kst-snapshots* *kst-event*
                      *kst-rows* *kst-ml* :verified :verified 5 6 7)
        (cons (list* *kst-successor* *kst-event* *kst-prior*)
              (cons *kst-successor* *kst-snapshots*))))
; The cut itself is not the completed state: the change is missing.
(assert-event
 (not (equal (fn-ks-cut *kst-prior* *kst-snapshots* *kst-event*)
             (fn-ks-accept *kst-prior* *kst-snapshots* *kst-event*
                           *kst-rows* *kst-ml* :verified :verified 5 6 7))))

; fn-ks-recover-after-an-acting-acceptance-changes-nothing, reached: after
; the completed succession, recovery under no rows and refused observations
; leaves the state; the newest record is the kind-3 change, never pending.
(assert-event (null (fn-ks-pending *kst-successor*)))
(assert-event
 (let ((st (fn-ks-accept *kst-prior* *kst-snapshots* *kst-event*
                         *kst-rows* *kst-ml* :verified :verified 5 6 7)))
   (equal (fn-ks-recover st nil nil :refused :refused 8 9 10) st)))
; Tooth (the hypothesis: the acceptance acted).  An acceptance that declined
; (PoP refused) leaves the statement newest; recovery whose observation
; verified then makes the change.
(assert-event
 (null (fn-ks-execute *kst-event* *kst-snapshots* *kst-rows* *kst-ml*
                      :refused :verified 5 6 7)))
(must-fail
 (assert-event
  (let ((st (fn-ks-accept *kst-prior* *kst-snapshots* *kst-event*
                          *kst-rows* *kst-ml* :refused :verified 5 6 7)))
    (equal (fn-ks-recover st *kst-rows* *kst-ml* :verified :verified 8 9 10)
           st))))
