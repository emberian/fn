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

; =============================================================================
; Packet 7 (PRF-124): the recorded disposition at reopen.  The statement's
; txid, a `keys' grant as a configuration record, and journals before and
; after it.
(defconst *kst-tx* (fn-ks-txid *kst-event*))
(assert-event (natp *kst-tx*))
(make-event `(defconst *kst-grant*
               ',(fn-cfg-record-make 1 (+ 1 *kst-tx*) 1
                                     (list (fn-cfg-grant-control
                                            "fn.keys" (kst-hex *tha-principal*)
                                            "keys"))
                                     nil)))
(make-event `(defconst *kst-grant-before*
               ',(fn-cfg-record-make 1 *kst-tx* 1
                                     (list (fn-cfg-grant-control
                                            "fn.keys" (kst-hex *tha-principal*)
                                            "keys"))
                                     nil)))
; With no configuration record through its txid the statement had no grant:
; its plan declines.
(assert-event
 (equal (car (fn-ks-plan *kst-event* *kst-snapshots*
                         (fn-cfg-authorities
                          (fn-cfg-value (fn-ctl-config-at *kst-tx* nil)))
                         *kst-ml* :verified :verified))
        :decline))
(assert-event (fn-ks-configs-after-p *kst-tx* (list *kst-grant*)))
; The grant, once in force, would make it act.
(assert-event
 (equal (fn-cfg-authorities
         (fn-cfg-value (fn-ctl-config-at *kst-tx* (list *kst-grant-before*))))
        *kst-rows*))
(defmacro kst-declined ()
  '(fn-ks-accept *kst-prior* *kst-snapshots* *kst-event*
                 (fn-cfg-authorities
                  (fn-cfg-value (fn-ctl-config-at *kst-tx* nil)))
                 *kst-ml* :verified :verified 5 6 7))
; fn-ks-a-decline-replays-as-a-decline, reached: the later grant appended,
; the recorded recovery leaves the declined acceptance's state.
(assert-event (equal (kst-declined)
                     (fn-ks-cut *kst-prior* *kst-snapshots* *kst-event*)))
(assert-event
 (equal (fn-ks-recover-recorded (kst-declined) (append nil (list *kst-grant*))
                                *kst-ml* :verified :verified 8 9 10)
        (kst-declined)))
; Hypothesis removal (the record is later than the statement): the same
; grant at the statement's own txid is in force there, and the recovery acts.
(assert-event (not (fn-ks-configs-after-p *kst-tx* (list *kst-grant-before*))))
(must-fail
 (assert-event
  (equal (fn-ks-recover-recorded (kst-declined) (list *kst-grant-before*)
                                 *kst-ml* :verified :verified 8 9 10)
         (kst-declined))))
; -----------------------------------------------------------------------------
; COUNTEREXAMPLE FIXTURE: the removed `:current' reopen (gpt-6's review of
; wave 2, section 5; no supported switch recreates it).  The trace of
; planning/evidence/peering-compose-2026-09-25.md Packet 7: a statement
; declined for want of a `keys' grant, the grant published live after it,
; a restart.  The pre-packet open decided the pending statement under the
; open's LIVE grants and answered `enrol-successor committed at-open'; the
; recorded reopen (fn-ks-statement-rows with AT-OPEN, what the host calls)
; answers `declined no-grant at-open'.
(defconst *kst-live-after-grant*
  (fn-cfg-authorities (fn-cfg-value (fn-ctl-config-at (+ 1 *kst-tx*)
                                                      (list *kst-grant*)))))
(assert-event (equal *kst-live-after-grant* *kst-rows*))
(defmacro kst-old-reopen-plan ()
  '(fn-ks-plan *kst-event* *kst-snapshots* *kst-live-after-grant*
              *kst-ml* :verified :verified))
(defmacro kst-recorded-reopen-plan ()
  '(fn-ks-plan *kst-event* *kst-snapshots*
              (fn-ks-statement-rows *kst-event* t *kst-live-after-grant*
                                    (list *kst-grant*))
              *kst-ml* :verified :verified))
; The old reopen's answer: it acted on the old decline.
(assert-event (equal (car (kst-old-reopen-plan)) :enroll))
(assert-event
 (equal (fn-ks-log-line (kst-old-reopen-plan) :committed t)
        (fn-record-string-octets
         "key-statement enrol-successor committed at-open")))
(assert-event
 (not (equal (fn-ks-recover (kst-declined) *kst-live-after-grant* *kst-ml*
                            :verified :verified 8 9 10)
             (kst-declined))))
; The recorded reopen's answer on the same trace: declined, state unchanged.
(assert-event
 (equal (fn-ks-log-line (kst-recorded-reopen-plan) nil t)
        (fn-record-string-octets "key-statement declined no-grant at-open")))
(assert-event
 (equal (fn-ks-recover-recorded (kst-declined) (list *kst-grant*)
                                *kst-ml* :verified :verified 8 9 10)
        (kst-declined)))
; The old policy would not answer `declined', and the two reopens differ.
(must-fail (assert-event (equal (car (kst-old-reopen-plan)) :decline)))
(must-fail
 (assert-event
  (equal (fn-ks-recover-recorded (kst-declined) (list *kst-grant*)
                                 *kst-ml* :verified :verified 8 9 10)
         (fn-ks-recover (kst-declined) *kst-live-after-grant* *kst-ml*
                        :verified :verified 8 9 10))))
; At acceptance (AT-OPEN nil) the host's rows are the live ones, unchanged.
(assert-event (equal (fn-ks-statement-rows *kst-event* nil *kst-rows* nil)
                     *kst-rows*))
; Hypothesis removal (the plan declined): a plan that acts but whose kind-3
; event the acceptance could not build at its coordinates (a non-natural
; sequence) leaves the statement pending, and the recovery builds it.
(assert-event
 (equal (car (fn-ks-plan *kst-event* *kst-snapshots*
                         (fn-cfg-authorities
                          (fn-cfg-value (fn-ctl-config-at
                                         *kst-tx* (list *kst-grant-before*))))
                         *kst-ml* :verified :verified))
        :enroll))
(must-fail
 (assert-event
  (let ((st (fn-ks-accept *kst-prior* *kst-snapshots* *kst-event*
                          *kst-rows* *kst-ml* :verified :verified
                          :bad :bad :bad)))
    (equal (fn-ks-recover-recorded st (list *kst-grant-before*)
                                   *kst-ml* :verified :verified 8 9 10)
           st))))

; fn-ks-reopen-is-blind-to-later-configuration, reached (both sides) and its
; hypothesis removed (a record at the statement's txid changes the answer).
(assert-event
 (equal (fn-ks-recover-recorded (fn-ks-cut *kst-prior* *kst-snapshots* *kst-event*)
                                (append (list *kst-grant-before*)
                                        (list *kst-grant*))
                                *kst-ml* :verified :verified 5 6 7)
        (fn-ks-recover-recorded (fn-ks-cut *kst-prior* *kst-snapshots* *kst-event*)
                                (list *kst-grant-before*)
                                *kst-ml* :verified :verified 5 6 7)))
(must-fail
 (assert-event
  (equal (fn-ks-recover-recorded (fn-ks-cut *kst-prior* *kst-snapshots* *kst-event*)
                                 (append nil (list *kst-grant-before*))
                                 *kst-ml* :verified :verified 5 6 7)
         (fn-ks-recover-recorded (fn-ks-cut *kst-prior* *kst-snapshots* *kst-event*)
                                 nil *kst-ml* :verified :verified 5 6 7))))
; fn-ks-recorded-recovery-completes-the-cut, reached where the journal
; replays: the cut, recovered under the grant in force at the txid, is the
; acting acceptance.
(assert-event
 (equal (fn-ks-recover-recorded (fn-ks-cut *kst-prior* *kst-snapshots* *kst-event*)
                                (list *kst-grant-before*)
                                *kst-ml* :verified :verified 5 6 7)
        (fn-ks-accept *kst-prior* *kst-snapshots* *kst-event* *kst-rows*
                      *kst-ml* :verified :verified 5 6 7)))

; =============================================================================
; PRF-140: fn-ks-accepted-statement-finishes-under-its-admission-context.
; The statement accepted under the grant (journal *kst-grant-before*, at the
; statement's txid), the process killed at the cut, then the grant revoked
; (a later record) before the restart.
(defconst *kst-stamp* (fn-clock-observation 7 1000 5 t))
(defun kst-record (sequence txid generation delta)
  (declare (xargs :mode :program))
  (fn-cfg-record-make sequence txid generation (list delta) *kst-stamp*))
(make-event `(defconst *kst-grant-delta*
               ',(fn-cfg-grant-control "fn.keys" (kst-hex *tha-principal*)
                                       "keys")))
(make-event `(defconst *kst-revoke-delta*
               ',(fn-cfg-revoke-control "fn.keys" (kst-hex *tha-principal*))))
; The grant in force at the statement's txid; its revocation one txid later;
; the same revocation at the txid; the grant only after the txid; a grant
; whose generation does not follow (config-at folds it, replay refuses it).
(make-event `(defconst *kst-admit*
               ',(kst-record 0 *kst-tx* 1 *kst-grant-delta*)))
(make-event `(defconst *kst-revoke*
               ',(kst-record 1 (+ 1 *kst-tx*) 2 *kst-revoke-delta*)))
(make-event `(defconst *kst-revoke-at-tx*
               ',(kst-record 1 *kst-tx* 2 *kst-revoke-delta*)))
(make-event `(defconst *kst-grant-after*
               ',(kst-record 0 (+ 1 *kst-tx*) 1 *kst-grant-delta*)))
(make-event `(defconst *kst-grant-bad-generation*
               ',(kst-record 0 *kst-tx* 5 *kst-grant-delta*)))
(defconst *kst-admission* (list *kst-admit*))
(assert-event (fn-cfg-recordp *kst-admit*))
(assert-event (fn-cfg-recordp *kst-revoke*))
(assert-event (not (equal (fn-config-replay 0 510 (list *kst-admit* *kst-revoke*))
                          :fault)))
(defmacro kst-cut-state ()
  '(fn-ks-cut *kst-prior* *kst-snapshots* *kst-event*))
(defmacro kst-replay-rows (configs)
  `(fn-cfg-authorities (fn-cfg-value (fn-config-replay 0 510 ,configs))))

; The antecedent, every literal.
(assert-event (fn-ctl-configs-all-through-p *kst-tx* *kst-admission*))
(assert-event (not (equal (fn-config-replay 0 510 *kst-admission*) :fault)))
(assert-event (fn-ks-configs-after-p *kst-tx* (list *kst-revoke*)))
(assert-event (equal (kst-replay-rows *kst-admission*) *kst-rows*))
; Today's configuration has no grant: deciding under it would decline.
(assert-event
 (equal (fn-ks-log-line
         (fn-ks-plan *kst-event* *kst-snapshots*
                     (kst-replay-rows (append *kst-admission* (list *kst-revoke*)))
                     *kst-ml* :verified :verified)
         nil t)
        (fn-record-string-octets "key-statement declined no-grant at-open")))
; The conclusion, reached: the recorded recovery of the cut over the whole
; journal is the acting acceptance under the admission grants.
(assert-event
 (equal (fn-ks-recover-recorded (kst-cut-state)
                                (append *kst-admission* (list *kst-revoke*))
                                *kst-ml* :verified :verified 5 6 7)
        (fn-ks-accept *kst-prior* *kst-snapshots* *kst-event*
                      (kst-replay-rows *kst-admission*)
                      *kst-ml* :verified :verified 5 6 7)))
(assert-event
 (not (equal (fn-ks-accept *kst-prior* *kst-snapshots* *kst-event*
                           (kst-replay-rows *kst-admission*)
                           *kst-ml* :verified :verified 5 6 7)
             (kst-cut-state))))
(assert-event
 (equal (fn-ks-log-line
         (fn-ks-plan *kst-event* *kst-snapshots*
                     (fn-ks-statement-rows *kst-event* t nil
                                           (append *kst-admission*
                                                   (list *kst-revoke*)))
                     *kst-ml* :verified :verified)
         :committed t)
        (fn-record-string-octets
         "key-statement enrol-successor committed at-open")))

; Hypothesis removal (every admission record at or before the txid): the
; grant published AFTER the statement is in the replay but not in force at
; the txid; the others hold and the conclusion fails.
(assert-event (not (fn-ctl-configs-all-through-p *kst-tx* (list *kst-grant-after*))))
(assert-event (not (equal (fn-config-replay 0 510 (list *kst-grant-after*)) :fault)))
(assert-event (fn-ks-configs-after-p *kst-tx* nil))
(must-fail
 (assert-event
  (equal (fn-ks-recover-recorded (kst-cut-state)
                                 (append (list *kst-grant-after*) nil)
                                 *kst-ml* :verified :verified 5 6 7)
         (fn-ks-accept *kst-prior* *kst-snapshots* *kst-event*
                       (kst-replay-rows (list *kst-grant-after*))
                       *kst-ml* :verified :verified 5 6 7))))
; Hypothesis removal (the admission journal replays): a grant whose
; generation does not follow is folded by config-at but refused by replay.
(assert-event (fn-ctl-configs-all-through-p *kst-tx*
                                            (list *kst-grant-bad-generation*)))
(assert-event (equal (fn-config-replay 0 510 (list *kst-grant-bad-generation*))
                     :fault))
(must-fail
 (assert-event
  (equal (fn-ks-recover-recorded (kst-cut-state)
                                 (append (list *kst-grant-bad-generation*) nil)
                                 *kst-ml* :verified :verified 5 6 7)
         (fn-ks-accept *kst-prior* *kst-snapshots* *kst-event*
                       (kst-replay-rows (list *kst-grant-bad-generation*))
                       *kst-ml* :verified :verified 5 6 7))))
; Hypothesis removal (every later record is later than the txid): a
; revocation at the statement's own txid is in force there.
(assert-event (not (fn-ks-configs-after-p *kst-tx* (list *kst-revoke-at-tx*))))
(must-fail
 (assert-event
  (equal (fn-ks-recover-recorded (kst-cut-state)
                                 (append *kst-admission* (list *kst-revoke-at-tx*))
                                 *kst-ml* :verified :verified 5 6 7)
         (fn-ks-accept *kst-prior* *kst-snapshots* *kst-event*
                       (kst-replay-rows *kst-admission*)
                       *kst-ml* :verified :verified 5 6 7))))

; =============================================================================
; PRF-166 (PKT-325): `keys redecide MSGID'.  The statement declined at
; acceptance for want of a grant (kst-declined: records (statement prior),
; the keyring at generation 4); the grant was published after its txid
; (*kst-grant-after*); the operator redecides at its own txid, later still.
(defconst *kst-rtx* (+ 2 *kst-tx*))
(defconst *kst-after* (list *kst-grant-after*))
(defmacro kst-redecide (st msgid rows)
  `(fn-ks-redecide ,st ,msgid ,rows *kst-ml* :verified :verified 8 *kst-rtx* 10))
(defmacro kst-redecided ()
  '(kst-redecide (kst-declined) *kst-msgid* (kst-replay-rows *kst-after*)))
(assert-event (equal (fn-ks-find-statement *kst-msgid* (car (kst-declined)))
                     *kst-event*))
(assert-event (not (fn-ks-acted-p *kst-event* (cdr (kst-declined)))))

; fn-ks-redecide-decides-under-the-configuration-at-its-own-txid, reached:
; every antecedent literal, and the conclusion with an acting redecide.
(assert-event (fn-ctl-configs-all-through-p *kst-rtx* *kst-after*))
(assert-event (not (equal (fn-config-replay 0 510 *kst-after*) :fault)))
(assert-event (equal (kst-redecided)
                     (kst-redecide (kst-declined) *kst-msgid*
                                   (fn-ks-redecide-rows *kst-rtx* *kst-after*))))
(assert-event (not (equal (kst-redecided) (kst-declined))))
(assert-event
 (equal (fn-ks-redecide-log-line
         (fn-ks-redecide-plan *kst-event* *kst-snapshots*
                              (kst-replay-rows *kst-after*)
                              *kst-ml* :verified :verified)
         :committed)
        (fn-record-string-octets
         "key-statement redecide enrol-successor committed")))
; Hypothesis removal (every journal record precedes the redecide's txid): at
; the statement's own txid the grant is not yet in force; the replay holds.
(assert-event (not (fn-ctl-configs-all-through-p *kst-tx* *kst-after*)))
(must-fail
 (assert-event
  (equal (kst-redecide (kst-declined) *kst-msgid* (kst-replay-rows *kst-after*))
         (fn-ks-redecide (kst-declined) *kst-msgid*
                         (fn-ks-redecide-rows *kst-tx* *kst-after*)
                         *kst-ml* :verified :verified 8 *kst-tx* 10))))
; Hypothesis removal (the journal replays): a grant whose generation does not
; follow is folded at the txid but faults the replay; all-through holds.
(assert-event (fn-ctl-configs-all-through-p *kst-rtx*
                                            (list *kst-grant-bad-generation*)))
(must-fail
 (assert-event
  (equal (kst-redecide (kst-declined) *kst-msgid*
                       (kst-replay-rows (list *kst-grant-bad-generation*)))
         (kst-redecide (kst-declined) *kst-msgid*
                       (fn-ks-redecide-rows *kst-rtx*
                                            (list *kst-grant-bad-generation*))))))

; fn-ks-reopen-after-a-redecide, both arms reached (no hypotheses).  Acting:
; the open's recovery under the journal with a later revocation appended
; leaves the redecided Store.  Not acting (no grant): the recovery is that of
; the unchanged declined Store, which declines again.
(assert-event
 (equal (fn-ks-recover-recorded (kst-redecided)
                                (append *kst-after* (list *kst-revoke*))
                                *kst-ml* :verified :verified 11 12 13)
        (kst-redecided)))
(assert-event (equal (kst-redecide (kst-declined) *kst-msgid* nil) (kst-declined)))
(assert-event
 (equal (fn-ks-recover-recorded (kst-redecide (kst-declined) *kst-msgid* nil)
                                *kst-after* *kst-ml* :verified :verified 11 12 13)
        (fn-ks-recover-recorded (kst-declined) *kst-after*
                                *kst-ml* :verified :verified 11 12 13)))

; fn-ks-redecide-of-no-stored-statement-is-refused-by-name, reached.
(defconst *kst-absent* "<absent@fn-keys.invalid>")
(assert-event (not (fn-ks-find-statement *kst-absent* (car (kst-declined)))))
(assert-event
 (equal (fn-ks-redecide-plan (fn-ks-find-statement *kst-absent*
                                                   (car (kst-declined)))
                             *kst-snapshots* (kst-replay-rows *kst-after*)
                             *kst-ml* :verified :verified)
        '(:refused :not-a-key-statement)))
(assert-event (equal (kst-redecide (kst-declined) *kst-absent*
                                   (kst-replay-rows *kst-after*))
                     (kst-declined)))
(assert-event
 (equal (fn-ks-redecide-log-line '(:refused :not-a-key-statement) nil)
        (fn-record-string-octets
         "key-statement redecide refused not-a-key-statement")))
; Hypothesis removal: the stored statement's Message-ID is found and acts.
(must-fail
 (assert-event (equal (kst-redecided) (kst-declined))))

; fn-ks-redecide-of-an-acted-statement-is-refused-by-name and
; fn-ks-a-redecide-that-acted-is-refused-the-second-time, reached: the same
; MSGID after the redecide acted, under the same grants.
(defmacro kst-redecided-twice-plan (rows)
  `(fn-ks-redecide-plan (fn-ks-find-statement *kst-msgid* (car (kst-redecided)))
                        (cdr (kst-redecided)) ,rows *kst-ml* :verified
                        :verified))
(assert-event (fn-ks-redecide-event *kst-event* *kst-snapshots*
                                    (kst-replay-rows *kst-after*) *kst-ml*
                                    :verified :verified 8 *kst-rtx* 10))
(assert-event (< 4 (fn-hl-next-generation *kst-snapshots*)))
(assert-event (fn-ks-acted-p *kst-event* (cdr (kst-redecided))))
(assert-event (equal (kst-redecided-twice-plan (kst-replay-rows *kst-after*))
                     '(:refused :already-acted)))
(assert-event (equal (kst-redecide (kst-redecided) *kst-msgid*
                                   (kst-replay-rows *kst-after*))
                     (kst-redecided)))
; Hypothesis removal (acted): before the redecide the statement has not
; acted, and the plan is not the refusal.
(must-fail
 (assert-event
  (equal (fn-ks-redecide-plan *kst-event* *kst-snapshots*
                              (kst-replay-rows *kst-after*) *kst-ml* :verified
                              :verified)
         '(:refused :already-acted))))
; Hypothesis removal (the redecide acted): with no grant it declined, and the
; same MSGID is decided again (declined no-grant), not refused.
(assert-event (not (fn-ks-redecide-event *kst-event* *kst-snapshots* nil
                                         *kst-ml* :verified :verified 8
                                         *kst-rtx* 10)))
(must-fail
 (assert-event
  (equal (fn-ks-redecide-plan
          (fn-ks-find-statement *kst-msgid*
                                (car (kst-redecide (kst-declined) *kst-msgid* nil)))
          *kst-snapshots* nil *kst-ml* :verified :verified)
         '(:refused :already-acted))))
; Hypothesis removal (the statement's generation precedes the next one),
; CORRUPTED STATE: a keyring whose newest snapshot (another principal's, at
; generation 1) is older than the statement's generation 4.  The redecide
; still acts, at generation 2, which is not after 4; the second is not refused.
(make-event `(defconst *kst-stale-head*
               ',(fn-hsig-keyring-event 1 1 1 1 (make-list 32 :initial-element 8)
                                        *tha-other-keys*)))
(make-event `(defconst *kst-stale-state*
               ',(cons (car (kst-declined))
                       (cons *kst-stale-head* *kst-snapshots*))))
(assert-event (fn-ks-redecide-event *kst-event* (cdr *kst-stale-state*)
                                    (kst-replay-rows *kst-after*) *kst-ml*
                                    :verified :verified 8 *kst-rtx* 10))
(assert-event (not (< 4 (fn-hl-next-generation (cdr *kst-stale-state*)))))
(must-fail
 (assert-event
  (equal (let ((st2 (kst-redecide *kst-stale-state* *kst-msgid*
                                  (kst-replay-rows *kst-after*))))
           (fn-ks-redecide-plan (fn-ks-find-statement *kst-msgid* (car st2))
                                (cdr st2) (kst-replay-rows *kst-after*)
                                *kst-ml* :verified :verified))
         '(:refused :already-acted))))

; fn-ks-redecide-of-an-unacted-statement-is-its-acceptance-decision, reached.
(assert-event
 (equal (fn-ks-redecide-plan *kst-event* *kst-snapshots*
                             (kst-replay-rows *kst-after*) *kst-ml* :verified
                             :verified)
        (list :enroll *tha-principal* *kst-new-keys*)))
(assert-event
 (equal (fn-ks-redecide-event *kst-event* *kst-snapshots*
                              (kst-replay-rows *kst-after*) *kst-ml* :verified
                              :verified 8 *kst-rtx* 10)
        (fn-ks-execute *kst-event* *kst-snapshots* (kst-replay-rows *kst-after*)
                       *kst-ml* :verified :verified 8 *kst-rtx* 10)))
; Hypothesis removal (a statement): an absent MSGID's refusal is not the
; plan of nothing (nil).
(must-fail
 (assert-event
  (equal (fn-ks-redecide-plan nil *kst-snapshots* (kst-replay-rows *kst-after*)
                              *kst-ml* :verified :verified)
         (fn-ks-plan nil *kst-snapshots* (kst-replay-rows *kst-after*)
                     *kst-ml* :verified :verified))))
; Hypothesis removal (not acted): after the redecide the refusal is not the
; plan (which declines not-current).
(assert-event
 (equal (fn-ks-plan *kst-event* (cdr (kst-redecided))
                    (kst-replay-rows *kst-after*) *kst-ml* :verified :verified)
        '(:decline :not-current)))
(must-fail
 (assert-event
  (equal (kst-redecided-twice-plan (kst-replay-rows *kst-after*))
         (fn-ks-plan *kst-event* (cdr (kst-redecided))
                     (kst-replay-rows *kst-after*) *kst-ml* :verified
                     :verified))))
