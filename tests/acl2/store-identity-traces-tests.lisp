; Composed identity-journal traces through the public store-node transitions.
;
; The observed hybrid values exercise the durable grammar and replay plumbing;
; they do not claim that ACL2 proves the native signature primitives.  Those
; observations remain in the documented crypto trust boundary.
(in-package "ACL2")
(include-book "../../books/store-observed")
(include-book "../../books/codec-attach")
(include-book "../../books/crypto-attach")
(include-book "../../books/hybrid-store")

(defconst *sit-groups* '("example"))
(defconst *sit-principal* (make-list 32 :initial-element 7))
(defconst *sit-ed-key* (make-list 32 :initial-element 11))
(defconst *sit-ml-key* (make-list 1952 :initial-element 13))
(defconst *sit-keys* (list (cons :ed25519 *sit-ed-key*)
                           (cons :ml-dsa-65 *sit-ml-key*)))
(defconst *sit-signatures*
  (list (cons :ed25519 (make-list 64 :initial-element 17))
        (cons :ml-dsa-65 (make-list 3309 :initial-element 19))))
(defconst *sit-source* '(65 13 10))
(make-event `(defconst *sit-snapshot* ',(fn-hsig-keyring-snapshot *sit-principal* *sit-keys*)))

(defun fn-sit-reserve (s)
  (fn-sn-io (fn-sn-io (fn-sn-io (fn-sn-io s :start-frontier nil)
                                :frontier-file :ok)
                      :frontier-replace :ok)
            :frontier-directory :ok))

(defun fn-sit-publish (s)
  (fn-sn-io (fn-sn-io (fn-sn-io s :record-file :ok)
                      :record-link :ok)
            :record-directory :ok))

(defun fn-sit-barriers (s n)
  (declare (xargs :measure (nfix n)))
  (if (zp n) s
    (fn-sit-barriers (fn-sn-io s :recovery-barrier :ok) (1- n))))

(defun fn-sit-commit-identity (s event)
  (fn-sn-finish (fn-sit-publish (fn-sn-prepare-identity
                                 (fn-sit-reserve s) event))))

(defun fn-sit-commit-legacy (s record)
  (fn-sn-finish (fn-sit-publish (fn-sn-prepare
                                 (fn-sit-reserve s) record))))

(defun fn-sit-commit-retention (s event)
  (fn-sn-finish (fn-sit-publish (fn-sn-prepare-retention
                                 (fn-sit-reserve s) event))))

; First enrollment is journal sequence 0 and allocator txid 0.  Publication
; must compare the identity sequence with the carried identity cursor, not
; with the already-advanced reservation frontier.
(make-event `(defconst *sit-enrollment* ',(fn-hsig-keyring-event 0 0 0 1 *sit-principal* *sit-keys*)))
(make-event `(defconst *sit-after-enrollment* ',(fn-sit-commit-identity (fn-sn-initial *sit-groups* 32)
                          *sit-enrollment*)))
(assert-event (equal (fn-sf-phase (fn-sn-files *sit-after-enrollment*)) :ready))
(assert-event (equal (fn-sn-keyring-snapshots *sit-after-enrollment*)
                     (list *sit-enrollment*)))

; The signed composite binds its embedded legacy record byte-for-byte.  The
; two :verified observations below stand for the native primitive results.
(make-event `(defconst *sit-signed-record* ',(fn-record-make 1 1 1 "<signed@example.invalid>" *sit-source* *sit-groups*
                  "signed-obligation" "signed-subject" "signed-release" 3 841000000)))
(make-event `(defconst *sit-composite* ',(fn-hsig-authorized-article-event
   1 1 1 1 *sit-snapshot* "<signed@example.invalid>"
   (fn-record-string-octets "signed-subject")
   (fn-record-encode-impl *sit-signed-record*)
   *sit-principal* *sit-keys* *sit-source* *sit-signatures* *sit-ml-key*
   :verified :verified)))
(make-event `(defconst *sit-after-composite* ',(fn-sit-commit-identity *sit-after-enrollment* *sit-composite*)))
(assert-event (equal (fn-sf-successes (fn-sn-files *sit-after-composite*))
                     '((0 . 0) (1 . 1))))
(assert-event (equal (fn-article-payload
                      (car (fn-stx-store (fn-sn-node *sit-after-composite*))))
                     *sit-source*))
(assert-event
 (equal (fn-stx-verdict-token
         (fn-sn-verdict-lookup *sit-after-composite* "<signed@example.invalid>"))
        :verified))

; Reopen from the actual durable record list, rather than calling an inner
; replay constructor.  Snapshot, historical verdict, and exact source survive.
(make-event `(defconst *sit-first-history* ',(fn-sf-records (fn-sn-files *sit-after-composite*))))
(make-event `(defconst *sit-first-open* ',(fn-sn-open-observed *sit-groups* 32 2 *sit-first-history*)))
(assert-event (fn-sn-open-okp *sit-first-open*))
(make-event `(defconst *sit-reopened* ',(fn-sn-open-state *sit-first-open*)))
(assert-event (equal (fn-sn-keyring-snapshots *sit-reopened*)
                     (list *sit-enrollment*)))
(assert-event
 (equal (fn-sn-verdict-lookup *sit-reopened* "<signed@example.invalid>")
        (fn-sn-verdict-lookup *sit-after-composite* "<signed@example.invalid>")))
(assert-event (equal (fn-article-payload
                      (car (fn-stx-store (fn-sn-node *sit-reopened*))))
                     *sit-source*))
(make-event `(defconst *sit-reopened-ready* ',(fn-sit-barriers *sit-reopened* 5)))
(assert-event (equal (fn-sf-phase (fn-sn-files *sit-reopened-ready*)) :ready))

; Refusal burns allocator txid 2 but consumes no journal sequence.  The next
; durable legacy record therefore has sequence 2 and txid 3.
(make-event `(defconst *sit-reserved-refusal* ',(fn-sit-reserve *sit-reopened-ready*)))
(make-event `(defconst *sit-refused* ',(fn-sn-refuse-reservation *sit-reserved-refusal* 2)))
(assert-event (equal (fn-sf-frontier (fn-sn-files *sit-refused*)) 3))
(assert-event (equal (fn-sf-successes (fn-sn-files *sit-refused*)) nil))

(make-event `(defconst *sit-legacy* ',(fn-record-make 2 3 3 "<legacy@example.invalid>" '(76 13 10) *sit-groups*
                  "legacy-obligation" "legacy-subject" "legacy-release" 2 841000000)))
(make-event `(defconst *sit-after-legacy* ',(fn-sit-commit-legacy *sit-refused* *sit-legacy*)))
(assert-event (equal (fn-sf-successes (fn-sn-files *sit-after-legacy*))
                     '((2 . 3))))
(assert-event
 (equal (fn-stx-verdict-token
         (fn-sn-verdict-lookup *sit-after-legacy* "<legacy@example.invalid>"))
        :unverified))

; A retention event shares the journal and allocator namespaces without
; allocating another article.
(make-event `(defconst *sit-retention* ',(fn-store-retention-event-make :undertake 3 4 4
                                 "forward-obligation" "forward-subject"
                                 "forward-evidence" 5)))
(make-event `(defconst *sit-finished* ',(fn-sit-commit-retention *sit-after-legacy* *sit-retention*)))
(assert-event (equal (fn-sf-successes (fn-sn-files *sit-finished*))
                     '((2 . 3) (3 . 4))))
(assert-event (equal (len (fn-stx-store (fn-sn-node *sit-finished*))) 2))
(assert-event
 (consp (fn-retain-find-id
         "forward-obligation"
         (fn-retain-pins (fn-node-retention (fn-sn-node *sit-finished*))))))

; The final reopen is the regression: journal next sequence is 4 while the
; allocator frontier is 5.  Recovery must retain both identities, both
; articles exactly once, the burned gap, and the retention event.
(make-event `(defconst *sit-history* ',(fn-sf-records (fn-sn-files *sit-finished*))))
(make-event `(defconst *sit-open* ',(fn-sn-open-observed *sit-groups* 32 5 *sit-history*)))
(assert-event (fn-sn-open-okp *sit-open*))
(make-event `(defconst *sit-recovered* ',(fn-sn-open-state *sit-open*)))
(assert-event (equal (fn-sf-successes (fn-sn-files *sit-recovered*))
                     nil))
(assert-event (equal (len (fn-stx-store (fn-sn-node *sit-recovered*))) 2))
(assert-event (equal (fn-sn-keyring-snapshots *sit-recovered*)
                     (list *sit-enrollment*)))
(assert-event
 (equal (fn-sn-verdict-lookup *sit-recovered* "<signed@example.invalid>")
        (fn-sn-verdict-lookup *sit-after-composite* "<signed@example.invalid>")))
(assert-event
 (equal (fn-sn-verdict-lookup *sit-recovered* "<legacy@example.invalid>") nil))
; A legacy fn-r has no durable verdict bytes.  Its live :unverified result
; above is intentionally absent after reopen; recovery neither invents
; historical authority nor re-evaluates it under the current keyring.
(assert-event (equal (fn-article-payload
                      (car (last (fn-stx-store (fn-sn-node *sit-recovered*)))))
                     *sit-source*))
(assert-event
(consp (fn-retain-find-id
         "forward-obligation"
         (fn-retain-pins (fn-node-retention (fn-sn-node *sit-recovered*))))))

; Structurally bound signed article, but no durable enrollment precedes it.
; The ordinary node replay accepts its article; the independent identity
; replay correctly rejects its missing historical snapshot. The composed
; recovery must report a fault, never open an empty node successfully.
(make-event `(defconst *sit-orphan-record* ',(fn-record-make 0 0 0 "<orphan@example.invalid>" *sit-source* *sit-groups*
                  "orphan-obligation" "orphan-subject" "orphan-release" 3 841000000)))
(make-event `(defconst *sit-orphan-composite* ',(fn-hsig-authorized-article-event
   0 0 0 1 *sit-snapshot* "<orphan@example.invalid>"
   (fn-record-string-octets "orphan-subject")
   (fn-record-encode-impl *sit-orphan-record*)
   *sit-principal* *sit-keys* *sit-source* *sit-signatures* *sit-ml-key*
   :verified :verified)))
(make-event `(defconst *sit-orphan-history* ',(list *sit-orphan-composite*)))
(assert-event (fn-stxa-bindsp *sit-orphan-composite*))
(assert-event (fn-sn-observed-historyp 1 *sit-orphan-history*))
(assert-event (fn-sf-history-recoverablep *sit-groups* 32 *sit-orphan-history* 1))
(assert-event (equal (fn-stxk-context-kind
                      (fn-replay-identity *sit-orphan-history*)) :fault))
(make-event `(defconst *sit-orphan-recovered* ',(fn-sn-recover (fn-sn-observed-seed *sit-groups* 32 1 *sit-orphan-history*))))
(assert-event (equal (fn-sf-phase (fn-sn-files *sit-orphan-recovered*)) :fault))
(assert-event (equal (fn-sf-records (fn-sn-files *sit-orphan-recovered*))
                     *sit-orphan-history*))
(assert-event (not (fn-sn-open-okp
                    (fn-sn-open-observed *sit-groups* 32 1 *sit-orphan-history*))))
(assert-event (equal (fn-sf-phase
                      (fn-sn-files (fn-sit-barriers *sit-orphan-recovered* 5)))
                     :fault))

; The selected version-1 path publishes the received portable carrier while
; retaining the signed exact source and ACL2-derived identity in the parent.
; Reopen reconstructs the historical verdict from the same bound composite.
(defun fn-sit-line (text)
  (append (fn-record-string-octets text) '(13 10)))
(defconst *sit-carried-source*
  (append (fn-sit-line "From: author@example.invalid")
          (fn-sit-line "Date: Wed, 23 Sep 2026 12:00:00 +0000")
          (fn-sit-line "Newsgroups: example")
          (fn-sit-line "Subject: signed exact source")
          (fn-sit-line "Message-ID: <carried@example.invalid>")
          '(13 10 98 111 100 121 13 10)))
(make-event `(defconst *sit-carried-received*
               ',(fn-hc-render-at-most *fn-article-max-octets*
                                       *sit-carried-source* *sit-principal*
                                       *sit-keys* *sit-signatures*)))
(assert-event (consp *sit-carried-received*))
(make-event `(defconst *sit-carried-subject-id*
               ',(fn-id-subject-of-payload *sit-carried-received*)))
(defconst *sit-carried-subject*
  (fn-record-octets-string (fn-id-text *sit-carried-subject-id*)))
(defconst *sit-carried-obligation*
  (fn-record-octets-string
   (fn-id-text
    (fn-id-obligation-of
     (fn-record-string-octets "<carried@example.invalid>")
     *sit-carried-subject-id*))))
(make-event `(defconst *sit-carried-composite*
               ',(fn-hsig-authorized-carried-submission-event
                  1 1 1 1 *sit-snapshot* "<carried@example.invalid>"
                  *sit-carried-source* *sit-carried-received* *sit-groups*
                  *sit-carried-obligation* *sit-carried-subject*
                  "carried-release"
                  (fn-charge-for-payload (len *sit-carried-received*))
                  *sit-principal* *sit-keys* *sit-signatures* *sit-ml-key*
                  :verified :verified
                  (fn-clock-observation 1 841000000000 0 t))))
(assert-event (fn-stxa-p *sit-carried-composite*))
(assert-event (equal (fn-stxa-schema *sit-carried-composite*) 1))
(make-event `(defconst *sit-after-carried*
               ',(fn-sit-commit-identity *sit-after-enrollment*
                                         *sit-carried-composite*)))
(assert-event (equal (fn-sf-phase (fn-sn-files *sit-after-carried*)) :ready))
(assert-event
 (equal (fn-article-payload
         (car (fn-stx-store (fn-sn-node *sit-after-carried*))))
        *sit-carried-received*))
(assert-event
 (equal (fn-stx-verdict-detail
         (fn-sn-verdict-lookup *sit-after-carried*
                               "<carried@example.invalid>"))
        *sit-principal*))
(make-event `(defconst *sit-carried-history*
               ',(fn-sf-records (fn-sn-files *sit-after-carried*))))
(make-event `(defconst *sit-carried-open*
               ',(fn-sn-open-observed *sit-groups* 32 2
                                     *sit-carried-history*)))
(assert-event (fn-sn-open-okp *sit-carried-open*))
(make-event `(defconst *sit-carried-reopened*
               ',(fn-sn-open-state *sit-carried-open*)))
(assert-event
 (equal (fn-article-payload
         (car (fn-stx-store (fn-sn-node *sit-carried-reopened*))))
        *sit-carried-received*))
(assert-event
 (equal (fn-sn-verdict-lookup *sit-carried-reopened*
                              "<carried@example.invalid>")
        (fn-sn-verdict-lookup *sit-after-carried*
                              "<carried@example.invalid>")))
(assert-event
 (equal (fn-stxa-authored-source (cadr *sit-carried-history*))
        *sit-carried-source*))

; ---------------------------------------------------------------------------
; Teeth for the two arms `books/store-node-traces' grew on 2026-09-22.
;
; The deferred link (`fn-snt-deferred-linkp'): a reachable record phase whose
; staged candidate is NOT an article record, which is the shape
; `fn-sn-prepare-retention' and `fn-sn-prepare-identity' leave and which the
; article arm of the relation is false of.  The witnesses are the same
; publications this book already commits, stopped one step earlier, so they
; separate the two arms by the candidate's kind and not by a weaker clause.
(make-event `(defconst *sit-staged-retention* ',(fn-sn-prepare-retention (fn-sit-reserve *sit-after-legacy*) *sit-retention*)))
(assert-event (equal (fn-sf-phase (fn-sn-files *sit-staged-retention*))
                     :record-staged))
(assert-event
 (not (fn-record-p (fn-sf-record-candidate (fn-sn-files *sit-staged-retention*)))))
(assert-event (fn-snt-relation *sit-staged-retention*))
(assert-event (fn-snt-relation (fn-sit-publish *sit-staged-retention*)))
(assert-event
 (equal (fn-sf-phase (fn-sn-files (fn-sit-publish *sit-staged-retention*)))
        :completing))
(assert-event (fn-snt-relation (fn-sn-finish (fn-sit-publish *sit-staged-retention*))))

(make-event `(defconst *sit-staged-identity* ',(fn-sn-prepare-identity (fn-sit-reserve (fn-sn-initial *sit-groups* 32))
                          *sit-enrollment*)))
(assert-event (equal (fn-sf-phase (fn-sn-files *sit-staged-identity*))
                     :record-staged))
(assert-event
 (not (fn-record-p (fn-sf-record-candidate (fn-sn-files *sit-staged-identity*)))))
(assert-event (fn-snt-relation *sit-staged-identity*))
(assert-event (fn-snt-relation (fn-sit-publish *sit-staged-identity*)))
(assert-event (fn-snt-relation (fn-sn-finish (fn-sit-publish *sit-staged-identity*))))

; The article arm is still exercised, and by a state of the same machine: a
; staged legacy record IS a `fn-record-p', so the relation takes the pending
; link there.  Without this pair the deferred assertions above would not
; separate the two arms.
(make-event `(defconst *sit-staged-legacy* ',(fn-sn-prepare (fn-sit-reserve *sit-refused*) *sit-legacy*)))
(assert-event
 (fn-record-p (fn-sf-record-candidate (fn-sn-files *sit-staged-legacy*))))
(assert-event (fn-snt-relation *sit-staged-legacy*))

; A known abort of a staged retention candidate returns to `:ready' with the
; live node at the durable frontier, which is the advance `6ab2c783' left out
; of `fn-sn-known-abort' (books/store-node-resolution).  Without it the state
; below is `:ready' with a node one transaction id behind its own frontier
; and the relation is false of it.
(make-event `(defconst *sit-retention-aborted* ',(fn-sn-known-abort *sit-staged-retention*)))
(assert-event (equal (fn-sf-phase (fn-sn-files *sit-retention-aborted*)) :ready))
(assert-event
 (equal (fn-state-next-txid (fn-node-acceptance (fn-sn-node *sit-retention-aborted*)))
        (fn-sf-frontier (fn-sn-files *sit-retention-aborted*))))
(assert-event (fn-snt-relation *sit-retention-aborted*))

; The `:fault' arm (`40bb3f74'): the composed recovery above publishes it,
; and the relation now has a case for it.  `*sit-orphan-recovered*' is the
; reachable witness this book already builds; the seed it comes from is the
; `:replaying' state the same arm is proved from.
(assert-event
 (fn-snt-relation (fn-sn-observed-seed *sit-groups* 32 1 *sit-orphan-history*)))
(assert-event (fn-snt-relation *sit-orphan-recovered*))
