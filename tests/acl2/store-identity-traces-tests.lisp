; Composed identity-journal traces through the public store-node transitions.
;
; The observed hybrid values exercise the durable grammar and replay plumbing;
; they do not claim that ACL2 proves the native signature primitives.  Those
; observations remain in the documented crypto trust boundary.
(in-package "ACL2")
(include-book "../../books/store-observed")
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
(defconst *sit-snapshot*
  (fn-hsig-keyring-snapshot *sit-principal* *sit-keys*))

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
(defconst *sit-enrollment*
  (fn-hsig-keyring-event 0 0 0 1 *sit-principal* *sit-keys*))
(defconst *sit-after-enrollment*
  (fn-sit-commit-identity (fn-sn-initial *sit-groups* 32)
                          *sit-enrollment*))
(assert-event (equal (fn-sf-phase (fn-sn-files *sit-after-enrollment*)) :ready))
(assert-event (equal (fn-sn-keyring-snapshots *sit-after-enrollment*)
                     (list *sit-enrollment*)))

; The signed composite binds its embedded legacy record byte-for-byte.  The
; two :verified observations below stand for the native primitive results.
(defconst *sit-signed-record*
  (fn-record-make 1 1 1 "<signed@example.invalid>" *sit-source* *sit-groups*
                  "signed-obligation" "signed-subject" "signed-release" 3))
(defconst *sit-composite*
  (fn-hsig-authorized-article-event
   1 1 1 1 *sit-snapshot* "<signed@example.invalid>"
   (fn-record-string-octets "signed-subject")
   (fn-record-encode *sit-signed-record*)
   *sit-principal* *sit-keys* *sit-source* *sit-signatures* *sit-ml-key*
   :verified :verified))
(defconst *sit-after-composite*
  (fn-sit-commit-identity *sit-after-enrollment* *sit-composite*))
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
(defconst *sit-first-history*
  (fn-sf-records (fn-sn-files *sit-after-composite*)))
(defconst *sit-first-open*
  (fn-sn-open-observed *sit-groups* 32 2 *sit-first-history*))
(assert-event (fn-sn-open-okp *sit-first-open*))
(defconst *sit-reopened* (fn-sn-open-state *sit-first-open*))
(assert-event (equal (fn-sn-keyring-snapshots *sit-reopened*)
                     (list *sit-enrollment*)))
(assert-event
 (equal (fn-sn-verdict-lookup *sit-reopened* "<signed@example.invalid>")
        (fn-sn-verdict-lookup *sit-after-composite* "<signed@example.invalid>")))
(assert-event (equal (fn-article-payload
                      (car (fn-stx-store (fn-sn-node *sit-reopened*))))
                     *sit-source*))
(defconst *sit-reopened-ready* (fn-sit-barriers *sit-reopened* 5))
(assert-event (equal (fn-sf-phase (fn-sn-files *sit-reopened-ready*)) :ready))

; Refusal burns allocator txid 2 but consumes no journal sequence.  The next
; durable legacy record therefore has sequence 2 and txid 3.
(defconst *sit-reserved-refusal* (fn-sit-reserve *sit-reopened-ready*))
(defconst *sit-refused* (fn-sn-refuse-reservation *sit-reserved-refusal* 2))
(assert-event (equal (fn-sf-frontier (fn-sn-files *sit-refused*)) 3))
(assert-event (equal (fn-sf-successes (fn-sn-files *sit-refused*)) nil))

(defconst *sit-legacy*
  (fn-record-make 2 3 3 "<legacy@example.invalid>" '(76 13 10) *sit-groups*
                  "legacy-obligation" "legacy-subject" "legacy-release" 2))
(defconst *sit-after-legacy* (fn-sit-commit-legacy *sit-refused* *sit-legacy*))
(assert-event (equal (fn-sf-successes (fn-sn-files *sit-after-legacy*))
                     '((2 . 3))))
(assert-event
 (equal (fn-stx-verdict-token
         (fn-sn-verdict-lookup *sit-after-legacy* "<legacy@example.invalid>"))
        :unverified))

; A retention event shares the journal and allocator namespaces without
; allocating another article.
(defconst *sit-retention*
  (fn-store-retention-event-make :undertake 3 4 4
                                 "forward-obligation" "forward-subject"
                                 "forward-evidence" 5))
(defconst *sit-finished*
  (fn-sit-commit-retention *sit-after-legacy* *sit-retention*))
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
(defconst *sit-history* (fn-sf-records (fn-sn-files *sit-finished*)))
(defconst *sit-open* (fn-sn-open-observed *sit-groups* 32 5 *sit-history*))
(assert-event (fn-sn-open-okp *sit-open*))
(defconst *sit-recovered* (fn-sn-open-state *sit-open*))
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
(defconst *sit-orphan-record*
  (fn-record-make 0 0 0 "<orphan@example.invalid>" *sit-source* *sit-groups*
                  "orphan-obligation" "orphan-subject" "orphan-release" 3))
(defconst *sit-orphan-composite*
  (fn-hsig-authorized-article-event
   0 0 0 1 *sit-snapshot* "<orphan@example.invalid>"
   (fn-record-string-octets "orphan-subject")
   (fn-record-encode *sit-orphan-record*)
   *sit-principal* *sit-keys* *sit-source* *sit-signatures* *sit-ml-key*
   :verified :verified))
(defconst *sit-orphan-history* (list *sit-orphan-composite*))
(assert-event (fn-stxa-bindsp *sit-orphan-composite*))
(assert-event (fn-sn-observed-historyp 1 *sit-orphan-history*))
(assert-event (fn-sf-history-recoverablep *sit-groups* 32 *sit-orphan-history* 1))
(assert-event (equal (fn-stxk-context-kind
                      (fn-replay-identity *sit-orphan-history*)) :fault))
(defconst *sit-orphan-recovered*
  (fn-sn-recover (fn-sn-observed-seed *sit-groups* 32 1 *sit-orphan-history*)))
(assert-event (equal (fn-sf-phase (fn-sn-files *sit-orphan-recovered*)) :fault))
(assert-event (equal (fn-sf-records (fn-sn-files *sit-orphan-recovered*))
                     *sit-orphan-history*))
(assert-event (not (fn-sn-open-okp
                    (fn-sn-open-observed *sit-groups* 32 1 *sit-orphan-history*))))
(assert-event (equal (fn-sf-phase
                      (fn-sn-files (fn-sit-barriers *sit-orphan-recovered* 5)))
                     :fault))
