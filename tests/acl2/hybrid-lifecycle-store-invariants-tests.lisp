; Reachable kind-3 lifecycle after an accepted kind-4 historical verdict.
(in-package "ACL2")
(include-book "../../books/hybrid-lifecycle-store-invariants")
(include-book "../../books/store-identity-sequence-invariants")
(include-book "store-identity-traces-tests")
(include-book "std/testing/assert-equal" :dir :system)
(include-book "std/testing/must-fail" :dir :system)

(defconst *hls-b* (make-list 32 :initial-element 8))
(defconst *hls-b-keys*
  (list (cons :ed25519 (make-list 32 :initial-element 21))
        (cons :ml-dsa-65 (make-list 1952 :initial-element 22))))
(defconst *hls-a-new-keys*
  (list (cons :ed25519 (make-list 32 :initial-element 23))
        (cons :ml-dsa-65 (make-list 1952 :initial-element 24))))

; *sit-after-composite* has a real accepted article/verdict at journal
; sequence 1, preceded by A's generation-1 enrollment at sequence 0.
(assert-event (fn-snt-relation *sit-after-composite*))
(assert-event (fn-sn-identity-sequencep *sit-after-composite*))
; A kind-4 completion really *does* add a historical verdict. This is the
; counterexample when the snapshot-kind premise is removed from the theorem.
(make-event
 `(defconst *hls-kind4-completing*
    ',(fn-sit-publish
       (fn-sn-prepare-identity (fn-sit-reserve *sit-after-enrollment*)
                               *sit-composite*))))
(assert-event (fn-sn-completion-enabledp *hls-kind4-completing*))
(must-fail
 (assert-event
  (equal (fn-sn-verdicts (fn-sn-finish *hls-kind4-completing*))
         (fn-sn-verdicts *hls-kind4-completing*))))
(make-event
 `(defconst *hls-b2*
    ',(fn-hl-enroll-event 2 2 2 2 *hls-b* *hls-b-keys*
                          (fn-sn-keyring-snapshots *sit-after-composite*))))
(make-event
 `(defconst *hls-b-completing*
    ',(fn-sit-publish
       (fn-sn-prepare-identity (fn-sit-reserve *sit-after-composite*)
                               *hls-b2*))))
(assert-event (fn-sn-completion-enabledp *hls-b-completing*))
(assert-event (fn-stxk-p (fn-sn-completion-record *hls-b-completing*)))
(assert-event (fn-snt-relation *hls-b-completing*))
(assert-event (fn-sn-identity-sequencep *hls-b-completing*))
; Before the record-directory observation, `fn-sn-finish` cannot install B2.
; Dropping the completion premise from the selector projection is false here.
(make-event
 `(defconst *hls-b-staged*
    ',(fn-sn-prepare-identity (fn-sit-reserve *sit-after-composite*)
                              *hls-b2*)))
(assert-event (not (fn-sn-completion-enabledp *hls-b-staged*)))
(must-fail
 (assert-event
  (equal (fn-hls-current-enrollment (fn-sn-finish *hls-b-staged*) 2)
         (fn-hl-current-enrollment
          2 (fn-stxk-context-snapshots
             (fn-replay-identity-step
              (fn-sn-identity-context *hls-b-staged*) *hls-b2*))))))
; Model crash before durable record-directory publication: B2 never enters
; the history, even though it was a well-formed staged candidate.
(make-event
 `(defconst *hls-prepublication-recovered*
    ',(fn-sn-recover (fn-sn-crash *hls-b-staged* :old :absent))))
(assert-event (equal (fn-sf-phase (fn-sn-files *hls-prepublication-recovered*))
                     :recovering))
(assert-event (fn-snt-relation *hls-prepublication-recovered*))
(assert-equal (fn-hls-current-enrollment *hls-prepublication-recovered* 1)
              (list *sit-enrollment* *sit-principal* *sit-keys*))
(assert-equal (fn-hls-current-enrollment *hls-prepublication-recovered* 2)
              nil)
(assert-equal
 (fn-sn-verdict-lookup *hls-prepublication-recovered*
                       "<signed@example.invalid>")
 (fn-sn-verdict-lookup *sit-after-composite* "<signed@example.invalid>"))
; A directory-observed B2 record survives a crash even before live finish.
(make-event
 `(defconst *hls-published-recovered*
    ',(fn-sn-recover (fn-sn-crash *hls-b-completing* :old :present))))
(assert-event (equal (fn-sf-phase (fn-sn-files *hls-published-recovered*))
                     :recovering))
(assert-event (fn-snt-relation *hls-published-recovered*))
(assert-equal (fn-hls-current-enrollment *hls-published-recovered* 1)
              (list *sit-enrollment* *sit-principal* *sit-keys*))
(assert-equal (fn-hls-current-enrollment *hls-published-recovered* 2)
              (list *hls-b2* *hls-b* *hls-b-keys*))
(assert-equal
 (fn-sn-verdict-lookup *hls-published-recovered*
                       "<signed@example.invalid>")
 (fn-sn-verdict-lookup *sit-after-composite* "<signed@example.invalid>"))
(make-event `(defconst *hls-after-b* ',(fn-sn-finish *hls-b-completing*)))
(assert-event (fn-snt-relation *hls-after-b*))
(assert-event (fn-sn-identity-sequencep *hls-after-b*))
(assert-equal (fn-hls-current-enrollment *hls-after-b* 1)
              (list *sit-enrollment* *sit-principal* *sit-keys*))
(assert-equal (fn-hls-current-enrollment *hls-after-b* 2)
              (list *hls-b2* *hls-b* *hls-b-keys*))
(assert-equal (fn-sn-verdict-lookup *hls-after-b* "<signed@example.invalid>")
              (fn-sn-verdict-lookup *sit-after-composite*
                                    "<signed@example.invalid>"))

(make-event
 `(defconst *hls-a3*
    ',(fn-hl-enroll-event 3 3 3 3 *sit-principal* *hls-a-new-keys*
                          (fn-sn-keyring-snapshots *hls-after-b*))))
(make-event
 `(defconst *hls-after-a3*
    ',(fn-sit-commit-identity *hls-after-b* *hls-a3*)))
(assert-event (fn-snt-relation *hls-after-a3*))
(assert-event (fn-sn-identity-sequencep *hls-after-a3*))
(assert-equal (fn-hls-current-enrollment *hls-after-a3* 1) nil)
(assert-equal (fn-hls-current-enrollment *hls-after-a3* 3)
              (list *hls-a3* *sit-principal* *hls-a-new-keys*))
(assert-equal (fn-hls-current-enrollment *hls-after-a3* 2)
              (list *hls-b2* *hls-b* *hls-b-keys*))
(assert-equal (fn-sn-verdict-lookup *hls-after-a3* "<signed@example.invalid>")
              (fn-sn-verdict-lookup *sit-after-composite*
                                    "<signed@example.invalid>"))

(make-event
 `(defconst *hls-a4*
    ',(fn-hl-revoke-event 4 4 4 4 *sit-principal*
                          (fn-sn-keyring-snapshots *hls-after-a3*))))
(make-event
 `(defconst *hls-after-a4*
    ',(fn-sit-commit-identity *hls-after-a3* *hls-a4*)))
(assert-event (fn-snt-relation *hls-after-a4*))
(assert-event (fn-sn-identity-sequencep *hls-after-a4*))
(assert-equal (fn-hls-current-enrollment *hls-after-a4* 3) nil)
(assert-equal (fn-hls-current-enrollment *hls-after-a4* 2)
              (list *hls-b2* *hls-b* *hls-b-keys*))
(assert-equal (fn-sn-verdict-lookup *hls-after-a4* "<signed@example.invalid>")
              (fn-sn-verdict-lookup *sit-after-composite*
                                    "<signed@example.invalid>"))

; Reopen the actual durable five-record Store, not a hand-built identity
; context. The first accepted article still names A1 after A3 and A4.
(make-event
 `(defconst *hls-open*
    ',(fn-sn-open-observed
       *sit-groups* 32 5 (fn-sf-records (fn-sn-files *hls-after-a4*)))))
(assert-event (fn-sn-open-okp *hls-open*))
(make-event `(defconst *hls-reopened* ',(fn-sn-open-state *hls-open*)))
(assert-event (fn-snt-relation *hls-reopened*))
(assert-event (fn-sn-identity-sequencep *hls-reopened*))
(assert-equal (fn-sn-keyring-snapshots *hls-reopened*)
              (list *hls-a4* *hls-a3* *hls-b2* *sit-enrollment*))
(assert-equal (fn-hls-current-enrollment *hls-reopened* 1) nil)
(assert-equal (fn-hls-current-enrollment *hls-reopened* 3) nil)
(assert-equal (fn-hls-current-enrollment *hls-reopened* 2)
              (list *hls-b2* *hls-b* *hls-b-keys*))
(assert-equal (fn-sn-verdict-lookup *hls-reopened* "<signed@example.invalid>")
              (fn-sn-verdict-lookup *sit-after-composite*
                                    "<signed@example.invalid>"))
(assert-equal (fn-stxk-find 1 (fn-sn-keyring-snapshots *hls-reopened*))
              *sit-enrollment*)
