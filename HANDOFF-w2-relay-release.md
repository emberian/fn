# HANDOFF w2-relay-release

Branch `w2/relay-release` from `dev` (parent `4af825a`). HEAD is the commit
that carries this file together with the work below. Worktree
`/Users/ember/dev/fn/build/lanes/w2-relay-release`. Baseline
`make certify` before any edit: exit 0, evidence
`build/acl2/certify-20260919T100405Z-84522`. No shared book was edited:
`bp-workflow*.lisp`, `bp-workflow-records.lisp` and every receiver book are
byte-identical to `dev`; the release hook is a wrapper (below).

## Per book

| Book | Status | Evidence dir (`build/acl2/`) | Theorems |
| --- | --- | --- | --- |
| `books/bp-release.lisp` | certified | `certify-20260919T104220Z-93899` | 0 (34 fns, 13 guard-verified) |
| `books/bp-release-invariants.lisp` | certified | `certify-20260919T104626Z-95251` | 45 |
| `tests/acl2/bp-release-tests.lisp` | certified | `certify-20260919T105233Z-96342` | 65 assert-event, 4 must-fail |
| `books/relay.lisp` | certified | `certify-20260919T113544Z-5422` | 0 (32 fns) |
| `books/relay-invariants.lisp` | certified | `certify-20260919T124327Z-15997` | 52 |
| `books/relay-crash-invariants.lisp` | certified | `certify-20260919T124331Z-16045` | 7 |
| `tests/acl2/relay-tests.lisp` | certified | `certify-20260919T124333Z-16071` | 61 assert-event, 4 must-fail |

Every root certified one at a time with `FN_ACL2_TIMEOUT_SECONDS=1800`.
`python3 tools/ledger.py --write` run; `make check` green; no theorem of
these books is flagged SUSPECT by the ledger. No `skip-proofs`, `defaxiom`
or `defttag`. The relay theorems were split into two books so each certifies
inside the budget (the one real cost was opening `fn-sn-node` and
`fn-bp-state-node`: 82 s versus 0.01 s for one shape lemma, measured; both
are now opaque at the top of `relay-invariants.lisp`).

## Subject and host line

The host calls `fn-bp-apply-journal-record` at `host/workflow-host.lisp:27`
(`fn-workflow-preflight-record`) and `:40` (`fn-workflow-apply-record`);
`tools/workflow_journal.py` drives the same entry. `fn-bprl-apply-journal-record`
extends it with two records and equals it on every record it accepts:

```
(defthm fn-bprl-apply-journal-record-agrees-with-host-on-bp-records
  (implies (fn-bp-journal-recordp r)
           (equal (fn-bprl-apply-journal-record s r)
                  (fn-bp-apply-journal-record s r))))
```

The host switch to the wrapper is an open item (below); until then the two
new records are refused by the host-called function, which the test book
checks.

## Keystones, verbatim (packet A, `books/bp-release-invariants.lisp`)

```
(defthm fn-bprl-authorized-receipt-evidence-matches-required
  (implies (fn-bp-authorized-receiptp config work receipt)
           (equal (fn-bprl-evidence-string (fn-bprl-receipt-evidence receipt))
                  (fn-bprl-required-evidence config work))))

(defthm fn-bprl-release-removes-the-forward-pin
  (implies (fn-bprl-decision-okp (fn-bprl-release-decision s receipt-id))
           (let* ((receipt (fn-bprl-find-receipt receipt-id (fn-bp-state-receipts s)))
                  (work (fn-bp-find-work (fn-bp-receipt-work-id receipt) (fn-bp-state-works s)))
                  (next (fn-bprl-decision-state (fn-bprl-release-decision s receipt-id))))
             (and (equal (fn-retain-find-id (fn-bp-work-obligation-id work) (fn-bprl-pins next)) nil)
                  (equal (car (fn-retain-releases (fn-node-retention (fn-bp-state-node next))))
                         (fn-retain-make-release (fn-bp-work-obligation-id work)
                                                 (fn-bp-work-subject work) :forward
                                                 (fn-bprl-evidence-string
                                                  (fn-bprl-decision-evidence
                                                   (fn-bprl-release-decision s receipt-id)))))))))

(defthm fn-bprl-release-preserves-independent-pin
  (implies (and (fn-bprl-decision-okp (fn-bprl-release-decision s receipt-id))
                (not (equal other (fn-bp-work-obligation-id
                                   (fn-bp-find-work (fn-bp-receipt-work-id
                                                     (fn-bprl-find-receipt receipt-id (fn-bp-state-receipts s)))
                                                    (fn-bp-state-works s))))))
           (equal (fn-retain-find-id other (fn-bprl-pins (fn-bprl-decision-state
                                                           (fn-bprl-release-decision s receipt-id))))
                  (fn-retain-find-id other (fn-bprl-pins s)))))
;; fn-bprl-release-preserves-archive-pin: the same with other := the work's archive id.

(defthm fn-bprl-release-preserves-node-state
  (implies (fn-bprl-decision-okp (fn-bprl-release-decision s receipt-id))
           (fn-node-statep (fn-bp-state-node (fn-bprl-decision-state (fn-bprl-release-decision s receipt-id))))))
;; fn-bprl-release-preserves-state (fn-bp-statep), fn-bprl-release-preserves-binding-state
;; (hyp adds (fn-bp-binding-statep s)); fn-bprl-undertake-preserves-{node-state,state,binding-state}.

(defthm fn-bprl-undertake-pins-the-forwarding-obligation
  (implies (fn-bprl-undertake-okp s (fn-bp-find-work work-id (fn-bp-state-works s)) charge)
           (fn-bprl-work-pinnedp (fn-bprl-undertake s work-id charge)
                                 (fn-bp-find-work work-id (fn-bp-state-works s)))))

(defthm fn-bprl-no-receipt-no-release-no-peer-reliance
  (implies (not (consp (fn-bprl-find-receipt receipt-id (fn-bp-state-receipts s))))
           (and (not (fn-bprl-decision-okp (fn-bprl-release-decision s receipt-id)))
                (equal (fn-bprl-decision-state (fn-bprl-release-decision s receipt-id)) s)
                (not (fn-assume-peer-retainsp
                      (fn-bprl-find-receipt receipt-id (fn-bp-state-receipts s)) failures)))))
```

Hypothesis stack of the release keystones: `fn-bprl-decision-okp`, which is
(by `fn-bprl-decision-okp-formula`) `fn-bprl-release-okp s receipt work` =
`fn-bp-statep s`, no pending intent, not fenced, receipt found by id in
committed history, work found by the receipt's work id, the work carries that
receipt, `fn-bp-authorized-receiptp config work receipt`, node stage null,
obligation id differs from the archive id and from every archive binding id,
and the `:forward` pin present with the required evidence. Inhabited: the
test witness `*rl-receipted*` satisfies all of it and `*rl-released*` is its
release. The decision consults no A-POLICY boolean of its own: the receipt was
admitted through `fn-bp-prepare-receipt` with the explicit boolean, and
`fn-bprl-release-evidence-has-policy-shape` proves the decision yields the
`terms`/`evidence` shapes `fn-assume-policy-authorizedp` consumes.

## Keystones, verbatim (packet B, `books/relay-invariants.lisp`, `relay-crash-invariants.lisp`)

```
(defthm fn-relay-step-monotone
  (implies (and (fn-bp-statep s) (consp (fn-bp-find-work id (fn-bp-state-works s))))
           (consp (fn-bp-find-work id (fn-bp-state-works (fn-bp-result-state (fn-bp-step s event)))))))

;; fn-relay-{sender-step,accept,record-undertaking,undertake,commit-receipt}-preserves-invp:
;;   (implies (fn-relay-invp rs) (fn-relay-invp <that transition's state>))

(defthm fn-relay-crash-recover-preserves-invp
  (implies (fn-relay-invp rs)
           (fn-relay-invp (fn-relay-crash-recover rs receiver-outcome sender-result))))

(defthm fn-relay-forwarding-receipt-has-durable-onward-obligation
  (implies (and (fn-relay-invp rs) (equal (car (fn-relay-receipt rs upstream)) :forwarding))
           (let* ((entry (fn-bpr-find-receipt upstream (fn-bpr-state-receipts (fn-relay-receiver rs))))
                  (ctx (fn-bpr-receipt-entry-context entry))
                  (u (fn-relay-find-undertaking (fn-bpr-context-work-id ctx) (fn-relay-undertakings rs)))
                  (work (fn-bp-find-work (fn-relay-undertaking-onward u) (fn-bp-state-works (fn-relay-sender rs)))))
             (and (consp u) (consp work)
                  (fn-bp-work-boundp (fn-relay-node rs) work)
                  (fn-relay-content-durablep (fn-relay-node rs) ctx)))))

(defthm fn-relay-crash-recover-never-yields-a-promise-alone
  (implies (and (fn-relay-invp rs)
                (equal (car (fn-relay-receipt (fn-relay-crash-recover rs receiver-outcome sender-result) upstream))
                       :forwarding))
           ;; same four conclusions, in the recovered state
           ...))

(defthm fn-relay-receipt-kind-is-archived-or-forwarding
  (implies (and (fn-relay-invp rs) (consp (fn-relay-receipt rs upstream)))
           (fn-relay-kindp (car (fn-relay-receipt rs upstream)))))
```

Hypothesis stack: `fn-relay-invp` = `fn-relay-statep` (sender is
`fn-bp-binding-statep`, its node is `(fn-sn-node store)`, terms table and
undertakings well-formed) and every committed or pending receipt entry is
backed (known kind, content binding present, and for `:forwarding` a recorded
undertaking whose onward work is present). Inhabited: `*ry-committed*`,
`*ry-pending-committed*`, `*ry-restarted*` in the test book. The crash
constructor is `fn-bpr-commit-receipt` with `:committed`/`:absent` composed
with `fn-bp-step` on `(:restart)` then `storage-recover` with
`:committed`/`:absent`; the theorem quantifies over both outcomes.

## Teeth (all ground, all in the two test books)

Release: stale (prepared-not-committed; unknown id), duplicated (second
decision), not undertaken (committed receipt, no pin), wrong-subject,
unauthorized issuer, wrong-incarnation, insufficient terms, wrong-work
(receipt naming another work; receipt not carried by the work), archive-id
collision, staged archive transaction, no capacity, unknown work, zero charge,
second undertaking; journal: release record accepted and equals the decision
state, mismatched-evidence record refused, replayed twice refused, undertake
record accepted/refused, ordinary record identical to the host function;
`must-fail`: independent-pin without the inequality, evidence match without
authorization, release without the pin, undertake on a staged node.

Relay: forwarding intent refused with no onward work, with a pending enqueue,
with a durable work but no recorded undertaking, with a work naming other
content, with unknown terms, with A-POLICY `nil`, for an unknown context;
crash at pending enqueue (`:absent`/`:committed`) yields no promise; crash at
receipt intent yields no promise (`:absent`) or a backed promise
(`:committed`); promise survives attempt and restart; `:archived` receipt over
the same bytes with an empty sender; `:destination` is not a kind; fabricated
promise-alone and promise-unbacked states are `fn-relay-statep` and not
`fn-relay-invp`; `must-fail`: promise-alone has no undertaking, pending
enqueue is not durable, an intent is not a promise, archived has no onward
work.

## FNWF record proposal (modeled in `books/bp-release.lisp`, byte grammar open)

- `(:undertake work-id charge)`: `fn-bprl-undertake`; effect `(:undertaken work-id)`.
- `(:release receipt-id work-id subject issuer policy-id terms-id incarnation)`:
  `fn-bprl-release-decision` on `receipt-id`; accepted only if the recomputed
  typed evidence equals the record's seven fields; effect `(:released work-id)`.
- `(:relay-undertaking upstream-work-id onward-work-id)`: modeled as the
  `fn-relay-record-undertaking` transition; durable before any forwarding
  receipt intent relies on it.

## What remains

- Host switch: `host/workflow-host.lisp:27` and `:40` still call
  `fn-bp-apply-journal-record`; the wrapper is proved equal on its records.
- The retention ledger compares a string; `fn-bprl-render` is the ACL2-owned
  derivation. Typed evidence in `fn-retain-release` is a retention-book change
  (C2-10). The A-POLICY verdict is not yet a constrained call (D09).
- The release acts on the workflow's node image; propagating the released pin
  to the Store's node (`fn-sn`) is not modeled.
- Relay: content identity across later sender steps is by recorded onward
  work id plus `fn-bp-binding-statep`; Message-ID/subject/archive equalities
  are checked at `fn-relay-record-undertaking` and not carried as an invariant
  (needs a pending-agrees-with-durable invariant on the sender). The Store is
  fixed across relay steps, as in the receiver theorems. No byte grammar or
  host wiring for `:relay-undertaking`; no destination-application receipt.
- `fn-relay-statep` does not require `fn-bpr-statep` (the receiver's entry
  points check it themselves); the relay invariant needs only the entry list
  shape.
