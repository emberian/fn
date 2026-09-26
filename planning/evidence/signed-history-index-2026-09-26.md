# Signed correspondence stops growing with history (lane signed-history-index, 2026-09-26)

Brief: `build/coordinator/queue/w3-signed-history-index.txt` (rank 2 of the
next convergence, planning/review-2026-09-26-gpt6-answers.md §3 "Order of
attack", §4). Ids: PRF-144, PKT-330. Branch `lane/signed-history-index` from
dev 197b3437. Nothing here is deployed; native runs are loopback in
`/tank/fn/scratch/signed-history-index/` on hbox.

## What now works

1. **A signed POST's identity prepare no longer replays the history.** Before,
   `fn-ccar-sn-prepare-identity` staged through `fn-sf-prepare-record`, whose
   `fn-sf-history-recoverablep` replays `(append records (list event))`:
   every record re-recognized and every composite decoded and prepared, per
   signed POST (46.7 % of a signed POST in carry-kind's profile; PKT-223).
   Now it stages through `fn-spc-stage-record` (the specification's
   candidate predicate, no replay), as the article prepare has since w18.
2. **The BP receiver's signed-entry lookups read a maintained Message-ID
   index.** Before, `fn-bpaj-record-for-msgid` walked the whole history and
   decoded every kind-4 composite once per lookup, and
   `fn-bpaj-store-record-accepted-fast` did the same through
   `fn-bpr-article-records` (PKT-291 item 2). Now both read the Store's
   derived index: a character trie from Message-ID to the article records
   committed under it.

## Assurance chain

Prepare: native entry `fnn-owner-identity-commit` (host/native/owner.lisp)
→ `fn-owner-prepare-identity` (host/owner-host.lisp) →
`fn-ccar-ocfg-prepare-identity` → `fn-ccar-sn-prepare-identity` (executed,
guard-verified under `fn-sn-statep`) → refinement
`fn-ccar-sn-prepare-identity-is-sn-prepare-identity-under-relation` and, for
the host line, `fn-ccar-ocfg-prepare-identity-is-ocfg-step-under-relation`
→ maintained relation `fn-snt-relation` (conjoined by `fn-own-relation`;
established at observed open, preserved by the owner transition family, the
same premise as `fn-opc-prepare-equals-owner-event-under-relation`) →
behaviour: the staged composite and verdict are the specification's, so
PRF-117 (the D23 source decision) and `fn-sr-a-signed-retry-is-already-stored`
(the D25 duplicate) hold of what the host stages, unrestated → observed: the
signed POST rows below.

Index: native entry `fnn-bpapp-accept-locked` (host/native/bp-app.lisp) →
`fn-bprj-request-action` → `fn-bpaj-dispatch-fast` → the lookups →
`fn-cei-msgid-records` over `fn-sn-event-index` → refinement
`fn-bpaj-indexed-records-are-the-walk` under `fn-bpaj-store-indexedp` →
maintained relation `fn-cei-correspondencep` of the derived index and the
history (`fn-ceis-relatedp`): **established** by `fn-sn-initial` (empty
build) and by every open (`fn-sn-open-observed`, `fn-cpo-open-observed` and
the checkpoint open install `fn-cei-build` of the history they read);
**preserved** by every Store transition
(books/consumer-event-index-store-invariants.lisp: prepare, prepare-identity,
-retention, -consumer, -topic, io, finish, crash, recover), and the one
transition that grows the history, `fn-sn-io`'s record-directory append,
extends the index by `fn-cei-put` of the appended event
(`fn-cei-extend-preserves-correspondence`) → behaviour: PRF-132's keystones
(`fn-bpaj-dispatch-never-resubmits-a-stored-article`,
`fn-bpaj-dispatch-binds-the-stores-own-record`), now over the index with the
premise named.

## PRF-144, the theorems

| keystone | book | statement |
| --- | --- | --- |
| `fn-ccar-sn-prepare-identity-is-sn-prepare-identity-under-relation` | owner-commit-carried | `(fn-snt-relation s)` ⇒ `(fn-ccar-sn-prepare-identity s event)` = `(fn-sn-prepare-identity s event)` |
| `fn-ccar-ocfg-prepare-identity-is-ocfg-step-under-relation` | owner-commit-carried | `(fn-own-relation (fn-ocfg-owner oc))` ⇒ `(fn-ccar-ocfg-prepare-identity oc event)` = `(fn-ocfg-step oc (list :store (list :prepare-identity event)))`; host line: host/owner-host.lisp `fn-owner-prepare-identity` |
| `fn-cei-msgid-records-of-correspondence` | consumer-event-index | `(stringp msgid)` ∧ `(fn-cei-correspondencep index events)` ⇒ `(fn-cei-msgid-records msgid index)` = `(fn-cei-article-records-for msgid events)` |
| `fn-bpaj-indexed-records-are-the-walk` | bp-native-app-fast | `(fn-bpaj-store-indexedp store)` ∧ `(stringp msgid)` ⇒ `(fn-cei-msgid-records msgid (fn-sn-event-index store))` = `(fn-bpaj-record-for-msgid msgid (fn-sf-records (fn-sn-files store)))` |

Bridge lemma: `fn-spc-related-identity-candidate-is-recoverable`
(store-prepare-correspondence): in a `:reserved` state under
`fn-snt-relation`, a `fn-sf-candidatep` event the live node applies leaves
`(append records (list event))` recoverable at the frontier (from the
relation's `:reserved` arm and `fn-snt-deferred-preparation-outcome`). The
verdict the prepare stages is therefore the specification's; PRF-117 and
`fn-sr-a-signed-retry-is-already-stored` are cited, not restated.

The two carry-kind equalities without hypothesis
(`fn-ccar-sn-prepare-identity-is-sn-prepare-identity`,
`fn-ccar-ocfg-prepare-identity-is-ocfg-step`) are replaced by the two above:
they held only because the function replayed. The premise is the one the
article prepare's host keystone already carries.

The index changes three `-is-checked` equalities in bp-native-app-fast (the
store record check, the two lookups) and everything above them, and PRF-132's
two keystones: each now carries `fn-bpaj-store-indexedp`, named, closed, and
never evaluated on a served path.

Teeth:
- tests/acl2/store-events-carried-tests.lisp: reachable positive witness,
  the reserved owner reached by `fn-own-run` before a signed POST's
  composite: `fn-snt-relation` and `fn-own-relation` hold, both equalities
  hold, and the prepare stages the composite. Hypothesis removal (a
  CORRUPTED state, labelled): the same store with its groups emptied and its
  node kept: `fn-sn-statep` holds, `fn-snt-relation` does not, the
  specification refuses (its replay fails) and the incremental prepare
  stages; the conclusion fails.
- tests/acl2/bp-signed-binding-tests.lisp: the enrolled and committed Stores
  (built by the Store's own transitions) satisfy `fn-bpaj-store-indexedp`;
  the index answers the signed composite's record for its Message-ID; every
  PRF-132 witness asserts the premise; the forged-non-record witness rebuilds
  its index so the premise holds there too. New hypothesis removal (2b, a
  CORRUPTED Store, labelled): the committed Store with the index it carried
  before the commit: the premise fails, the record is in the history with the
  dispatcher's Message-ID, and the dispatcher answers `(:submit)`.
- The `(stringp msgid)` hypothesis of `fn-cei-msgid-records-of-correspondence`
  has no falsifying witness: every stored Message-ID is a string (`fn-record-p`)
  and every caller passes `fn-record-octets-string`. It is kept; no weakened
  theorem was proved (PKT-330 (5)).

## Certification (hbox, ACL2 8.7 `w28/acl2-literal-4g`, 2 jobs, 300 s)

- r1 `run-20260926T071056Z-e875` (`--affected-by` consumer-event-index,
  store-prepare-correspondence, owner-commit-carried, bp-native-app-fast,
  bp-signed-binding: 374 roots): 373 certified, 6 failed
  (`fn-bpaj-transit-record-lookup-fast-is-checked` and five includers);
  `manifests/certify-20260926T071134Z-704975.json`. Three books were over
  10 s in it (native-health 17.7 s, consumer-store-invariants 13.0 s,
  bp-node-fragment-replacement 11.2 s) with their certify-book events at 2.3,
  8.2 and 4.4 s: the box carried other lanes' loads (load average 7 to 8).
- r2 `run-20260926T072431Z-0826` (`--affected-by` bp-native-app-fast, 6
  roots): all passed, no book over 10 s;
  `manifests/certify-20260926T072459Z-774619.json`.
- r3 `run-20260926T072854Z-8db6` (the three slow books recertified alone):
  all passed, no book over 10 s;
  `manifests/certify-20260926T072913Z-810169.json`.
- The REPL (persvati for store/owner, hbox for BP) admitted every changed
  event first; the one r1 failure was a hint that let the Message-ID string
  and the index accessor open, invisible in a REPL session whose world held
  the old definitions (redefinition), which is why r2 was needed.
- `make check-lane` green in the worktree.
