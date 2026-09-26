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

## Measured (hbox, before and after, same conditions)

Harness `planning/evidence/signed-history-index-2026-09-26/measure_signed.py`
driven by `meas.sh` under `systemd-run --user -p MemoryMax=40G`, run
2026-09-26 07:33 to 08:10Z, the four rows interleaved (before then after at
N=1,000, then at N=10,000). Store on tmpfs (`/dev/shm`), profile `scale`
with `--max-transactions 1048576 --max-article-octets 16384`; history of N
POSTs of about 2 KiB, **32 of them hybrid-signed carriers** spread evenly,
N − 32 unsigned; then 7 rounds of one unsigned and one signed POST, each on
a fresh connection, timed from the terminating line to the reply (the
owner's whole commit). Before: dev ancestor 8d4ea42c's developer image
(commit-regression's build; nothing on the identity prepare or the BP
lookups changed between it and 197b3437). After: a888b104's developer image
(`native-after-a888b104`, built by tools/hbox_native.sh). The box carried
other lanes' loads (load average 6 to 8); tmpfs removes the storage
barrier, so the rows are the owner's CPU term, not a deployment latency.

| row | N | unsigned POST, median | signed POST, median | signed POST in the preload: first / middle / last |
| --- | ---: | ---: | ---: | --- |
| before | 1,000 | 0.043 s | **0.355 s** | 0.092 / 0.183 / 0.337 s |
| after | 1,000 | 0.043 s | **0.101 s** | 0.104 / 0.101 / 0.100 s |
| before | 10,000 | 0.047 s | **18.92 s** | 0.097 / 4.41 / 17.42 s |
| after | 10,000 | 0.048 s | **0.241 s** | 0.094 / 0.154 / 0.231 s |

Operation counts per signed POST's prepare (from the code, witnessed by the
theorems): before, `fn-sf-history-recoverablep` replays all N + 1 records
(every record re-recognized, each of the 32 + 1 composites decoded and
prepared through `fn-node-prepare`); after, no record of the history is
replayed or decoded. The before rows grow with N (0.355 → 18.9 s, ×53 for ×10
history: the replay is superlinear here). **The after rows are not flat**:
0.101 → 0.241 s (×2.4 for ×10 history). What remains grows linearly and
decodes nothing: the prepare's `fn-sf-candidatep` still takes `(len records)`
and `fn-sf-next-lower` of the history, the D25 existing-action and the
node-record check walk the node's article list, and the unsigned POST grows
the same way (0.043 → 0.048 s). These are PKT-330 (2).

The signed-record lookup, at the function level (hbox REPL over
tests/acl2/bp-signed-binding-tests: histories of N events, 32 of them the
test's signed composite, the rest plain article records with distinct
Message-IDs; the walk decodes every composite, the index none):

| lookup | N = 1,000 | N = 10,000 | counts |
| --- | ---: | ---: | --- |
| `fn-bpaj-record-for-msgid` (before), absent Message-ID | 12.5 ms | 36.5 ms | N events visited, 32 composites decoded |
| same, the signed Message-ID (32 matches) | 11.3 ms | 34.7 ms | N visited, 32 decoded |
| `fn-cei-msgid-records` (after), absent | 0.2 µs | 0.2 µs | one trie path, 0 events, 0 decodes |
| same, the signed Message-ID | 0.4 µs | 0.4 µs | one path, the 32 stored records |
| same, a plain Message-ID | — | 0.5 µs | one path |

(100 walks and 100,000 index lookups per figure; `fn-cei-build` of the
index: 0.01 s at N = 1,000 and 0.08 s at N = 10,000, paid once at open.) The
native BP receive path was not driven: the four-node mission lab is the only
native harness for it, and a 10,000-entry history there is not a lab this
lane could build inside its budget; the function-level rows are that path's
lookup, the one the dispatcher calls.

Logs (sha256): before-1000.log b3ca6c44…, after-1000.log b4b3aeb1…,
before-10000.log bcfeafac…, after-10000.log a655b10a…, summary.log
5336a310…; copies in planning/evidence/signed-history-index-2026-09-26/.

## Not done, and why

- **The loaded greeting (PKT-190)**: not started; the budget went to the
  index's certification and the matched native rows. PKT-330 (1).
- **Flat signed POST**: the replay is gone; a linear term that decodes
  nothing remains (above). PKT-330 (2) names each walk; the prepare's
  `(len records)` is hot-path-scans' byte-count seam.
- **An owner-level theorem for the index premise**: `fn-bpaj-store-indexedp`
  is established at every open and kept by the named Store transitions; the
  ones that keep it by construction have no named theorem, and no theorem
  states it of the host's live owner at every dispatch. PKT-330 (3).
- **The reconfigured owner**: the identity prepare's premise is the article
  prepare's; whether `fn-own-relation` holds of a live owner after a
  reconfiguration that drops a group is open for both (the corrupted-state
  witness shows exactly that state). PKT-330 (4).
- No deployment; the live node was not touched.

## Continuation (lane signed-history-index-2, 2026-09-26)

Brief: `build/coordinator/queue/done/w3-signed-history-index-2.txt`, on the
coordinator's statement item 11 (f370581b): the result is not merged while
PRF-132's keystones and the BP fast/checked equalities carry the index
premise as an assumption. Mandate §6: make the relation true at the actual
open and preserve it across every admitted transition that can reach the
call. Base: this branch at 4284073a, dev f370581b merged (268a807e).

### The relation, named once

`fn-ceis-indexedp` (books/consumer-event-index-store-invariants.lisp): the
Store's derived event index is `fn-cei-build` of its committed history, in
every phase. It replaces `fn-bpaj-store-indexedp` (retired: one name).
`fn-ceis-relatedp`, the earlier relation, is its crash-tolerant weakening
(vacuous while `:replaying` or `:fault`): `fn-ceis-indexedp-implies-related`,
`fn-ceis-related-live-phase-is-indexed`. The consumer poll's premise
(`fn-col-poll-agrees-under-maintained-store-relations`) is the weakening in
a live phase, so the same carried relation serves it.

### Established (host lines)

| entry | theorem |
| --- | --- |
| host/owner-host.lisp `fn-owner-recover-extended` (all three open paths: `fn-owner-recover`, `fn-owner-recover-from-checkpoint`, `fn-owner-recover-from-store-open`) installs `fn-ock-recover-extended` of the extended checkpoint = `fn-osi-open` | `fn-osi-open-installs-indexed-store`, **no hypothesis** (a refused open is `:fault`, whose empty Store is indexed: `fn-osi-refused-open-is-indexed`) |
| the Store open underneath, host/store-node-host.lisp (comment at :235: `fn-cpo-open-observed`, full replay `fn-cpr-replay`) | `fn-osi-cpo-open-observed-is-indexed` (the opened Store carries `fn-cei-build` of the history it read) |
| host/checkpoint-host.lisp :277 `fn-sn-open-observed` (and the model restart `fn-own-reopen`) | `fn-osi-sn-open-observed-is-indexed`, `fn-osi-own-reopen-is-indexed` |
| `fn-sn-initial` | `fn-ceis-initial-indexed` |

The BP service does not open the Store separately: host/native/bp-service.lisp
`fnn-bps-open` (:1076) opens the FNRJ journal and the BP node state; the
Store the dispatcher reads is the owner's (`fnn-bpapp-bind-owner-store` ->
host/bp-native-app-host.lisp `fn-owner-app-bind-receipt-store`, which binds
`(fn-own-store (fn-ocfg-owner oc))` of the installed owner before every
`fn-bprj-request-action`).

### Preserved

Store level (books/consumer-event-index-store-invariants.lisp):
`fn-ceis-io-preserves-indexed` (the record-directory append, the one
transition that grows the history, extends the index by `fn-cei-put` of the
appended event; every other io keeps both), `fn-ceis-prepare-article-`,
`-identity-`, `-retention-`, `-consumer-`, `-topic-preserves-indexed`,
`fn-ceis-finish-preserves-indexed`, `fn-ceis-recover-preserves-indexed`.
books/owner-store-indexed.lisp adds the transitions the record said kept it
"by construction" with no theorem: `fn-osi-refuse-reservation-keeps-indexed`,
`fn-osi-known-abort-keeps-indexed`, `fn-osi-ccar-prepare-identity-keeps-indexed`
(the carried identity prepare), `fn-osi-spc-prepare-keeps-indexed` (the
carried article prepare), `fn-osi-cpo-configure-durable-keeps-indexed` (the
configuration publication's Store; `fn-sn-with-configuration` inside it),
and `fn-osi-snrt-step-keeps-indexed` over the whole Store event family.
`fn-sn-set-keyring` and `fn-sn-sweep-staging` are not reachable at the
owner's Store (the sweep runs on the operator's standalone Store,
host/store-node-host.lisp :1099).

Owner level: `fn-osi-own-step-keeps-indexed`, `fn-osi-ocfg-step-keeps-indexed`
and one lemma per owner the host installs outside `fn-ocfg-step`.
`fn-osi-host-step` names every install in host/owner-host.lisp
(`fn-owner-install-ocfg` / `fn-owner-replace-core`, 21 sites) with the ACL2
function installed: `fn-ocfg-step` (fn-owner-step and its callers),
`fn-rcon-ocfg-io` (fn-owner-io), `fn-pcar-sbud-prepare` (fn-owner-prepare,
-prepare-buffer), `fn-ccar-ocfg-prepare-identity`, `fn-ccar-ocfg-complete`
(fn-owner-finish), `fn-ccar-own-finish` (fn-owner-finish-submission),
`fn-ocl-publish` (fn-owner-reconfigure-complete), `fn-own-configure`
(posting), `fn-osb-install` (profile), `fn-own-with-feeds` (feed port),
`fn-own-transit-outcome`, `fn-acar-own-outcome`, `fn-ocfg-open-peer`,
`fn-ocfg-read-step`, `fn-ocfg-open`, `fn-exp-open` (exposure open),
`fn-scar-ocfg-read-tls-prefix` (fn-owner-chunk), `fn-ocfg-fault`,
`fn-ocfg-observe`. **KEYSTONES**: `fn-osi-host-step-keeps-indexed`,
`fn-osi-host-run-keeps-indexed`, and `fn-osi-live-owner-store-is-indexed`,
no hypothesis: the Store of every owner the host reaches from its open by
those transitions (`fn-osi-live-store`) is indexed. This closes PKT-330 (3).

The one Store event that breaks the relation is the kernel's
`(:store (:crash ...))`: the crash image carries the empty index while its
history is kept. The host never issues it (a crash is process death; the
process's next owner is the open above), so `fn-osi-host-own-eventp`
excludes it from the `fn-ocfg-step` arm; the crash-tolerant
`fn-ceis-relatedp` holds across it and recovery rebuilds the index
(witnessed). No transition was found that fails to keep the index; no
defect needed a code change.

### PRF-132 restated, premise discharged

`fn-bpaj-dispatch-never-resubmits-a-stored-article` and
`fn-bpaj-dispatch-binds-the-stores-own-record` now live in
books/owner-store-indexed.lisp and are stated over
`(fn-osi-live-store configs prefix suffix frontier max-conns evs)` with
their pre-PRF-144 hypotheses only (record in the Store's article records,
`fn-record-p`, the Message-ID agreement; the `:bind` answer). Conclusions
unchanged. The store-level versions are the refinement lemmas
`fn-bpaj-dispatch-never-resubmits-under-index` and
`fn-bpaj-dispatch-binds-the-stores-own-record-under-index`
(books/bp-signed-binding.lisp), with `fn-bpaj-indexed-records-are-the-walk`
under them. The fast/checked equalities over the live Store:
`fn-osi-live-store-record-accepted-fast-is-checked`,
`fn-osi-live-record-lookup-fast-is-checked`,
`fn-osi-live-transit-record-lookup-fast-is-checked`,
`fn-osi-live-dispatch-fast-is-checked` (hypothesis `fn-sn-statep` of the
Store, as before PRF-144, carried by `fn-ocl-relation`). Assurance chain:
`fnn-bpapp-accept-locked` -> `fn-bprj-request-action` ->
`fn-bpaj-dispatch-fast` over the bound owner Store -> refinement
`fn-bpaj-indexed-records-are-the-walk` -> maintained relation
`fn-ceis-indexedp` (established at `fn-owner-recover-extended`, preserved by
`fn-osi-host-step`) -> PRF-132's keystones -> the mission's signed binding.

### Teeth (tests/acl2/owner-store-indexed-tests.lisp)

- Reachable positive witness at open: `fn-osi-open` over the signed history
  (a hybrid enrolment, then the kind-4 composite) under the default
  configuration record: not `:fault`, `fn-ocl-relation`, full and
  checkpoint paths equal, the Store indexed, the index answers the
  composite's record; after the five recovery barriers (host `:io` events)
  the live Store is `:ready`, both keystones' antecedents and conclusions
  hold (the dispatcher binds the composite's record, named event = the
  composite), and fast = checked.
- Transition sequence through the host's own functions: the owner opened
  over the enrolment alone, then barriers, reservation, the carried
  identity prepare of the composite, record-file/link/directory and the
  completion: indexed before and after, the index after is `fn-cei-build`
  of the extended history, the dispatcher submitted before and binds after.
  Crash (labelled: excluded from the host family): the crashed Store is not
  indexed, is `fn-ceis-relatedp`, and recovery re-indexes it.
- Hypothesis removal over live Stores: the enrolment-only live Store
  (record absent: submits); another Message-ID over the signed live Store
  (submits); the `:bind` antecedent (conclusion fails before the commit).
  `fn-record-p` has no live counter-witness (an open admits only Store
  events); its constructed must-fail stays on the refinement lemma; the
  hypothesis is kept, no weakened theorem proved (PKT-330 (5)).
- CORRUPTED (labelled), tests/acl2/bp-signed-binding-tests.lisp 2b: the
  committed Store with the index it carried before its commit fails
  `fn-ceis-indexedp` and the dispatcher submits a stored signed article.

### PKT-330 (4), answered (labelled counterexample, and a packet)

A group removal keeps `fn-own-relation`'s Store conjunct: `fn-ocl-publish`
installs `fn-cpo-configure-durable` of the Store
(`fn-ocl-complete-success-install-exact-store`), and removing `fn.letters`
from the live signed Store keeps the allocation domain (retired names stay),
so `fn-snt-relation` still holds (witness). But `fn-own-relation` does not
hold of every live owner: the owner the host's open installs over a history
whose configuration later reduced the capacity below an accepted undertaking
(config-observed-tests' image) satisfies `fn-ocl-relation` and
`fn-ceis-indexedp` and fails `fn-snt-relation`, hence `fn-own-relation`
(witness, labelled COUNTEREXAMPLE, reachable at the open). So the article
and identity prepare keystones stated under `fn-own-relation`
(`fn-opc-prepare-equals-owner-event-under-relation`,
`fn-ccar-ocfg-prepare-identity-is-ocfg-step-under-relation`) do not cover
that live owner; the index relation of this continuation does.

Packet (PKT-330 (4)). Trace: open over events (undertake 10, release) with
configs (default, set-capacity 1 at txid 7): `fn-ocl-relation` T,
`fn-own-relation` NIL. Constraint: the served path must not replay.
Default: restate both prepare keystones under `fn-ocl-relation`, against a
configured specification prepare whose replay is `fn-cst-replay-node`
(the configured replay `fn-cst-relation` already carries). Rejected
alternative: require every reconfiguration to keep the store-only replay
(forbids a valid capacity reduction below history, which the configured open accepts
(`fn-cst-open-success-has-historical-relation`); the configuration model deliberately keeps historical acceptance).
Affected: books/owner-prepare-correspondence.lisp,
books/owner-commit-carried.lisp, PRF-144 part 2 and the article prepare's
keystone. What continues without it: the host's behaviour (the carried
prepare stages; the store-only specification would refuse on such an owner)
and every index theorem here.
