# A signed article binds once, under the receiving Store's verdict (lane mission-signed-2, 2026-09-26)

Brief: `build/coordinator/queue/w2-mission-signed-2.txt` (continuation of
mission-signed; mandate §9, §5.7; D23, D25). Ids: PRF-132, PKT-291; SCN-066
and SCN-074 move on evidence. Previous records:
[mission-signed](mission-signed-2026-09-26.md) (the two refusal layers,
PRF-128, PKT-247) and [mission-four-node](mission-four-node-2026-09-25.md)
(the mission, its assurance chain, PRF-120). Branch `lane/mission-signed-2`
from dev 43fad7ab. Nothing here is deployed: every run is loopback in
`/tank/fn/scratch/mission-signed-2/` on an image built from this lane's
commit.

## The second refusal cause, traced (task 1)

The native entry is `fnn-bpapp-accept-locked` (host/native/bp-app.lisp): a
bounded loop that asks `fnn-bpapp-action` (ACL2 `fn-bprj-request-action`,
host/bp-receipt-journal-host.lisp, which is `fn-bpaj-dispatch-fast` over the
owner's bound Store) for the next step: `:persist-intent`, `:submit`, `:bind`,
`:prepare-receipt`. After `:submit` the loop rebinds the Store and asks
again. For a signed article, the owner's transit submission commits a
kind-4 acceptance composite (`fn-stxa-p`: the article record plus the
receiving Store's kind-2 verdict, built by `fn-hsig-authorized-article-event`
from the receiving node's enrolled snapshot and its own observations). The
dispatcher's lookup (`fn-bpaj-transit-record-lookup-fast` via
`fn-bpaj-record-for-msgid`) read only `fn-record-p` events, so over the
committed Store it answered `(:absent)`, the dispatcher answered `(:submit)`
a second time, and the owner's transfer decision refused that submission as
`(:have :history)`: `BP node delivery refused result=refused reason=history`
(image f1734955, `mission-signed/mission-f1734955/signed/b-serve-1.log`
lines 24-31: `BP accepted xfer=0`, then the carried source line, then the
refusal). The reading is reproduced in ACL2 by the labelled mutation witness
in tests/acl2/bp-signed-binding-tests.lisp: over a Store that committed a
signed composite, the pre-fix plain-record search finds nothing and the
dispatcher over the enrolled Store answers `(:submit)`.

Not confirmed on a rebuilt dev image before the change: the dev-head tree
(43fad7ab, `/tank/fn/gates/mission-signed-2-img-43fad7ab`) failed its
artifact acquisition (`no complete current artifact set passed an ACL2
load`, rejected=0; a later check found a complete composed set, so the
failure was transient) and was not rebuilt; the lane's image run below is the
after-image of the same path, f1734955 the before.

## What a node can now do

1. **A hybrid-signed report crosses the four-node mission and is accepted.**
   B's receiver binds the article record of the kind-4 composite its Store
   committed and answers `request-accepted`; it never submits the article a
   second time (PRF-132). A's signed carrier crosses X (fragmented,
   reassembled, SIGKILLed and restarted), dtn7 r1 and r2 and Y; B's copy
   verifies; B's receipt crosses its own outage and releases A's pin before
   B's consumer wakes; B's signed reply comes back the same way and A's
   receipt releases B's pin. All seven steps, image aa0f6c16.
2. **The verdict the delivery is bound to is the receiving Store's.** The
   request carries no verdict; what binds is the Store's own composite, whose
   kind-2 verdict it built from its enrolled keys and its own observations.
3. **The receiver's grounding covers signed articles.** Every receiver
   invariant (backed contexts, the evolving-Store relation, receipt
   grounding, node-committedness when idle) now reads a history's article
   records, a composite's included.

## PRF-132, books/bp-signed-binding.lisp

Subject: `fn-bpaj-dispatch-fast` (books/bp-native-app-fast.lisp). Host
lines: host/bp-receipt-journal-host.lisp `fn-bprj-request-action` calls it,
for host/native/bp-app.lisp `fnn-bpapp-action` in `fnn-bpapp-accept-locked`;
host/bp-native-app-host.lisp `fn-owner-app-plan-install` and
`fn-owner-app-record` call its lookup `fn-bpaj-transit-record-lookup-fast`.

| keystone | statement |
| --- | --- |
| `fn-bpaj-dispatch-never-resubmits-a-stored-article` | RECORD a member of the Store's article records (`fn-bpr-article-records (fn-sf-records (fn-sn-files store))`), `fn-record-p RECORD`, and RECORD's Message-ID the one the dispatcher reads (`fn-bpaj-dispatch-msgid`: the relaying agent's check for a transit intent, the injecting agent's for a direct one) ⇒ the dispatcher's answer is not `(:submit)` |
| `fn-bpaj-dispatch-binds-the-stores-own-record` | answer `(:bind RECORD)` ⇒ RECORD is an article record with the dispatcher's Message-ID, `fn-bpaj-store-record-accepted-fast` holds of it, and the event `fn-bpaj-article-event` finds is a member of the Store's history whose article record is RECORD; if that event is a signed composite, `fn-stxa-bindsp` holds of it (its kind-2 verdict is bound to RECORD's Message-ID, transaction, generation, profile and keyring generation) |

"Submitted exactly once": before the commit the dispatcher answers
`(:submit)` (the existing `:absent` branch); after it, never
(`...-never-resubmits-...`). A repeated delivery of the same signed request
is the D25 duplicate: status `:committed` answers the stored receipt; a new
request carrying the same article plans `:have` (`:duplicate`) and binds the
same record. "The verdict is the receiving node's own": the request carries
no verdict; what the delivery is bound to is the Store's composite, whose
verdict the Store built (hybrid-store's `fn-hsig-authorized-article-event`;
PRF-026 for the verdict a kind-4 completion records). Cited, not restated:
PRF-128 (the channel is admitted first), PRF-127 (relaying keeps the authored
source), PRF-117 (the D23 source decision).

Teeth (tests/acl2/bp-signed-binding-tests.lisp): the Store is built by its own
transitions (`fn-sn-prepare-identity`, the io words, `fn-sn-finish`): a
hybrid enrollment, then the signed composite of the mission's transit shape
(an injected article, stored as the relaying node's Path projection).
Reachable positive witness: over the enrolled Store the dispatcher answers
`(:submit)`, over the committed Store `(:bind RECORD)`; both keystones'
antecedents and conclusions asserted literally; the named event is the
composite itself and its verdict is `:verified` for `<a1@example.invalid>`;
the host's transit context for the bound record replays and the dispatcher
moves to `(:prepare-receipt)`. Hypothesis removal (never-resubmits): without
the Store holding the record (the enrolled Store) it submits; without
`fn-record-p` (a constructed, unreachable Store whose history holds a
non-record carrying the Message-ID; labelled) it submits; without the
Message-ID agreement (a second signed request over the committed Store) it
submits. Hypothesis removal (binds-own-record): without a `:bind` answer the
conclusion fails. Labelled mutation witness: the pre-PRF-132 plain-record
search finds nothing over the signed Store, the new one finds RECORD.

Assurance chain: native entry `fnn-bpapp-accept-locked` → `fnn-bpapp-action`
→ `fn-bprj-request-action` → `fn-bpaj-dispatch-fast` (executed subject;
the BP books are not guard-verified, as before) → keystones above → the
receiver relation (`fn-bprv-relationalp` / `fn-bprv-evolving-invariantp`,
established by replay at open, preserved by every receiver transition) now
grounds contexts in the same article records → observed: B answers
`request-accepted` for the signed report (native runs).

## The receiver invariants carried

`fn-bpr-article-records` (books/bp-receipt.lisp) maps each Store event to the
article record it commits: a plain record to itself, a composite to
`fn-replay-composite-record` (what replay installs), anything else to itself
(never `fn-record-p`). `fn-bpr-store-record-acceptedp` and
`fn-bpaj-store-record-accepted-fast` test membership there; the history stays
the Store's event list. Carried:

- bp-receiver-store-invariants: `fn-bprv-context-backedp` and its theorems
  over the article records (statements of `fn-bprv-acceptable-record-is-member`
  and `fn-bprv-backed-context-has-actual-ready-record` now say "member of the
  article records"); bp-receiver-retention-invariants
  `fn-bprv-replayed-receipt-is-grounded` likewise.
- bp-receiver-evolving-history-invariants: `fn-bprv-context-groundedp`
  searches the article records; new `fn-bprv-article-records-prefix`
  (a history prefix is an article-record prefix); L18
  `fn-bprv-evolving-output-is-history-grounded` over the article records.
- bp-receiver-evolving-node-invariants: new
  `fn-bprv-apply-composite-installs-record` (replay's article arm installs a
  composite's record and stays idle) and `fn-bprv-apply-event-installs-article`;
  `fn-bprv-replay-loop-installs-every-record`, L19
  `fn-bprv-history-record-is-node-committed-when-idle`,
  `fn-bprv-evolving-output-is-node-grounded-when-idle` and
  `fn-bprv-acceptable-at-ready-extension` over the article records.

specs/bp-evolving-store.md and specs/bp-node-machine.md §4.9.2 say so. Cost:
a lookup or acceptance check decodes each composite of the history once
(pessimistic: N events, C composites, each check C decodes of an article
record plus an N-long walk); a Message-ID index over events is owed
(PKT-291).

## Certification

hbox, ACL2 8.7 `w28/acl2-literal-4g`, 2 jobs, 300 s:
`run-20260926T024334Z-8257` (`--affected-by books/bp-receipt.lisp
--affected-by books/bp-signed-binding.lisp`: 124 roots, 142 books certified,
all passed; `manifests/certify-20260926T024359Z-186333.json`). This lane's
books: bp-receipt 2.1 s, bp-native-app 4.0 s, bp-native-app-fast 4.4 s,
bp-receiver-evolving-node-invariants 2.2 s, bp-receiver-evolving-store-invariants
4.8 s, bp-signed-binding 3.8 s, bp-signed-binding-tests 3.9 s,
bp-transit-join-tests 4.1 s. One book over 10 s, not this lane's:
books/byte-store-k0-staging 15.0 s (5.3 to 8.2 s in five earlier manifests,
unchanged here); see "Not done". Run two, `run-20260926T033200Z-9b20`, recertified that book alone
(7.4 s; `manifests/certify-20260926T033221Z-250495.json`). Two of three
runs used.

## Native runs (hbox, systemd-run MemoryMax=24G)

Image `aa0f6c16` (commit aa0f6c16, tree
`/tank/fn/gates/mission-signed-2-img-aa0f6c16`, built by
tools/runbooks/hbox-image-build.sh after run r1: acquisition composed,
validation OK). Core SHA-256: fn-host-dtn-developer.core 19a7c0d863ba5eea…,
fn-host-developer.core ee3d322eb5537be3…, fn-host-dtn.core a4e33ac5cb183100…,
fn-host.core c70ffaddbba249d2…. Runs in
`/tank/fn/scratch/mission-signed-2/native-aa0f6c16/`, each under
`systemd-run --user --scope -p MemoryMax=24G`.

- **First signed and unsigned runs (driver of 40f4098a's parent), both exit
  1, identically:** steps 0 to 3 and 5 hold, and for the signed report step
  3 is now `request-accepted` (layer 2 closed: `BP node source carried
  carrier=y-boundary author=a-author | BP application handoff durable | BP
  node delivery request-accepted`). Steps 4 and 6 fail (`no-receipt`,
  `no-verdict`). Cause, from the logs: with a listener per boundary
  (mission-signed), Y facing fn-b listens on r2's boundary, so B's receipt
  offer toward Y's b-boundary port fails connection-locally (`BP node receipt
  transfer failed peer=dtn://fn-a/ (connection-local; the job stays owed…)`)
  and is offered again only when B restarts in step 6; A's receipt in step 6
  the same toward X. Classification: harness (the driver's turn of the relay
  listeners; the unsigned control fails the same way, and it was never run
  past step 3 on the per-boundary driver before). Fixed in the driver
  (40f4098a): step 4 restarts B after Y turns toward fn-a, step 6 restarts A
  after X turns toward fn-b, so each offers its owed receipt on the new
  contact. No expectation changed.
- **Signed mission (`signed-r2`), exit 0, all seven steps, 153.9 s:**
  report.json 55580c3b36fb66dd…, signed-r2.out ff9cf70ceed04981…,
  b-serve-1.log 252ecd79484887f9…, a-serve-3.log 8329f53d1ad74e9b…; driver
  sha in driver-r2.sha256 (5d8c27a2…). Identities: authored source of the
  report f7fe359e… (= B's `hybrid-verify-source` export), A's stored report
  d6e45d60…, B's delivered copy 3e2f965c… (B's Path prepended); reply source
  96ff22ff…; A's obligation `receipted pinned=no` before B's consumer polls,
  B's `work-b-reply` `receipted pinned=no`. No finding.
- **Unsigned mission (`unsigned-r2`), exit 0, all seven steps, 134.2 s:**
  report.json 25bcafe453675d7e…, unsigned-r2.out 120e6948930e3397….
- **ambiguous-peer (`ambiguous`), exit 0, both steps:** X logs `BP channel
  admission refused reason=ambiguous-peer` and `BP refused xfer=0
  reason=ambiguous-peer`, no `BP accepted`; A's obligation stays pinned.
  report.json 0f6009a5e86838cf….
- **Request labs, 4/4 exit 0 with the gate's outcomes:** control, one and two
  dtn7 relays `request-accepted`, `receipt-accepted`, `pinned=no` (outs
  f9c5b617…, b045c061…, 6c9bc1fc…); unauthorized `request-refused`,
  `pinned=yes` (d5af09c4…).
- **test_bp_node_native filtered** (`-k receipt -k request -k
  uncertain_transfer -k kind_eight -k unrouted -k removed_route -k
  absent_bp_trust -k admitted_channel`): 13/13 OK, 58.2 s (bp-node.log
  5116caa856bc491b…).

## Not done, and why

- **Task 3, `bp-node serve` on several ports, not done (PKT-291).** The
  signed and unsigned runs pass only with the per-neighbour-listener
  workaround and the driver's restarts of the node whose receipt is owed.
  The design owed: ACL2 answers the listener set from the live
  configuration's transport-bp boundary rows (the channel table; the
  admission already names the neighbour by listener port,
  `fn-bpaj-session-principal`), the host binds each and accepts from any,
  with a theorem that each bound listener's sessions are admitted under
  exactly its row. Not started: the proof and native budget went to the
  binding and the regression gate.
- **A Message-ID index over Store events (PKT-291).** Each receiver lookup
  and acceptance check decodes every composite of the history once.
- **books/byte-store-k0-staging** measured 15.0 s at 2 jobs in r1 (hbox,
  concurrent with this lane's dev-image acquisition and other load), 7.4 s
  recertified alone at 2 jobs (`run-20260926T033200Z-9b20`,
  `manifests/certify-20260926T033221Z-250495.json`). Unchanged by this lane;
  recorded in PKT-291 as a measurement to watch, not adjudicated as noise.
- The dev-head confirmation image was not built (see the trace section).
- The BP books are still not guard-verified (as before this lane).
- `make check` is green in the worktree with planning/ledger.*,
  planning/current.md regenerated locally and not committed (the deputy's).
