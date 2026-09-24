# What landed, what remains on branches, and the next cycle

> Archived on 2026-09-24, superseded by [now.md](../now.md) and the [wind-down handoff](../handoff-2026-09-24-winddown.md).

Snapshot: `e657b1cf`, 2026-09-24. The retrospective is factual; the cycle
below is a recommendation for discussion. It changes no requirement, release
gate, authority policy or deployment. The live hbox node remains `da5fd8cb`.

Follow-up: the user selected worktree cleanup, finite packet integration and
bounded Luna trials. [Current work](../now.md) and the
[integration record](../evidence/cleanup-integration-2026-09-24.md) supersede the
queued/branch dispositions below; 101 trees have been archived and removed,
and ADVANCE, OVER and allocator/index foundation packets are now on `dev`.

The review covers the last **300 first-parent landings**, from `f1fdaf8d`
(exclusive) to `e657b1cf`, including 393 commits through merged ancestry.
That is roughly seven hours of September 23 development. A landing may be a
proof repair, native test, evidence record or checkpoint, not a new feature.
Inventory used `git rev-list`, `show`, `diff`, and source comparisons.

## What changed in that span

At the starting point, acceptance stamps were being integrated, the consumer
API was a design, and BP's native received-bundle journal and Store handoff
were being assembled. The live service already existed. The later changes
made much more of the core callable from native paths and exercised those
paths across restart; they also exposed concrete composition defects.

| Area | Landed change and strongest evidence | Remaining boundary |
| --- | --- | --- |
| News and authorship | Acceptance-stamp NEWNEWS and old-checkpoint migration; native exact-source hybrid render/verify, recorded verdict exposure and signed peering/restart; historical reader pins and Message-ID/group indexes. | The current combined image still needs its release qualification. Indexed OVER and the stronger ADVANCE relation await integration. Cryptographic primitives remain trusted. |
| Native owner and peering | TLS/authentication, isolated hbox–persvati exchange, INN exchange, live configuration, and repaired new-group POST and bound-request refusal handling. | These are named image/scenario results, not every matrix row or a new live deployment. Feed completion must be observed in the sender's durable state, not inferred from recipient arrival. |
| Durable consumers | ACL2 cursor scope, durable consumer events/replay, same-UID local controls, exact stored-event poll and advancing ACK. Image `1d26e01f` passes signed poll, repeat without ACK, killed ACK reply/reopen and no repeated acknowledged article. | The implemented profile is one group under a fixed owner/query/view. Poll currently traverses the earlier event prefix. Mini's actual durable transaction-to-ACK join and general multi-group/remote interface remain open. |
| Preservation | Selected pack/reclaim and fenced cold clone preserve the exercised consumer position and historical authorship. A new clone incarnation refuses old cursors; bounded paths and uncertain fence cleanup have explicit outcomes. | This does not establish general compaction/reclamation crash correspondence, all active-reader closure conditions, or physical power-loss durability. |
| BP/DTN | Native TCPCL/contact work, received-bundle FNBS persistence, observed-channel admission, application-to-Store handoff, durable return receipt jobs, replay, and additional fragment/expiry/deletion-report source. | The last qualified BP image covers the earlier whole-bundle profile. New native fragments still encounter a refusal before durable custody; admission plus expiry-safe reassembly is active branch work. New report/transit composition needs a source-matched native campaign. |
| Agent/OS integration | Mini independently verifies exact fn source and its own origin/grant, retains inbox/operation/reply/conflict evidence in signed transactions, and reopens exact replies. fn exports an ACL2-decoded poll projection. | Exported files alone do not prove Store admission. Final Mini v3 observed-poll → transaction → ACK must run as one causal path. Mini replay latency is still a practical limitation. |
| Topics and humans | Bounded signed topic metadata, exact authored-field binding and maximum-profile native inspection; a loopback NNTP web reader/composer with distinct posting outcomes. | Durable topic admission is on branches. Inspection does not install policy or confer Mini authority. The Python web client is separate from the native server and has no durable drafts or verified-author display. |

Useful evidence entry points:

- [Native poll, reader and clone](../evidence/native-poll-reader-clone-1d26-2026-09-23.md)
  and [bound-callback refusal](../evidence/native-owner-bound-1d26e01f-2026-09-23.md).
- [INN and selected peering](../evidence/nntp-peering-bc9be7ec-2026-09-23.md),
  [earlier BP admission](../evidence/native-bp-admission-c1bb-2026-09-23.md),
  and [topic/BP image](../evidence/native-topic-handoff-86323c89-2026-09-23.md).
- [Mini portable inbox/reply and measured replay cost](../evidence/dregg-e1-portable-inbox-p1.md),
  [consumer contract](../../specs/consumer-progress.md), and
  [human client](../../docs/human-web-client.md).

## What the assurance work bought

The useful advance is increasingly proving the functions the native host
actually calls and deriving their premises from maintained state. Examples
include historical reader state through configured-owner reads, exact carrier
and source bindings, strict consumer replay, and typed article frame/name
arguments along the served publication path.

For storage, K1/K2 connect a related modeled crash image to scan/kernel
admissibility; K5 bounds the old durable prefix and possible new record;
K6/K8 connect exact typed record bytes to issued links and directory fences.
The strongest landed K0 article result reaches the actual P-RECORD pair-10
cut from related reserved/staged input. **General establishment and
preservation of that byte/kernel relation across the complete host program,
all supported events and outcomes remains open.** Physical I/O assumptions
and platform qualification remain separate. The conditional results matter;
they must not be described as an unconditional crash-safety proof.

Native tests found real defects: an output filename entering a poll request,
a live-created group visible to readers but rejected by POST, a request left
busy after a known refusal, and a parsed/raw BP endpoint mismatch. The later
fragment investigation found that a promising reassembly component was not
yet reachable from native reception. Those findings explain why source,
component proof and image evidence must stay distinct.

Proof cost was also repaired repeatedly without weakening statements. After
the first BP union failed, current source `e657b1cf` passed the combined
incremental run: **14.452 seconds of certification, 575 compatible cached
books and ten newly certified books, four jobs**. This is a warm-cache
composition result, not a fresh-proof timing or native BP qualification.
See the [original manifest](../evidence/manifests/certify-20260924T001919Z-568673.json)
and [recovery record](../evidence/bp-repaired-e657-2026-09-24.md).

## The actual branch backlog

There are more than one hundred worktrees, mostly accumulated lane history.
Neither a non-ancestor branch nor `git cherry`'s `+` means its behavior is
missing: many patches were adapted when integrated. No worktree was removed
during this review. These are the consequential packets, not an exhaustive
list of branch names.

| Packet / worktree under `build/lanes/` | What remains to land or finish |
| --- | --- |
| `live-advance-union`, `b8a1a02b` | Final five commits beginning `5931450d`: an explicit ADVANCE outcome and preservation of historical reader/configuration pins, including refusal. Scoped ACL2 evidence exists; integrate with current owner and exercise the combined image. Earlier LISTGROUP changes on this branch are already adapted into dev. |
| `t17-over-range`, `9aa16a4f` | `421e588a` and `9aa16a4f`: use maintained group buckets and Message-ID trie for pinned OVER/XOVER, with correspondence and premise-removal tests. Scoped evidence exists; native concurrency/restart driver is prepared but unrun. |
| `byte-store-k568`, `fbfb5d5d` | Frontier file/rename/directory-fence proof sequence beginning `c807c546`, continuing through `fbfb5d5d`. Earlier article K0 work is already integrated. This advances the allocator program, not general K0 closure. |
| `topic-store-join`, `14ed645c` plus working changes | Durable topic slot12, configuration-preserving updater, actual owner proposal/control publication and native test. Parts are certified; the composed owner/recovery and native path remain unfinished. |
| `consumer-index-topic`, `18e9c602` plus working changes | Derived event index in slot13 and bounded indexed poll window. Component correspondence passes; whole Store-transition preservation and the actual owner caller are still being assembled. Coordinate the shared updater with topic work. |
| `bp-union-proof`, `b5c81e99` plus working changes | Reachable pre-fix fragment refusal witness, carrier admission separation, and expiry-safe fragment family/replay work. The actual native path must be enabled and tested together with durable expiry observations. |
| Mini `fn-evidence`, `d90b18ab` | Final v3 exact observed-poll/control binding and ACK gate. Needs the final live causal experiment and reply publication. This is outside the fn repository; do not merge or push Mini main. |
| Mini `fn-e2-materialized-cache`, `056846ce` | Exact prepared-write sharing and Lean equality of the complete intent fields, through `edc0effa`/`056846ce`. Reconcile with the final v3 branch and measure on the same fixture; a proved representation improvement is not yet a measured E2 speedup. |

The two Mini branches share their earlier E1 chain through `c832220a` and
diverge at the last integration/performance changes. The fn topic/index
branches also share substantial ancestry; integrate their coherent combined
state shape rather than cherry-picking a last WIP commit in isolation.

Several apparent leftovers are already accounted for: `f3428a7d` is integrated
as `eba44cb4`; the relevant books at `8c24fe82` and `fe230298` are byte-identical
to current dev. Consumer byte-reopen work is integrated at `7726bb20` and
`2669760e`; Mini projection/bounds work at `bac492e8` and `9e06a377`.
Generated ledger-only dirt in old stamp worktrees is distinct from the active
BP/topic/index source changes. Cleanup needs an explicit disposition for each
remaining tree; this review does not infer that everything else is disposable.

## Recommended next cycle

Keep the selected v0 and ambitious v1 direction. Change the planning unit to
complete observable exchanges and the invariants those exchanges need. The
September 22 trajectory retains its release properties and stable step IDs;
its old schedule and descriptions of then-missing code are historical.

**First recover and integrate what is already close.** Save active WIP, then
land the ADVANCE, OVER and qualified allocator proof packets as coherent
changes. Reconcile topic/index state layout directly between contributors.
Build one source-qualified image per useful convergence batch, shared by the
native campaigns. The existing successful ordinary run is not repeated just
to obtain another green label.

**Outcome A: a sleeping agent completes a recoverable conversation.** Use
the real fn poll → exact-source verification → Mini inbox/operation/reply
transaction → fn ACK → durable reply outbox → native reply post. Exercise
crashes before and after the consumer transaction, lost ACK, uncertain reply
post, repeat and changed-source conflict. Then carry that conversation between
separate stores/admins under the selected trusted-peer profile. Preserve the
separate meanings of Store acceptance, application result, processing ACK
and retention release. The event index and Mini representation optimization
advance alongside this experiment; a correctness witness need not wait for
all performance work, but the measured usable workflow must include it.

**Outcome B: a real interrupted BP exchange completes.** Join native fragment
admission, durable custody, restart, expiry-safe reassembly, Store dispatch,
return receipt and narrowly authorized release. Also test deletion/status
report recovery and a second interrupted contact. Inspect exact retained
bytes and unchanged unrelated obligations. Ordinary whole-bundle exchange
remains useful while fragmentation is repaired. Native fragment acceptance
and its expiry rule must land together.

**Carry four supporting tracks concurrently.**

1. K0: derive the byte/kernel relation across the host-called publication
   programs and their supported failure/recovery outcomes. A two-article
   served trace with interrupted publication is a useful witness of the
   general theorem, not a substitute for it. Keep the physical cut/model
   mapping and actual byte-image differential beside this proof work.
2. Topics: finish durable local anchor/install/report admission under the
   bounded experimental controller/roster profile. Exercise native reopen,
   authorization, budgets, missing parents and conflicting evidence. Keep
   application execution authority in Mini; broader governance remains a
   separately proposed extension.
3. Served efficiency/preservation: finish index correspondence at the actual
   poll/reader callers, then measure workload scaling and selected-pack/reopen
   behavior. Do not disguise whole-history work as a bounded page operation.
4. Product qualification: one combined native image, the remaining applicable
   v0 matrix rows, real NNTP peers, interrupted contacts, migration and
   resource refusal on isolated hbox/persvati stores. Improve the human and
   operator view of provenance/outcomes using existing ACL2 decisions; keep
   speculative interfaces from becoming dependencies of the two exchanges.

An initial ten-Sol arrangement can pair Mini integration with Mini cost work,
BP semantics with BP native tests, storage induction with physical cut
testing, topic admission with consumer/index integration, and combined-image
qualification with human/operator usability. These are cooperating outcomes,
not exclusive file assignments. Root does convergence and targeted
architectural review. Agents can move between pairs when another interface
or test becomes the useful next task.

Use fresh bounded briefs for new outcomes, preserve compact checkpoint
handoffs, and retire idle agents instead of continuing large contexts for
status polling. Keep proof/build capacity separately bounded. Submit a shared
run once, record its handle, and use the wait for other substantive work.
Batch routine ledger/status updates with coherent landings while preserving
original failed evidence. Consolidate current status rather than adding
another contradictory 'current' paragraph each time.

## What to discuss together

My recommendation is to make the recoverable agent conversation and the
interrupted BP exchange the next two demonstrations, while the supporting
tracks keep advancing. This raises the practical bar without inventing a new
release definition. LTP, richer governance, private-group cryptography and
public web service remain separately staged work; none is needed to complete
these two demonstrations.

The useful preference question is which demonstration should get the first
available integration capacity. My default is Mini's local transaction/ACK
join first, because both sides already have native evidence, with BP repair
and qualification running in parallel. That priority is a recommendation,
not a change to DTN's v0 requirement.
