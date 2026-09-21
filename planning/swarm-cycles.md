# Active development cycles — 2026-09-21

Root has taken over development at `8b474e2`. The feed and transit candidates
have both landed; their merged certification record is
[the owner batch manifest](evidence/manifests/certify-20260921T051833Z-3941584.json).
That is book evidence, not a measurement of the merged running service. The
older C1–C3 plan below remains design history; its opening implementation
inventory is not current.

The user reaffirmed wide implementation waves, selective certification and
coherent batch convergence. v0 means every selected feature usable between two
peered fn nodes; v1 reaches M6 and beyond. A local pilot does not replace v0.
Native signatures, exact authored bytes with separate projections, retention
until authorized release, and NNTP/CLI before web remain the selected directions.
Private group cryptography remains deferred, with privacy boundaries preserved.

## Current staffing and integration checkpoint

D07 selects a Python-free production runtime. The integrated native storage
adapter now consumes ACL2 metadata, frontier, filename and provenance definitions.
The bounded native configuration profile is integrated through `c322da5`, with
its default-path repair; its operator/owner consumer still needs integration.
The packaged operator service remains Python-based development infrastructure.
No component test closes the full native service or v0 contract.

| Active lane / worker | Next complete result |
| --- | --- |
| `owner-convergence` / Sol | Native multiplexed owner, control, live configuration and physical feed replay/append; shared submission preserves feed intent and uncertain persistence fences the service. Unify configured article bounds and measure the frozen service. |
| `submission-path` / Sol | Carrier repair landed; preserve distinct core faults, stop mutation after journal uncertainty, and prevent cross-session evidence overwrite through durable ACL2-owned identity. |
| `bp-fidelity-convergence` / Sol | BP sequence recovery/reservation on observed files, with returned-allocation non-reuse across admissible physical crash traces. |
| `artifact-set` / Sol | Native workflow/receipt journals over the same store state, with a shared ACL2-owned persistence operation and raw I/O interpreter. |
| `native-storage-codec` / Sol | Native checkpoint capture, selection and recovery adoption; coordinate the shared persistence operation and retain explicit checkpoint/corruption authority. Codec adoption and artifact handoff are landed. |
| `native-config-impl` / Terra | ACL2-owned safe FNFD peer filenames and explicit legacy handling, adopted by both native and development callers. Config parsing/default normalization is landed. |
| `storage-codecs` / Terra | I/O outcome and nonblocking progress packets landed; now measure actual saved-image store costs and identify growing-history walks without disabling invariant obligations. |
| `storage-initializer` / Terra | Actual native initialization failure/death/restart tests and cut fidelity; propagate enumeration errors and investigate staging recovery differences. |
| `feed-correspondence-terra` / Terra | Adopt the certified total feed output boundary in the actual owner, preserving durable intent when encoding is refused. |
| `wire-composition-sol` / Sol | Finish actual wire-driver composition from the certified reconstruction and rendered-bound helper packet. |
| `recover-user-direction` / Sol | Native freshness-anchor wire parsing/acquisition over ACL2-owned subjects and isolated cryptographic primitives; preserve D22's unsupported-tree outcome. |
| `integrated-runtime` / Terra | Native operator grammar/status/recover component landed; install the common entry, standalone help and shared owner callbacks with one result contract. |

Terra and Luna handle bounded implementation/mechanical work; Sol handles
substantial implementation, proof debugging and integration. Root Astra reviews
coherent batches, resolves difficult composition questions, updates registries
and keeps independent work moving. These are assignments, not assurance levels.
Use both farms with owned closures; integrated certification follows a frozen
batch rather than each intermediate commit.

The [consolidation audit](duplication-audit-2026-09-21.md) tracks concrete
competing decisions and their repairs. A separately proved logical model and
concrete representation remain intentional; a second host implementation of
identity, durability or policy does not. New native paths inherit the existing
assurance obligations instead of starting a less constrained Lisp implementation.

Earlier integration evidence remains source-specific. The W12 Python service
matrix at `cdbd6b2` recorded authentication-gate and BP-crash disagreements; its
probe ordering repair did not turn that original run into a pass. PRF-044 covers
the named conditional storage results and fresh initializer image, with actual
host/cut correspondence and general recovery still open. The earlier W12 plan
below is retained as historical task scope, not current staffing.

## W12: repair complete operational paths

Each lane owns implementation, its executable contract, meaningful proof/tests,
and a handoff of remaining obligations. These packets are active work, not
completion claims. All start from `8b474e2` in isolated `build/lanes/w12-*`
worktrees. Root owns integration, registry identifiers and current status.

| Lane / worker | Delivered behavior and assurance obligation | Farm |
| --- | --- | --- |
| `auth-policy` / Terra | Reader login policy composes with configured transit authorization; capabilities describe reachable commands; live peer and ordinary-client cases exercise the actual dispatcher | persvati |
| `artifact-set` / Sol | Select a coherent certification artifact set for the actual source/toolchain; build and load it; isolate deployment directories and locks by source tree | hbox |
| `feed-durability` / Astra | ACL2 owns FNFD envelope/recovery decisions; distinguish torn suffix from corruption, synchronize directory publication, fence the owner after uncertain persistence, and test restart at the changed cuts | hbox |
| `storage-relation` / Astra | Establish concrete initialization correspondence and preservation under explicit host program inputs; expose false unrestricted K0 cases without assuming the desired conclusion | hbox |
| `storage-codecs` / Terra | Realize configuration/frontier/name representations in ACL2 and adopt them through storage I/O; prove codec facts needed by the physical relation | persvati |
| `bp-sequence` / Terra | Persist native BP creation-sequence reservations and recover them without reusing an uncertain allocation; caller-supplied uniqueness is no longer the implementation | persvati |
| `submission-path` / Sol | Route CLI/control and NNTP through the same acceptance decision; specify and close the article-commit/feed-intent crash gap using durable evidence | persvati |
| `wire-block` / Terra | ACL2 renders the outbound article block; preserve trailing content and dot transparency through the host-called function and wire tests | hbox |

Terra means `gpt-5.6-terra`, Sol means `gpt-5.6-sol`, and Astra means
`gpt-6-astra`. These names allocate work; they confer no assurance. Root also
recovered the user's earlier direction with `cv`; read-only orientation is
complete and does not count as implementation.

Interfaces shared by lanes are agreed directly with their owners. In particular,
feed recovery, posting completion and network output must share the same global
uncertainty fence. Rebuilding feed work from current peer configuration is not
assumed equivalent to preserving the targets promised at original acceptance.
Storage relation proofs consume the concrete codec contract; arbitrary program
bytes are not silently treated as host-generated next-frontier bytes.

## W13: compose the durable services

The `bp-lifecycle` Sol lane is active in `build/lanes/w13-bp-lifecycle`,
starting from `8b474e2` and consuming the `bp-sequence` interface directly.
It owns a new native queue/contact/restart machine and service entry, while
the sequence lane retains allocation/codec ownership. Its farm is persvati.

Start independent packets as W12 supplies their actual prerequisites; do not
wait for an unrelated whole-tree green gate.

- Carry native BP sequence persistence into the node lifecycle, durable queue,
  contact scheduling, reception and application receipts. Exercise an evolving
  receiver store through real outages. Transport ACK, remote archive acceptance
  and agent execution remain different events.
- Adopt the live owner configuration and checkpoint validators on running paths,
  with configuration generations and recovery evidence preserved. Connect the
  concrete storage relation to the host's operation/cut table.
- Complete statement admission policy, persisted verification context, membership
  epochs and reader provenance exposure. Extend the carried index explicitly;
  do not introduce a served whole-store recognizer.
- Expand fault injection over the composed acceptance/feed/BP/recovery boundaries,
  including ambiguous barriers, corrupt complete records and capacity exhaustion.
  Each process-death cut must name a model transition.

## W14: release completion and sustained operation

- Close the v0 feature matrix on the integrated source: two peered running nodes,
  selected reader and transit profiles, real BP/convergence-layer behavior,
  identity/authority, reconfiguration, storage and recovery. Use independent
  client/BPA implementations where their interoperability is claimed.
- Carry authorized release, compaction, repair, backup/restore, migration and
  capacity headroom through long-running and restarted workloads. Retained
  obligations survive transport expiry; no automatic article expiry is added.
- Extend M6 contact/clock/transport profiles, then additional human interfaces
  under D17. Agent coordination consumes durable articles and explicit receipts;
  delivery does not authorize execution or establish agent task completion.

These cycles organize the frontier; they do not defer an already implemented
critical recovery/composition defect into future feature work. Release status
comes from covered contracts and evidence, not a count of roots or tests.

## Execution and integration

Use both `hbox` (isolated state under `/tank/fn/lanes`) and `persvati`.
Each current lane may certify its owned closure with up to four jobs; root
coordinates aggregate load and the final frozen batch. Inspect actual process
RSS/anonymous memory on hbox rather than interpreting its large ARC as proof of
process exhaustion. Do not repeatedly certify unrelated roots or launch a broad
check merely because context compacted.

Commit named lane files frequently; intermediate commits may be incomplete.
Root reviews a coherent batch once, repairs concrete defects, integrates forward,
and keeps independent work moving. Record exact revision/content, tools,
invocations, results and limitations. Historical matrix runs remain immutable;
a current pointer advances only to an actual integrated measurement. Generate
registry events and ledgers through their tools. Remove clean lane worktrees
only after their work lands. No public deployment is authorized by this plan.

## Historical plan from 2026-09-18

# Three broad development cycles (historical)

Status: **planned**, based on source checkpoint `2c31913`, 2026-09-18.
The user requested substantial feature completion together with expanding
assurance. This is an executable work plan, not new implementation evidence or a
claim that the decisions below have been selected. Task IDs here identify work
packets; requirement, proof and scenario IDs retain their existing meanings.

The [current evidence](../tests/evidence/2026-09-18-bp-composition-assurance.md)
closes sender binding, fixed-Store receiver replay and five process-death cuts.
The next work should widen beyond BP proofs alone. NNTP is still read-only;
checkpoint/index and fragment assembly have logical foundations without their
full running paths; native identity/authority remains largely unimplemented.

## Outcomes and scope

| Cycle | What should be usable at its exit | Assurance delivered with it |
| --- | --- | --- |
| C1: writable local node and durable foundations | Initialize/recover one node, post through ordinary NNTP, read threads through the complete selected reader/overview profile, observe bounded capacity and recovery status | Actual owner/POST completion relation, changed command/session and codec proofs, existing BP guard/refinement closure, evolving-Store receiver relation, real rejection/crash/backpressure cases |
| C2: signed, disconnected community | Native signing and honest legacy provenance, restartable fragmented transfers, scheduled relays, carried-media import, real checkpoint recovery, local human/agent tools | Authority confinement, source/preimage and dependency validation, durable progress/accounting, relay undertaking composition, checkpoint selection/replay equivalence |
| C3: long-lived operation and release assessment | Authorized reclamation and physical compaction, explicit backup/restore/repair workflows, measured operating profile, extended transport experiments | Protected closure across crashes/readers, origin non-reuse, conditional scheduling progress, combined fault campaign and independently exercised release checklist |

These are outcomes, not an estimate of three short runs or a promise that every
research question will close. Each cycle contains several frozen integration
batches. Advance independent work as soon as its actual prerequisites exist;
do not make all of C2 wait for every C1 packet. Native signing remains required
for the first release (D02). C1 is a useful **local laboratory pilot**, not a
relaxed definition of that release. BP remains central throughout all cycles.

A release candidate still needs the selected D05/D18 scope and a documented
platform/authority profile. Mission qualification, public deployment and private
group encryption do not follow from completing this plan.

## Roles

Terra, Sol, Luna and Astra are the 2026-09-18 Codex worker roles: Terra is
`gpt-5.6-terra`, Sol is `gpt-5.6-sol`, Luna is `gpt-5.6-luna`, and Astra is the
Codex root. These names are staffing allocations for this plan, not correctness
claims — a role's output is evidence only when it carries its own
certification, tests and theorem statements, not because of which model
produced it.

## Parallel execution

Use up to **ten independent implementation/proof owners**, root integration,
one Sol convergence owner, and one spare slot for a difficult proof or fault
investigation. That fits thirteen total agents. More packets than slots are
intentional: fast lanes release capacity to their successors. Do not spawn a
worker until it has a concrete owned artifact and useful independent work.

Terra owns bounded implementation/host/harness packets; Sol owns composition,
refinement and difficult induction; Luna can own inventories, independent
vectors and narrow tooling. Root/Astra reviews coherent contracts and integrates
frozen batches. These are workload allocations, not claims that a model's code
is correct by reputation. Each owner supplies evidence for its own artifact.

At launch, pin a source revision and give each owner its packet below, exact
writable paths, dependencies, acceptance criteria and forbidden semantic shortcuts.
Use isolated checkouts/copies. One owner mutates each base file; other owners
export new books/modules or a patch against a frozen interface. In particular:

| Shared area | Integration rule |
| --- | --- |
| `books/nntp.lisp`, wire dispatcher, `tools/run_reader.py` | One service integrator adopts reader, POST and owner contributions. Command workers develop separate helper books and transcripts. |
| `tools/run_store.py`, `host/store-node-host.lisp`, store books | One storage integrator owns adoption. Quota, checkpoint, index and compaction lanes initially add separate modules and contracts. |
| BP base books and journals | Guard owner freezes semantics-preserving base edits; FNWF/FNRJ owners add separate proof/codec books and own their corresponding host journal only. Rebase once onto the frozen guard version. |
| Portable source/schema/authority | One profile owner supplies the common exact vectors and versioned interfaces before dependent signing, injection or batching changes. |
| Registries, milestones and evidence | Root updates them with the integrated result. Workers supply proposed scope deltas, not concurrent edits to these files. |

Before integration every handoff names hashes, actual changed behavior, theorem
hypotheses, commands/results, known defects and remaining gaps. Certify only owned
roots while lanes run. Root freezes a coherent dependency closure, certifies the
changed roots and dependents, runs its meaningful host/scenario tests, then
commits. Run a full all-roots/simulator/host batch at each cycle exit, with exact
input hashes, rather than presenting accumulated historical counts as one run.

Review a batch once. Repair concrete findings; keep unrelated lanes moving.
A proof-search stall gets a reduced counterexample/lemma task for the spare slot,
not another general review. A failed dependency blocks only its consumers.
No second runtime implementation of ACL2 decisions is an acceptable shortcut.

## Contract work at the start

These small interfaces allow the first workers to proceed in parallel. Their
owners finish exact examples and rejection cases early in C1, then freeze them.
They are local engineering contracts, not publication of a permanent ABI.

| Contract | Required content | Owner / consumers |
| --- | --- | --- |
| Owner events and effects | Connection/generation, submission identity, committed view version, one pending transaction, known refusal/durable/indeterminate completion, partial output and read pin lifetime | C1-05; POST, reader, UI and all admission paths |
| Source and provenance | Exact received/native source, separate injected/served representation, explicit principal/policy evidence, conflict identity, no authority from `From` | C1-11; C1-06, C2-01/02/03/05/11 |
| Physical image and history | Bounded frame decoding, sequence/frontier/config binding, one-use side-effect permissions, fence/recovery, exact live/replay relation | C1-02/03; C1-04, checkpoint, scheduler, fragments |
| Resource reservation | Article/object, journal/history, staging, evidence and resolution headroom; reader/transfer pins; reservation identity and durable release | C1-08; every producer and later compaction |
| Transfer and undertaking | Unverified candidate versus complete accepted object; archive receipt versus accepted forwarding terms; durable obligation before a receipt that attests it | C2-04/05/07; scheduler, BP, carried media |

## C1 packets

The launch order below adopts the independent review's re-sequencing
(`review-2026-09-18-independent.md` §8): substrate — identity, causality, the
crash model and named assumptions — before service, because C1-11, C2-06 and
C2-12 were previously deferred while gating everything built on top of them.
Six packets are new or reshaped (C1-00, C1-13 through C1-16, and reshapes of
C1-04/07/09/10/12); the rest keep their existing IDs and scope from the table
this replaces. Tier is a staffing allocation (see Roles above), not a
correctness claim.

| Order | Packet | Change | Tier |
| --- | --- | --- | --- |
| 0 | C1-00 repair (new) | D1, D2, D3, D10, D11, D12, D13, D14 and the small items from the review; registry hygiene from review §4 (cite keystones, retitle tautologies, retract "certified" where the theorem is on an uncalled API); stale evidence lines | Sonnet |
| 1 | C1-11 substrate (promoted, reshaped) | Adopt the block shape as the fn statement header; import CellId and capability-chain authority; hybrid signature profile; policy term plus evidence hash in every receipt and journal record (closes D9). Emits the profile and vectors from Lean; ACL2 consumes. Gates C1-06 and all of C2 | Fable design, Opus implementation |
| 2 | C1-13 bytes into ACL2 (new) | Frame codecs (FNST/FNWF/FNRJ/FNBI + trailer), content-identity derivation, Message-ID bound, charge policy, group table: one owner in ACL2; Python becomes a byte pump. Kills the §4 twins | Opus |
| 3 | C1-14 crash-model fidelity (new) | Add the two syscall-returned-unobserved crash points (D4); restate acknowledged-history retention over records or make `successes` survive `open-observed` (D5); prove `open-observed ⇒ fn-snt-relation` (D6); `F_FULLFSYNC` and staged init | Fable |
| 4 | C1-15 assumptions as encapsulates (new) | A-DURABILITY, A-HOST, A-CRYPTO, A-PEER, A-POLICY as constrained functions with local witnesses; functional instantiation is the platform-qualification hook | Opus |
| 5 | C1-16 teeth ledger (new) | For every keystone: a must-fail sibling per hypothesis, checked as `must-fail`; `proofs.json` `events` generated from the books, not hand-listed | Sonnet |
| 6 | C1-01 BP guards | Unchanged | Sonnet |
| 7 | C1-02 / C1-03 FNWF / FNRJ refinement | Add: lift sender theorems to `fn-bp-replay-journal` and `fn-bp-apply-journal-record` (D7); state "durable intent before submit" as a theorem (D8); fix status regression to `:intent` | Fable |
| 8 | C1-04 evolving Store | Reshape: the Store must be indexed by the relation, not positional; depends on C1-14 | Fable |
| 9 | C1-05 mutable owner | Add: reader version pin; clock observation type | Opus |
| 10 | C1-07 reader | Fix D3 first; real effect typing (status code, CRLF, dot-stuffing, 512-octet initial line) | Opus |
| 11 | C1-08 resource | Per-principal accounting; depends on C1-11 | Opus |
| 12 | C1-09 index / C1-10 checkpoint | Fix `X ⊆ X`; verify checkpoint guards; strengthen the equivalence to exhibit the frontier's rejecting role | Sonnet / Opus |
| 13 | C1-06 POST | After C1-11 and C1-13 | Opus |
| 14 | C1-12 LTP | Reshape: model the BP primary block first; LTP feasibility only against that | Opus |

Non-negotiable prompt content for every C1 lane, learned from the review: paste
real signatures and absolute paths; forbid `inv ⇒ inv` corollaries as
deliverables; require a must-fail witness per hypothesis; require that the
theorem subject be the function the host calls, named; build the whole tree
after any shared-struct edit; report the pessimistic number with its covered
scope in the same sentence.

The hygiene lane's 2026-09-18 pass already closed part of order 12: the index
`X ⊆ X` tautology is replaced with soundness/completeness against authoritative
memberships, and `books/checkpoint.lisp` is fully guard verified with a new
`fn-checkpoint-restore-rejects-frontier-reuse` theorem exhibiting the frontier's
rejecting role. See `planning/assurance-closure.md` and `HANDOFF.md` in that
lane's worktree for the exact theorem statements.

C1 acceptance demonstration: initialize and recover; two clients post/read a
cross-post; drop a success and retry; kill during publication; recover one
article with unchanged memberships/pin; refuse an unaffordable post; retain
responsiveness with a stalled client. Compare live service results with ACL2
traces. Reader capability advertisement grows only as the applicable audit closes.
The BP codec/refinement work closes its own named seams concurrently.

The byte/refinement tasks must address the actual immutable-file/Store adapter
as well as the newly modeled FNWF/FNRJ seams. Existing record canonicality and
observed-image proofs are reusable premises; `books/journal.lisp` is the old
isolated-slot experiment and is not a substitute. Hash/OS behavior stays an
explicit assumption, with host checks/tests at the boundary.

## C2 packets

| ID / owner | Concrete artifact and dependencies | Required exit and ledger |
| --- | --- | --- |
| C2-01 / Sol + codec owner | Selected native envelope, version/domain-separated identity and signature-preimage codec; C1-11 and D01/D08/D09 profile | Golden independent vectors, both round-trip directions/canonicality, bounded unknown-schema carriage without authority, exact source/projection preservation and migration compatibility. `PRF-003/005/016`, `SCN-012/013`. |
| C2-02 / Terra + Sol authority owner | Real signature provider and persisted principal/key/delegation/group-policy state from selected D09/D11; C2-01 contract | Maintained provider/version and independent verification vectors; positive/negative authorization; crash/reopen, rotation, delegation/recovery and offline revocation semantics. Signing keys stay outside generic immutable replication. Prove policy confinement conditional on verification facts, not cryptographic strength. `PRF-013/014`, `SCN-012/013`. |
| C2-03 / Terra + integration | Native signing/submission tool and authenticated receipt ingress through the same service owner; C1-05/06 and C2-01/02 | Signed native and gateway-attested legacy articles coexist honestly; unsigned/foreign/wrong-scope receipt cannot discharge work; persist verification context/evidence and decisions. Complete D02's running path. `PRF-003/012/013/015`, `SCN-008/012/014/015`. |
| C2-04 / Sol | Durable fragment reservation/chunk/progress journal around actual transfer definitions; C1 byte/resource patterns | Restart reproduces exact gaps, bytes and reservations; duplicate/overlap/reorder/corruption/refusal traces preserve accounting; complete assembly remains unverified until C2-05. No receipt for a candidate. `PRF-007/011/016`, `SCN-009/013/015`. |
| C2-05 / Terra + Sol | Portable object/dependency container and validation-to-acceptance composition; C2-01/04 and D08/D15 | Complete article plus dependency closure publishes atomically; unrelated articles in a batch can progress independently. Tampered/missing/cyclic/oversized dependencies cannot publish or create acceptance receipts. Exact-ID and conflict evidence survive. Experimental opaque-byte work can start before the public profile freezes. `PRF-001/005/011/016`, `SCN-009/012/013`. |
| C2-06 / Sol | Durable contact/retry scheduler and bounded work selection; C1-02/08 | Explicit contact/clock/expiry observations, stable generation, deterministic priority and starvation policy; expiry/contact loss preserve work/pins; every selected attempt uses durable permission. Safety traces now, conditional progress in C3-03. `PRF-001/012/018`, `SCN-010/015/017`. |
| C2-07 / Sol or Astra | Relay undertaking/receipt composition and terms continuity; C1-04, C2-03/06 and D12 | A receipt promising onward responsibility requires durable receiver content AND its onward obligation/work. Model partial cross-journal completion, uncertainty and recovery; never acknowledge the promise in an enqueue-later gap. Distinguish archival acceptance from forwarding undertaking and destination acceptance. Trusted-peer experiment can precede authenticated deployment; full claim needs concrete authority. `PRF-004/007/012/013`, `SCN-001/008/017`. |
| C2-08 / Terra | Carried-media importer/exporter and actual four-node non-overlapping BP/contact lab; C2-05/06/07 | Same bounded staging and acceptance path for network/media; media read-only, partial copy/reimport/quota/corruption safe. Restart relay, lose receipt, expire attempt, reorder/duplicate. Destination has one acceptance; local numbers stay local; every promised relay obligation is recoverable. `PRF-011/012/016`, `SCN-001/008/009/010/017`. |
| C2-09 / Sol + Terra adoption | Actual checkpoint generation publication/selection and recovery; C1-10 plus byte relation and quotas | Make complete new generation reachable/durable before authority selection; retain old authority until committed selection. Crash at each namespace/barrier cut yields a complete permitted generation. Detect corruption explicitly rather than silently rolling back. Prove actual selected-checkpoint/suffix equals full authoritative replay. `PRF-007/008/010`, `SCN-003/004/006`. |
| C2-10 / Sol | Protected-root/dependency closure, persistent authorized release/withdrawal and logical compaction state machine; C1-08, C2-02/03/09 | Roots include archive/forward obligations, evidence/policy, identity history, unresolved transactions, checkpoints and read/transfer tokens. Prove unrelated pins retained, reserve-copy-publish-reclaim safety and no-space refusal. Keep all duplicate history initially. Specify content/history separation before any body deletion; do not assume old inline-payload records already permit reclamation. `PRF-004/007/009/013`, `SCN-005/007/008/016`. |
| C2-11 / Terra | Native signing/posting and operator/agent CLI tools over the same owner API; ordinary NNTP clients first per D17; C1 service contract and C2 signing API | Bounded file/stdin submission with stable retry identity, signature/provenance inspection, explicit post/queued/received states, capacity/recovery status, and init/recover/backup workflows. CLI calls the actual owner decisions and never implies a human-read receipt. Exercise native tools and an independent NNTP reader against the same store. Web reader/composer is later M6 work. `HST-001/002`, `NNT-005/006`, `SCN-012/014/015`. |
| C2-12 / Sol | Origin/incarnation/sequence model and explicit writable restore/clone protocol; D10 and C1-11 authority interfaces | Fresh namespace or verified external monotone anchor before resumed issuance; old snapshot cannot reuse identity for a different event; preserve fork evidence. Test same-incarnation refusal, fresh-incarnation success and crashes around allocation. Read-only restore/validation can start earlier. `PRF-001/017`, `SCN-006/011`. |

C2 demonstration uses `home -> relay-a -> relay-b -> destination`, with at least
one carried-media hop, non-overlapping contacts, retained identities, lost
receipts, restart, fragment interruption and resource refusal. In a separate
client session, a human composes/reads the same signed or explicitly legacy
article. A manually reenqueued archival relay may be useful earlier, but does
not satisfy the accepted-forwarding-responsibility part of `SCN-001`.

LTP integration may begin here once C1-12 has an actual supported route. It need
not wait for compaction or UI. Keep the current working TCP lab as a separate
interoperability baseline rather than replacing it prematurely.

## C3 packets

These packets consume C2 artifacts as they become ready. Start C3-10
incrementally as new public entry points freeze; resource assurance must not
be postponed wholesale to the final release review.

| ID / owner | Concrete artifact and dependencies | Required exit and ledger |
| --- | --- | --- |
| C3-01 / Terra + Sol | Physical compaction/generation adoption from C2-09/10, including reader/transfer pin lifetimes and format migration | Copy exactly the protected closure, reserve scratch space, publish before retirement, defer unlink until pins drain. Enumerate every copy/publication/reclaim crash and ENOSPC cut; acknowledged content/obligations/history remain. Physical body reclamation additionally needs the selected retained-history behavior; representation compaction can proceed while all bodies stay pinned. `PRF-007/009/010`, `SCN-003/005/007/016`. |
| C3-02 / Terra | Operator status, scrubbing, consistent backup/export, restore and explicit fault/quarantine/salvage workflow; C2-09/12 | Ordinary recovery never treats salvage as success or truncates damaged committed history silently. Validate restore before write access, show missing/corrupt dependencies and retained promises. Exact replacement repair needs validated source identity and retained evidence. Whole-valid-store rollback detection requires a selected external anchor; otherwise report that limit. `STO-008`, `FLR-003`, `PRF-007/017`, `SCN-006/011`. |
| C3-03 / Sol or Astra | Conditional scheduler/handoff progress over actual C2 scheduler and validated transfer/relay transitions | State surviving-node, capacity, workload/admission, useful recurring contact/route, retry and fairness hypotheses precisely. Prove eventual selection/delivery only under them; include a starvation counterexample when they fail and safety under clock jumps/outages. A simulation is not the liveness theorem. `PRF-011/012/018`, `SCN-001/010/017`. |
| C3-04 / Terra | Actual BP-over-LTP profile and second adapter qualification where C1-12 established feasibility | Pinned existing implementation, interruption/restart/expiry/backpressure, exact application bytes and durable receipt return. Record which session/segment behavior is delegated and its limits. If an external dependency is unavailable, deliver the exact blocker and runnable remaining harness; do not label LTP complete. `REP-006`, `SCN-010/017`. |
| C3-05 / Terra + host owner | Reproducible local packaging, authentication/transport boundary and measured resource profile; D07/D14/D16 deployment choices | One documented init/run/recover/update path; secrets isolated; private community access policy; no public listener by default. Benchmark full replay/checkpoint, article/queue limits, work and actual memory with hostile inputs. A raw compiled Lisp path needs complete call-graph guards and correspondence; retaining the interpreted bridge is an explicit measured choice, not a second semantics implementation. `PRF-014/016`, `HST-001..004`, `SCN-013/015`. |
| C3-06 / independent fault owner | Combined deterministic and generated scenario campaign over the frozen integrated core/host | Systematically enumerate write/barrier/publication/deletion/effect cuts; combine restart, quota, corruption, duplicate, stale completion and client partition; preserve previously acknowledged content and independent pins. Track actual branch/transition coverage and minimal failure traces. Re-run independent NNTP, codec, crypto and BPA vectors. `SCN-001..017` with explicit partial cases; all implicated proof targets keep their own claims. |
| C3-07 / platform owner | Named OS/filesystem/device qualification and optional external freshness-anchor experiment; D14 and actual available environment | Record barrier/write-unit/cache/namespace/locking/error assumptions and real evidence. Linux VM/process kills can validate adapters but are not device power-cut tests. If hardware is unavailable, retain the unclosed physical qualification item rather than pausing all development or claiming it passed. `HST-003`, `FLR-001..003`, `SCN-003/006`. |
| C3-08 / research/profile owner | Private-profile threat/metadata and library evaluation packet, separate from shipped features | Exercise design cases for partitions, delayed epochs, device recovery, revocation, archive/key separation and equality leakage; assess current primary research and implementation evidence. No new ratchet, automatic MLS selection or private-group feature claim. This completes a reviewable design packet, not `SEC-004` integration. `SEC-001..004`, partial `SCN-018`. |
| C3-09 / root + convergence | Release assessment with actual users/clients and stable-profile audit; D05/D18 | Check every applicable clause and requirement against named evidence; map every remaining limitation to a precise experimental/deployment boundary. Native signatures and honest legacy provenance must be running. Require full frozen certification/simulator/host runs, reproducible commands and operator walkthrough. Report release blockers rather than resolving D18 by theorem counts. |
| C3-10 / Sol + narrow proof owners | Remaining whole-operation work and execution correspondence for the final public call graph; consume each feature's frozen codec/parser/dispatcher | Inventory every untrusted entry point and existing work-bound gap, including wildmat parsing and added BP/batch/NNTP paths. Prove stated total work/structural-allocation bounds with malformed inputs and value correspondence; distinguish them from measured host memory. Preserve guard evidence after feature edits. `PRF-006/014/016`, `SCN-013/014/015`. |

## Decisions and safe parallel work

Only explicit user choices enter the decision register as selected. These are
recommended engineering directions or bounded experiments until then. Do not
turn a missing answer into a project-wide approval gate.

| Decision | Concrete next artifact | What can proceed before selection |
| --- | --- | --- |
| D01 — selected | Sign exact authored source bytes; mutable Path/Xref and gateway injection records are separate projections | Source/provenance implementation proceeds against that fixed boundary; concrete envelope/preimage encoding and legacy conflict policy still need design |
| D05 | Clause checklist for complete READER + POST + OVER and configured unmoderated groups | Implement/audit that proposed superset; advertise only finished bundles |
| D06 | Journal authority, complete checkpoint and rebuildable memory index; physical generation machine | Index adoption and candidate checkpoint codec now; disk index remains measurement-driven |
| D07 | Measured host packaging and supported runtime comparison | Keep the current actual ACL2 bridge working; no rewrite prerequisite |
| D08 | One restricted canonical portable profile with vectors/unknown-schema policy | Explicitly experimental local codecs and opaque transport bytes; no accidental public ABI freeze |
| D09 / D11 | Key custody, principal/delegation/group authority, rotation/recovery/offline revocation, algorithm/longevity comparison with current sources | Executable policy model and negative vectors; concrete crypto remains a named dependency of signed deployment |
| D10 | Restore/clone trace with fresh issuance namespace or independently validated monotone anchor | Read-only backup/export/restore validation and the model with an explicit freshness premise |
| D12 | Typed archive/onward/destination receipts and exact successor terms; independent archive pins | Cooperative local lab policy and durable relay composition; no authenticated handoff claim |
| D13 | Ancient reimport after authorized body release; retained duplicate history and explicit resurrection behavior | Protect all history; compact representation without history pruning. Body deletion waits for its content/history contract, not a timestamp expiry shortcut. |
| D14 / D16 | Named platform and measured small-community/stress budgets | Local adapter/crash models, configured conservative bounds and experiments; no universal filesystem/device claim |
| D17 — selected | NNTP and command-line clients first; web later | C2-11 owns native signing/posting and operator CLI workflows; web remains later M6 work |
| D18 | Concrete release checklist with evidence and named residual trust assumptions | All scoped implementation/proof work; do not silently lower the first-release requirements |

D01/D17 are now selected: exact authored source bytes with separate projections,
and NNTP/command-line clients before web. D02/D03/D04 stay selected: native author
signatures plus legacy provenance;
keep until explicit authorized release with capacity refusal; shared groups first
with private cryptography deferred. None is weakened to make a cycle look done.

## Coverage and checks at cycle boundaries

| Existing obligation | Planned packets |
| --- | --- |
| `OBJ-001..005`, `ENC-001..004` | C1-06/11, C2-01/02/05, C3-06 |
| `OBJ-006`, origin/restore `PRF-017` | C2-12, C3-02/06 |
| `OBJ-007`, authority `PRF-013` | C1-11, C2-02/03/07/10, C3-09 |
| `STO-001..006`, `PRF-001..003/005/007/008/010/014` | C1-02..05/08..10, C2-09, C3-06 |
| `STO-007/008`, `RET-005/006`, `PRF-009` | C2-10, C3-01/02/06; history pruning remains a separate D13 choice |
| `RET-001..004`, `PRF-004/012` | C1-03/04/06/08, C2-03/07/10, C3-01/06 |
| `REP-001..006`, `PRF-011/016/018` | C1-12, C2-04..08/12, C3-03/04/06 |
| `NNT-001..006`, `PRF-006/015` | C1-05..07/09, C2-03/11, C3-06/09/10 |
| `HST-001..004`, `FLR-001..004` | C1-01..05/08, C2-06/09/12, C3-02..07/10 |
| `SEC-001..004` | Preserve boundaries in C1-11/C2-02/11; C3-08 research/design only; private implementation remains outside selected release scope |

`STO-008`, `FLR-003`, `HST-003` and the private-profile requirements do not all
need invented ACL2 proof IDs. Their registry verification types and scenario
records must track operational/design/qualification evidence directly. A named
external assumption is not discharged by adding another theorem.

For each integrated packet record: affected stable IDs, new reachable behavior,
new state/composition/durability/codec/resource/authority/transport obligations,
actual proof and test evidence, and the remaining environmental hypotheses.
Unproved claims stay open even when a neighboring feature works. Conversely,
new feature development does not wait for unrelated future qualification.

Success is completing these running paths and their specified assurance,
not maximizing worker count or producing another list of detached helper books.


## Planning validation

This plan was synthesized from the current architecture, decisions, requirements,
proofs, scenario catalog and subsystem specifications, with independent
storage, local-service, DTN and assurance audits against `2c31913`. It introduces
34 unique work packets. Explicit packet and ledger references were checked;
`make check` passed for 74 Markdown files, 49 requirements, 18 proof targets and
18 scenarios. These are planning/structural checks. No implementation tests,
ACL2 certifications, external cryptographic audit or new transport experiment
were run for this planning task.
