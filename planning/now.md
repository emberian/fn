# Current work: executable components and integration

The [decision workbook](decisions.md) is a backlog, not a questionnaire that must
be completed before coding. The user authorized broad Terra implementation waves
with Luna/Sol/Astra work and convergence in batches. Routine reversible choices
are owned by the implementation team; public byte formats, cryptographic suites,
and deployment remain explicitly separate decisions.

## Completed integrated checkpoints

- Acceptance has certified initial-state, transition-preservation, immutable
  binding, and local-number uniqueness results. The theorem hypotheses retain
  the abstract durable-completion/recovery boundary.
- Wire framing, CBOR primitives, retention accounting, journal crash experiments,
  disconnected fact exchange, and an experimental NNTP reader have executable
  books and assertion tests. Their full subsystem contracts are still open.
- The acceptance simulator executes the actual definitions in ACL2.
- The node now connects retention and acceptance in one transaction, with
  general transition preservation and article-to-pin binding proofs.
- The reader runs over a real loopback socket via a persistent ACL2 process;
  independent `nntplib` client traffic and the socket regression suite passed.
- Review repairs strengthened wire-state bounds, distinguished journal sequence
  from transaction identity, and hardened NNTP numeric/projection handling.

The first [checkpoint](../tests/evidence/2026-09-18-integrated.md) covered 19
certified roots and nine Python tests. The later
[storage batch](../tests/evidence/2026-09-18-storage.md) passed `make test` with
25 roots, the simulator, and 26 Python tests. It adds complete primitive and
record round trips, typed replay proofs, a real immutable-file store with durable
allocation, and a reader over recovered state. Independent NNTP client traffic
and maximum-profile 128-article replay also passed. The third
[article batch](../tests/evidence/2026-09-18-articles.md) passed with 29 roots,
the simulator, and 27 Python tests. It adds exact successful-parse input
preservation, general retention-release invariants, and LISTGROUP ranges/cursors;
independent client traffic also passed. Each record retains exact source hashes,
outcomes, proof scope, and remaining limitations.

The fourth [reader/storage batch](../tests/evidence/2026-09-18-wildmat-storage.md)
passed with 33 roots, the simulator, and 31 Python tests plus the independent
client. It adds UTF-8 wildmat/filtering, explicit command bounds, two real recovery
hardening fixes, and an executable file-publication kernel with initial fence/gate
proofs and crash traces. It does not close full adapter refinement.

See [implementation status](../docs/implementation.md), the
[proof registry](proofs.json), and [milestones](milestones.md) for scope. A
certified component does not close a complete milestone or prove the host/disk.

## Working rhythm

One writer owns each area. Agents certify their own roots while independent
areas advance. Root integrates a frozen batch, runs the combined suite, records
evidence, and updates the registries. Review each coherent batch once; repair
correctness findings, track remaining proof scope, then advance.

The user requested frequent local checkpoint commits on 2026-09-18. Commits are
for synchronization and may include unfinished work; a commit is not evidence
of passing tests. Keep generated logs/certificates under ignored build paths,
and retain concise evidence summaries and exact source hashes in the repository.

## Current engineering choices

- ACL2 8.7 on SBCL 2.6.8 for the development model, with Python tooling.
- Interpreted ACL2 bridge for the first host experiment; raw Common Lisp calls
  to unguarded logical functions are not the integration argument.
- One owner and one shared-state transaction pending at a time.
- Exact octet payloads and exact Message-ID strings; no native signing preimage.
- Local cross-post names must all be configured; failure is atomic.
- No automatic expiry or history pruning. Resource charges include retained
  history, and inadequate capacity rejects new obligations.
- Experimental CBOR uint32/byte-string primitives; no persistent/native schema
  frozen by their existence.

## Active assurance-closure wave

On 2026-09-18 the user explicitly prioritized burning down the remaining hard
assurance work rather than continuing to widen prototype surface area. The fifth
[fields/transfer/storage batch](../tests/evidence/2026-09-18-fields-transfer.md)
has passed with 38 certified roots, the actual-core simulator and 32 Python tests.
Source hashes were unchanged. Semantic fields, bounded transfer staging,
file-kernel step/crash preservation and the real recovery-read fence are integrated.

The sixth [assurance checkpoint](../tests/evidence/2026-09-18-assurance.md)
now records 54 certified roots, the simulator, 45 passing Python tests and 38
independent CBOR cases. It retains the initial stale test expectations and their
corrected recheck. General finite file traces, article recognizer/bounds,
UTF-8/parser/DP correspondence, transfer state/assembly/hot-path work, record
canonicality and all CBOR/record guards are integrated. Fault coverage includes
47 injected rows, six process-death cuts and 211-state/9,038-edge exploration.

The seventh [composed-store checkpoint](../tests/evidence/2026-09-18-composed-store.md)
passed 75 roots, the simulator and 67 Python tests at `80afcbe`, with unchanged
inputs. Independent client traffic over reopened state also passed. These results
are separate from the earlier 54-root record.

| Owner | Current closure target and state |
| --- | --- |
| Astra | Mixed live file/node and refusal/abort trace relation certified; observed-image exact replay and five-barrier recovery gate certified |
| Root | 75-root/67-test integration passed; 533 guarded functions across 15 base books |
| Terra | Composed store/reader adapter merged; one-use completion gate fixes passed targeted regressions, combined run passed |
| Luna | Arbitrary finite actual node traces preserve state and prior article/archive bindings; successful publication assertions passed |
| Sol + Astra | Full implemented NNTP command/step effect typing and arbitrary finite session/cursor preservation certified |
| Terra | Exchange ingest and policy-changing traces preserve state/conflicting facts; all 40 guards certified and integrated |
| Sol + Terra | Full public missing-range value correspondence and hypothesis-free polynomial work bound certified, including structural equality |
| Terra | Wildmat matcher whole-operation work bound and all 54 guards certified |
| Sol + Astra | All 115 NNTP guards integrated, with 17 socket/partition tests and independent client passing |
| Terra | All 30 article-field guards integrated; exact legacy BP article ingress model certified |

The 75-root checkpoint runtime graphs cover acceptance (63), wire (38), wildmat (54), article (45),
retention (35), node (30), replay (13), CBOR (21), records (45), file kernel (47),
store wrappers/resolution/observed opening (40), transfer (62), and exchange (40): 533 guard-verified functions.
The subsequent [reader/checkpoint/index batch](../tests/evidence/2026-09-18-reader-checkpoint-index.md)
adds NNTP115 and semantic fields30, making 678 functions in those 17 base graphs;
the derived index separately guards 20 functions. Logical checkpoint equivalence
and derived index correctness are integrated, while physical checkpoint/index
adoption remains open.

All 452 pre-existing logical function bodies in the newly integrated graphs
are unchanged; 15 proved executable/domain helpers were added. The 75-root frozen combined run passed; the follow-on record describes the later changed roots and reader tests.

The [closure inventory](assurance-closure.md) retains the finite exit criteria.
No completed helper is being used to close a wider unfinished row. Work proceeds
through complete proof/integration tasks, with harder proof composition assigned
to Sol/Astra and independent Terra/Luna work continuing.

The [local persistence experiment](../specs/store-experiment.md) is integrated:
bounded transaction bytes, replay, allocation across aborted process lifetimes,
fault tests, and a read-only NNTP view. The [walkthrough](../docs/local-experiment.md)
makes this checkpoint executable without treating it as the final news service.

The user has promoted BPv7 to the active architectural path. Coordinated
lanes now implement an existing BPA integration (Terra), durable outbox/attempt/
receipt semantics and trace proofs (Sol), and the actual workflow journal/ACL2
bridge with crash tests (Sol), and actual legacy-article ingress (Terra). The [BP path](../specs/bp-path.md) requires a real
interrupted two-node exchange; these lanes do not wait for indexes, compaction
or a complete NNTP profile.

The frozen composed-adapter/guard batch passed; record and integrate subsequent bounded artifacts while those lanes progress.
Checkpoint-plus-suffix equivalence, corrected index completeness, article work
and remaining runtime guards continue independently. Integrate article injection/provenance and
complete the selected reader profile. The isolated-slot journal is not the real
adapter model; store-files/store-node are the selected refinement path.
The next user-facing design discussion has
[concrete native-versus-legacy byte examples](../docs/article-byte-examples.md)
for D01, followed by principal/key custody (D09). These proposals do not silently
select a signing grammar or cryptographic suite.

Private-group cryptography remains a separate requirements/research track.
Shared community groups come first; MLS is a candidate, not a commitment.

Actual [BP-to-fn receiver ingress](../tests/evidence/2026-09-18-bp-ingress.md)
now passes with real loopback BPAs, restart, durable article acceptance and
new-BID duplicate recognition. The shared receiver uses the real parser and
composed Store. Inbox-only mode explicitly refuses a nonempty workflow history.
Sender workflow integration is closing permanent transaction-pair reservation
and durable prepare/outcome replay; the portable experimental ADU codec carries
request/receipt context without changing article bytes. These are active tasks,
not completed retention-handoff or authentication claims.


The [article work batch](../tests/evidence/2026-09-18-article-work.md) passed all
seven new roots. Complete public parser value correspondence and structural-work
bounds now include malformed inputs and repeated prefix copies. Original parser
sources are unchanged; physical allocation/runtime costs remain separate.

The [bounded BPA receive boundary](../tests/evidence/2026-09-18-bpa-boundary.md)
is integrated: capped HTTP inventory/raw download, pinned upstream payload
extractor, eight mock cases and the repeated real acceptance/duplicate lab pass.
Sender workflow preflight and restart fencing fixes are being integrated next.

The [sender workflow/ADU batch](../tests/evidence/2026-09-18-bp-workflow.md)
is integrated with five scoped certified roots and 33 host checks. Live ACL2
preflight precedes publication, recovered intents require explicit recovery,
and submit permission is consumed once. Receiver request/decision persistence
and the actual BP return receipt are the next complete integration exit.
