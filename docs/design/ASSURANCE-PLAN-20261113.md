# Assurance completion plan

Owner: integration. Commissioned by ember on 2026-11-13, following the
[adversarial audit](ASSURANCE-AUDIT-20261113.md). This is the execution plan;
`fn2-squares` remains the obligation store. Reports and public-claim coverage
must be derived from that store and the actual served call/attachment graph.

## Destination and proof structure

The destination remains a working persistent engine and its intended network
consumers with a connected assurance argument. Every public guarantee needs
an exact served subject, supported domain, admitted statement, applicable
representation/effect links, artifact identity, and explicit trust assumptions.
Do not count an unproved internal algorithm as an environmental assumption.

Keep four statements distinct: safety for every finite execution prefix;
equality/correctness of completed results; progress under explicit fairness and
I/O assumptions; resource bounds in a named cost model. Actual latency and
device qualification require additional evidence. A conditional ACK safety
theorem assuming recovery finishes is not a recovery termination theorem.

The public roots must cover durable acceptance and uncertainty, recovery,
authorization and identity, exact framing/parsing, ownership and reclamation,
supported-profile resource bounds, and progress. Review this catalogue against
the specifications; automation cannot infer specification completeness.

## Stage 0: falsify and establish the interfaces

Run small proof/evaluation spikes before distributing leaf proofs. Record a
full antecedent and observable counterexample; a failed proof search is not one.

| Spike | Owner | Required result before fan-out |
|---|---|---|
| Durability inductiveness | durability | Preserve the now-observed counterexample to the old turn invariant; formulate and initialize a full reachable invariant with commit-row/ghost-history coverage, J/J3/J5/F/X/Q and frontier relationships. Prove one real transition and its projection to the user guarantee. |
| Quantitative machine contract | composed-build | Exercise a real generated issue arm at budgets zero/one, exhausted credit, stopped/refusal states. Prove returned counts match actual effects and fit budget; reject an unchanged-core budget+1 attachment. |
| Formula-bound evidence | evidence + child compiler | Generate witnesses from the registered extraction equality; preserve the unconditional theorem. Detect the existing sibling-clobber mutant and unchanged refusal. Reject constant-T, false-antecedent, wrong-endpoint and stale-formula evidence. |
| Native execution prefix | native + durability | Execute Accept-prefix counterexample candidate; establish a useful prefix relation, completion condition and short-read effect witness. Model physical return separately from completion posting. |
| Canonical semantic bridge | Lean | Complete one fresh served function slice through live ACL2 export, canonical-body evaluation, representation/domain correspondence and DSL interpretation. Use CNS draining if its dependency closure is tractable; echo is a control, not a substitute for consequential coverage. |

Confirmed durability spike: in the qualified baseline world, an install-row
state is typed/WFP and satisfies every current turn-invariant clause with an
empty ghost history; one real turn changes installed frontier 0 to 1 and
falsifies the invariant. This refutes the arbitrary-state statement, not the
public ACK guarantee or durability of an initialized running node. Preserve
the executable witness and prove initialization excludes it through the new
invariant. Do not patch the theorem with a convenient unestablished premise.
Reproduction is lane commit `319620bed`, `tests/dur-turn-counterexample.lisp`;
qualified baseline REPL evidence is in
`forge:/build/lanes/stride-owed-integrated/build/proof-repl/stride-turn-inductive/log`.
The control is record-certified in `certify-20261114T001317Z-3423328`.

The native Accept-prefix equality counterexample is also record-certified
(`c18a79e64`, run `certify-20261114T002126Z-3432086`). A real zero-budget issue
was observed with a queued Close descriptor in the assurance-budget lane; its
fix and record gate remain in progress. The obsolete 4129 bound still needs an
executed witness; source inspection alone is not a counterexample.

## Shared foundations to freeze

### Quantitative callbacks and turns

For each actual run returning `(bytes steps descriptors runnable after)`, prove
natural counts, descriptors <= supplied budget, declared kind maximum including
stopped/refused outcomes, and correspondence of reported descriptors to issued
effects. Separately connect successful phase charges to phase bounds. Runtime
stopping after an overrun does not prove a bound. Budget admission must precede
effects or preserve an explicit resumable continuation; retry must not repeat
reservations/writes. Prove supported profiles can provide the required quantum.

Put these constraints in the shared generator and prove selected attachments
satisfy them. Then derive dispatch, service, harvest and loop accumulator bounds.
Replace the old 4129 claim only after a concrete refutation/statement audit,
with a documented registry-derived theorem, not a silent rebaseline.
Q1 entry/partition/step/exit proofs follow these transition contracts.
Primitive work/allocation semantics is a separate dependency of the actual
bounded-work claim; summing declarations alone is insufficient.

### Evidence and claim graph

Extend `fn2-squares`, reusing statement/formals/body identity, sides, contracts,
dependencies and origin metadata. A shared evidence form takes exact variable
bindings, a declared endpoint mutation or a canonical hypothesis clause.
The generator constructs H AND C for positives. Mutation evidence requires
original H/C and false mutated C; hypothesis removal requires the remaining
clauses, false removed clause, and false C. Check guards/ABI without adding
guard hypotheses to an existing unconditional equality theorem.

Initially support explicit equality and implication/conjunction shapes; refuse
unsupported forms. Opaque predicates require a checked decomposition. Keep old
teeth marked as not formula-bound until converted. Proof admission, witness
execution and certification remain distinct statuses. Declared dependency edges
are not automatically precise proof dependencies; export conservative trust
closure honestly. Pilot on child extraction before moving to durability.

### Native effects and trust boundary

Use one operation-incarnation schema for descriptor/take/ack, submission,
physical return, terminal posting, loan release and reclamation. Carry raw code,
count, errors, actual byte effects, capability generation and pending ownership.
Model crash points between physical return and posting, short/error results,
duplicate/stale/cancel behavior, and no reissue of completed physical work.

Prototype a small logical host-transition declaration with generated raw control
for one storage operation; compare against translation validation of the existing
dispatcher before selecting the general implementation. Keep OS/FFI leaves small
and explicit. Do not attempt arbitrary SBCL verification or declare the whole
host trusted to evade the problem. Prefix refinement preserves legal concurrent
linearization order; completed-run equality needs genuine drain/close conditions.

TLS extends the same schema with handshake phase, connection-owned staging,
pending ciphertext/plaintext observations, token, timer and saved op reference.
Copying all input into owned staging is not the same as OpenSSL consuming it.
Preserve every suffix and account for allocation through connection lifetime.

### Canonical body and domain bridge

Freeze shared `BodyCorrect`/representation/domain interfaces and fuel or recursive
composition lemmas before parallel certificate generation. A slice must identify
all called functions and attachment selections; unresolved callees stay explicit
obligations, not arbitrary dispatch assumptions hidden by a pilot verdict.
Prove primitive correspondence on reachable domains, then close recursive SCCs
and all served roots. Fix external import/cache provenance before reusing results.
Even all interpretation roots passing is not closure-wide semantic equivalence.
Use `Translation.evalExport` for the canonical interface, keeping its guarded
domain separate from existing unconditional interpretation contracts. Existing
`Countdown` adequacy/uniqueness results can support recursive families; fuel
exhaustion is not a successful evaluation. Selected attachments need checked
constraint satisfaction and exact selection identity, not mere substitution.

## Stage 1: swarm over independent obligations

Fan out after the relevant pilot's interface is stable, not after every pilot
finishes. One owner edits each shared generator/API. Leaf lanes implement/prove
instances against that interface; report missing general lemmas back to its owner.

| Work family | Can split by | Must consume / produce |
|---|---|---|
| Machine quantitative contracts | generated kind families | fixed callback API / actual attachment proofs, effect accounting and controls |
| Durability preservation | issue, harvest, install, fence, recovery transitions | one full invariant / preservation plus projection; separate progress rank |
| Q1 composition | entry, partition, transition cases, exit | quantitative contracts / actual turn refinement, no shared-handler semantic claim |
| Independent application semantics | authorization, transaction/upload, consumer/cursor, boot/commit | specification-rooted contracts / shared-handler mutations and observable guarantees |
| Canonical Lean closure | dependency SCCs and primitive-domain families | fixed representation/body interface / body and domain proofs, exact closure coverage |
| Native correspondence | storage, network, cancellation/ownership, TLS | shared host-effect schema / per-operation refinements and reachable cut witnesses |
| Operational cost | parser, buffer, hashing, storage traversal primitives | explicit cost semantics / bounds connected to actual implementation |

Qualification runs proceed alongside proofs: process-death tests, modeled
short/torn/error/fence outcomes, and deployment-specific storage qualification.
They complement rather than discharge universal correspondence claims.

## Stage 2: converge and make missing coverage fail

Integrate existing READY work first in reviewed batches; preserve its narrow
certification scope. Batch foundational invalidations, then freeze one coherent
served source/profile and qualify its exact closure. Regenerate OWED and canonical
exports from that world; run actual image/host/socket checks on matching artifacts.

A strict assurance gate is separate from regression mode. It must refuse omitted
served roots, stale bodies/attachments/toolchains, owed required dependencies,
unbound evidence, missing body/domain proofs, unaccounted raw substitutions, and
incomplete native cut relations. Mutation controls must demonstrate those failures.
Every remaining trusted edge is named in the resulting public claim, never hidden
behind a generic green status. Independent review traces a representative guarantee
from wire input through persistence and recovery to the wire response.

## Coordination

Keep existing native, TLS, compiler and timer work moving; do not discard useful
integration for a speculative rewrite. Current reservations and qualified cache
origins are exchanged directly between owners. Forge aggregate caps stay <=26 GiB;
typically only a few proof jobs run even when many agents analyze or edit.
No bb2 writes, no production/service changes, no cache deletion. Use bounded REPL
spikes, narrow record gates, then one batched convergence. A lane is READY with
named commits, exact proof/test scopes and any remaining red, not a narrative of
completion. The integrator alone changes shared dev.

## Whole-path completion targets — 2026-11-14

The destination remains the persistent NNTP/storage/consumer system, including its
network consumers. Increase the depth of each completion claim, not the count of
isolated certified fixtures. A helper package is an intermediate deliverable until
its actual served caller consumes the contract in a qualified composed world.

1. **Accepted data through recovery.** Durability and native owners connect actual
   initialization (including nonempty group/principal genesis), admission, collect,
   seal, persisted acceptance and reopen. Preserve the declared broad/crash-only
   fault distinction. The same preserved image must exhibit the specific broad
   uncertainty diagnosis and exact prior accepted article recovery under crash-only.
   This runtime control supplements the general ACK/recovery proof; SIGKILL does
   not discharge power-loss, persistence-fence or arbitrary-corruption assumptions.
2. **Independent CNS effects.** The Q1 semantics owner defines before/after effects
   without invoking production release/reclaim/timer handlers on the checking side.
   Exercise the actual draining run, with held lease, reusable/retired rows, a live
   sibling timer/range, and both early and late refusals. A late name-range refusal
   may follow successful workspace release; unchanged-core rollback is not its spec.
   Corrupting the sibling on both Q1 executions must be detected independently even
   if their shared-handler comparison agrees. Bridge ownership then connects the
   same served root to canonical evaluation, guards/domains and primitive contracts.
3. **Actual turn resource guarantees.** The scheduler owner connects a supported
   assembled profile through actual admission, dispatch and turn execution. Prove
   numeric and residual bounds even for stopped structural states. Keep net queue
   delta separate from issued-incarnation history; issue/ack/reuse must not erase
   the latter's accounting. Insufficient residual must preserve core and selection
   cursor, with a separate fresh-quantum retry witness. Scheduler fairness, available
   credits and actual instruction/allocation cost are separate obligations.
4. **Full-duplex TLS ownership and bytes.** The transport owner connects allocation,
   handshake, concurrent record operations, cancellation and exactly-once cleanup
   through the same capability ledger and logical per-operation state. A blocked
   receive must not prevent a send needed for progress. Retained seed, fragmented
   BIO input, short writes, stale returns and exhaustion must reach native controls.
   Logical handle/staging proofs do not establish OpenSSL behavior or byte effects.

The existing core emitter already aliases `CoreWorld.fns` to `LayerAWorld.fns`
and names actual served functions in dispatch equations. A suspected namespace
mismatch was withdrawn after tracing those definitions. Preserve that connection;
close remaining guard/domain and MBE logical/executable obligations explicitly.
The MEMBER-EQ-EXEC pilot alone is not a proof of every MEMBER-EQUAL logical path.

External review is advisory. Three bounded, tool-disabled `claude-kimi` reviews
were requested over secret-scanned packets: system ambition, bridge/evidence,
and runtime/durability/TLS. Large packets timed out without responses. A smaller
system-status review returned and recommended one matrix from top claim through
live obligation, served entrypoint, frozen artifact, fault model and independent
scenario. Adopt that as the completion measure; counts remain build progress only.
That status-only review blurred prover-job memory exhaustion with runtime node
resource behavior. Reject that inference: the observed 2 GiB OOM was certification,
not node execution. The targeted evidence-code review returned no new defect in
the live-statement witness/recheck machinery and rejected the obsolete raw-formula
attack; source locators and controls were independently checked. This is only the
evidence slice, not the larger Lean bridge or universal/runtime correctness. The
final small TLS handoff review also returned no supported defect: identity,
lifecycle, copied-seed and output-consumption checks match the caller, and the
unfed seed suffix is deliberately retained for later records. Physical copy,
record migration and socket behavior are outside that result. Larger runtime and
bridge reviews timed out and received no clearance. An absent response is not a
clean review, and no finding is attributed to Kimi without an actual response.
Validate alleged defects against source before assigning fixes, retain rejected
suspicions, and distinguish known unfinished work from newly discovered defects.

## Additional independent assurance lanes — 2026-11-14

These lanes expand beyond the existing durability, extraction, TLS, scheduler
resource and ACL2–Lean work. Each starts from semantic freeze `6e07e62f3` with
planning commit `06b1785df`; newer lane results require explicit integration.
Source investigation and bounded local controls do not allocate remote build slots.

| Owner / lane | Actual assurance subject | Required useful result |
|---|---|---|
| authorization_assurance / assurance-authorization | Served principal, authority and incarnation binding | Connected stale-principal/grant refusal contract; actual admitted-row witness and meaningful removal/mutation control. First trace targets CNS→control generation binding and propagation into transaction authority. |
| parser_assurance / assurance-parser-boundaries | Receive-to-command framing and consumption | Actual split/coalesced/EOF/limit boundary behavior checked against an independent expectation, with a shared fix or a proved boundary contract. |
| storage_fault_assurance / assurance-storage-faults | Short/torn/error/fence and ambiguous persistence effects | One faithful deterministic fault control or normalization repair beyond SIGKILL, preserving accepted/refused/uncertain distinctions and explicit device assumptions. |
| sol_artifact_assurance / assurance-artifact-binding | Certified source through loaded image and qualification receipt | Fail-closed binding plus stale/replaced/omitted artifact controls; no change to certification eligibility or historical identity. |
| sol_assumption_assurance / assurance-assumption-boundaries | Reachable assumptions, attachments, raw substitutions and guard boundaries | A concrete escape from existing inventories/gates repaired with a reachable-edge mutation, or a precise audited coverage result. Inventory alone is not a semantic proof. |
| progress_assurance / assurance-progress | Actual selection, runnable/wait/timer transitions and fairness | Conditional progress tied to the served scheduler, with explicit environment/quantum assumptions and an adversarial schedule or missing-assumption control. |

Existing owners retain shared generators, quantitative run interfaces, TLS state,
canonical bridge APIs and certification infrastructure. New lanes initially own
separate contracts/fixtures or narrowly coordinated tooling changes. A suspected
leaf defect must be checked through its actual callers: for example, a principal
check preceding an admin check on the same unchanged core can rule out an apparent
local bypass. Reports distinguish confirmed defects, coverage gaps and withdrawn
suspicions. Remote proof work still requires named capacity within the 26 GiB cap.

## Distributed, temporal and completion coverage — 2026-11-14

A further six independent lanes start source-first from the same semantic B base.
They add no remote compute reservations; current jobs and capacity remain under
convergence coordination.

| Owner / lane | Assurance subject | Required useful result |
|---|---|---|
| peer_assurance / assurance-peer-contracts | Inbound transfer decisions, replay/identity, catch-up and custody coverage | A connected inbound contract/control, plus honest separation of actual served behavior from outbound/catch-up models and interim commands. |
| revocation_assurance / assurance-revocation | Authority changes during selection, page assembly and handoff | An independent two-head schedule and stated authorization linearization contract; no silent retroactive-rescission requirement. Coordinate, but do not duplicate, membership and permission decisions. |
| reclamation_assurance / assurance-reclamation | Persistent extent/article lifetime versus readers, pins and checkpoints | A connected lifetime invariant or exact served-entry coverage refusal; allocator model proofs alone cannot establish a served collector. |
| sol_crash_cut_assurance / assurance-crash-cut-map | Physical effect/return cuts before modeled completion | One source-connected cut-family mapping witness and omitted/misattributed-cut controls; preserve the incomplete global mapping verdict. |
| identity_codec_assurance / assurance-identity-codecs | Actual wire, stored and retrieved article identity representations | A served correspondence with independent octet expectations and meaningful normalization/identity mutation; cryptographic collision resistance stays an explicit assumption. |
| sol_claim_completion / assurance-claim-completion | Required product claims through their live proof dependencies | Qualified live-world checks over existing square rows and named product scope; refuse owed, missing, stale, witness-only or unreachable-only coverage. Reuse the bridge inventory rather than create a second claim ledger. |

Initial traces found no served collector calling the allocator reclaim/checkpoint
primitives, and outbound peer/catch-up paths remain model/design coverage. These
are implementation/coverage gaps, not demonstrated premature-reclamation or peer
safety defects. A suspected uncertain peer reply issue is being checked through
actual transaction composition rather than inferred from a defensive answer branch.
The device-syscall-return cut occurs after physical effects and before completion;
a simulator step that combines effects and posting is not by itself its mapping.

Authorization remains release-blocking: original B delivered exact article bytes
with required grants disabled. The defensive repair worker was stopped twice by
automatic content review for possible cybersecurity risk; source changes remain
preserved, but its fixed-callback qualification is incomplete. Do not relabel the
passing baseline native recovery tests as permission correctness or release approval.
