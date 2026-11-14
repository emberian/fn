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

Other suspected counterexamples remain unexecuted: zero-budget issue, obsolete
4129 turn bound, and native Accept-prefix equality. Their status must not be
upgraded from source inspection alone.

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
