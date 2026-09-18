# Working on fn

Read [the project guide](docs/README.md), [architecture](docs/architecture.md),
[milestones](planning/milestones.md), and [decisions](planning/decisions.md) before
substantial changes. Then read the specification for the affected subsystem.

## Scope and authority

- The user has chosen an ambitious design-first project: a specialized storage
  layer and an executable ACL2 news core, with NNTP and eventual disconnected/DTN
  operation. Preserve that scope while implementing it in small complete steps.
- Agreed directions are recorded in the decision register. Proposals and open
  questions are not established requirements. Resolve routine choices with the
  current task's authorization; this file introduces no additional approval gate.
- Requirements live in `planning/requirements.json`; proof targets live in
  `planning/proofs.json`. Their IDs are stable. Update the registry, relevant
  specification, and scenario together when changing a contract.
- Preserve the supplied RFC files. Reference their sections; distinguish an RFC
  requirement, a stronger fn guarantee, and a local policy choice.
- No server, proof, or flight-readiness claim follows from this scaffold.

## Implementation discipline

- Keep protocol/storage decisions in executable ACL2 definitions. Host code
  performs I/O and enforces boundary guards; avoid a second implementation of
  core semantics in the adapter.
- Keep the logical model separate from its concrete representation. Optimize via
  explicit correspondence arguments. See [the proof plan](docs/proofs.md).
- Treat octets, parsed article fields, content identities, Message-IDs, and local
  article numbers as distinct types/concepts.
- Persist accepted obligations and allocation decisions. Never infer durable
  acceptance from socket writes, transport ACKs, or an in-memory index update.
- Treat ambiguous persistence failures as recovery events. Do not silently roll
  back or continue mutating after an uncertain commit.
- Parsing external data must not invoke the Lisp reader or evaluator. Bound
  lengths, nesting, work, and allocations before consuming untrusted inputs.
- Preserve conflicting evidence and explicit provenance. Do not introduce
  last-writer-wins based on wall-clock time or merge local NNTP numbers globally.
- Do not use `skip-proofs`, `defaxiom`, or trust tags to report proof completion.
  If an integration genuinely needs a trusted facility, isolate and document it
  in the trust boundary and report its assumptions. Never conceal proof gaps.
- Do not use an abstract cryptographic model to claim that real signatures,
  hashes, storage hardware, or a peer's honesty have been proved.

## Evidence and handoff

- `make check` verifies scaffolding only. `make certify` invokes real ACL2 for
  the current integrated book/test batch; `python3 tools/run_simulator.py` runs
  deterministic scenarios against the same acceptance definitions.
- Certify only owned book roots during parallel edits. Root coordinates a frozen
  integrated batch. Review coherent batches once, fix concrete defects, and keep
  independent implementation work moving; do not create serial review loops.
- Add substantive model, codec, fault, and interoperability tests as those layers
  appear. The [validation plan](tests/README.md) defines the intended evidence.
- Record exact tool versions, invocation, input revision/content digest, result,
  and limitations for certification or integration evidence.
- A proposed theorem is not a theorem proved by ACL2. An admitted definition is
  not guard verification. Passing tests is not a proof or an RFC audit.
- Before ending a development task, keep the milestone's current task and the
  registries accurate. Report what changed, what ran, and what remains open.
- Do not create deployment, publication, or messaging side effects unless the
  user's task authorizes them. Local design and implementation need no invented
  approval ceremony.
