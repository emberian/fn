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

## Assurance rules (adopted 2026-09-18 after the independent review)

Each rule names the finding in [the review](planning/review-2026-09-18-independent.md)
that motivated it. Green is not true; these rules are how a claim earns its name.

- **The theorem subject is the function the host calls.** A property proved of
  a sibling API (a feed function the host does not use, an inner dispatcher
  under an outer interpreter, a helper with no caller) counts for a requirement
  only together with a named theorem equating it to the called function. Say
  which host line calls the subject. (D6, D7; wire and transfer rows of §4.)
- **Cite keystones, never corollaries.** A theorem whose proof is
  `:in-theory '(X-preserves-state has-Y)` is not a registry event; cite the
  lemma that does the work. A definition restated, `X ⊆ X`, `(equal e e)`, or
  a hypothesis that is the negation of the branch test is not a proof event.
  Name such lemmas honestly (`-unfolds`, `-by-definition`). (§4 rows 1 to 8.)
- **Teeth ship with the theorem.** Every keystone has, in its test book, a
  reachable non-degenerate witness and one `must-fail` case per hypothesis
  showing the conclusion fails without it. A separating witness must separate
  predicates by more than their weakest clause. (Binding witness, §4.)
- **Assumptions are constrained functions.** A named assumption (`A-*`) exists
  as an `encapsulate` with a local witness in `books/assumptions.lisp`, and the
  theorems that depend on it mention it. Prose alone is not an assumption.
- **One owner per decision, and it is ACL2.** Python and host Lisp may not
  compute a value that ACL2 also computes or compares: identity derivation,
  bounds, group tables, charges, framing, integrity trailers. If ACL2 cannot
  compute it yet, that is an open item in the registry, not a Python function.
  (Twins table, §4.)
- **Every process-death cut is a model crash point.** A test that kills the
  host at a boundary the model cannot express is a fidelity defect, not a
  passing test. Add the transition or retract the "every crash point" claim.
  (D4.)
- **The ledger is generated.** `proofs.json` events, guard counts, root
  counts and test counts come from `tools/ledger.py` over the books and
  evidence, never from typing. Prose carries the property, its hypotheses and
  its covered scope in one sentence; it does not carry counts.
- **Three outcomes stay distinct all the way out.** Uncertain, refused and
  accepted are reported distinctly at every boundary, including CLI exit
  codes and test expectations. (D13.)
- **Unreachable branches are not evidence.** A theorem about a branch the
  composed machine cannot reach is marked `unreachable-in-composition` in its
  book or the branch is removed. (Storage F9, F10.)
- **No whole-state revalidation on a served path.** A recognizer over the
  entire store or the entire retained input must not run per command or per
  byte; carry the invariant in state and prove it preserved. (D3, wire.)
- **Quote the pessimistic number with its covered scope in the same
  sentence.** A bound is stated with its exponent and its distance from the
  measured cost; a "certified" claim names the theorem and its hypothesis
  stack. Report the collision figure, not the second-preimage figure.
- **Housekeeping.** Function prefixes are registered in
  [`docs/prefixes.md`](docs/prefixes.md); lane worktrees under `build/lanes/`
  are removed when the lane lands; role names used in planning are defined in
  [`planning/swarm-cycles.md`](planning/swarm-cycles.md) or not used.

## Evidence and handoff

- `make check` verifies scaffolding only. `make certify` invokes real ACL2 for
  the current integrated book/test batch; `python3 tools/run_simulator.py` runs
  deterministic scenarios against the same acceptance definitions.
- Certify only owned book roots during parallel edits. Root coordinates a frozen
  integrated batch. Review coherent batches once, fix concrete defects, and keep
  independent implementation work moving; do not create serial review loops.
- Add substantive model, codec, fault, and interoperability tests as those layers
  appear. The [validation plan](tests/README.md) defines the intended evidence.
- For each behavior-changing batch, record added or changed assurance obligations
  alongside the implementation. Apply the [assurance scope rules](docs/proofs.md#assurance-grows-with-the-implemented-surface):
  distinguish missing evidence for implemented behavior from future feature work,
  and close critical composition/recovery gaps before adding dependent behavior.
  Counts of proofs/tests do not establish coverage; this adds no approval gate.
- Record exact tool versions, invocation, input revision/content digest, result,
  and limitations for certification or integration evidence.
- A proposed theorem is not a theorem proved by ACL2. An admitted definition is
  not guard verification. Passing tests is not a proof or an RFC audit.
- Before ending a development task, keep the milestone's current task and the
  registries accurate. Report what changed, what ran, and what remains open.
- Do not create deployment, publication, or messaging side effects unless the
  user's task authorizes them. Local design and implementation need no invented
  approval ceremony.
