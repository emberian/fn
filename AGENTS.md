# Working on fn

Read [the project guide](docs/README.md), [architecture](docs/architecture.md),
[decisions](planning/decisions.md), [now](planning/now.md) and
[the current view](planning/current.md) before substantial changes, then the
specification for the affected subsystem. How lanes work is
[how we work](planning/how-we-work.md).

## Scope and authority

- fn is an ambitious, design-first project: a specialized store and an
  executable ACL2 news core, served over NNTP and carried over BP for
  disconnected operation. Preserve that scope; advance it in small complete
  steps.
- Agreed directions live in the decision register. Proposals and open
  questions are not requirements. This file adds no approval gate.
- Requirements live in `planning/requirements.json`, proof targets in
  `planning/proofs.json`; IDs are stable and the coordinator assigns new
  ones at merge (`tools/next_id.py`). Change the registry, the specification
  and the scenario together.
- Preserve the supplied RFCs and cite their sections; distinguish an RFC
  requirement, a stronger fn guarantee and a local policy.
- A claim names its coordinate: source revision, proof (a committed
  manifest), qualified image, deployment. `planning/current.md` keeps the
  four apart; none implies another.

## Implementation discipline

- ACL2 owns every decision: identity derivation, bounds, group tables,
  charges, framing, integrity trailers, reply lines. Host code performs I/O
  and calls it; Python and host Lisp never compute a value ACL2 also
  computes or compares. What ACL2 cannot decide yet is an open registry
  item, not a host function.
- No arbitrary implementation ceilings on stored data (D27). Admission
  limits belong to the operator's supported profile. Bound work and
  allocation per scheduling step, using streaming or resumable operations
  where needed; exhausting a work quantum yields or resumes, it never
  silently truncates data. Validate that every supported profile is
  representable by the selected codecs and runtime: profile validation,
  representation and format evolution must agree.
- The served path uses concrete representations (D27). Octet lists are the
  logical model. Each representation boundary has a named abstraction or
  refinement theorem connecting the host-called implementation to its
  logical model, including outputs and effects; executable functions are
  guard-verified, representation invariants are established and preserved,
  and cost improvements are measured under matched conditions. A boundary
  theorem, not a twin of every helper.
- Parsing external data never invokes the Lisp reader or evaluator. Bound
  the work and allocation one request may cause before consuming it.
- Octets, parsed fields, content identities, Message-IDs and local article
  numbers are distinct types.
- Durable acceptance comes only from persisted state, never from a socket
  write, a transport ACK or an in-memory update. An ambiguous persistence
  failure is a recovery event: never roll back silently or keep mutating.
- Keep conflicting evidence and its provenance. No last-writer-wins on
  wall-clock time; never merge local NNTP numbers globally.
- No `skip-proofs`, `defaxiom` or trust tags toward a completion claim; a
  trusted facility is isolated in the trust boundary with its assumptions.
- An abstract cryptographic model proves nothing about real signatures,
  hashes, disks or a peer's honesty.

## What makes a claim

From [the 2026-09-18 review](planning/review-2026-09-18-independent.md) and
the 2026-09-22 proof-engineering review. Green is not true.

- **The subject is the function the host calls.** A theorem about another
  function counts only with a named theorem equating the two. Name the host
  function that calls the subject; `current_view.py` finds the line, and a
  line number never goes into a book. A theorem about a branch the composed
  machine cannot reach is marked `unreachable-in-composition` or the branch
  goes. (`reach_check --strict`.)
- **Cite keystones.** `ledger.py --check` refuses a flagged corollary or
  restatement; name those lemmas `-unfolds` or `-by-definition`.
- **Teeth ship with each keystone.** A reachable positive witness asserts
  the complete antecedent and conclusion, per literal theorem. A
  hypothesis-removal witness affirmatively checks every retained
  hypothesis, failure of the omitted hypothesis, and failure of the
  conclusion. Label corrupted-state and mutation witnesses separately.
  Remove a redundant hypothesis only after proving the weakened theorem;
  failed proof search is not a counterexample.
- **A named assumption is an `encapsulate`** with a local witness in
  `books/assumptions.lisp`, and the theorems that use it mention it.
- **Every process-death cut is a model crash point.**
  (`transcribe_check`, `native_program_check`.)
- **No whole-state revalidation on a served path**: carry the invariant in
  state and prove it preserved.
- **Uncertain, refused and accepted stay distinct** at every boundary,
  exit codes and test expectations included.
- **Counts are generated** (`tools/ledger.py`, `tools/current_view.py`);
  prose carries the property, its hypotheses and its scope. A conflict in a
  generated file is resolved by regenerating it.
- **Quote the pessimistic number with its scope** in the same sentence; the
  collision figure, not the second-preimage one.
- **Behaviour and its invariants land together.** A lane certifies what it
  changed and what includes it before it reports, and cites the manifest.
  A commit message is not certification; `green_check` is.
- **Open a codec in a hint**, never at the top of a book (`theory_check`).
- A proposed theorem is not proved; an admitted definition is not
  guard-verified; passing tests are not a proof.

## Working together (ember's corrections)

- Never `git stash`, reset or check out the shared `~/dev/fn` checkout; other
  agents are live in it. Work in your own worktree under `build/lanes/`;
  the coordinator merges.
- About ten useful lanes; claims announce intent and lock nothing. Lanes
  coordinate through their `LANEDUMP.md`; the coordinator names each lane's
  model in its brief.
- Orient to the plan, not to another audit. Waves, not per-cut
  qualification: qualify one immutable candidate at convergence while the
  next wave runs. A regression the cut finds does not freeze unrelated
  development, but it blocks the affected deployment or claim until the
  repaired candidate has matching evidence; unchanged evidence is reused,
  a green verdict is never transferred to changed bytes.
- Run the narrowest thing that could refute you: affected roots, never a
  lane `--closure`. Reuse matching evidence; coordinate expensive runs.
- On hbox: `swarm-build` around every build; `free` lies (read `arcstats`
  and RSS). On the laptop, ACL2 only through `tools/acl2` or
  `tools/proof_repl.py`: the slot pool (`tools/acl2_slots.py`) caps each
  process at 8,000 MB and admits six, which is the machine-memory budget;
  the login shell's export is a second line, never the protection.
- No deployment, publication or messaging side effects unless the task
  authorizes them; the live node is protected.
- Before ending: registries and `current-view.json` accurate; report what
  changed, what ran and what remains open.
