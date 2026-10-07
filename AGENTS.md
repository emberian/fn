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
  `planning/proofs.json`; IDs are stable; a lane claims a new one in the
  shared ledger before writing it (`tools/next_id.py claim`) and the
  coordinator checks the claims at merge (`tools/next_id.py check`).
  Change the registry, the specification and the scenario together.
- Preserve the supplied RFCs and cite their sections; distinguish an RFC
  requirement, a stronger fn guarantee and a local policy.
- A claim names its coordinate: source revision, proof (a cert-cache
  entry at the book's current closure key, read by `green_check`), qualified
  image, deployment.
  `planning/current.md` keeps the four apart; none implies another.
- A report a reader needs is a short committed file (`evidence_size_check`
  keeps logs out); a log stays on the box and is named `box:path`. Code a
  tool or test runs lives under `tools/` or `tests/`.

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
  restatement; name those lemmas `-unfolds` or `-by-definition` and do not
  cite them as events.
- **Teeth ship with each keystone.** A reachable positive witness asserts
  the complete antecedent and conclusion, per literal theorem. A
  hypothesis-removal witness affirmatively checks every retained
  hypothesis, failure of the omitted hypothesis, and failure of the
  conclusion. Label corrupted-state and mutation witnesses separately.
  Remove a redundant hypothesis only after proving the weakened theorem;
  failed proof search is not a counterexample.
- **A named assumption is an `encapsulate`** with a local witness in
  `books/assumptions.lisp` or a book it includes (`books/assumptions-*.lisp`),
  and the theorems that use it mention it.
- **Every process-death cut is a model crash point.**
  (`native_program_check`.)
- **No whole-state revalidation on a served path**: carry the invariant in
  state and prove it preserved.
- **Uncertain, refused and accepted stay distinct** at every boundary,
  exit codes and test expectations included.
- **Counts are generated** (`tools/ledger.py`, `tools/current_view.py`,
  `tools/coverage.py` for what the world says about each host-called entry);
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
  coordinate through `build/coordinator/lanedumps/<lane>.md` (first section: a
  continuation, at most 150 lines; a root `LANEDUMP.md` stays untracked scratch
  and `tools/lanedump_check.py` refuses a tracked one); the coordinator names
  each lane's model in its brief.
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

## Advisory external model reviews (ember, 2026-10-03)

Ember explicitly authorized every agent to consult the available `kimi`, `grok`
and ZAI interfaces periodically for adversarial review. Batch substantial shared
changes and sometimes seek early design critique; this is not an every-change
ritual. Their models differ in ability. Treat findings skeptically, discuss or
rebut them, verify concrete source claims with witnesses, and preserve material
dissent with the resulting engineering reason. Reviews are advisory, never an
approval gate or a vote. The owner remains responsible for implementation,
integration and evidence.

Discover the actual CLI help and local invocation guidance. Send only the minimal
relevant project context, preferably pasted source in an empty review directory,
and disable editing/tools/subagents/web when supported. Do not transmit personal
files or secrets, print credential files, or include keys in command arguments or
logs. `~/.zai-key` is available to a credential-aware client, not a file to display.
This authorization is for model consultation, not messages to people, deployment
or publication. Future lane briefs inherit this practice.

## Working fast without lying (ember, 2026-10-06/07)

The coordinator's standing rules are `build/coordinator/DEPUTY-RULES.md`; this is
the part every lane needs.

- **Iterate in the REPL, certify at READY.** Proof work happens in
  `tools/proof_repl.py` (cached dependencies, seconds per `defthm`) on persvati,
  hbox or the laptop pool; pass `--certify-missing` when a dependency's cert is
  missing and `--load-limit 0` for long events. One-shot `tools/acl2` loads and
  `certify-book` are the gate, not the inner loop. Certify of record is hbox or
  persvati (`farm.py`); a laptop cert is the author's check only (arm64).
- **Fast gates to merge, full gates at convergence.** A lane merges on its own
  narrow evidence: `--affected-by` certify of the books it touched, the filtered
  tests it touched, `host_check --load` if it touched `host/`, and no contract
  breach. Images, natives, host-ld, full-tree `green_check` and `check-fast` run
  in a convergence phase on a tagged dev sha; every red there is attributed to
  the lane that caused it and goes back to it. Merging continues during
  convergence, fixes only. Say which mode and which closure every green number
  covers (`green_check --profile default` is not the tree).
- **Transformations, not hand edits.** More than ~5 identical sites is a tool in
  `tools/` with tests: read books with a position-keeping reader
  (`tools/lisp_rewrite.py`), rewrite structurally, confine the byte diff to the
  rewritten form, refuse what it can't transform by named reason, emit the
  residual. Hand conversions already done are its fixtures. `ast-grep` where a
  tree-sitter grammar exists; the reader for Lisp.
- **Pull the next known step into the lane in hand.** Fix the defect, don't just
  own it; drain the class, not the book; prove the corollary the next lane needs;
  fix the root a checker reveals, not the instance. Owed items are for work that
  needs a different lane or a decision. Same gates, bigger steps; keep the
  continuation file current so a big step that dies is resumable.
- **No process kills on shared hosts.** Never `kill`, `pkill`, `killall` or
  `systemctl stop` anything you did not start, and never by name or user match
  (a `pkill -x sbcl -u hbox` took down the production node on 2026-10-07). Stop
  your own job by the PID you recorded, or give every long command a `timeout`
  so there is nothing to kill. Report a dead process; don't restart it.
- **Context is a budget.** `wc -l` before any Read; over 800 lines is grep plus
  ±60; never a worktree `LANEDUMP.md`; long output to `/tmp/<lane>-<what>.log`
  and read its tail. Commit within 30 minutes, proof lanes per lemma. A lane
  that dies of prompt length is restarted from its continuation file, never
  resumed.
- **Push `HEAD:lane/<name>` only**; the integrator is the only writer of
  `origin/dev` and merges in trains with one regeneration per train
  (`tools/train.py`). Certificates for one image come from one origin; a set
  that doesn't compose is recertified into one, never patched.
- **Statement-first for programs.** A multi-lane program (storage, extraction,
  generators) starts with a written program doc: current invariants with
  file:line, target definitions and keystone statements with their teeth,
  dependencies on other programs, memory and I/O estimates against the bar,
  then the lane plan. Lanes code after the doc exists.
- **Measure before you cut.** A memory or performance claim carries a measured
  before/after on a quiet hbox (RSS, not reservation; the bar is 128 MB for the
  whole resident process, core included). A measuring script's own buffers are
  not the subject.
- **No migration or compatibility duty** (D68): old layouts and their readers
  are deleted with their proofs, not carried.
- **Extra lanes on `claude-grok`** (`claude-grok -p '<task>' --output-format
  json`) for bounded mechanical work with the gate command in the brief. Review
  and revise its output yourself rather than iterating with it; no shell on the
  farms beyond one certify command, no kills, no pushes to dev.
