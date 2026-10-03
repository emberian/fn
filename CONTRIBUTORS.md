# Contributors' guide: how fn is built, the state it is in, and where it is going

This is the orientation for anyone (human or agent) joining the work. The rules themselves are in
[AGENTS.md](AGENTS.md); the user-facing guides are in [docs/](docs/README.md). This file explains the
goals, the honest state of the architecture, and the structures we use to coordinate the work.

## 1. What fn is

fn is a news system: a specialized store and an executable ACL2 news core, served over NNTP and carried
over the Bundle Protocol (BP) for disconnected operation. Every decision the server makes (identity, bounds,
group tables, charges, framing, integrity, reply lines) is decided by ACL2 code that is proved, and the
served product is an SBCL core built from those books (no ACL2 at run time).

## 2. Goals, vision, constraints

**The vision: software with a warranty.** Every resource spent on a user's behalf is accounted for up
front, and every claim the project makes names its evidence (a source revision, a proof manifest, a
qualified image, a deployment) and is true of the function the host actually calls.

**Standing constraints** (decision register: [planning/decisions.md](planning/decisions.md)):
- **No arbitrary ceilings on stored data (D27).** Admission limits belong to the operator's profile; work and
  allocation are bounded per scheduling step, and exhausting a quantum yields or resumes, never truncates.
- **No whole-state revalidation on a served path.** Carry the invariant in state and prove it preserved.
- **Uncertain, refused and accepted stay distinct** at every boundary, exit codes included.
- **Durable acceptance comes only from persisted state.**
- **No skip-proofs, defaxiom or trust tags toward a completion claim.** A trusted facility is isolated and
  named as an assumption (`books/assumptions*.lisp`).
- **Fix forward; never revert to make something green.** Unwiring keeps the code and records its completion.
- **No migrations.** Nodes redeploy fresh at a release; one store format.
- **Releases are a sequence** (6.6.0 .. 6.6.5, then 6.7.x, then 6.6.6, then a `.6` appended per release).

**Directions decided in October 2026:**
- **Move the host into ACL2.** The original split ("ACL2 decides, the host performs I/O") left all
  coordination (sections, handoffs, lifecycle, failure handling, retries, deadlines) outside the logic.
  ACL2 now owns coordination too; the host shrinks to thin, named primitives (syscalls, sockets, file
  descriptors, threads and mutexes, the clock, crypto and compression FFI), each specified as an oracle step
  with a named assumption. Plan: `planning/design/tcb-shrink-2026-10-03.md`.
- **A whole-system theorem.** A host model in ACL2 whose steps are the host's atomic sections, with
  theorems over every interleaving and every crash cut, so the per-call theorems compose.
- **Generators over hand-written instances.** When a shape is written a second time, write the macro:
  `def-loop`, `def-representation`, `def-carried`, and in progress `def-owner-writer`, the teeth generator,
  `def-carried-view`, `def-cursor`, `def-holder`, `def-nntp-command`, `def-entry` with derived cost.

## 3. The state of the architecture (October 2026)

The books are substantial: roughly 636k lines of ACL2 proving properties of the functions the host calls.
The weaknesses are around them:

- **The host is large and unproved.** About 58k loaded lines of SBCL Lisp (host/*.lisp ~26k, of which 70%
  of functions are `:program` mode; host/native ~41k), with ~390 lock sites and ~440 handler clauses that no
  theorem covers. Every theorem is about one call, or a serial fold of calls, and assumes the host calls it
  atomically on a valid state with effects in order. The October inspections (an 18-reader sweep, two
  independent standing reviews, a lock-discipline check) found the expected consequences: swallowed faults,
  blocking I/O under the owner mutex, lifecycle races, a client or peer event stopping the whole node,
  descriptors closed that the host did not own. These are tracked in the repair ledger (section 4).
- **Whole-state revalidation is still on the POST path.** `fn-owner-io`'s guard re-validates the store on
  every call, O(store) per POST. The fix is raw dispatch over the carried invariant (stage 5: the owner's
  state moves into its own stobj, its writers become `:logic`), or redesigning the store-file step idiom.
- **Certification debt.** At the current bytes only a minority of books have an archived green verdict; a
  whole-tree requested certify is owed. Some checks in `make check-lane` are red on dev.
- **Claim drift.** Comments and specs that the code contradicts, tests that cannot fail, parked code still
  counted. The tools that police claims were themselves partly fail-open until October.

None of this is hidden: each item is in the ledger with its evidence and owner.

## 4. How the work is organized

The current model roles, dispatch order and behavior-first operating contract are
in [the overnight plan](planning/overnight-2026-10-03.md). Earlier role names below
describe the previous team, not additional agents to launch.

### Roles
- **Coordinator** (one session): priorities, decisions, conflicts. Does not relay routine messages.
- **Runner** (one agent): the sole integrator of `origin/dev`.
- **Lanes**: one agent per area of work, each with a branch `lane/<name>` and a worktree under `build/lanes/`.
- **Deputies** (Fable): design and generator work (the declaration macros, the host model).
- **Reviewer** (the liaison, with GPT-6-Astra via Codex when available): reviews READYs adversarially and
  takes workstreams of its own.

### The repair ledger: the single list of open work
`planning/repair/repair.py`, one JSON file per item under `planning/repair/items/`.
Every finding from every source (inspections, reviews, check-lane, measurements) is an item with an owner
and a state: `open`, `in-progress`, `ready` (merged into `origin/next`), `landed` (on `origin/dev`),
`refuted`, `duplicate`, `deferred`. `repair.py list --owner LANE --open`; `repair.py report` writes `STATUS.md`.
Items are also tagged by exposure (live today / conditional / latent), locus (the subsystem), and
disposition: LOCAL (fix where it is), DISSOLVES-IN a rebuild slice (the finding becomes that slice's
acceptance test), or BRIDGE (live today, so a small fix now that the slice later supersedes).
New findings go into the ledger, not only into a message. Each lane holds at most two items in flight.

### The merge train: `origin/next`
The runner merges review-cleared work into `origin/next`; fast checks run once per batch.
A breaking merge is repaired forward, with the affected candidate or claim held until repaired. When `next` passes the fast checks
and one native and image run, `dev` fast-forwards to it and an image set is published. Base new work on
`origin/next`.

### Each check runs once
A lane: REPL admission, a certify of the books it changed (`tools/farm.py`, cached by content), and natives
only for modules its host change affects, with a red-before and green-after run for the defect. A reviewer
reads the diff and the evidence and does not re-run. The runner: fast checks on the train and one native
and image run per promotion. Evidence (run ids, manifests) is reused when the bytes match.
(`planning/landing-pipeline.md`)

### What makes a claim
See AGENTS.md "What makes a claim": the subject is the function the host calls; keystones ship with teeth
(a positive witness, one removal per hypothesis, a labelled mutation); cost claims are measured guards-on on
realistic state and need a visit bound, not only an output bound.

### Design decisions
A design question gets a decision file under `planning/design/` (the rule today, why it came up,
measurements, options, a lean). The coordinator and Astra settle it between them (at most two rounds);
ember is asked only when the two disagree, when it is a matter of product intent, or when the step is
irreversible or outward-facing. Accepted decisions become D-numbers in `planning/decisions.md`.

### Checks that run on every integration
`make check-fast` (interface_emit, host_check, ledger, reach_check, build_lists_check, secrets_check,
`tools/lock_discipline_check.py --check`). The lock-discipline check fails closed on any new lock, blocking,
failure-routing or descriptor-ownership finding against a shrink-only baseline (`tools/lock_discipline_baseline.json`).

### Evidence
Certification manifests and native logs are filed in the content-addressed archive on hbox
(`tools/evidence_store.py`) and indexed by `planning/evidence-index.tsv`; `planning/evidence/<path>` stays the
name you cite. `tools/green_check.py --strict` counts a book as green only at its current bytes, with an
archived manifest from a run that requested it.

### Machines
hbox (main build and native box; builds under `swarm-build`), persvati (second check box). Never touch the
live node or its store. Disk in `~/dev/fn` is capped at 30 GB: remove a lane's worktree when it lands.

### What is tracked, and what stays local
Tracked, so anyone can take the state forward:
- `planning/repair/`: the repair ledger (one JSON per item, `repair.py`, the generated `STATUS.md`).
- `planning/design/`: design decision records, with consultation answers and the decisions taken; accepted ones
  become D-numbers in `planning/decisions.md`.
- `planning/landing-pipeline.md` (the merge train; each check runs once) and the current plan
  (`planning/plan-2026-10-03.md`).
- `planning/handoff-2026-10-03/`: each workstream's continuation at the end of the October 2026 wave (branch, sha,
  what is verified and what is not, the next steps).

Local to a coordinator session, under `build/coordinator/` (untracked): the live lane notes, the runner's
announcements, the roster, the lane briefs. Anything durable in them moves into the ledger, a design record or a
handoff file.

## 5. Contributing a change

1. Pick an item from the ledger (or add one), set it `in-progress`.
2. Branch from `origin/next` into a worktree under `build/lanes/<name>`; never stash, reset or check out the
   shared checkout.
3. Write the failing test or witness first; fix; prove and certify what you changed; run the natives your
   host change affects.
4. Send a READY: the sha, the ledger ids, the evidence (run ids, manifests), what you did not run.
5. After review, the runner merges it into `next`; when `next` reaches `dev`, the item is `landed`.
