# How we work now

A lane is briefed from this page, [now](now.md) (dev, the goal, the lanes)
and [the current view](current.md). Release scope is
[the trajectory plan](plan-2026-09-22-trajectory.md) §0 to §2. The rules of
[AGENTS.md](../AGENTS.md) apply in full; this page is the loop.

## The loop

1. **Start from ground truth, in your own worktree.** The brief names the
   step, the functions and books, the host function that calls the subject,
   the theorem statements, the teeth owed, the box and the evidence file,
   with absolute paths and pasted signatures. A brief that describes a
   signature instead of pasting it means: read the named source at the
   pinned revision first, and ask only when that does not resolve the
   contract.
2. **Iterate in a live session.** `tools/proof_repl.py start NAME BOOK
   --upto EVENT`, then `send`; 300 s bounds a discovery attempt, and a
   timeout is a finding with the theorem named. Compare attempts by the
   prover steps each answer reports, not by seconds (`send-range` and
   `probe` for a stretch or a trial copy). A session stops itself after 20
   idle minutes (`--idle-timeout MIN`, 0 = never; raise it before a long
   farm or native wait), and `reap --idle MIN` clears idle sessions box-wide.
   A dependency uncertified at your bytes refuses `start` by name:
   `--certify-missing` certifies it, `--source-deps` loads it from source
   (`--ld-local` keeps its local events local; its non-local includes are
   sent before the encapsulate). `start` runs each of the book's events
   under the per-form prover limit (`--load-limit S`, default `--limit`),
   so a runaway lemma stops the load with its checkpoints in `status`.
   `--host hbox|persvati` runs any command in your tree on that box;
   `--host laptop` (or `auto`, when the laptop is less loaded per core and
   has a free slot) runs the session here, with the ACL2 that
   `tools/build_local_acl2.sh` built and named in ~/.config/fn/acl2.
   `forms BOOK` numbers a book's forms for `#N`. An admitted form is not a
   certificate. A raw host file (`host/native/*.lisp`) loads in seconds with
   `tools/host_check.py --load` (errors, arity, macro order, undefined
   names), before any image build.
3. **Certify incrementally.** `farm.py submit <box> --affected-by <book>` (or
   the changed books and tests as plain roots): cached books install, the
   rest certify. Never `--closure` for lane work. Wait with one background
   command and do other work. A run that says ALL FROM THE CACHE certified
   nothing of yours; a KILLED run (exit 143, earlyoom) has no verdict, it
   did not fail.
   **Claim an id before you write it**: `python3 tools/next_id.py claim
   PRF --lane NAME --note '...'` (any kind: D, PRF, SCN, PKT, a
   requirement prefix) takes the next number no branch, worktree, LANEDUMP
   or earlier claim holds, in the shared ledger
   (`build/coordinator/id-claims.jsonl`); `next_id.py check` lists your new
   ids against it before you report.
4. **Report what the tools say**: theorem statements, host function, teeth
   book, the `green_check` line, run id and committed manifest, evidence
   file, and what you did not do. "Committed" means the line in
   `planning/evidence-index.tsv`: `evidence_manifests.py add RUN` uploads the
   manifest to the evidence archive (hbox `/tank/fn/evidence`, by sha256) and
   stages that line; `evidence_store.py put PATH` does the same for a report,
   log or transcript under `planning/evidence/`. A reader fetches by hash
   (`evidence_store.py cat PATH`, or any tool, through build/evidence-cache).
5. **The coordinator merges as lanes land**, regenerates the ledger and
   `current.md` in the merge (never hand-resolving a generated file),
   checks new registry IDs against the claims ledger (`next_id.py check`;
   the registry merge driver names an unclaimed row and a collision's
   claimant), runs `make check` and
   `teeth_check --strict --changed-since`, removes the lane's worktree, and
   coalesces the certification of merged bytes against the current frontier
   (one run per batch of merges, reusing matching results; never one run
   per merge).
   A lane merges `dev` mid-flight only for a landed change it needs, then
   recertifies what that moved.
6. **Waves converge once.** At convergence, one immutable candidate: a
   fresh closure and one qualification lane over the whole set while the
   next wave runs. Never re-qualify interim cuts. A regression the cut finds
   does not freeze unrelated development, but it blocks the affected
   deployment or claim until the repaired candidate has matching evidence;
   unchanged evidence is reused, a green verdict is never transferred to
   changed bytes. Deploy when the candidate is green.
7. **Green has two coordinates** (2026-09-28). BOOK GREEN at sha X: make
   check (green_check in it), the union cites of every merged lane, and the
   OpenBSD guest's certification of the default closure. NATIVE GREEN at sha
   Y: the native modules on the images built at Y. Natives re-run only when
   host/, packaging/, a tool the natives call, or the images' book closure
   (the image digest) changed since the last native green; a change to books
   outside the image closure reuses the last native verdict, named with its
   sha. The report says `BOOK GREEN <X> / NATIVE GREEN <Y> (image digest
   ...)`. No module runs at 1M: open_depth runs at 100k, and a scale claim
   comes from a curve (1k to 100k, fitted and extrapolated; tools/
   scale_curve.py), stated with its fit and range.

## Width and who proves

Start around ten lanes; add one only for substantive work. Claims announce
intent and do not reserve files; lanes that overlap agree on the interface
and on who assembles the combined change, then certify its bytes. A lane
whose brief says implement-only hands a failed proof (source, event, log)
to the proof owner rather than searching for it.

## Proof cost

- A book over ten seconds at two jobs is a defect (D26). The seconds are the
  book's fastest passed 2-job measurement of its current bytes, and over the
  line they count only when quiet (1-minute load at most a quarter of the
  box's CPUs, recorded per book) or above 30 s; otherwise `UNQUIET`, a
  warning to re-measure quietly. Compare attempts, and ratchet baseline
  books, by ACL2's prover steps, which no load moves: `proof_cost` fails on
  a book not in the baseline conclusively above 11 s, or on a baseline book
  whose steps rose more than 10 %; 10 to 11 s prints `NEAR`; a failed
  certification is `FAILED`, never `IMPROVED` (docs/proofs.md). The baseline only shrinks, by proof
  work: read the certify log's per-event times and `Rules:`, one
  instrumented session at most, never raise a timeout or weaken a statement.
- The band and the threshold are operating rules, not proof that an
  excursion is noise: keep matched host, toolchain and job conditions when
  adjudicating one. Splitting a book must reduce total or critical-path
  work, never only the per-book figure.
- Aim for under three minutes from edit to certified verdict; record queue,
  install, proof and total time when you claim a speedup.

## Boxes

`swarm-build` around every hbox build; on the laptop, `tools/acl2` or
`tools/proof_repl.py` for every ACL2 (the pool, `tools/acl2_slots.py`, caps
each process at 8,000 MB and admits six: the machine-memory budget; a bare
`acl2 <` bypasses it and is how the laptop hard-crashed on 2026-09-25); no bare `&` in a lane shell; `free` lies on hbox; a farm run's
`--remote-root` is absolute; certificates install from the box's cache,
never from a live worktree. The box-specific environment for a remote REPL
and the full trap list are in the `proof_repl.py` header and the runbooks.

## What a step is

DONE or NOT. DONE means the theorems over the host-called subject exist with
teeth, the affected closure is green at the current bytes, the behaviour is
observed on an image, and the evidence file is filed (indexed and archived). A step that would need a
`partial` row is two steps. A branch someone else left is an input to a
brief, never a thing to resume. Intermediate reds stay visible and never
excuse a weaker statement or a host twin.

## Short local loops and frozen convergence (2026-10-03)

Send the first discriminating subject result from a warm scoped session or
selected test method immediately. Finish evidence filing and affected-root
certification asynchronously; an unfinished check remains unfinished. Reuse the
unchanged dependency world and resume the failing event. `--ld-leak` is a
source-discovery facility: final admission/certification reproduces without
leaked LOCAL rules. Narrow reviews need the changed contract and actual callers,
not another reread of unchanged whole-system design.

Integration qualifies one immutable runnable candidate while subsequent READY
source continues in the next wave. Interfaces/world checks required for that
candidate run against its bytes; unrelated ledger regeneration and subsequent
repairs must not move the qualification frontier. Integration remains the sole
dev writer and scarce build scheduler.

Existing-log examples distinguish proof cost from total feedback. Served's
residual loop took0.5–0.8s wall including sync (0.05 ACL2s/29,380steps), while two
plan dependency replays took120/125 ACL2s and33Msteps. Foundations reduced a
reader equality proof53.13s/5.58Msteps to0.06s/446steps; its73 cost fixtures took
0.68s wall. Runtime's actual real-thread fixtures took0.30s and15 structure tests
3.78s. Tools' narrow shape method took0.007s while selecting its whole-tree test
class took71s. Empirical edit-to-first actual native verdict took5.15s and paired
restart/correctness measurements10.75s on an explicitly historical image.
Groundwork's HM run took190s overall for10.28s certification, with10.66s measured
slot wait; remaining wrapper/evidence overhead is being isolated. Scoped
`green_check --changed-since` currently performs whole-world analysis before
filtering; Tools owns narrowing that computation while preserving final full
validation. These measurements describe those loops, not universal baselines.

External model reviews run asynchronously and are timeboxed advisory work. A
CLI timeout, truncated reasoning or unavailable response is not a completed
review. Concrete suggestions are independently checked; disagreements remain
with their reasons. Current Kimi supports an explicit agent file with `tools:
[]` and `subagents: []`; use an empty task directory and explicit empty skills
directory for a supplied-source review. Grok's empty tool allowlist still starts
configured MCP services, so do not assume it isolates all local initialization.
Never put keys in argv, output or review context; send minimal project source.

Finding IDs name acceptance obligations, not mandatory separate mini-projects.
Group common-cause ownership or generator defects into coherent consumed
changes: the captured export/reclaim capability repaired15 getter findings in
one slice; physical actor families share one startup/join/fault mechanism.
Helpers send source READY directly to their assembler; DC03 rows feed Served's
actual switch. Shared ledger/current/lock generation runs once per candidate,
not as a full ritual in each helper. Actual interface prerequisites still run;
source integration may carry explicit pending report/evidence status. Owners
retain residual obligations and do not reopen unchanged proved facts.
