# Deputy-scholar brief (read before any tool call)

You own one cluster of books. Fix everything you can inside it; keep its
include-closure certifying; return one report and one proposal for the
cross-cluster steps you could not take alone.

## Box rules (each one cost a lane hours in the last cycle)

- Certificates are installed in your worktree before you start (content
  hashed: `ACL2_BOOK_HASH_ALISTP=NIL` is set by every tool). Never run a full
  `make certify`. Certify only books in your cluster's closure, one root at a
  time, with `FN_ACL2_TIMEOUT_SECONDS=1800 python3 tools/certify_books.py <book>`.
- Any form slower than a minute: run `python3 tools/proof_profile.py <book>
  <form> --host hbox` FIRST and cure the fan it names (zero-useful rules,
  opened recognizers); never add hints before profiling.
- Iterate with `ld` on a scratch driver that starts with
  `(set-prover-step-limit 2000000)` and includes only your dependencies; the
  runner is for the end, not for search. Start it as
  `tools/acl2 --timeout 240 < driver.lsp` (equivalently `make acl2-ld`), never
  as bare `acl2`: the wrapper takes a slot from the machine-wide pool the
  runner uses, sets the same two environment variables, and kills the child at
  240 s and exits 124, so a runaway frees its slot with no PID to find. Bare
  `acl2` takes no slot -- on 2026-09-19 that put six ACL2 processes on a
  four-slot laptop. Do not hunt PIDs: raise or lower `--timeout` instead.
- At most ONE ACL2 process of yours at a time. Any run over two minutes uses
  the Bash tool's `run_in_background: true` and you wait for its notification.
  Never a polling loop; never `pgrep -f` on other lanes' processes; never
  `pkill`, `killall` or any pattern kill.
- A wide certification goes to the farm, never to the laptop:
  `python3 tools/farm.py submit persvati --jobs 12 --remote-root
  /home/ember/fn-lanes/<lane> --affected-by <book>.lisp --closure`, then
  `wait <run-id>`. `--remote-root` is absolute (a `~` is resolved against the
  host's `$HOME`, but write the path out); `--affected-by` selects over every
  Makefile root; `--closure` certifies their dependencies too, which is what
  a box holding no usable certificate needs. Add `--dry-run` to
  `tools/certify_books.py` locally to see the exact list first. `submit`
  installs the box's own cache (`/home/ember/fn-certcache` on persvati) into
  the mirrored tree before the runner starts and prints what it found
  (`installed N, ... uncached N`), so `--closure` now certifies what the box
  lacks rather than everything; `wait` publishes the run's pairs back there
  for the next lane. If your `installed` count is near zero, say so in your
  report: it means the box's cache has nothing for your books, not that the
  run was wasted.
- **READING `free` ON hbox IS WRONG.** hbox is a ZFS box, and the ZFS ARC is
  counted in `used` and in unreclaimable slab, never in `buff/cache`, so
  `free`'s `available` column badly under-reports. Measured 2026-09-21:
  `free -g` said 98 G used and 25 G available, while `/proc/meminfo` showed
  Slab 87.0 G with SUnreclaim 82.3 G, AnonPages just 1.2 G, and the ARC at
  45.1 G of which 43.8 G is metadata, dnode, dbuf and bonus caches. The sum
  of every process's RSS on the box was **2.7 G across 988 processes**, and
  no HOL process was resident at all. So hbox had ~29 G free outright plus
  ~45 G the ARC gives back under pressure, and 24 near-idle CPUs. To judge
  hbox, read `AnonPages` and the RSS sum, not `free`'s `used`.
- Box facts, measured 2026-09-20. persvati's ACL2 is
  `$HOME/fn-tools/acl2-8.7/saved_acl2`; hbox's is
  `/tank/fn/acl2-8.7/saved_acl2`, and `tools/certify_books.py` on hbox needs
  `FN_ACL2` set to it or it reports "ACL2 executable is unavailable".
  `farm.py submit` mirrors tracked files only: `scp` a scratch driver
  separately. Choose the box by measurement, not by habit: `ssh <box> uptime`
  and `free -g` first, take the lower load, and stay at `--jobs 6` on a box
  another lane is using (a `--jobs 12` race on a busy persvati lost
  `books/nntp-effects` once and cascaded "no certificate" into six roots).
  On hbox every ACL2 run goes through `swarm-build`.
- **One lock per box, and a farm run does not take it.** A gate --
  `~/fn-gates/<tree>-<rev>/gate.sh` on persvati, `/tank/fn/gates/<tree>-<rev>`
  on hbox -- holds `flock` on ONE file for its whole certification:
  `$HOME/fn-gates/.gate.lock` on persvati, `/tank/fn/gates/.lock` on hbox.
  `tools/verdict.py` takes that same file (it used to keep a second scheme of
  its own, which is not a lock), refuses with the holding process named, and
  queues only with `--wait-for-lock`. A `flock` dies with its holder, so
  nothing there is ever stale and nothing is ever removed by hand. Your
  `farm.py submit` deliberately does NOT take it -- it is a `--closure` run
  into your own remote root, not a gate -- so check the lock before you start
  a gate, not before you submit:
  `ssh <box> 'flock -n <lockfile> true && echo free || echo held'`.
- **The box cache is seeded as each book certifies**, so a run that fails
  (every wide run on this tree does) still leaves its passing pairs for you;
  if `wait` times out it fetches and publishes what exists before returning 3,
  and the run id stays usable for a second `wait`. Measured before/after in
  `planning/evidence/farm-cache-failed-run-2026-09-20.md`.
- **Run a harness from the tree you mean.** Every harness writes its evidence
  under the worktree the COMMAND was invoked from (`git rev-parse
  --show-toplevel`), not the one the script file lives in; a relative
  `--evidence` is anchored there too. Before this, a lane running the main
  checkout's `tools/twonode_gate.py` wrote its record into
  `/Users/ember/dev/fn`, where it sat untracked and blocked a merge.
- `certify-book` STOPS AT THE FIRST FAILURE, so "the book is open at X and
  everything else certifies" is a claim only about the events BEFORE X. The
  events after it have never run. Say "certified up to X; the N events after
  it are unattempted" instead, and expect a tail when X closes: one book's
  keystone closed on 2026-09-20 and ten of the eleven events behind it were
  then open, including four of the five keystones the book exists for.
- **A CLAIM catches an identifier collision at MERGE, not at allocation.**
  Measured 2026-09-21: two lanes both ran `tools/next_id.py`, both posted a
  board CLAIM, and both took D21 anyway, because neither could see the
  other's claim until one had merged. So expect to renumber, do it in one
  pass on the merge, and never assume your id survived just because you
  claimed it. If your id appears in a spec or a book comment, grep for it
  after merging dev.
- `python3 tools/next_id.py` prints the next free identifier in every
  registry. Run it, claim what it prints on the board with a one-line CLAIM,
  then write the row. The CLAIM line is what has actually been catching
  collisions: it caught D19 within the hour when two lanes reached for it.
- A new registry id is allocated by merging dev FIRST and taking the next free
  number, and it is claimed in one board line the moment you take it. Two
  lanes assigned PRF-029 on the same afternoon and one target had to be
  renumbered after the fact (2026-09-20).
- Registries are shared rows, not files. `planning/requirements.json`,
  `planning/proofs.json`, `tests/scenarios/catalog.json` and `docs/prefixes.md`
  are edited by reading, changing the named rows, and writing, immediately
  after merging dev; never by dumping a copy you read earlier (a whole-file
  rewrite during a wave dropped two proof targets another lane had added, on
  2026-09-20). Counts and events come from `tools/ledger.py --write`.
- Never `git stash`; never `git add -A`; commit named files with
  `git commit -F <msgfile>` where `<msgfile>` is named after your lane
  (e.g. `commit-<cluster>-<n>.txt` in the scratchpad: two lanes sharing
  `msg.txt` swapped commit messages on 2026-09-19); never search under
  `build/` or `/`.
- Commit named files at each milestone (a book certifies, a spec section
  lands), not only at the end: a harness restart ends your agent for good and
  a successor lane picks up your worktree cold from what is on disk.
- Hard budget: the tool-call number in your prompt. When it is spent, commit
  what certifies, write the report, stop.

## Micro discipline (apply everywhere in your cluster)

1. **Opaque records, generated.** Every new record is one `fn-defrecord` form
   (books/defrecord.lisp) plus `fn-defrecord-export` at book end; it generates
   the shape predicate, constructor, `mbe` accessors, accessor-of-constructor,
   injectivity, the three forward-chaining shape facts and the withdrawal.
   Never hand-write that pattern again (the fifth lint counts it). A property
   of a transition is proved with `fn-deftransition` (recognizer closed).
   Nothing downstream opens a record.
2. **Export policy.** A book ends with an explicit theory event. It exports
   keystones and record lemmas. Every accessor or unfold equality used only
   for guard proofs is `:rule-classes nil` (used via `:use`) or `local`.
   No `len`-backchaining or accessor-equality rule leaves a book enabled.
3. **Recognizers are carried invariants.** A whole-state recognizer guards the
   executable path under `mbe`; it is proved preserved by every transition
   and never re-run per operation.
4. **Teeth as concrete witnesses.** One `assert-event` per hypothesis on a
   specific violating value (under `with-guard-checking :none` when outside a
   guard). Never a general negated `must-fail`; never a trivially true
   assertion; if a hypothesis proves unnecessary, delete it from the theorem
   and say so.
5. **Layering.** Split books over 800 lines at their seams; fold ad-hoc
   `-invariants`/`-traces`/`-teeth` sprawl into definitions, properties and
   one test book per cluster, when that does not cross cluster boundaries.
6. **Honesty.** A theorem you cannot close within budget is removed and
   recorded open, never weakened; a claim in a spec that a theorem no longer
   supports is walked back in the same commit.

## Report (`planning/deputies/<cluster>.md`, at most 60 lines)

HEAD; per book: certified (evidence dir) or open (failing form); before/after
ledger numbers for your cluster (global rewrite rules exported, SUSPECT
count, closure certify wall time); what you changed and why; the proposal:
the cross-cluster steps, each with the exact interface change and who owns it.

## Talking to other deputies (tested 2026-09-19)

- Your prompt carries a roster: cluster name → agent ID for every sibling
  (later launches are sent to you by message). Siblings are reachable ONLY
  by that ID: descriptions and cluster names do not resolve, and you have no
  agent listing.
- `SendMessage` is a deferred tool: load it first with
  `ToolSearch` query `select:SendMessage`, then `SendMessage` with `to` set
  to the ID. A message arrives at the recipient's next tool round wrapped as
  `<agent-message from="<id>">` and wakes a finished agent; `to: "main"`
  reaches the root.
- A direct message is for a blocking ASK only, and every ASK is also
  appended to the board with the file:line it concerns. Answer an ASK sent to
  you in one message and post the ANSWER on the board. Never message to
  report progress, never poll for replies; keep working and check the board
  before your final report.
