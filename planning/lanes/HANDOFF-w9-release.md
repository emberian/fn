# w9/release: the bookkeeping and the deployment that make a v0 claim checkable

Branch `w9/release` from `dev` `52eb0db`, worktree `build/lanes/w9-release`.

## What landed

1. **`tools/verdict.py`** -- one command for one commit's whole verdict. It
   ships the commit to a farm box, runs the box gate over it (`make certify`,
   `python3 -m unittest discover -s tests`, `sh tools/gate_publish.sh`)
   detached so a dropped ssh cannot take the gate with it, then runs
   `tools/deploy_gate.py`, `tools/twonode_gate.py`, `tools/inn_lab.py` (hbox)
   and `tools/scale_gate.py --reuse` against that same commit, and writes
   `planning/evidence/verdict-<rev>-<date>.md`: a fiber per row, the certify
   roots that failed with the deputy that owns them, the Python suite counts,
   and one sentence saying what the tree can claim.
   - **The lock.** Every host the run touches gets an atomic `mkdir` beside
     that box's gate directories (`$HOME/fn-gates/.verdict.lock`, or
     `/tank/fn/gates/.verdict.lock` on hbox), released in a `finally`. A held
     lock is reported with its age and its owner file and never stolen;
     `--force-unlock` is the deliberate act.
   - **A fiber that did not run is a row saying so** and a named limit inside
     the claim sentence, never an absence.
   - Owners come from `planning/deputies/CLUSTERS.md`, matched by book-name
     prefix in the `OWNERS` table; a root matching no row reads `unassigned`.

2. **`tools/live_service.py`** -- fn installed as a running service on a box,
   and the record of how. `install`, `status`, `start`, `stop`. It ships the
   tree to `~/fn-live/fn`, installs certificates from the box's own cache
   (it never certifies), runs `fn init` with the groups, writes a peer record
   naming the other box, installs `packaging/fn.service` relocated under
   `$HOME` with the `User=`/`Group=`/`Protect*` directives a user manager
   cannot apply removed, starts it and greets it over a socket.
   - Where there is no user systemd it writes `~/fn-live/run.sh`, a `setsid`
     wrapper, and the evidence says in as many words that this is **not** a
     supervised service.
   - It tries the **owner** (`fn run`) first and falls back to
     `tools/run_reader.py` -- the same second choice `tools/deploy_gate.py`
     makes -- recording why in the evidence.

3. **A packaging defect, found by running the packaged unit.**
   `packaging/fn.service` had `ExecStart=... bin/fn run --config <path>`.
   `--config` is a top-level option; after the verb argparse rejects it, the
   process exits 2, and under `Restart=on-failure` with no limit that is a
   loop -- **157 restarts in fifteen minutes on persvati**. Fixed in the unit,
   in `packaging/net.fn.plist` (same wrong order) and in the `fn init` line of
   `docs/operator.md`, and the unit now carries `StartLimitIntervalSec=60` /
   `StartLimitBurst=5` so a service that cannot start stops and says so.

4. **Six fiber evidence records**, `planning/evidence/fiber-<wave>-2026-09-20.md`,
   one per v0 wave: what is proved, what is only tested, the pessimistic
   numbers with the scope they cover, what is open, every number cited to the
   file it came from.

5. **`planning/milestones.md`**: a v0 checklist with a row per item, its
   status (`done` / `partial` / `open` / `blocked`) and its evidence link, and
   a current task rewritten around what running the service proved.

## What the next lane should know

- **`books/owner` is still the blocker, and now it is visible from outside.**
  `fn run` cannot start on either box: ACL2 refuses
  `(include-book "books/owner")`, so the live unit serves the reader path.
  Everything about concurrency, POST durability under load and the v0.1 gate
  condition waits on that one root.
- **A connection can post exactly once.** Diagnosed on the board
  (w5/owner-followups): one clock observation pinned per connection at accept
  means one durable injected identity per connection. Whoever owns the clock
  seam decides: re-observe per submission, or make the injected identity not
  depend on the observation alone.
- **Two live nodes are peers on paper only.** `fn run` refuses a non-loopback
  `[listener] host`, so the peer records `tools/live_service.py` writes name
  addresses neither node can reach. A `--host` argument on the owner, or a
  documented tunnel, is what turns the records into a path.
- **`fn peer add` does not exist.** `bin/fn`'s verbs are init, run, post,
  group, status, recover, anchor; `tools/run_store.py` has no `peer` verb.
  `tools/live_service.py` probes for both and calls the CLI the moment one
  lands; until then it writes the same reviewable stub
  `tools/twonode_gate.py` writes, at `~/fn-live/peers/<name>.peer`, with the
  transport pointing at the peer box rather than at loopback.
- **Do not run a second gate on a box while a verdict run holds its lock.**
  The lock exists because a gate is certified once and published once; a
  second `make certify` publishing into the same cache while the first is
  mid-publish gives the second a cache it cannot vouch for. `tools/farm.py`
  runs do not take the lock -- they are `--closure` runs into their own remote
  root, not gates -- so they can and do run alongside; that is deliberate.
- **The verdict evidence file is the tree's front page.** Re-run
  `python3 tools/verdict.py <commit> --host persvati` after a convergence
  merge, commit the record, and let the registries follow it rather than the
  other way round.

## Operator commands

`docs/operator.md` carries them. In short, for one box:

    python3 tools/live_service.py install <commit> --host persvati \
        --node fnA --port 11190 --host hbox --node fnB --port 11190
    python3 tools/live_service.py status --host persvati
    ssh -N -L 11190:127.0.0.1:11190 persvati      # from the laptop
    python3.12 -c "import nntplib; print(nntplib.NNTP('127.0.0.1', 11190).getwelcome())"
