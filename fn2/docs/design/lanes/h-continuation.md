# fn2 layer H continuation (present state, rewritten whole; 2026-10-31, eighth seat, at CONVERGE)

Seat: the Opus owner of layer H, the surface test harness. The seat writes the code itself; Codex is a pair for bounded
pieces. The present-state doc is `fn2/docs/h-harness.md` (rewrite it whole, never append). Main is the coordinator
(SendMessage "main"). The flow is WORKFLOW-20261031: no per-commit gates, everything slow in one unattended nightly,
and READY per commit. The fleet is converged and stopped (ember, 2026-10-31, so Gemini can take a turn): no new
work until main restarts H.

## Where H stands
- **Last H commits, all pushed:** H19-H25 plus the nightly certify list (fe8127048 .. cda4d37ee).
  - The nntp S form reads `fn2_conn_interim.json` at run time. A verb that has left the table is judged by the model
    as served. The cursor's LIST forms (no keyword / ACTIVE / COUNTS / NEWSGROUPS, without a wildmat) are served
    where the carrier serves reading.
  - `sim_nntp.CARRIERS`: both carriers use the seeded store (fn2/tests/seeded-store.lsp, shared by sim-session,
    native-serve and native-session). local.test holds <a|b|c@example.invalid> numbered 1-3, each rebuilt as a
    120-octet, one-line article whose overview row equals the session's, with Xref `.invalid local.test:N`.
    local.empty holds none. Policy is D3_POLICY with archive on.
  - Model policy `archive` (default on). Off, a well-formed GROUP, LISTGROUP, STAT, OVER, XOVER, HDR or XPAT
    answers 503 and NEXT/LAST answer 412 (*fn2-answer-unread*).
  - LIST status is `n` when posting is off.
- **Interim table:** `fn2_conn_interim.json` is D's generated table (tools/acl2 < fn2/tests/conn-interim-export.lsp |
  python3 fn2/tests/conn-interim-json.py, after certifying books/conn-answer). At the cursor: 14 verbs served,
  16 interim rows (D6 10, D5 3, D7 1, E2 1, E4 1).
- **IN FLIGHT AT CONVERGE:** a hand run of the nightly at 48305081a (D's Xref fix). It is the first both-carriers run
  that judges the cursor over the seeded store. PID file: build/h8/nightly/running.pid. Output:
  build/h8/nightly/2026-10-31-48305081a/ and the line in build/h8/nightly/LATEST.txt. The seat READYs that line
  when it ends; the result is recorded under "Last line" below.
- **Last line:** see LATEST.txt. Before the Xref fix, the simulator carrier failed at the first OVER (8 fields, no
  Xref; D fixed it in 48305081a). The socket carrier was green at dc2651b2a (no-archive then).
- **Owed to H:**
  - an fn2 owner for the nntp differential (F);
  - Fn2Backend.init with groups, when the served node takes groups at init (E rows);
  - E's sim-layer-e invocation for "M2 cuts n/12" (H_NIGHTLY_M2 writes OUT/m2.json);
  - the W7 perf adapter and perf rows with no tools/load cell;
  - bp bundle convergence with F8.

## The nightlies
- **The Mac (H's row):** crontab `30 3 * * * /bin/sh /Users/ember/dev/fn/fn2/tests/harness/laptop_nightly.sh`.
  - The worktree is build/lanes/h-nightly, fast-forwarded to origin/dev each night.
  - It certifies tests/conn-unit, sim/echo, sim/check-wire, sim/check-envelope and books/owed-cursor.
  - It runs `--target fn2` and `--target fn2-native` for the nntp family, whole and in parallel, at 1,000 x 50.
  - It writes build/h8/nightly/<date>-<sha>/ (table.md, summary.txt, sim/, native/, cert.log) and LATEST.txt.
  - PID file: build/h8/nightly/running.pid (stop: kill -- -<pid>). It refuses under 60 GiB free or while a run is live.
  - The line reads: M2 cuts n/12 (0/12 until H_NIGHTLY_M2), then the served surface, then per target served /
    interim by quest / WIRE opened-judged-unjudged-refused / disagreements, then NOT RUN by owner.
  - To run it by hand, detached: `nohup env -i HOME=$HOME USER=$USER /bin/sh fn2/tests/harness/laptop_nightly.sh
    > /dev/null 2>&1 < /dev/null &`. Under the fleet's load, a certify after a foundation move takes 40-60 min.
- **hbox (fn1):** fn2/tests/harness/hbox_nightly.sh. The recipe is in h-harness.md: SWARM_MEM_MAX=64G, image set
  c14e9e8e. The last run was 2026-10-30; every S and F form passes against fn1.
- **Triggers:**
  - A READY that flips verbs: confirm the nntp family on both carriers with one hand run.
  - Regenerate the interim table whenever *fn2-answer-interim* changes (D's job; H regenerates if D did not).

## Targets (details in h-harness.md)
- fn1 runs everything on hbox.
- fn2: S under the simulator (FN2_SURFACE_SIM_NNTP=fn2.tests.surface.fn2_sim_session:session).
- fn2-native: S on the socket (FN2_SURFACE_NATIVE_NNTP=fn2.tests.surface.fn2_native_session:session), and E/F/H
  through Fn2Backend's served node (tools/acl2 < fn2/tests/native-serve.lsp, a PID file per start, group signals).
  A native or fixture outcome that names a missing host contract is owed (a named skip), never red.

## Unit acceptance (laptop, about 90 s, 412+ OK)
`build/h-venv/bin/python -m unittest fn2.tests.harness.test_harness fn2.tests.history.test_history
fn2.tests.history.test_convergence fn2.tests.model.test_nntp_model fn2.tests.model.test_differential
fn2.tests.model.test_consumer_model fn2.tests.model.test_limits_model fn2.tests.model.test_operator_model
fn2.tests.model.test_store_ops_model fn2.tests.model.test_web_model fn2.tests.model.test_peering_model
fn2.tests.model.test_bp_model fn2.tests.surface.test_run_surface fn2.tests.surface.tls_auth.test_model_tls_auth_unit
fn2.tests.surface.test_adjudications fn2.tests.surface.test_live_evidence fn2.tests.surface.test_fixtures
fn2.tests.surface.test_perf fn2.tests.surface.test_argv_fuzz fn2.tests.surface.test_config_fuzz
fn2.tests.surface.test_http_fuzz fn2.tests.surface.test_codec_fuzz fn2.tests.surface.test_sim_target`

## Commit discipline
Shared tree /Users/ember/dev/fn on dev. Commit by path: `git commit --no-gpg-sign -F <msg> -- <paths>`, never stage
and never use -A, never stash. `python3 tools/secrets_check.py`, `git fetch origin dev`, merge if behind, push. Quest
messages live in build/coordinator/fn2/lanes/h-quests/<Q>.commitmsg. When another seat has an unpushed local commit
under the tree, do not merge over it; use a detached worktree at origin/dev. Every changed nntp_model.py moves the
evidence seat's upload-model pin (tests/evidence/upload-model.lisp); tell main.

## fn1-bug ledger (S forms and differential; every row is backed by a recorded fn1 reply)
| row | family | what fn1 does vs the spec | recorded in |
|---|---|---|---|
| A01 | operator, store_ops | a non-ASCII argument: host usage error, no ARGV-MALFORMED tag (specs/native-admin.md:12-15) | argv_fuzz.ADJUDICATIONS; h-harness.md H7b |
| H7-03 | peering, nntp | TAKETHIS article answered 436 closing (H2d class, widened by reply) | model/adjudications.json |
| H7-07 | tls_auth | AUTHINFO PASS after a pending XREDEEM CODE NAME answered 481 (counted) where RFC 4643 2.3.2 says 482 | model/adjudications.json |
| L01, L02, L04 | config_limits | live policy refusal rows (HY's 152-pair probe); L03/L05/L06 are spec-ambiguity | fn2/tests/model/limits_model.py ADJUDICATIONS; h-quests/hy-policy-pairs-fn1.json; fn2/docs/h-harness.md (HY) |
| O01 | operator | `group retire` accepted but the wire keeps serving the group (effect row) | operator_model.py ADJUDICATIONS; h-harness.md "HZ"; wp2-operator.json, hz-micro.py |
| W01 | web/nntp (outside the S profile) | access change on an open connection: LIST ACTIVE live, POST still pinned after GROUP | h-harness.md "HZ3"; h-quests/w01-micro.py |
| P01 | peering | a transferred article fed by its Newsgroups names, not its local memberships (effect row) | peering_model.py ADJUDICATIONS; h-harness.md "HZ4"; wp2-peering.json |
| B01 | bp | `carry pause *` is a separate wildcard hold: listed paused, `resume WORK` refuses not-paused (effect row) | bp_model.py ADJUDICATIONS; h-harness.md "HZ4"; h-quests/b01-micro.py |
| C01 | consumer | repeated unregister `scope` (adjudicated, HT) | fn2/tests/model/consumer_model.py (adjudication table) |
| H2d TAKETHIS | nntp | TAKETHIS 436 without the Message-ID (13 rows) | fn2/tests/model/adjudications.json, DIFFERENCES.md |
| observed, not adjudicated | nntp | a transit IHAVE with two Path fields accepted (235); nntp_model refuses duplicates | h-harness.md "HZ4" (for the nntp differential) |

## Pitfalls hit
- A session API keyed by slot id judges only the last incarnation: every carrier must give each open its own id
  (SimTarget enforces opened == judged since H11).
- macOS has no `setsid`: launch detached laptop runs as `nohup python3 -c 'import os,sys; os.setsid(); os.execvp(sys.argv[1], sys.argv[1:])' CMD ... & echo $! > X.pid`, then check `ps -o pid=,pgid= -p $(cat X.pid)` agree.
- build/ is git-ignored: only fn2/ files are committed; continuation, quest files and dry-run logs live on the laptop.
- The hbox nightly output dir is `/tank/fn/scratch/fn2-h-harness/nightly-YYYYMMDD` (no dashes); surface.json under it.
- `bp receive` without a STORE (with an enrolled bp-boundary for the peer at the receive port) refuses every inbound bundle at the receive boundary; accepted bundles journal to lifecycle/*.fnb (the log's `BP accepted ... path=`), not receive-evidence/*.adu.
- fn1 refuses a control socket path past 103 octets (CONTROL-PATH-TOO-LONG): a deep --out kills every differential node (fixed: short scratch dir in differential.owner).
- `fn --fn config check` answers an oversize profile with a fault; the operator verbs say usage: fuzz through `operator PATH show`.
- Never put a running seat script under edit in place: replace by `mv` of a new file (sh reads scripts incrementally).
- A fuzz value list must not contain flag names (`--off`, `--queue`): flag-shaped values ask a question no spec decides.
- fn1's connection capacity follows the launch's cgroup ceiling (limit = ceiling - ~134 MB): a swarm-build under 32 GiB shrinks C' below 31 and natives holding many connections meet a correct 400. Launch nightlies at 64G.
- Link the WHOLE image set (fn-host* incl. *.world-deps), never a fixed list.
- surface.json at the hbox cadence is huge (1.7 GB for H5b): read it on hbox only.
- bp: enqueue every work before any request (an enqueue needs no pending journal transaction and a fresh txid).
- The argv preflight's tagged line has subject `request` (`usage operator request ARGV-MALFORMED`).
- `OWNER-OPEN ... reason=absent` precedes every store-opening reply: take `reason=` from the tagged/`store:` line only (bp_reason).
- Shared index: anything staged can be swept into another seat's bare commit. Commit `-- <paths>`, never stage.
- NntpModel Conn copies policy/credentials at connect: set policy['stored_articles'][id] before connecting
  (or on the conn), and mark temporary model conns quit (31-connection model limit).
- Web face: fnr_pre persists while the browser presents a live one (HEAD does not invalidate it); CSRF is on every
  signed-in page, absent until one is read after sign-in.
- `git worktree remove` deletes the worktree's git-ignored build/ (venv, evidence copies): copy evidence out first.
- fn1 CLI replies: the tagged line can follow `Password: Confirm password: ` on the same line; `store` sub-verbs
  inspect/import (and the direct `fn store S ...` verbs) print no tagged line; reasons appear as `reason=X`.
- The direct `fn store S import --FIELD N` ignores the override; use `operator CONFIG store import`.
- hbox: venv has hypothesis but no cryptography, /usr/bin/python3 the reverse (both 3.12.7): run /usr/bin/python3 with
  PYTHONPATH=$B/venv/lib/python3.12/site-packages.
- The inventory JSON is now a build output: `inventory.load()` (or `python3 -m fn2.tests.harness.inventory --out build/natives`),
  never `fn2/tests/harness/natives-inventory.json` (h1b-fn1.sh's MODS line reads the old path: use inventory.load()).
- The hbox venv has no system site-packages: natives needing `cryptography` must run with /usr/bin/python3.
- Codex content flag on fuzzing: rephrase as conformance testing of our own server; resume by session id.
- zsh: `echo =====` is a glob error; use `---`.
- `native_env.py plan` without `--allow-skips` refuses opt-in-gated modules (exit 2, empty output).
- Parallel Codex sessions share build/REPORT.md unless each prompt names its own file.
- The differential's reader sessions bind source 127.0.0.2: absent on macOS (EADDRNOTAVAIL), present on Linux.
- Codex's sandbox denies loopback bind: tests needing TCP run on the seat (laptop or hbox), never trusted from Codex alone.
- Launch on hbox without hanging: `ssh hbox 'cd DIR && (SWARM_MEM_MAX=..G setsid nohup swarm-build sh X.sh > X.log 2>&1 < /dev/null & echo $! > X.pid)'`.
- Old note: plain nohup ssh launches of swarm-build hang until the job ends: launch with run_in_background, poll with `until ssh ... grep -q DONE`.
