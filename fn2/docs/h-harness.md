# fn2 layer H: the surface test harness (present state)

H is the behavioural and property-based suite over fn's whole surface: nine families
(nntp, consumer, operator, web, peering, bp, tls_auth, config_limits, store_ops), each in
the forms of RELEASE-PLAN §2.2: E examples (the 120 carried fn1 natives and conformance
fixtures), S stateful property tests against a reference model, F fuzzing, H history
checking, and R published performance rows. It runs against fn1, which is the evidence for
what the models say, and against fn2 as layers D and E serve. The record of how each piece
was built, quest by quest, is this file's git history up to 27978259c.

## Where things are

| piece | path |
|---|---|
| Node adapter (one interface, fn1 and fn2 backends) | `fn2/tests/harness/node.py`, `shim.py`, `run_natives.py`, `inventory.py`, `judgments/` |
| reference models | `fn2/tests/model/` (`nntp_model.py` is H2's NNTP model; one model per family; `differential.py` is the seeded wire differential; `adjudications.json` is the wire ledger) |
| history checkers | `fn2/tests/history/` (consumer, durable acceptance, convergence; `from_observe` adapts native observation logs) |
| surface suite and runner | `fn2/tests/surface/` (`families.json` is the manifest; `run_surface.py`; one package per family; the drivers; `README.md` has the driver table) |
| fn2 session carriers | `sim_target.py` (SimTarget, NativeTarget); D's `fn2_sim_session.py`; A's `fn2_native_session.py` |
| nightlies | `fn2/tests/harness/hbox_nightly.sh` (fn1, hbox), `fn2/tests/harness/laptop_nightly.sh` (fn2, the Mac) |
| release-gate matrix | `fn2/docs/release-gates.md` |

Unit acceptance runs on the laptop, about 90 s, 412 tests: `build/h-venv/bin/python -m unittest`
over the module list in the H continuation. The fn1 node runs on hbox only.

## Targets

`run_surface --target T --family F [--box laptop|hbox] --out DIR` (or `FN2_SURFACE_TARGET`).
`surface.TARGETS` maps each target to a Node backend:

| target | backend | what answers |
|---|---|---|
| `fn1` | fn1 | fn1's image set on hbox (`/tank/fn/images/keyed/c14e9e8e...`, TREE_SHA d377d4559): every family |
| `fn2` | fn2 | S forms named in `serves_sim.fn2` run under layer D's simulator session (`FN2_SURFACE_SIM_<FAMILY>`, SimTarget); the other forms follow `serves.fn2` (empty: a named not-yet-serving skip) |
| `fn2-native` | fn2 | S forms named in `serves_native.fn2-native` run on a loopback socket through A's session hook (`FN2_SURFACE_NATIVE_<FAMILY>`, NativeTarget); the families in `serves.fn2-native` (nntp) run their E, F and H forms through Fn2Backend's served node |

**The session carriers.** Both carriers speak one API: `open(peer) -> (id, greeting)`,
`send(id, octets, chunks) -> (reply, closed)` at quiescence for that connection,
`close(id)`, and `stop() -> {id: WIRE verdict}`. Every open is one connection incarnation
with its own id. SimTarget fails a case that a WIRE verdict refused, and also a case with
a connection that never got a verdict. Evidence records `wire` as opened / distinct ids /
judged / ok / refused / unjudged. The native hook folds ENVELOPE's verdict over the
boundary trace into every connection's verdict.

**The nntp S form against fn2** (`nntp/sim_nntp.py`) sends every command in a random
two-chunk cut. A served verb (`fn2_conn_interim.json` "served_verbs", plus STARTTLS) is
judged by NntpModel under D3's profile, `D3_POLICY`: posting off, no TLS, no credentials,
no SASL mechanism, and no AUTHINFO label until E2. An interim verb must answer the table's
code and is counted as OWED with its quest. D regenerates the table, and the S form reads it.

**Fn2Backend.** `start` runs the served node: `tools/acl2 < fn2/tests/native-serve.lsp`
in a new session, with `FN2_LISTENER_PORT` set to the fixture's port and
`FN2_LISTENER_ADDRESS` to 127.0.0.1. Each start writes a PID file, `<node root>/fn2-node-N.pid`,
naming the session leader. `start` returns at `LISTENING <port>`, which must equal the
configured port. `Fn2Process` signals the process group, because tools/acl2 is a wrapper,
so fn1's `stop` gets `STOPPED <reason>` and exit 0. The served node reads only the
listener. `start` therefore names, instead of ignoring, any fn.toml key outside
store.path, listener.host/port and control.path, a verb other than `run`, a death cut, an
implicit-TLS listener, a missing plain listener, and any host other than 127.0.0.1. Every
other execution entry (`init`, `operator`, `store`, `invoke`, `post`, `kill_at`, ...)
raises fn1's `NodeDead` with the requirement, prefixed `node dead: fn2 layer D not yet
serving`. Any other image path runs the placeholder host
(`build/fn2-host-placeholder/fn`), which refuses every verb by name on stderr.

**Owed is named, never red.** Against an fn2 target, a native or fixture outcome that names
a host contract the served node does not provide counts as owed. That is either the
adapter's NodeDead requirement or the placeholder's refusal. Such a test is a skip listing
the requirements, and the requirements go into its `owed_host` evidence. Any other outcome
is judged as it is on fn1. Exit codes: 1 for any failure, or for a served family that
executed nothing; 3 when anything selected is NOT RUN for a reason that is not an
inventoried retirement or an `intended-skips.json` entry; 0 otherwise.

## fn2 today

The last laptop nightly's line is in `build/h8/nightly/LATEST.txt` (below). At dev b1ccb0444
(the cursor, D6 1/n, with the interim table regenerated), 1,000 examples × 50 steps:

| target | form | result |
|---|---|---|
| both | served surface | 14 verbs: CAPABILITIES HELP QUIT MODE DATE AUTHINFO XREDEEM, and the cursor's GROUP LISTGROUP NEXT LAST STAT OVER XOVER. 16 interim rows left: D6 10, D5 3, D7 1, E2 1, E4 1 |
| `fn2` | S | 20,723 served, 0 disagreements, 9,777 interim (POST 811 for D5; 8,966 for D6), WIRE 18,837 opened = judged ok |
| `fn2-native` | S | the same counts, WIRE and ENVELOPE ok on all 18,837 connections |
| `fn2-native` | E | 0 failures. The natives are owed host contracts (`operator CONFIG init` with groups, `store STORE init`, the FNCT control socket, the developer `model` and `store` verbs). There are also 3 intended skips (hbox fixtures), 1 opt-in, and the rfc3977 fixture (owed at its setup's `init`). |
| `fn2-native` | F | named skip: the differential's owner is fn1's fuzz Node with groups and a login |
| `fn2-native` | H | named skip: no nntp operations observed |

**What the S form does not reach yet: the cursor's own replies.** Both sessions run a profile
with no read rows, so the node serves no archive. A well-formed GROUP, LISTGROUP, STAT, OVER or
XOVER answers 503, and NEXT and LAST answer 412 (`*fn2-answer-unread*`). The model states this
as policy `archive` false in `D3_POLICY`. The cursor's 211, 223, 224 and 42x replies get judged
once a session profile has read rows and a published group. `D3_POLICY` then sets `archive` true
and the model's groups to that group. Likewise, the E rows that need groups turn live when the
served node takes groups at `init`.

## The laptop nightly (fn2; cron 03:30, `fn2/tests/harness/laptop_nightly.sh`)

`30 3 * * * /bin/sh /Users/ember/dev/fn/fn2/tests/harness/laptop_nightly.sh` in ember's crontab
runs this sequence:
1. It re-execs as a session leader and writes `build/h8/nightly/running.pid` (stop: `kill -- -$(cat ...)`).
2. It refuses under 60 GiB free, or while a run is live.
3. It fast-forwards the worktree `build/lanes/h-nightly` to origin/dev, and refuses if that worktree has local changes.
4. It certifies tests/conn-unit, sim/echo, sim/check-wire and sim/check-envelope there, teeing the log to `cert.log`.
5. It runs `--target fn2 --family nntp` and `--target fn2-native --family nntp`, whole and in parallel, at 1,000 × 50, with the rfc3977 fixture hook exported.
6. It writes `build/h8/nightly/<date>-<sha>/` with `table.md` (every test's outcome per target), `summary.txt` and `sim/` `native/` (the surface.json of each target).

The summary is one line: served / interim by quest / WIRE opened-judged-unjudged-refused /
disagreements per target, then the NOT RUN rows grouped by owner
(`fn2.tests.surface.nightly_nntp`). It is copied to `build/h8/nightly/LATEST.txt` for main's
morning read. A certify red writes `CERTIFY RED` there instead. Cron does not run while the
Mac sleeps, so a missed night shows as an old date in LATEST.txt.

## The hbox nightly (fn1; `fn2/tests/harness/hbox_nightly.sh`)

`cd TREE && SWARM_MEM_MAX=64G setsid nohup swarm-build sh fn2/tests/harness/hbox_nightly.sh OUT > OUT.log
2>&1 < /dev/null &`. TREE is an extracted tree of the commit under test, and OUT a fresh directory. The
script refuses an existing OUT, under 60 GiB free, and a memory ceiling under 32 GiB. It writes
`OUT/nightly.pid`, links the image set into `TREE/build`, and exports the production and developer images
with their identities, the pinned OpenSSL wrapper, the durable tmp and the opt-ins (`FN2_NIGHTLY_OPT_INS`,
default `FN_RUN_SLOW=1 FN_RUN_RELOCATION_E2E=1`). It then runs `run_surface --box hbox` under the wall cap
(`FN2_NIGHTLY_HOURS`, default 8) and renders `OUT/nightly.md` against `fn2/tests/surface/known-fn1.json`. An
unmatched non-ok row prints `unclassified`. The last nightly (2026-10-30, tree e495a7b55, 22,086 s) has
every S and F form passing against fn1. Its 11 non-ok rows are 8 known fn1 reds, 2 unprovisioned rows, and
the web S fix (since rerun PASS). The report is `build/coordinator/fn2/nightly/2026-10-30.md`. fn1's
connection capacity follows the launch's cgroup ceiling, so always launch at 64G.

## The adapter

`shim.PATCH_POINTS` declares every name the adapter replaces on the real `tests.native_harness`
module, per backend. For fn1 that is `Node` and `Client`. For fn2 it is those plus
`native_image`, `executable`, `requires`, `run`, `start`, `start_filed` and
`installed_launcher`. `shim.install(backend)` sets them and `uninstall()` restores them. The
natives are never edited. A green fn1 run through the shim is the evidence that the adapter
preserves behaviour: H1's acceptance found 794 tests, every non-ok test identical run directly.
`NodeInterface` is the structural protocol: start, stop, config, socket, control, kill_at and
observe. Under fn2, `native_image` resolves every image variable to `FN2_HOST` (default
`fn2/host/fn`, or the placeholder). fn1's `[resources] cold_*` keys are written as
`[profile]`. `FN2_OBSERVE_DIR` turns on JSONL observation per test (nanosecond times,
command and reply octets, process snapshots), and without it observation does nothing.
Each native module runs in a fresh session with a PID file, and a timeout kills only that
group. Retired methods (`inventory.load()`, judgments under `fn2/tests/harness/judgments/`) are
reported as intended skips. Every fn2 non-ok test is classified as `named-node-dead`,
`named-placeholder`, `retired`, `intended-skip` or `other`.

## Models, ledgers and adjudications

- **NNTP (H2, `nntp_model.py`).** The model is built from specs/nntp.md and RFC 3977/4643/6048,
  and covers commands, codes, framing, group and article numbers, auth state, POST/IHAVE/TAKETHIS
  judgement, and D3's profile. The seeded wire differential (`differential.py`) runs fn1's
  generator under the model. Its rows are judged against `adjudications.json` (match by exact
  bytes, or by a predicate in `surface/adjudication_predicates.py`). A row is recorded as
  fn1-bug, model-bug (fixed with its spec line), driver-bug or spec-ambiguity. Against fn2,
  only spec-ambiguity rows are recorded.
- **Family models.** consumer, limits, operator, store_ops, web, peering and bp each have a fake
  and mutation controls. Each model's SPEC-MAP lists its spec lines and its provisional tags.
- **History (H3).** The consumer checks are at-least-once, forward-only durable ack,
  redelivery before ack and no lost wake. Durable acceptance under crash cuts is checked by
  `durable`. Convergence V1-V4 is checked by `convergence`. Nine injected anomaly kinds are
  caught at 100/100. fn1's consumer, peering and bp logs show 0 anomalies.

### The fn1-bug ledger (each row backed by a recorded fn1 reply)

| row | family | what fn1 does against the spec | recorded in |
|---|---|---|---|
| A01 | operator, store_ops | a non-ASCII argument gets a host usage error with no ARGV-MALFORMED tag (specs/native-admin.md:12-15) | `argv_fuzz.ADJUDICATIONS` |
| H7-03, H2d | nntp, peering | TAKETHIS answered 436 closing, and 436 without the Message-ID | `model/adjudications.json` |
| H7-07 | tls_auth | AUTHINFO PASS after a pending XREDEEM CODE NAME gets 481 where RFC 4643 2.3.2 says 482 | `model/adjudications.json` |
| L01, L02, L04 | config_limits | live policy refusals (L03, L05, L06 are spec-ambiguity) | `limits_model.py` ADJUDICATIONS |
| O01 | operator | `group retire` is accepted, but the wire keeps serving the group | `operator_model.py` ADJUDICATIONS |
| W01 | web, nntp (outside the S profile) | an access change on an open connection: LIST ACTIVE live, POST pinned after GROUP | `h-quests/w01-micro.py` |
| P01 | peering | a transferred article is fed by its Newsgroups names, not its local memberships | `peering_model.py` ADJUDICATIONS |
| B01 | bp | `carry pause *` is a separate wildcard hold | `bp_model.py` ADJUDICATIONS |
| C01 | consumer | a repeated unregister answers `scope` | `consumer_model.py` |

Known fn1 reds that are not the harness's: agent_wait, control, bounds_join, conformance,
decoded_custody, live_reconfiguration, mux (×2), owner (×2), public_limits (×2),
served_crash_model, store_identity, visibility_join, status_live_posts (timeout). They are
listed in `fn2/tests/surface/known-fn1.json`.

## Spec pins read by layer D (adjudications both sides apply)

| pin | spec line | the one answer | where each side reads it |
|---|---|---|---|
| P-UTF8-WS (H6, 2026-10-29) | specs/nntp.md:513-518 (NNT-003: "drain rejected input to a safe protocol boundary or close the connection"); RFC 3977 §3.1 | A command line that is not UTF-8 is **malformed** whatever else is wrong with it: the line is decoded before it has words, so surrounding whitespace on a bad-UTF-8 line does not make it a plain syntax error. The answer is `501`, then the connection closes. A valid-UTF-8 line with leading or trailing whitespace stays a plain `501` with the connection kept. | H: `fn2/tests/model/nntp_model.py` `_dispatch` (decode before the whitespace check), test `test_invalid_utf8_is_malformed_before_whitespace`. D: the grammar's `:malformed` class; `fn2/tests/grammar-fuzz-oracle.py`'s whitespace-order exception now counts 0 on the 4,416 cases (13,501 lines, 0 disagreements) and can be deleted. |

| P-FNCU-HEADER (H7) | specs/consumer-progress.md:45-50 (`fncu`, version 1; "an unknown version is refused") | A cursor whose first five octets are anything but `fncu` 01 is refused as `version`. That includes an empty file, a short file and another magic. | H: `fn2/tests/surface/fncu_fuzz.py`. fn1: books/consumer-position.lisp `fn-cp-cursor-decode`. |
| P-FNCU-EPOCH (H7) | specs/consumer-progress.md:45-50 (four u32 fields, no positivity stated) | The registration epoch is positive, so an epoch of 0 is refused as `grammar`. The query version, view version and position may be 0. | H: `fncu_fuzz.py`. fn1: `fn-cp-cursorp` (`posp` of the epoch). |

| P-SASL-LINE (H7c) | specs/nntp.md:513-518 (a malformed line) and 1724-1725 (504 for a response that is not canonical base64) | A SASL response is a line before it is base64. Past 512 octets, or carrying a bare CR or LF, it is malformed, so 501, and the exchange ends. Any other line that is not canonical base64 is 504, including an empty line and one with control octets. fn1 agrees on all five shapes the fuzz met. | H: nntp_model `_sasl_response`, test `test_sasl_response_is_a_line_before_it_is_base64`. |
| P-DUP-FIELD (H12, 2026-10-30) | specs/nntp.md §POST (a definite 441 refusal; no wording for a duplicated field) | A POST whose header repeats From, Subject, Newsgroups, Message-ID, Date or Path is a definite `441`. The wording is the catalogue's: `441 posting failed; <Field> appears more than once`. The model accepts it beside its older words (duplicat, malformed, field, Path). The model moved, and D's conn-answer stays as it is. Found by the evidence seat's upload contract (dev 424f3f9ef): fixture `from-duplicate`, which was listed in `*fn2-q1c-upload-open*`. | H: nntp_model's duplicate-field reason, test `test_duplicate_field_reason_is_the_catalogue_wording`. fn1: books/protocol-table.lisp. D: books/nntp-grammar.lisp `:refused-from-duplicate` and its siblings. |

The model still accepts a malformed line's 501 *without* a close (EOF optional, the fn1 tolerance
`test_malformed_eof_is_optional_and_requires_observed_eof` records); for fn2 the pin is 501 and close, which is what D answers.



## Open precedence questions handed to layer D (recommendations, not rulings)

- **A13** (a malformed unknown keyword; fn1 answers 501): a token that fails RFC 3977 §9.8's keyword
  grammar gets 501, and a well-formed unrecognised keyword gets 500.
- **A15** (malformed UTF-8 TAKETHIS on a reader connection; fn1 answers 502): framing and UTF-8
  validation come before authorisation, so the reply is 501, and a well-formed transit command
  gets 502.
- **A16** (an empty Path plus an unnamed header): malformed header framing takes the generic syntax
  refusal, and a valid block with a bad Path gets the named Path refusal.
- **A14** (a malformed TAKETHIS answered by silence) is evidence, not precedence:
  `differential --takethis-probe` records whether the server was waiting for the body.

## Drivers (the table with hooks is `fn2/tests/surface/README.md`)

- **E fixtures** `fixtures:fixture`: the RFC 3977 transcripts replayed live with their setup built,
  consumer-position vectors, the bp golden bundles (re-authored octet-equal), and the SCRAM RFC 7677
  vector. web and wire-grammar are named skips until E3 and E5 export them.
- **F** `fuzz:fuzz`: tls_auth and peering run the differential with `--focus auth|feed`; operator and
  store_ops run `argv_fuzz`; config_limits runs `config_fuzz`; web runs `http_fuzz`; consumer runs
  `fncu_fuzz --with-fnct`; bp runs `bp_fuzz --with-tcpcl`. nntp F is the differential itself.
  Each driver runs alone with `--target fake --plant P` as its mutation control.
- **H** `history_drivers:history` over the natives' own observation logs.
- **R** `perf:perf`: tools/load cells mapped by `perf.ROWS`, with the unmeasured rows named. R is
  published and never a gate.

Owed: the W7 perf adapter, perf rows with no tools/load cell (consumer wake, web p99, W3-W5),
bp bundle convergence with the F8 scenario, and an fn2 owner for the nntp differential.

## Pitfalls that bind

- fn1 refuses a control socket path past 103 octets, so the differential puts each node in a short
  scratch directory.
- The differential's reader sessions bind source 127.0.0.2, which is absent on macOS.
- `fn --fn config check` answers an oversize profile with a fault. Fuzz through `operator PATH show`.
- NntpModel's Conn copies policy at connect: set `stored_articles` before connecting.
- A running seat script is replaced by `mv`, never edited in place: sh reads scripts incrementally.
- `git worktree remove` deletes the worktree's git-ignored build/, so copy evidence out first.
