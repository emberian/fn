# operator-walk: one installed `fn` from nothing to a recovered node (PRF-130, HST-008, SCN-076, PKT-264)

Lane `lane/operator-walk` from dev 7284cca8, 2026-09-26. Brief:
`build/coordinator/queue/w2-operator-walk.txt` (continuation of
operator-health, PRF-112). Commits: ca3d3919, 05f176aa, cbd3a994, a828ac47
and the record commit.

## What now works

An operator installs the production image with `packaging/install-native.sh`
and uses only `PREFIX/bin/fn` (which is `packaging/fn`). On two hbox scratch
nodes the walk went from no configuration to a recovered, serving node in 45
steps, every exit code as the page says (table below). Before this lane four
of those steps were defects; each is fixed on the path the operator takes:

| walk step | before (operator-health's record) | now | decided by |
|---|---|---|---|
| `status`/`health`/`run` before `init` | `fault ... missing store directory`, exit 4 | `refused operator status NO-STORE`, exit 6, after ACL2's line naming `init` | `fn-native-operator-store-outcome` over the `lstat` of the five store entries, before any open |
| `init --profile scale` under a mission | `usage operator init MISSION-FIXES-PROFILE`, nothing else | the same result line, after ACL2's line saying init takes GROUP words only and how to raise a bound | `fn-native-operator-result-hint`; `help init` says it too |
| a peer answering 501 to `MODE STREAM` | re-dialled with `MODE STREAM` at every backoff, indefinitely | `MODE STREAM` sent once in 40 s; the owner logs `refused feed peer=nostream stopped reason=mode-stream-refused (...)` and does not dial it again this run | `fn-fc-streaming-refusal-p`, `fn-fc-dial-allowedp` (books/feed-connection.lisp) |
| reading docs/operator.md | "Install the native production entry" .. "Stranded forwarding rows" twice, the second copy older | once (the newer copy kept; every line unique to the removed copy was superseded) | |

Found by this walk and fixed:
- Step 33: the new hint first said "raise it with `store upgrade-profile
  [scale|default]`"; on a small-community store `upgrade-profile scale` is
  refused `not-an-upgrade max-transactions` (the presets are smaller than a
  mission). The hint and the page now name field raises (`--FIELD N`), and
  step 34 raises one (0). Classification: implementation (my hint).
- A SIGKILLed owner leaves `control.sock`. The first harness waited on the
  file and asked `health` during the next owner's recovery: `fenced
  reason=store-held` (20) and `status` refused `store is already locked`
  (1). Both are the correct answers for that instant (a process holds the
  store and the socket does not answer); the harness now waits for the
  listener. Classification: harness. The page's fenced row does not yet say
  "an owner still starting"; PKT-264.

Also delivered:
- `store rollback-check --snapshot SNAPSHOT` (the upgrade rehearsal's
  rollback): ACL2 compares the two committed histories and prints the count
  and the sentence. On the walk's copy: `rollback snapshot loses
  transactions=2 snapshot-transactions=2 store-transactions=4` /
  `restoring this snapshot loses every transaction committed after it: 2,
  the articles accepted since it among them; the snapshot cannot give them
  back`; against the other node's store `refused snapshot-not-a-prefix` (1).
  docs/operator.md "Upgrade, and what a rollback loses" carries the sentence
  in bold and the two rollbacks side by side.
- `packaging/fn` is the installed entry: `packaging/fn-native` renamed (a
  link keeps the old name for its 19 callers); it locates the image and
  forwards every argument. Its header lists where each decision of the
  spike's bash wrapper (spike/mega f6d947d0, read, not merged) went; the
  wrapper's host-side decisions (mission table, doctor thresholds, awk
  TOML reads, the upgrade's format comparison, rotation, backup/restore,
  unit rendering) are ACL2 verbs or gone. `install-native.sh` installs it.

## Assurance chain

native entry `PREFIX/bin/fn` (packaging/fn, exec only) -> `fnn-command-operator`
(host/native/operator.lisp) -> `fn-native-operator-run` (plan) ->
`fnn-operator-dispatch-plan` calls `fnn-operator-store-outcome`, which
observes `fnn-operator-init-observed` (lstat on ACL2's marker names) and
calls `fn-native-operator-host-store-outcome` = `fn-native-operator-store-outcome`
-> a non-accepted outcome is printed by `fnn-operator-emit-result` (ACL2's
hint line, then the tagged line) with `fn-native-operator-exit-code` of the
same result. No relation is maintained across calls: each command observes
once and decides once (operator commands are not a served path).

Feed stop: `fnn-feed-reply-step` (host/native/feed-service.lisp) ->
`fn-owner-feed-reply-chunk` (host/owner-host.lisp) computes `fn-fc-step` and
`fn-fc-streaming-refusal-p` on the same state, records
`fn-fc-stopped-put` in the owner-process global `fn-owner-feed-stopped` and
ACL2's log line; `fnn-feed-dial-plan` reads `fn-owner-feed-has-queued` =
`fn-fc-dial-allowedp` over that table. The table is established empty at
start (unbound global = nil) and changed only by that put; it is not durable.

Snapshot loss: `fnn-command-rollback-snapshot` (host/native/io.lisp) observes
`(sequence . octet-length)` of each store's transaction files
(`fnn-transaction-files`, no lock, no replay) and prints
`fn-native-operator-snapshot-loss-report` of `fn-native-operator-snapshot-loss`.

## Theorems (PRF-130)

books/native-operator.lisp:
- `fn-native-operator-absent-store-is-refused` (keystone): an accepted plan
  whose native action opens a store (`fn-native-operator-result-needs-storep`)
  and an observation with no marker give status `:refused`, reason
  `:no-store`, exit code 6 and native action `:none`. Host line: 
  `fnn-operator-store-outcome` in host/native/operator.lisp.
- `fn-native-operator-store-outcome-passes-a-present-store`: with a marker
  observed, or a plan that needs no store, the plan is unchanged.
- `fn-native-operator-snapshot-loss-counts-the-suffix` (keystone): `:loses`
  exactly when the snapshot's history is a prefix of the store's, and the
  count is `len(store) - len(snapshot)`. Host line:
  `fnn-command-rollback-snapshot` in host/native/io.lisp.

books/feed-connection.lisp:
- `fn-fc-mode-stream-refusal-stops-the-dial` (keystone, rule-classes nil):
  from a state in the `:mode` phase, a complete line whose code is not 203
  gives a `:refused` step whose next phase is `:closed`, classified by
  `fn-fc-streaming-refusal-p`, and after `fn-fc-stopped-put peer
  :mode-stream-refused` the dial is not allowed for that peer whatever is
  queued. Host lines: `fn-owner-feed-reply-chunk`,
  `fn-owner-feed-has-queued` (host/owner-host.lisp).
- `fn-fc-dial-allowedp-of-put-other`: other peers keep their dial.

The existing grammar of `fn-fc-step` is unchanged (a non-203 MODE reply was
already `:refused`), so the feed-connection gate invariants are untouched.

Teeth:
- tests/acl2/native-operator-tests.lisp: the reachable witness is the plan
  `fn-native-operator-run` makes for `status` (and `health`, `run --once`)
  under the minimal configuration, with the host's empty observation: exit
  6, reason, action `:none`, a hint string. Hypothesis removal: `help` (needs
  no store) passes through with exit 0, plus a `must-fail` of the theorem
  without the needs-store hypothesis; `config.json` observed passes the
  status plan through with exit 0, plus a `must-fail` without the absent
  hypothesis; the conclusion's failure for an ordinary refusal (exit 1).
  Snapshot: `(:loses 3)`, `(:loses 0)`, a diverged and an ahead snapshot
  refused, the rendered report, the parse (absolute path only), and a
  `must-fail` of the count without the prefix hypothesis.
- tests/acl2/feed-connection-tests.lisp: 501 in the `:mode` phase is a
  refusal, closed, a streaming refusal, and the recorded peer is not dialled
  while another is. Hypothesis removal: a greeting refusal (not in `:mode`)
  is not a streaming refusal; 203 is `:ready`, not a refusal; a partial line
  is `:need-input`; nothing queued means no dial.
- tests/acl2/native-mission-tests.lisp: the mission usage carries a hint.

## Certification

| run | box | what | result | manifest |
|---|---|---|---|---|
| run-20260926T013700Z-b836 | persvati | affected-by native-health, native-operator, feed-connection at ca3d3919 | failed: `fn-fc-mode-stream-refusal-stops-the-dial` (the free `reason` could be nil; and the proof opened the wire reader) and its dependents | `manifests/certify-20260926T013741Z-3737875.json` |
| run-20260926T014043Z-cd40 | persvati | the same at 05f176aa | passed, 13 books: native-operator 5.5 s, peer-pull-session 5.4 s, feed-connection-invariants 2.3 s, native-operator-tests 2.3 s, feed-connection 1.7 s, native-mission 1.6 s | `manifests/certify-20260926T014104Z-3769637.json` |
| run-20260926T015120Z-7c1b | persvati | affected-by native-operator, feed-connection at a828ac47 (the hint text) | passed, 6 books: native-operator 5.5 s, native-operator-tests 2.3 s | `manifests/certify-20260926T015150Z-3864458.json` |

The keystone proofs were first admitted in persvati REPLs (proof_repl.py
against /home/ember/fn-gates/operator-walk-r1 with FN_CERT_CACHE=/home/ember/fn-certcache).
native-operator was 3.6 s before this lane; the two new keystones cost 1.4 s
until they stopped unfolding the native-action table (a local lemma for
`:none` of a refused result).

hbox: `tools/farm.py submit hbox` with the 160 default image roots refused
three times at its cache preflight with a truncated root list, while the
same `certs.py install-partial` run by hand over the pushed tree installed
364 of 369 and answered rc 0 (harness, not diagnosed further; PKT-264). The
image was therefore certified in place: /tank/fn/gates/operator-walk-r4
(the farm push of 05f176aa, then host/owner-host.lisp and
books/native-operator.lisp at a828ac47), `swarm-build tools/certify_books.py
--incremental --jobs 2 --timeout-seconds 300` over the image roots (5 books,
then native-operator), evidence `build/acl2/certify-20260926T014439Z-94204`
and `certify-20260926T015203Z-101909` on hbox; `proof_artifacts.py validate`
`result=loaded` (160 roots). These are hbox run directories, not farm
manifests.

The first image build (at 05f176aa) printed two ACL2 errors and still
produced an image: `fn-owner-feed-reply-chunk` nested `f-put-global` without
binding STATE, and everything after it in host/owner-host.lisp was then
undefined. Fixed at cbd3a994; the builds used for the walk report
`errors=0`. A build that prints `ACL2 Error` and exits 0 is a build-script
defect (PKT-264).

## Native (hbox, production image, installed)

Image: build/fn-host of a828ac47 in /tank/fn/gates/operator-walk-r4,
launcher af11e365a5798caafbbd86c151fdcf3b31c880141e5480d1255103b7ad96409d,
core d00e2740d11998f3dffb3f1cb61cde6b9fab961db092861704cbfc7aa0d87e96.
Installed by `packaging/install-native.sh` to
/tank/fn/scratch/operator-walk/prefix: bin/fn 61f6f464..., libexec/fn/fn-host
1dc48e08... (installed-path rewrite), core d00e2740....

Script: [`walk.sh`](operator-walk-2026-09-26/walk.sh), run under
`systemd-run --user --scope -p MemoryMax=24G`; owners as `systemd-run
--user -p MemoryMax=24G` units on loopback ports 31601 (a), 31602 (b),
31611 (the copy); the non-streaming peer
[`nostream_peer.py`](operator-walk-2026-09-26/nostream_peer.py) on 31603.
Every command's argv, stdout, stderr and exit code is in
[`native-out/`](operator-walk-2026-09-26/native-out/) (SHA256SUMS
677a02f37f030a69...; summary.txt 609934b13a32aff8..., written after the
sums; a-fn.log 0b9a0753dac2b758..., nostream.log 26a49101ab5d7e51...).

| # | step | exit |
|---|---|---|
| 0 | install into the prefix | 0 |
| 1-2 | `help`; `status` with no fn.toml | 0; 5 (configuration file is missing) |
| 3 | `mission small-community --port 31601` | 0 |
| 4-6 | `status`, `health`, `run --once` before init | 6, 6, 6 (`NO-STORE`, the init line first) |
| 7 | `init --profile scale` under the mission | 5, with the accepted form |
| 8-9 | `init`; `init` again | 0; 1 `STORE-EXISTS` |
| 10-13 | `show listener port`; `policy set path-identity`; `status`; `health` offline | 0; 0; 0; 19 (feed states unobserved) |
| 14-16 | node b: mission, init, path identity | 0, 0, 0 |
| 17-18 | enrol a login (`principal set-password walker --posting`, password on the terminal); `principal list` | 0 (`effective-at-next-start`); 0 |
| 19-21 | `peer add` a->b (streaming), b<-a; `peer list` | 0, 0, 0 |
| 22-25 | both started; `status` live; `post`; b's `status`; a's `health` live | 0; 0 (b logs `accepted peer`, a logs `accepted feed peer=b ... code=239`); 0; 0 |
| 26 | `post` of an article over the mission's 1 MiB bound | 1 (`refused operator post REFUSED`: no reason; PKT-264) |
| 27-29 | `peer add nostream` (streaming) to the 501 peer; `post`; 40 s; `health` | 0; 0 (MODE STREAM once, one stop line); 26 unavailable-peer |
| 30-31 | backup (stop, `cp -a`), start, two posts | 0, 0 |
| 32-34 | on a copy (paths rewritten, loopback 31611): `store needs-upgrade`; `upgrade-profile scale`; `upgrade-profile --max-history-octets 2199023255552` | 0 (`current`); 1 `not-an-upgrade max-transactions`; 0 |
| 35-37 | `rollback-check KEPT`; `upgrade-profile --history-marker required`; `rollback-check KEPT` | 0 `sound`; 0; 1 `history-marker-required-dropped` |
| 38-39 | `rollback-check --snapshot` the backup; the other node's store | 0 `loses transactions=2`; 1 `snapshot-not-a-prefix` |
| 40-41 | the snapshot restored over the copy's store; `recover`; `status` | 0; 0 |
| 42-45 | SIGKILL of a's owner (the control socket file stays); `status`; `recover`; start; `health`; `status` | 0 (offline route); 0; 26 (nostream still has work); 0 |

Classification of what differed from my expectations in the first pass: step
33 (implementation, my hint: fixed), steps 43-44 (harness: fixed). Nothing
was made green by changing an expected answer; 33's expectation changed
from 0 to 1 because `scale` is smaller than the mission (the refusal is
ACL2's `fn-profile-upgradep`), and the raise is a new step.

## Not done, and why

- **Item 5, the `bp-node health` verb (PRF-130 part 2, PKT-174's default):**
  not started; the budget went to the walk, the three fixes and the rollback
  count. PKT-174 is not retired. See PKT-264.
- **The peer's streaming refusal is not durable:** the stop lasts one owner
  process (a restart spends one `MODE STREAM` again), and there is no
  automatic IHAVE fallback on the same connection: the feed's streaming flag
  lives in its limits, copied from the peer record at open, and changing it
  is an owner feed-table transition with its own invariant obligations.
- **SCN-076 is not a tests/ module:** the walk is 45 steps with a 40 s wait
  and cannot meet test_budget.py's 20 s per test as one test.
- The upgrade rehearsal ran with one image (the candidate). The old image's
  refusal of a format-8 store was rehearsed by qual-bbf52159 and not
  repeated.

## PKT-264 (what this lane found and did not finish)

- Trace: operator walk 2026-09-26, the steps above.
- Open items, each with its default:
  1. `bp-node health JOURNAL ...` in the DTN image feeding `fn-nh-verdict`
     from the BP node's own report (stranded rows at the retry bound, no
     route, unavailable neighbour, receipt debt), store states unobserved;
     the theorem that the DTN verdict is `fn-nh-verdict` over that report.
     Default: PKT-174's (a BP feed-source in books/native-health.lisp,
     host/native/bp-node.lisp). Rejected: opening the DTN journal from the
     store image (two lock disciplines, a second journal owner).
  2. A refused control post names no reason (`refused operator post
     REFUSED`, and the owner log line has none). Default: the FNCT reply
     carries ACL2's refusal reason word, printed like the hint line.
     Affected: books/native-control.lisp, the control frame codec.
  3. A durable streaming refusal and an IHAVE fallback (RFC 4644 2.3).
     Default: a feed record of the peer's refusal replayed at open, the
     feed's limits opened with streaming off; rejected: rewriting the
     operator's peer record automatically (it is the operator's).
  4. `health` right after a restart following a crash says `fenced
     store-held` until the owner listens. Default: the page's fenced row
     says "an owner still starting answers so until it listens", or ACL2
     distinguishes a lock whose holder has not yet published its socket.
  5. `tools/build_native_host.sh` exits 0 after `ACL2 Error` in a host
     file; default: fail the build on any ACL2 error line.
  6. `farm.py submit hbox` with the 160 image roots fails its preflight
     where the same command by hand succeeds; default: print the preflight's
     head, not its tail, and diagnose.
  7. SCN-076 as a tests/ module within the 180 s / 20 s budgets.
  8. `rollback-check --snapshot` counts transaction files; a compacted
     history (records in a pack) is not counted. Default: count through the
     same observation the open uses for packs.
- Continues without them: every operator step of the walk above.
