# Handoff: w10/owner-feed (the owner drives the outbound feed)

Branch `w10/owner-feed` from `dev` at `92e4a40`, worktree
`build/lanes/w10-owner-feed`. Spec:
[`specs/peering.md`](../../specs/peering.md) §3 and its wave-10 status
section, which is this lane's per-item record. This lane is milestone 3 of
[`HANDOFF-w9-peering-e2e.md`](HANDOFF-w9-peering-e2e.md) and the parts of
milestones 4 and 5 that depend on it.

## What exists

| File | What |
| --- | --- |
| `books/owner-feed.lisp` (new, `fn-own-feed-`) | The owner's half of the outbound feed, the half `books/peer-feed.lisp` says it does not own. The feed TABLE, one `(name record feed)` per configured outbound peer; `fn-own-feed-tablep` binds the key, `fn-feed-peer` and `fn-sched-contact-peer` to one name. The SCOPE decision `fn-own-feed-offerablep` (outbound wildmat, Path loop check, origin peer) over the article's own octets. `fn-own-feed-targets`, `fn-own-feed-accept`, `fn-own-feed-reconfigure` (merge, never replace; retire only an idle feed), `fn-own-feed-restart-all`, `fn-own-feed-tick-peer` / `-tick`. The RFC 3977 §3.2 reply reader `fn-own-feed-response-code` / `-parse-response`. The FNFD record builders and the two record folds. |
| `tests/acl2/owner-feed-tests.lisp` (new) | 98 assertions: a real replayed configuration with three peers (streaming outbound, outbound with a non-matching wildmat, inbound-only), a real parsed article and the same article with the peer's identity in Path, the table, the targets, four teeth for `fn-own-feed-offerablep` and six for `fn-own-feed-tablep`, the enqueue with its FNFD record replayed back to the same feed, the tick with and without a connection, the reply reader and its three refusals, the restart fence, the retire-only-when-idle rule. |
| `books/owner.lisp` (edit) | The owner record gains a **thirteenth** field, `feeds`. `fn-own-make` takes thirteen arguments with `feeds` last; `fn-own-feeds` is the accessor and `fn-own-with-feeds` the update. `fn-own-reopen` restarts every feed (K5). The durable branch of `fn-own-outcome` and `fn-own-transit-outcome` calls `fn-own-feed-durable`. New `fn-own-step` arms: `(:feeds cfg)`, `(:feed-conn peer conn)`, `(:feed-replay peer entries)`, `(:tick obs)`, `(:feed-octets peer octets obs)`. **No existing function, arity or statement changed otherwise, and `fn-own-relation` gains no conjunct.** |
| `host/owner-host.lisp` (edit) | The feed bridge: `fn-owner-feed-configure`, `-peers`, `-host`, `-port`, `-streamingp`, `-queue-length`, `-connect`, `-tick`, `-octets`, `-frames`, `-command`, `-record-peers`, `-replay-frame`, `-restart`. Frames carry a zero trailer; the host seals them (A-CRYPTO), exactly as `tools/run_feed.py` does. |
| `tools/run_owner.py` (edit) | The `Feed` class and the driver: one outbound client connection per peer with work, the journal replayed and fenced at startup, the FNFD records appended and fsynced BEFORE the bytes they authorize, the reply lines fed back through ACL2. |
| `tools/run_feed.py` (edit) | The Python status twin is **deleted**. `status()` is gone; `Acl2Feed.response_code` calls `fn-own-feed-response-code`, which is why the module now includes `books/owner-feed`. The file is a thin driver for `tests/test_feed.py`; the live feed is the owner's. |
| `tools/twonode_gate.py` (edit) | `scenario_owner_feed` (A posts through the server, A's own feed delivers to B, byte-identity, the 435/438 second offer; then B to A) and `scenario_feed_restart` (B down, A posts, `kill -9` A, both restart, B ends with exactly one copy: K5). The driver gains a `post` phase and a `wait` phase. |
| `books/peer-inbound.lisp` | Taken from `w10/auth-served` at `e1159a7` mid-lane to unblock loading, then **replaced by dev's** at the merge of `2505a8f` (`w6/peering-inbound-2`), which is the version with a certificate. Nothing of this lane is in that file. |
| `Makefile`, `docs/prefixes.md`, `specs/peering.md`, `planning/proofs.json`, `planning/requirements.json` | Two roots (`books/owner-feed` and its tests, before `books/owner`, which now includes it); the `fn-own-feed-` row; the wave-10 status section; PRF-029 linked from REP-001, REP-002 and REP-005. |

## The three design decisions a successor should not undo

1. **The peer record rides in the table entry.** An entry is
   `(name record feed)`, not `(name . feed)`. The configuration is read once,
   at `fn-own-feed-reconfigure`; the durable path — `fn-own-feed-accept`,
   called from the `:durable` branch of `fn-own-outcome` — takes no
   configuration argument and cannot be given a stale one. Without this the
   enqueue arm needs `cfg` threaded through `fn-own-outcome`, which changes
   the statement of every owner keystone that mentions it.

2. **The owner's feed tick does not route through `fn-sched-table-tick`.**
   `fn-sched-tick-step` selects an `fn-sched-item` work, records a decision
   and drives a BP attempt through `fn-sched-drive-attempt`; its effects are
   `fn-bp-result-effects`, not NNTP commands, and its queue is not the feed
   queue. Routing the feed through it adds a table that decides nothing about
   the feed and makes `fn-sched-table-tick-is-the-peer-tick` a decoration
   rather than a subject rule. What the feed DOES take from the scheduler is
   the contact model: each feed carries an `fn-sched-contactp` whose peer the
   table binds to the key, and `fn-feed-selection` gates on
   `fn-sched-contact-holdsp`. Posted as a NOTE on the board.

3. **`fn-feedp` preservation is cited, never restated.**
   `books/owner-feed` includes `books/peer-feed-invariants` for
   `fn-feed-enqueue-preserves-feedp`, `fn-feed-restart-preserves-feedp` and
   `fn-feed-tick-step-preserves-feedp`. That is why this book cannot certify
   yet (below). Copying those three proofs here to get a green badge would be
   a twin of a sibling cluster's keystones; the dependency is the right shape
   and the blocker is one form in the feed lane.

## Certification, per root

Nothing in this lane is certified. The two reasons are both other lanes'
open forms, and both are named exactly.

| Root | State | Evidence |
| --- | --- | --- |
| `books/owner-feed` | **admitted, no open form; NOT certified** | laptop ACL2 8.7, `tools/acl2 --timeout 840` over the driver `ld books/peer-feed-invariants.lisp` (`:ld-error-action :continue`), `(in-theory (disable fn-feed-vocabulary))`, `ld books/owner-feed.lisp`. Zero `ACL2 Error` in the owner-feed portion. |
| `tests/acl2/owner-feed-tests` | **admitted, 98/98 assertions pass; NOT certified** | the same driver with the test body appended; 98 `:PASSED`, no failure. |
| `books/owner`, `books/owner-invariants`, `tests/acl2/owner-tests` | **not admitted at all** | `include-book "served"` needs a certificate `books/served` does not have. With `books/peer-inbound.lisp` taken from `w10/auth-served`, persvati run `run-20260920T200209Z-0bf0` (remote root `/home/ember/fn-lanes/w10-owner-feed-b`) **did** produce `books/peer-inbound.cert`, `books/nntp-post.cert` and `books/nntp-effects.cert` — the blocker the wave-9 handoff named is closed — but `books/served` then failed one level up, at **`fn-served-dispatch-effects-are-typed`** (`books--served.certify.log:1852`). The checkpoint is the submission branch of a NON-peer session: with `(not (fn-peer-sessionp (fn-served-conn-session conn)))` and a `fn-post-result-submission` from `fn-peer-step`, the goal wants `(fn-served-effectsp (append <peer-step effects> (list (list :submit <submission>))))` and nothing says that submission is an injected one. One lemma, in the served/auth lane's cluster. |
| `books/peer-feed-invariants` (dependency) | **open at `fn-feed-apply-record-preserves-feedp`** | persvati `run-20260920T190044Z-c815`, `books--peer-feed-invariants.certify.log:15702`. The residue has MOVED since the w6 handoff: the `find`/`consp` bridge is closed, and what remains is the attempt bound in the `:feed-sent` arm — `(fn-feed-attempts-belowp (fn-feed-queue-set-state (fn-feed-queue f) msgid '(:sent 0)) (fn-feed-next-attempt f))` with `(fn-bp-nth 1 (state)) = 0` in the split. The feed lane owns it. |
| `make check` | green | 202 Markdown files, 56 requirements, 29 proof targets, 19 scenarios; ledger current. |
| `tests/test_twonode_gate.py` | 19 tests, green | laptop, `python3 -m unittest tests.test_twonode_gate`. |

## After the merge of dev at `2505a8f`

The lane merged `dev` once the coordinator reported that `books/served`,
`books/owner` and `books/ideal` have certificates there. Two things follow.

- `books/peer-inbound.lisp` is dev's again (the `w10/auth-served` copy this
  lane carried mid-run is gone), and `books/peer-feed-invariants.lisp` is
  dev's at `c34995d`, which is a commit later than the one this lane's
  earlier farm runs measured. Whether `fn-feed-apply-record-preserves-feedp`
  closes there — and so whether `books/owner-feed` can certify at all — is
  answered by a re-`ld` against the merged source: **it is still open.**
  `fn-feed-apply-record-preserves-feedp` fails at `c34995d` exactly as it did
  at `8148b04`, so `books/owner-feed` still cannot certify. The decisive farm
  run is persvati `run-20260920T201914Z-0a52` (remote root
  `/home/ember/fn-lanes/w10-owner-feed-b`, `--jobs 4 --timeout-seconds 5400
  --closure books/owner-feed tests/acl2/owner-feed-tests books/owner
  books/owner-invariants tests/acl2/owner-tests`); it was still running when
  this lane ended, and `python3 tools/farm.py wait persvati
  run-20260920T201914Z-0a52 --remote-root /home/ember/fn-lanes/w10-owner-feed-b`
  brings its evidence and its certificate pairs home.
- **`fn-own-conn-boundedp` (books/owner.lisp:572) is a live defect and is
  NOT this lane's to fix** (coordinator, 2026-09-20; the inbound lane owns
  it). It tests `fn-post-sessionp` on what is now a six-field peer session,
  so it is false on every connection, the enqueue branch below it is
  unreachable, and every theorem hypothesising `fn-own-relation` is vacuous
  on reachable states. This lane did not touch that predicate or the three
  branches that test it. **None of this lane's keystones hypothesise
  `fn-own-relation`**: they hypothesise `fn-own-feed-tablep`, the feed
  table's own carried recognizer, which is independent of the connection
  shape. The owner-side statements listed as open below are the ones that
  will need `fn-own-relation`, and they should be written against it AFTER
  the fix (the connection's session recognizer is the served one, not the
  post shape).

## What is open, with the obligation each needs

1. **Certify the owner chain.** Merge `w10/auth-served`'s
   `books/peer-inbound.lisp` fix into dev, then
   `python3 tools/farm.py submit persvati --jobs 4 --timeout-seconds 5400
   --remote-root /home/ember/fn-lanes/w10-owner-feed --closure books/owner-feed
   tests/acl2/owner-feed-tests books/owner books/owner-invariants`. Use
   `--timeout-seconds 5400`: `books/nntp-effects` needs about 2600 s and a cut
   at the default 1800 s reads as "no certificate" rather than as a failure.
2. **The owner-side keystones, stated over `fn-own-step`.** Not written,
   because they cannot be admitted on this tree and a theorem that cannot be
   admitted is not a theorem. What they should be:
   `fn-own-feed-durable-is-the-target-enqueue` — the feed table after
   `(:outcome id :durable)` is `fn-own-feed-accept` of the submission's
   origin, Message-ID and octets, which composes with
   `fn-own-feed-never-offers-a-loop` to give K2's outbound half at the host's
   own entry point; plus preservation of `fn-own-relation` by the five new
   arms (each threads `feeds` and touches no other field, so each is the
   existing arm's proof with one more `fn-own-make` component).
3. **The wildmat twin.** `fn-own-feed-group-matchp` is the same call as
   `fn-peer-wildmat-matchp` (`books/peer-inbound.lisp`). One
   `:rule-classes nil` equality in `books/owner-invariants.lisp`, where both
   are visible, names it. `books/owner-feed` cannot include
   `books/peer-inbound` without inheriting the served chain's blocker.
4. **The two-node run.** `scenario_owner_feed` and `scenario_feed_restart`
   are written and unit-tested against the fake, and **were not run on
   persvati**: `tools/run_owner.py` starts with `(include-book "books/owner")`,
   so without a certificate for `books/owner` the gate falls back to
   `tools/run_reader.py` and there is no feed to exercise. The run is one
   command after item 1: `python3 tools/twonode_gate.py <commit> --host persvati`,
   then `planning/evidence/twonode-feed-w10-<date>.md` with versions,
   revision, invocation, results and limits.
5. **Process-death cut points in the campaign model.** `tests/campaign/`
   was not extended. The feed adds two cut points the model does not
   express: between the `(:feed-offer ...)` record reaching the journal and
   the `:command` bytes reaching the socket, and between the reply arriving
   and the `(:feed-outcome ...)` record reaching the journal. Both are
   resolved by the restart fence in the model
   (`fn-own-feed-restart-all` on reopen) and by the peer's history on the
   wire, but AGENTS.md's rule is that a cut the model cannot express is a
   fidelity defect: **recorded here as a gap, not as a passing test.**
6. **RFC 3977 §3.1.1 dot stuffing** of an outgoing article block is
   `Session.send_block` in `tools/run_feed.py`, reused by the owner.
   `books/wire.lisp` has the stuffer; wiring the feed's article effect
   through it is one packet.
7. **fn does not prepend its own path-identity to a transit article's Path**
   (RFC 5537 §3.2.1). `fn-peer-injection-arguments` stages the peer's octets
   verbatim, so a relayed article leaves this node with the Path it arrived
   with. The outbound loop check still refuses a target already named in Path
   and refuses the origin outright, but on the return leg loop suppression
   rests on the peer's history answer (435/438) rather than on Path. A POSTed
   article is unaffected (`fn-inj-prefix` writes the Path line). Inbound
   lane's; posted as a NOTE on the board.
8. **The retry bound is a constant, not a peer-record slot.**
   `*fn-own-feed-retry-bound*` is 3, the same default `tools/run_feed.py`
   used; `books/peer-config.lisp`'s outbound half is groups, streaming,
   max-queue and backoff. Making it configurable is a peer-record change.

## How to iterate on this cluster

`books/owner-feed` cannot be `ld`ed on its own, because
`books/peer-feed-invariants` has no certificate. The driver that works:

```lisp
(set-prover-step-limit 2000000)
(set-ld-error-action :continue state)
(ld "<abs>/books/peer-feed-invariants.lisp" :ld-error-action :continue)
(in-theory (disable fn-feed-vocabulary))          ; see below
(ld "<abs>/books/owner-feed.lisp" :ld-error-action :continue)
```

Three traps, each paid for once here:

- **Absolute paths.** A second `ld` with a relative path resolves against the
  first file's cbd, so `"books/owner-feed.lisp"` becomes `books/books/...`
  and ACL2 spins on a hard `SET-CBD` error — 976 MB of log in one run.
- **`ld` of a book's SOURCE runs its `local` events**, so
  `books/peer-feed-invariants`'s local `in-theory` leaves the feed
  transitions OPEN where `include-book` would leave them shut, and its export
  `deftheory` fails (it names theorems that did not close). Re-disabling
  `fn-feed-vocabulary` between the two files makes the hints below the ones
  certification will see.
- **`mv-nth`.** Opened, `(mv-nth 0 (fn-feed-tick-step ...))` becomes
  `(car ...)` and every rule stated over the tick stops matching. The same
  trap `books/peer-feed-invariants.lisp` documents; disable it in any hint
  that lifts a tick.
