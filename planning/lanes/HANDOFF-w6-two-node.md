# Handoff: w6/two-node

The first harness that runs TWO fn nodes against each other, so the peering
wave's work lands against a running pair instead of against a description of
one.

## What landed

- [`tools/twonode_gate.py`](../../tools/twonode_gate.py) --
  `python3 tools/twonode_gate.py <commit-ish> --host persvati`.
- [`tests/test_twonode_gate.py`](../../tests/test_twonode_gate.py) and
  [`tests/twonode_gate_fake/tools/run_peer.py`](../../tests/twonode_gate_fake/tools/run_peer.py)
  -- nineteen tests; the whole gate run twice against local fake hosts, with
  no ssh and no ACL2.
- [`planning/evidence/twonode-dfd8758-2026-09-20.md`](../evidence/twonode-dfd8758-2026-09-20.md)
  -- the real run against `dev` on persvati, 63 steps, 0 failed, 5 not
  exercised, 103 s wall.
- `tools/deploy_gate.py` gained four class attributes (`TITLE`, `TOOL`,
  `PREAMBLE`, `FACT_KEYS`, `STANDING_GAPS`) and three node-parameterized
  methods (`server_command(store, run)`, `start_server(..., run)`,
  `stop_server(..., run)`). Nothing else there changed and its eleven tests
  are untouched and green.

## The shape of a run

One `git archive` lands at `~/fn-deploy/<rev>` exactly as the deploy gate's
does, and the certificate pick, the step accounting, the "what was NOT
exercised" list and the evidence renderer are that gate's, reused by
subclassing `DeployGate`. What this gate adds is a second node: `a` and `b`
under `~/fn-deploy/<rev>/`, each with its own store (`<node>/store`), its own
two groups, its own peer directory, its own log and pidfile, and its own
listener on a free port.

Then three scenarios, in this order, because each is the control for the next.

1. **independent.** X is posted on A and Y on B through the store CLI, so the
   three outcomes are observed per node in the exit codes first (accepted 0,
   refused 1, uncertain 3; D13). Both servers start; each must serve its own
   article (`220`) and answer `430` for the other's, and both must still be
   running afterwards. Without this control, "B has X" later would say
   nothing, because B might have had X all along.
2. **feed.** X is offered from A to B by hand over a raw socket, RFC 3977
   §6.3.2: the gate reads X off A with `ARTICLE`, offers `IHAVE <x>` to B,
   sends the block on `335`, and expects `235`. Three teeth follow: B is
   reread from a fresh connection and must return the *same octets* line for
   line; a second `IHAVE <x>` must draw `435` from the Message-ID history and
   the article must not be stored twice; and an article whose `Path` already
   names B's path-identity must be refused after its `335` (RFC 5537 §3.5)
   and must be absent from B afterwards.
3. **kill.** B is SIGKILLed from inside a transfer it has already agreed to
   take -- mid-`IHAVE` when the transit surface answered, mid-`POST`
   otherwise -- then recovered through `run_store recover` and restarted.
   Everything B acknowledged must still be there (`inspect` exits 0), the
   interrupted transfer must not be (`inspect` exits 1), and A must be alive
   and unchanged throughout.

Every command is recorded with its exit code, its first output line and its
wall time, and the run ends with both servers stopped, a `CLEAN`/`STRAY`
process check scoped to this revision's deploy path, and `~/fn-deploy/<rev>`
removed unless `--keep`.

## The surface the harness calls (peering lanes: this is the ask)

The gate finds the transit surface by **asking a live server**, never by
looking for a file name, so nothing here has to be updated when the peering
lane lands:

- `CAPABILITIES` on the peer connection is expected to gain `IHAVE` and
  `STREAMING` (specs/peering.md §1.1).
- `MODE STREAM` -> `203`.
- `IHAVE <msgid>` -> `335` (send it), `435` (not wanted, and this is what
  duplicate suppression must return), `436` (try later). Anything in
  `500`/`501`/`502` is read as "this tree has no transit surface", the
  scenario is recorded as `peering: not available on this tree`, and the gate
  passes on its independent scenario alone.
- after the block: `235` accepted, `437` rejected permanently. The loop case
  -- our own path-identity already in `Path` -- is expected to be a `335`
  followed by `437`, because the `Path` is inside the article and cannot be
  known at offer time.
- the peer record: when a CLI that writes an `fn-cfg-peerp` exists the gate
  calls it. It probes, in order, `python3 tools/run_store.py --store S peer
  --help` and `./bin/fn peer --help`. Until one of those exists it writes the
  record of specs/peering.md §1.2 to `<node>/peers/<other>.peer` as an inert
  stub, with the six fields in order, and marks the step "peer record: not
  available on this tree".

If a peering lane lands its server under a name none of `bin/fn run
--store`, `tools/run_owner.py`, `tools/run_reader.py` covers, point the gate
at it with `--server-command 'python3 tools/<x>.py --store {store} --port 0'`
rather than editing the selection.

## Why the feed scenario passing today would be a lie

There is no transit surface on `dev`: `books/nntp-responses.lisp` is the only
file in the tree that contains the string `IHAVE`, and `books/nntp.lisp`
answers the keyword with the 500 transcript (w3/reader-profile's NOTE on the
board says so in as many words). So the feed scenario records the gap and the
gate stays green on its independent scenario. A harness that went red until
the peering lane landed would simply be switched off, and a harness that
passed a weaker scenario under the same name would be worse. The three feed
steps are written into the evidence as *not exercised*, which is never a pass
(`Step.exercised`), and the kill scenario says in its own gap that the cut
landed in a POST rather than in a transfer.

## What the fakes are and are not

`tests/twonode_gate_fake/tools/run_peer.py` answers `IHAVE`, `CHECK`,
`TAKETHIS` and `MODE STREAM` and suppresses duplicates and loops. It is a
*line filter in front of* `tests/deploy_gate_fake/tools/run_reader.py`, so
the reader half is the deploy gate's fake and not a second copy of it. Its
replies are that file's, not ACL2's. It exists so the gate's own feed and
kill-mid-transfer code is exercised before fn can exercise it; a green
`TransitTests` says the harness drives a transit surface correctly and says
nothing whatever about fn.

## What the first real run found (dfd8758, persvati, 103 s)

1. **Two fn nodes do run side by side, and they are genuinely separate.**
   Two stores, two ports (38573 and 38351), two logs, two pidfiles; each node
   served its own article with `220` and the other's with `430`; both stayed
   up. The independence control is the one scenario with teeth today.
2. **They cannot reach each other at all.** `IHAVE` on node B draws
   `500 command not recognized` and `CAPABILITIES` is `VERSION 2 / READER /
   OVER MSGID / LIST ... / IMPLEMENTATION` with no `IHAVE` and no
   `STREAMING`. Three feed steps are recorded as not exercised.
3. **`books/owner` still does not include**, on both nodes, so the gate fell
   back to `tools/run_reader.py --post` twice and said so per node. This is
   the fourth independent observation of the finding w5-fn-cli and
   w5/deploy-gate already put on the board; the two-node harness will start
   using the owner the moment it starts.
4. **The kill and the recovery are clean at two nodes as at one.** SIGKILL of
   B from inside an open POST gives `ECONNRESET`; `<interrupted@...>` is
   absent after recovery (`inspect` exits 1) while `<beta@b...>` rereads
   (`inspect` exits 0); node A was `ALIVE` before, during and after, and its
   own presence check is unchanged.
5. **The injected uncertain publication is durable on both nodes**
   (`inspect` exits 0 for `<uncertain-a@...>` and `<uncertain-b@...>` after
   recovery) and each recovery reports `staging-orphans=1`, stable across the
   kill recovery too. The gate asserts the uncertain article in *neither*
   direction and records which way it went; w5/deploy-gate saw the same
   orphan and it is still worth a decision.
6. **The box is left clean**: both servers stopped, the revision-scoped
   process check reports `CLEAN`, `~/fn-deploy/<rev>` removed.

## Open for the next lane

- Re-run the gate the day `IHAVE` is served. Nothing in the gate should need
  editing; the three skipped steps become three assertions with teeth.
- The two nodes are on one host over loopback. There is no partition, no
  latency, no clock disagreement, and killing B is not a partition because A
  stays reachable. A real partition scenario wants two boxes.
- No peer is authenticated: the peer records are configuration only, so a
  node would accept transit from whoever connects. specs/peering.md §6 owns
  that; the gate records it as a standing gap.
- Two articles crossing once is **not** the merge property of
  specs/peering.md §4 (K4). The gate compares octets; the convergence claim
  needs the certified statement, and the gate must not be cited for it.
- The gate exercises one kill point. `tests/campaign/cuts.py` owns the
  enumerated table.
