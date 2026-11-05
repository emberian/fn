# fn2 layer A continuation (pool, vocabulary, host ABI, simulator, executor; present state at origin/dev a4bea27de, rewritten whole 2026-11-04)

Layer doc: `docs/a-pool-host-sim.md`. Brief: `docs/design/briefs/FN2-LAYER-A-POOL-HOST-SIM.md`. The form's generator
is the form seat's (form-continuation.md); this notebook is the rest of A. No A seat is live on 2026-11-04.

## On dev (A, newest first)
- aac7a29e7 (F5): `fn2-op-reserve` keeps 4 descriptor and outbox slots for cleanup issues (close, cancel, arm-wake,
  fence) when capacity >= 16 (`books/vocab.lisp`); `:owner-uid` in `fn2-control` from the supported profile
  (`books/exec-state.lisp`); `defresource`/`defservice`/`defaction`/`fn2-assemble` in `books/resources.lisp`.
- 736591806 (F4): per-kind leaf books; `fn2-machine-run` and the observe router dispatch over constrained stubs,
  attached in `books/assembly-attach.lisp` (`fn2-machine-attach-all-events`); `assembly-reference-children` on
  `assembly-init`, `executor-access` on `assembly-access`.
- 2314c1e90 (F1): `fn2-decl-layer` resolves promoted paths.
- Earlier (in history; the 10-31 notebook is in git before this commit): the core's wfp per child (867e87a23), the
  calendar scheduler and the ledger's grant source, the native event loop, the socket and the configured
  `:local` listener with uid/gid (371c48e4e), the turn's work bound from the registry, the Q1 contracts
  (`tests/q1-contracts{,-b,-c,-d}.lisp`) and controls (`tests/q1-controls.lsp`, judge `q1-controls-check.lisp`).

## What serves
A serves no verb of its own; every verb on H's line (26, both carriers, 0 disagreements at 132ac2c62) runs through
A's executor (`fn2-turn`), the simulator carrier (`sim/`) and the native adapter (`host/`).

## Owed, with the exact next step
1. **Timer service.** `(defservice :timer :ready fn2-timer-service-ready-p :step fn2-timer-service-step ...)` names
   two functions that do not exist. Next: define them over `fn2-control-idle-deadline` as a calendar service in
   `books/sched.lisp` (which hardcodes four services today), and make the calendar read the `fn2-services` table.
   Needed by D7 (deadlines, STARTTLS), E4, E5 and cns's `wait-ms`.
2. **Outbound connect.** `(defaction :connect :issue fn2-issue-connect ...)` names an undefined issue. `:connect` and
   `:connect-result` are in the vocabulary enums (`books/vocab.lisp:11,30`). Next: `fn2-issue-connect` in
   `arm-children.lisp`, the simulator network's connect, the host adapter's. Needed by E4 and E5.
3. **The F5 tables consumed.** Only `tests/resources-unit.lisp` reads `fn2-resources`, `fn2-services`,
   `fn2-actions` and `fn2-app-manifests`. Next: `fn2-resource-assembled-order` replaces `*fn2-resource-order*` in the
   D0 check, and the probe app (`fn2-probe-app`: listener, echo, scribe) builds through `fn2-assemble` with no NNTP
   book included. That build is the zero-fork test.
4. **FLOOR** (ENVELOPE-AND-HOST §2.8): no measurement against fn2 exists.
5. **Multi-node simulation**: `sim/network.lisp` drives one core; E4 and E5 need N cores on one network.
6. **Path defects left by the promotion.** `tests/consumer-codec-unit.lisp:18-20` reads fixtures at
   `../../tests/fixtures/...` (outside the tree since 49787612f). Owner: E; noted here because it is the same class
   as `tests/sim-layer-a.lisp`'s scenario path, fixed on lane/notebooks-lean.

## Seams
- To the form seat: the listener's registry arms by family; `fn2-account-request-park` with a `:child`.
- To D and E: `fn2-control-owner-uid` (the ctl owner check reads it); the cleanup reserve.
- To H: the seeded store `tests/seeded-store.lsp` is shared by sim-session, native-serve and native-session.

## Boxes
bb2 certifies (`tools/box_certify_bb2.sh <lane> -j 4 <books>`); the Mac runs the REPL. Forge and hbox are not used
this round.
