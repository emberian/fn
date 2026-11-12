# fn2

The bottom-up, semantics-first rebuild of fn: the persistent event log between systems, built in place here and swapped to the repository root when it serves. Start at `docs/design/FN2-ORIENTATION.md` (ember's words, the rulings, where the tree is, the order). Each layer's own decisions as built: `docs/<layer>.md`. Owed keystones, written and unproved on purpose: `docs/OWED.md`.

## What is here
- `books/`: the ACL2 books. The declaration forms (`columns.lisp` `defcolumns`; `machines.lisp` and `machine-arms.lisp` `defmachine` with its step language; `arms.lisp` `defcost`; `layout.lisp` `deflayout`; `runs-schema.lisp` `defrunschema`; `declare.lisp`, `owed.lisp`, `squares.lisp` the registry and the obligation store); layer A's pool, vocabulary, core, scheduler, executor and reference turn; layer B's crash and log models, formats, commit batch, allocator and recovery; layer C's ordered-run engine (runs, identity, overlays, filters, folds, reads, the sealer); layer D's connection, upload and transaction machines, the grammar DSL and the principal ledger; layer E's consumer port and durable authority; the `assembly-*` books that make the core from the registered kinds.
- `sim/`: the deterministic simulator (the host's primitive set, seeded faults) and its checkers (OWN, WORK, TRACE, ACCOUNT, IDENTITY, WIRE, HISTORY, RECOVERY, RECLAIM, DEATH, DEADLOCK, ENVELOPE).
- `host/`: the native adapter: the event loop over the served core, the TCP and `0600` Unix-domain socket sessions (with peer UID credentials), the file-backed storage device, and the BLAKE3 FFI.
- `tools/fn_admin.py` and `./fn`: the operator, consumer, and NNTP CLI over the node's TCP and `FNCT` Unix-domain sockets.
- `tests/`: unit books, the scenario drivers, the Q1 evidence and controls, `tests/test_fn2_user_surface.py`, and `tests/harness/`.
- `meta/`: the Lean metatheory (squares, coherence, revision conservativity, parametricity).
- `tools/certify.sh`: certify books with the fn toolchain's ACL2.

## Native image node & CLI

After certifying `books/node-profile.lisp` with the project toolchain:

```sh
# 1. Initialize a fresh preallocated store image (never truncates an existing file)
./fn init build/node.img --size-mb 32 --group ops.alerts --group ops.audit

# 2. Recover, fence the new writer epoch, and serve TCP NNTP + 0600 FNCT Unix socket
./fn serve build/node.img --port 1119 --control-sock /tmp/fn2-ctl.sock

# 3. Create durable principals and grant/inspect rights over --control-sock
./fn principal create watcher --control-sock /tmp/fn2-ctl.sock
./fn grant set watcher consume --control-sock /tmp/fn2-ctl.sock
./fn grant set watcher read ops.alerts --control-sock /tmp/fn2-ctl.sock
./fn grant set watcher append ops.alerts --control-sock /tmp/fn2-ctl.sock
./fn grant set anonymous append ops.alerts --control-sock /tmp/fn2-ctl.sock
./fn grant get watcher read ops.alerts --control-sock /tmp/fn2-ctl.sock

# 4. Register a consumer cursor, append/read/wait/ack over --control-sock
./fn stream register --as watcher --consumer inbox1 --cursor-file build/watcher.cur --control-sock /tmp/fn2-ctl.sock
./fn stream append --as watcher --group ops.alerts --subject "Ready" --body "hello" --control-sock /tmp/fn2-ctl.sock
./fn stream wait --as watcher --cursor-file build/watcher.cur --seconds 10 --control-sock /tmp/fn2-ctl.sock
./fn stream read --as watcher --cursor-file build/watcher.cur --control-sock /tmp/fn2-ctl.sock
./fn stream ack 2 --as watcher --consumer inbox1 --cursor-file build/watcher.cur --control-sock /tmp/fn2-ctl.sock
./fn stream status --as watcher --consumer inbox1 --control-sock /tmp/fn2-ctl.sock

# 5. List groups, post, and read articles over NNTP TCP (--port / $FN_PORT)
./fn groups --port 1119
./fn post ops.alerts --subject "Notice" --from "op@fn2.invalid" --body "text" --port 1119
./fn article ops.alerts 1 --port 1119
```

Every subcommand accepts `--json` (and `$FN_CONTROL_SOCK`, `$FN_PORT`, `$FN_HOST` defaults) and keeps outcomes distinct at the exit boundary: `0` (`accepted`), `1` (`refused`), `2` (CLI usage / transport / startup bind error), `3` (`uncertain`).

`python3 tests/native-image-restart.py` and `python3 tests/test_fn2_user_surface.py` verify live TCP + Unix-domain operations and immediate `SIGKILL` crash recovery. The file-device contract and startup layout are in [`docs/a-pool-host-sim.md`](docs/a-pool-host-sim.md), and served authority in [`docs/design/AUTHORITY-20261105.md`](docs/design/AUTHORITY-20261105.md).

## How changes are checked
The changed books certify, the scenarios for what changed pass in the REPL on the tiny profile, the author reads what was written; one unattended nightly runs the whole closure, every scenario, the drivers and the surface harness (`docs/design/WORKFLOW-20261031.md`). Performance is reported beside the profile, never a gate. Proofs come when assurance is wanted.

## Rules every book follows
The derived path is the only path. Assert, never absorb. The DSLs generate meaning, not storage. Layers meet at seams. One representation for bytes. Bounded everything; exhaustion is a continuation. (The full method: `docs/design/briefs/FN2-SEAT-COMMON.md`.)
