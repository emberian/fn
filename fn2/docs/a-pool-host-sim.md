# fn2 layer A: the byte pool, the vocabulary, the host, the simulator, the executor loop

Present state, rewritten whole by the layer-A seat. The contract is
`build/coordinator/briefs/FN2-LAYER-A-POOL-HOST-SIM.md`; the decisions it serves are
`build/coordinator/fn2/EXECUTION-MODEL.md` (rules 3, 6, 7, 10; §7a item 3) and the normative
tables of `fn2/EXECUTION-MODEL-ROUND2-ASTRA.md` (§A.1, §B.1, §C, §D, §F). This file records the
choices the layer makes inside those decisions, each with its reason. A departure from a decision
that is not recorded here is a defect.

## 1. Where each piece lives
| piece | file(s) | language |
|---|---|---|
| owed keystones | `fn2/books/owed.lisp`, `fn2/docs/OWED.md` | ACL2 book |
| records/columns DSL seed | `fn2/books/columns.lisp` | ACL2 book (macro) |
| byte pool | `fn2/books/pool.lisp` | ACL2 book, guard-verified |
| events, actions, outstanding table, outbox | `fn2/books/vocab.lisp` | ACL2 book, guard-verified |
| scheduler, executor loop, echo/null/scribe machines | `fn2/books/executor.lisp` (+ `fn2/books/machines-a.lisp`) | ACL2 book, guard-verified |
| simulator: SimNetwork, SimStorage, SimClock, PRNG, faults, recovery stub | `fn2/sim/*.lisp` | ACL2 books, guard-verified |
| checkers: TRACE, WORK, OWN, ACCOUNT (+ framework for the other seven) | `fn2/sim/check*.lisp` | ACL2 books |
| Linux adapter (and the darwin development backend) | `fn2/host/*.lisp` | raw SBCL, loaded by a session script behind one trust tag |
| acceptance | `fn2/tests/sim-layer-a.lisp` (simulator driver), `fn2/tests/native-echo*.{lsp,py}` | ACL2 driver; native test |

**The simulator is ACL2 logic (decision A-SIM-IN-LOGIC).** ENVELOPE §2.6: the simulator "should be
the same definition as the logic's environment model (one source; the model is the oracle and the
simulator is its evaluation)". So SimStorage, SimNetwork and the checkers are guard-verified ACL2
over their own stobj, and the eventual crash-composition and refinement proofs can be stated over
them without a second model. The Linux adapter is the only raw Lisp in fn2 and it decides nothing.

Package: `"ACL2"`, every name prefixed `fn2-`. No `defpkg`, no trust tag, no `skip-proofs`, no
`defaxiom`, no `:program` in any book; the host's trust tag lives in the session script that loads
`fn2/host/`, never in a book.

## 2. Widths (decision A-WIDTHS)
ROUND2 §B.1 writes process-local generations as `u64`. On SBCL a `u64` is not a fixnum and every
read of one may cons a bignum. fn2 holds in-memory generations and counters as `(unsigned-byte 60)`
(`:u60` in the column DSL): fixnums, sums of two still fixnums, and an explicit exhaustion rule
instead of a width argument: a slot or row whose generation would pass the profile's
`generation-limit` (at most `2^60 - 1`) is **retired**, never reused, never wrapped (§B.1 "No counter
wraps into a previously valid identity"; "Process-local slots may be retired"). The profile sets
the limit and the starting generation, so the simulator starts generations near the limit
(scenario 19). Persistent `u64` encodings (layer B on) are a separate on-disk type and are written
as two fixnum halves or a checked byte encoding, never as a resident bignum.

## 3. The byte pool (contract item 1; rule 6)
- **Carving.** At init the profile names size classes `((count . bytes) ...)`; the pool resizes its
  byte array to the sum and its slot table to the total count, and carves slot `i` a fixed extent
  `[base(i), base(i)+cap(i))`. No allocation after init; no fragmentation; a class with no free slot
  answers `:exhausted`, which the caller holds as a continuation (rule 3).
- **Handle** = `(slot, generation, offset, length)` with `offset`/`length` relative to the slot's
  extent, passed as four scalars (multiple values; no cons).
- **States**: `free`, `workspace(owner)`, `leased-in(op)`, `leased-out(count)` (the ops that hold it
  are named in the outstanding table), `handed(from, to)`, `retired`. Owner is an `MRef`
  `(kind, slot, generation)`; an op is an `OpRef` `(slot, generation)`.
- **Readable bytes** are the slot prefix `[0, fill)`. `lease-in` lends `[fill, fill+len)` (append
  discipline: receives and reads land after the readable prefix); the adapter writes only inside
  the lent range; `complete-in(n)` sets `fill := lease-off + n` and returns the slot to workspace.
  This is the byte-fill theorem's subject (EXECUTION-MODEL §4): a completion exposes exactly the
  range written under its loan. `reset` discards the prefix (`fill := 0`); a machine that keeps a
  partial command compacts it with its own bounded copies.
- **Immutable output**: `lease-out` needs `off+len <= fill`, works from `workspace` or an existing
  `leased-out` of the same owner, counts borrows; `release-out` decrements and returns to workspace
  at zero. A slot with borrows is never written, released or reused. Zero-copy send progress is not
  release: release happens on the terminal result when no release is pending, else on
  `BorrowReleased`.
- **Generations** increase on `release`; every export compares the handle's generation and answers
  `:stale` with the pool unchanged on mismatch, `:bounds`, `:state` or `:owner` likewise.
- The octet list exists only in the logic: the pool's views (`fn2-pool-slot-view`,
  `fn2-pool-bytes-view`) are `defun-nx`; nothing on a served path builds a list of bytes.

## 4. The host/core ABI (contract items 2-3; EXECUTION-MODEL §7a item 3; ROUND2 §D)
- **Outstanding table** `O` rows (profile). An op row's phase: `free → reserved → queued →
  submitted → resulted → (release-pending →) done → free`. Reserving an op reserves, together: the
  row, one outbox descriptor, its pool range(s), and two result cells (terminal, release): `Qr = 2O`
  by construction, so a genuine completion always has a place (D.1 "credits reserved before
  submission").
- **Outbox** ring of `Qa` descriptors (profile). The core appends a descriptor only for a reserved
  op (op phase `reserved → queued`). A descriptor in `[outbox-head, outbox-tail)` is **queued**. The
  adapter reads descriptors from `outbox-head` and calls `fn2-outbox-ack(n)` after it has taken `n`
  of them; from that call they are **submitted** (`queued → submitted`) and the adapter owns their
  physical execution. A full outbox is backpressure: the transition that wanted it keeps its
  continuation. Death between take and ack: the descriptors were possibly executed; for sockets
  nothing survives the process; for storage every write since the last successful barrier is
  uncertain, which the recovery stub (and layer B's recovery) must classify, never assume absent.
- **Results.** The adapter posts an observation with `fn2-post-result(cell, opref, fields)`; it is
  bounded validation only: the op row's generation and phase must match and the cell must be unposted,
  else the observation is counted (`stray`) and dropped and changes nothing else (fn's T6). A posted
  cell enters the posted FIFO (capacity `2O`, cannot overflow). `fn2-turn` harvests at most `H`
  posted cells in posting order.
- **When bytes become core-readable**: never at post time. A `ReceiveResult`/`ReadResult` makes its
  range readable only when `fn2-turn` harvests it and runs `complete-in`. The adapter posts only
  after its physical write ended and never touches the range afterwards.
- **Unsolicited inputs**: the clock mailbox (one coalesced cell: monotonic, realtime, validity), a
  sticky signal word (shutdown/reload). The control inbox `Qc` arrives with layer D/E.
- **Capabilities**: a connection is a host-issued opaque `(index, nonce)`; the core never sees a
  descriptor or fd.
- **Single-shot** accept, receive, read, send (ROUND2 D.1); a short send is terminal; the remainder
  is a new action.

## 5. Executor (contract item 5)
`fn2-transition`, `fn2-reference-turn`, `fn2-turn` as ROUND2 §A.1; budgets `H = 128`,
`K = 64`, `Aturn = 256` and per-run caps (4 KiB, 32 structural steps, 4 descriptors) as profile
values; the 80-entry calendar of §C.2 over `P = 64` principal slots plus the four service classes;
intrusive FIFO runnable lists per principal, one link per machine; wait outside only when nothing is
eligible (§C.4). `fn2-turn` appends one fixed-width record per transition to a bounded trace ring
when the profile's trace flag is on; the TRACE checker replays the calendar rule over its own list
model of the run queues and checks every selection and the action order. Machines in layer A: the
echo machine, the null connection machine, and **scribe**, a test-only storage probe (write a
stamped sector, fence, read back) that exists until layer B's commit machine replaces it.

## 6. Simulator and checkers (contract item 4)
Seeded PRNG (splitmix64-style over fixnum halves); profile, seed, observation order, fault choices
and revision recorded per run; the fault classes of the brief, each with a per-run probability
drawn from the seed (swarm testing); death at any action boundary and during the recovery stub.
**Recovery stub** (layer A only): the data file is sectors; a sector written by scribe carries
magic, its own address, a sequence number and a checksum; the stub classifies each sector as
never-written, valid, torn/corrupt or misdirected and the file as `intact / torn tail / damaged /
unknown` by ROUND2 §E.4's rules restricted to that format. Layer B replaces it.
Checkers implemented in A: TRACE, WORK, OWN, ACCOUNT; the framework names all eleven and the
other seven report `not-yet` until their layers.

## 7. Platform backends (ember's ruling: nothing refused)
Linux: epoll readiness, one preallocated data file `O_DIRECT`, barrier `fdatasync`, ops executed by
the executor thread at submission and their completions posted at the next harvest (one thread; the
core cannot distinguish this from an asynchronous backend, and the simulator models full
asynchrony and reordering). darwin development backend: `poll(2)`, `F_NOCACHE`, barrier
`F_FULLFSYNC`; it claims the weaker model. A copy-on-write file system is documented (its soundness
requirements: honest barrier, no relocation under direct I/O, declared write-damage radius), never
refused.

## 8. Owed keystones
`(defthm-owed NAME (VARS) FORMULA :teeth ...)` translates the statement (so it names real
functions with real arities), records it in the world table `fn2-owed`, proves nothing, and has a
row in `fn2/docs/OWED.md` with its teeth. Layer A owes: pool generation/staleness, byte-fill,
no-reuse-while-borrowed, conservation; outstanding-table result reservation; turn bounds (WORK);
the refinement obligation of EXECUTION-MODEL §4 over `fn2-turn` and `fn2-reference-turn`.

## 9. Departures and open items
- `u60` in-memory generations instead of `u64` (§2).
- A send carries one range in layer A (ROUND2 D.3 allows four); the descriptor reserves the field
  width for four.
