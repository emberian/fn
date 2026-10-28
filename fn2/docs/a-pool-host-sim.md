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
| checkers: OWN (independent), TRACE and WORK (see the caveat in §6); ACCOUNT owed in A6; framework names all eleven | `fn2/sim/check*.lisp` | ACL2 books |
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
`fn2-turn` calls `fn2-reference-turn`, a bounded loop over `fn2-transition`;
there is no fusion. A turn stops at the first exhausted `H`, `K`, or `Aturn`
budget, or when nothing eligible remains. Results are `(mv status nobs nvisits
nactions fn2-core)`; `fn2-core-idle-deadline` supplies the accompanying sleep
bound (`2^60-1` means no requested deadline). `:more` preserves runnable work,
`:idle` permits adapter progress, and `:stop` records a sticky stop.

`sched.lisp` stores one intrusive link per global machine index, principal
FIFO heads/tails/counts/weight-one entries, four service flags, the calendar,
and its cursor. The concrete calendar is exactly four groups of sixteen
principals followed by commit, timer/grant, wake and maintenance (80 entries);
tiny has four principals then those services (eight entries). Tail insertion
is idempotent. All A4 connections use anonymous principal zero. Listener rows
occupy `[0, accept-credits)`, connections the following `C` indices, and scribe
one final index. A4 implements the declared per-run caps 4,096 bytes, 32
structural steps and four descriptors; its machine initializer currently
requires those exact execution-quanta profile values. Resident capacities
remain profile parameters.

The core owns the pool, outstanding operations, scheduler, machine columns,
trace ring and one control row. Harvest captures the outstanding owner before
finishing its operation row, returns input ownership, then changes machine
state and wakes its continuation. Posted results retain FIFO order; the clock
mailbox follows the posted FIFO, then sticky signals. One calendar visit
selects one bounded continuation; new machines enter before the selected
machine's own tail requeue. Resource waits are separate from runnable links;
operation/output-credit waits have a FIFO, and the sole pool-waiting scribe
has a reserved wait reference. Adapter-only waits do not keep `:more` asserted.

Echo reserves its RX slot when accepting a connection, receives into that
slot, and sends the received range itself. A short send issues the remaining
range as a new operation. Terminal results and external borrow releases are
tracked independently; reset, row reuse and slot release wait for both. Null
connections discard the received range. Listener credits each retain at most
one pending accept; an accepted capability that cannot obtain a connection
row and RX slot is closed. Scribe encodes the A3 sector format incrementally,
writes, waits for its fence, reads and verifies; failed write/fence outcomes
stop the probe without retry. Its `completed` frontier advances only on the
successful fence, and `verified` advances after complete readback.

`fn2-request-wake` coalesces the earliest explicitly registered wake
requirement. The timer/grant service emits `ArmWake` with dedicated u60
deadline and observation-generation fields; each new clock view advances the
token, with stop at exhaustion. The simulator keeps one replaceable request,
retains the earliest deadline within a view, ignores stale views, and bounds
its virtual-time advance by that deadline. Layer A's machines do not yet use
a general timer heap. Trace and ServicePosture action payloads remain out of
scope.

Tracing uses a fixed-width ring sized to four times `(H+K)`, overwrites the
oldest entry and counts loss. Records include selection, work, additional wake,
and up to four ordered operation references copied from the outbox. TRACE
reconstructs its own list FIFOs and literal calendar, with observation-owner
and actual-output evidence; WORK sums transition certificates independently.
The work model counts byte work and structural units, plus fixed calendar
and return overhead; measured CPU is a separate acceptance result. The owed
refinement relation `fn2-representation-relation` is currently equality of
the complete concrete and reference cores, including the action ring.

## 6. Simulator and checkers (contract item 4)
Seeded PRNG (splitmix64-style over fixnum halves); profile, seed, observation order, fault choices
and revision recorded per run; the fault classes of the brief, each with a per-run probability
drawn from the seed (swarm testing); death at any action boundary and during the recovery stub.
**Recovery stub** (layer A only): the data file is sectors; a sector written by scribe carries
magic, its own address, a sequence number and a checksum; the stub classifies each sector as
never-written, valid, torn/corrupt or misdirected and the file as `intact / torn tail / damaged /
unknown` by ROUND2 §E.4's rules restricted to that format. Layer B replaces it.
Checkers implemented at bed9edc28: 3 of 11. OWN is an independent monitor. TRACE checks the
executor's own trace records against a list model of the calendar and FIFO rules (not yet against
an independent reference transition system: repair R3). WORK sums the machines' self-declared
per-run counts (not yet recomputed from the outbox: repair R5). ACCOUNT is not implemented
(`fn2-check` returns `:not-yet`); it is owed in A6 before layer D. The other seven report
`:not-yet` until their layers. (Corrected 2026-10-28 after the Fable review, REVIEW-20261028.md
finding 2: an earlier revision of this paragraph claimed ACCOUNT was implemented.)

**A3 scribe format.** The probe is append-only, with one record per 4,096-byte
sector. Fields are little-endian u32: magic `0x324e4653` at byte 0, version `1`
at byte 4, the sector's zero-based address at byte 8, sequence `address + 1`
at byte 12, and checksum at byte 16. Bytes 20–4095 are payload. The checksum
is FNV-1a-32 over all 4,096 bytes with bytes 16–19 treated as zero. An all-zero
sector is never-written. The address and sequence encodings reserve sequence
zero; this probe format is replaced by layer B, not a persistent namespace
limit for fn2. `A-INTEGRITY-EVIDENCE` restricts use of this checksum to evidence
against the simulator's accidental faults; it makes no cryptographic claim.
Recovery receives an explicit acknowledged contiguous sequence frontier;
sector validity alone does not establish acknowledgement.
`fn2-recover-start` / `fn2-recover-step` retain only scalar scan progress;
each step reads one sector and writes no storage. A death discards that
progress and starts again. `fn2-recover-stub` uses the same step to scan the
whole supplied byte image.

**A3 fault-profile encoding.** The simulator reserves 26 u8 probability
cells, one per fault class. An enabled class draws a threshold in `1..64`
at run initialization; a later choice selects a class and compares a
`0..255` draw with that threshold. A successful choice spends one unit of
the run's fault budget. `:broad` enables every class, `:none` disables them,
and `:crash-only` enables fragmentation, short sends, delay, tears, fail-slow,
process death and release ordering. IDs `0..25`, in order, are fragment,
short-send, delay, reset, half-open, nonreading, read-io, bitrot, misread,
miswrite, lying-flush, tear, no-space, dead, fail-slow, crash,
monotonic-jump, realtime-back, duplicate, stale, forged, overcount,
malformed, flush-io, short-write and release-order; `26` means no fault.
Fault-choice counters count selections, which may be inapplicable to the
selected operation; they are not physical-effect coverage claims.
The 64-entry observation ring uses event tags `256` for clock observations
`257` for fault choices, and `258` for bytes drained by simulated clients;
operation results retain A2's event codes. Client-byte records put the connection
index/nonce in the op/gen fields, byte in count, and monotonic time in aux0. Each
record folds all ten scalar fields into the rolling u32 digest, splitting
u60 fields into two u32 halves before multiplication.

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
- A2 boundary details: the tiny calendar has 8 entries; row conservation includes retired rows; a release harvested before its terminal leaves the op submitted; ArmWake/Trace/ServicePosture finish at acknowledgment because they have no result event; clock bits 0/1 mean realtime-valid/negative and bits 2/3 record backward/malformed input, with a retained monotonic high-water and separate saturating rejected count.
