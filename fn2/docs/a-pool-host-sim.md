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
| scheduler, executor loop, listener/connection/scribe machines | `fn2/books/executor.lisp` (+ `fn2/books/machines-a.lisp`) | ACL2 book, guard-verified |
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

## 2. Column widths (decision A-WIDTH-PER-COLUMN)
fn2 has **no fixed word**: width is a per-column property of the DSL. Native
`defcolumns` kinds include `:u64`, stored in `(unsigned-byte 64)` stobj arrays.
Arithmetic above `2^62` allocates in SBCL, so hot counters default to `:u60`;
a `:u64` column on a served path must record a `:why` explaining its width.
The DSL requires this for every `:u64` declaration and records it under
`:column-reasons` in the column registry.
Widths beyond 64 bits use a `(hi, lo)` column pair or a pool range. Pair comparison
and increment-with-carry operate on the columns without constructing one wider
resident integer. `defwide-columns` declares `hi` and `lo`, with `:u60` limbs
by default (120 bits), or justified `:u64` limbs (128 bits). Its `-COMPARE`
returns `:lt`, `:eq` or `:gt`; `-INCREMENT` returns `:ok` or `:exhausted`,
leaving an exhausted pair unchanged. Planet-scale identity is content hashes in the pool and
`(history incarnation, local sequence)` per STORAGE-DESIGN, never one wider counter.
An **incarnation column belongs beside any counter that could wrap**. The pair
`(incarnation, counter)` is the identity; a counter at its limit retires and the
incarnation advances, never wrapping into a previous identity. Incarnation
exhaustion retires the namespace rather than reusing it. This extends the pool's
existing generation-retirement discipline: a slot at the profile's generation
limit retires. The current pool uses `:u60` generations and does not yet advance
an incarnation; that is an implementation choice, not a fixed-word ruling.

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
**Boundary validation, internal assertions (R5d).** Validate external scalars at
`fn2-post-result`, `fn2-post-clock`, `fn2-outbox-ack` and the adapter boundary.
Inside the core, guards and `mbt` carry established invariants. A residual
impossibility stops the executor with a named reason; it must never masquerade
as successful progress or an empty observation. Ordinary resource exhaustion
before reservation remains backpressure. After reservation, an unsuccessful
descriptor update or enqueue is corruption. At harvest, a failed input loan
completion, output borrow release or operation finish stops before the machine
can observe the result. The retained state is evidence, not a rollback or a
successfully released resource.

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

**Decision A-STORAGE-ABI (R4).** The core observes an I/O effect only at its
completion, when the result is harvested. The simulator's completion-time,
reorderable semantics is the contract: in-flight operations can complete in
any order, and a read issued while a write to the same sectors is in flight
may observe either value. A completed read is an observation in its own right;
it does not establish that the overlapping write has completed or is durable.
Only the completed fence's specified coverage establishes ordering and
persistence (§E.3: complete dependencies, then the covering barrier).

**The native adapter must obey this sentence:** an adapter may execute an
operation physically at any time between acknowledgement and posting its
result, but it must not make an effect observable to the core through any
other path before that result is harvested, and the core must not rely on any
ordering of in-flight operations other than what a completed fence establishes.
Physical input fills remain under the exclusive loan until harvest; neither
posting a result nor seeing bytes in the pool authorizes a core read. Physical
write completion alone authorizes neither publication nor durable acceptance.

**A5 re-do item.** The parked `fn2/a5-native-wip` adapter executes storage
operations inline during `fn2-native-take`, after `fn2-host-outbox-ack`, and
queues their results for later posting by `fn2-native-post-completions`.
That is a legal schedule, including its stronger physical ordering. It needs
no asynchronous storage rewrite to satisfy this decision. Preserve the
acknowledge/execute/post/harvest boundary, update its machine accessors to the
R4 declarations, and retain death cuts around each boundary. Confirm that no
native status/read path exposes an unharvested input or treats inline write
success as a durable core outcome. Future workers/io_uring may reorder freely
under this same contract; their fence implementation must establish §E.3
coverage without assuming take order.

## 5. Executor (contract item 5)
`fn2-turn` calls `fn2-concrete-turn` / `fn2-concrete-loop`, the bounded
dispatcher over `fn2-transition` and the intrusive scheduler;
there is no fusion. A turn stops at the first exhausted `H`, `K`, or `Aturn`
budget, or when nothing eligible remains. Results are `(mv status nobs nvisits
nactions fn2-core)`; `fn2-core-idle-deadline` supplies the accompanying sleep
bound (`2^60-1` means no requested deadline). `:more` preserves runnable work,
`:idle` permits adapter progress, and `:stop` records a sticky stop.

The control row's `stop-reason` uses the declared `fn2-stop-reason` enum;
`fn2-core-stop` retains the first reason. `:none` means no stop. The corruption
reasons are `:issue-unreserve`, `:issue-range`, `:issue-capability`,
`:issue-storage`, `:issue-cancel-target`, `:issue-wake`, `:issue-enqueue`, `:harvest-fifo`,
`:harvest-input`, `:harvest-output`, `:harvest-finish`, `:wake-bounds`,
`:wake-state`, `:machine-write`, `:machine-observation`, `:machine-phase`
and `:pool-release`. `:signal`, `:clock-exhausted` and `:work-overflow` name
the other stop paths. Scenarios print the enum keyword and require `:none`
for a green run; corruption controls require their specific reason. TRACE
compares this control state and must stop identically. A stopped harvest
delivers no observation to the machine. A malformed posted-FIFO head stops
instead of being mistaken for an empty FIFO, and waking an already queued
machine succeeds while scheduler bounds/state failures stop.

`sched.lisp` stores one intrusive link per global machine index, principal
FIFO heads/tails/counts, four service flags, the calendar,
and its cursor. The concrete calendar is exactly four groups of sixteen
principals followed by commit, timer/grant, wake and maintenance (80 entries);
tiny has four principals then those services (eight entries). Tail insertion
is idempotent. All A4 connections use anonymous principal zero. Listener rows
occupy `[0, accept-credits)`, followed by `C` connection rows and one scribe row.
The `fn2-echo` connection declaration has a per-row mode bit for echo or discard;
both modes share one free list and one admission count. A listener supplies the mode
to each admitted connection; the shared directory has no echo-mode flag. These disjoint global ID
ranges and their inverse are generated from the `defmachine` declarations.
Each kind has its own nested table. A4 implements the declared per-run caps 4,096 bytes, 32
structural steps and four descriptors. Every continuation returns through a
guard-checked `fn2-machine-finish` against those declared simultaneous caps.
`fn2-machine-with-work` preflights payload and descriptor callbacks through the
same generated `NAME-charge`; an overcap proposal yields before its mutation
body, preserving the continuation. Successful receive/read harvests charge the
exposed count before observation delivery. Every descriptor charges its range
length; scribe additionally charges its bounded fill, checksum patch and verify
chunks. A read/receive thus charges the requested descriptor span and, when it
completes, the bytes exposed. Internal chunks conservatively charge attempted
work on an early refusal. Structural units cover bounded scalar/queue updates
and checksum iterations; they are abstract cost units, not CPU instructions.
The independent checker measures visible I/O and observation work; internal
scalar operations and hashing remain code-reviewed bounds. Both loops reserve
one maximum transition before executing another, retaining the existing
`H*24 + K*4129 + 1` turn cost bound as harvest bytes consume that allowance.
Exhaustion returns `:more` with pending work retained. The machine
initializer requires those execution-quanta profile values. Resident capacities
remain profile parameters.

`defmachine` owns both phase dispatch and `:observes` event routing. Declarations
name functions, never pasted code forms. The fixed run convention is
`(id budget ROW-fields... fn2-core)`; observation handlers receive
`(id event outcome reason count aux0 aux1 ROW-fields... fn2-core)` and return
`(mv wake fn2-core)`. `ROW-fields...` are scalar values in declared column order,
recorded in the machine world table's `:calling-convention`. The generated entry
binds its own table once and reads its own accessors; it releases the child before
calling code that may update the parent core. Per-kind writes bind that child once
for the whole field batch. Initial values are constants or named functions of
`(slot base n gen)`. Each `:obligations` entry is explicitly `:owed`, references a
registered `defthm-owed`, or names a registered obligation generator; unknown hooks
are refused at expansion. The router validates the row's kind, generation and non-free
state before invoking the handler, then performs generic pending accounting.
Handlers see every completion before the pending decrement and own any event-cell
store; a handler may accumulate several completions before its machine runs.
Scribe retains its single event cell by storing in its own handler. An unrouted
event or a write to a field absent from the target kind stops the executor.
Per-kind phase-write macros reject another kind's
constants. Global field setters guard both the declared width and the presence
of that field in the target kind. Unknown kinds cannot pass the charge guard.

`books/assembly.lisp` is the sole served core instance. `defcorechild FIELD
STOBJ :init FORM :profilep FORM :why "reason"` in `core-children.lisp` records
an ordered `fn2-core-children` world-table entry. `:init` returns the child
stobj, with `profile` and that stobj as its only free runtime inputs;
`:profilep` is a guard-verified predicate form over `profile`. The conjunction
of all those predicates and `fn2-profilep` must suffice to verify every init
call and establish each child's `-wfp`. Sizes come from the profile. The
registration requires a nonempty reason and rejects duplicate fields or stobjs.
Layer A registers pool, ops, sched, machines, trace, control through the same
declaration (`:order :foundation`), in that order. Generated machine-child
registrations follow (`:order :machine`), then other registrations in declaration
order (`:order :extension`, the default). No hand-maintained child list remains.

The registry generates `fn2-core`, its `wfp`, `init`, `profilep`, rectangular
read-over-write facts, `fn2-machine-core-child-shapes`, and the congruent
`fn2-ref-core` with every child's clone and copy. Reference difference includes
every state child. Only an explicit `:reference :environment` with `:why` opts a
child out: scheduler has an independent list relation, and trace is diagnostic
output checked separately. Pool byte comparison retains its live-byte domain.
B registers its existing `defcolumns` tables in a registration book that includes
`core-children`, then adds that book to `assembly-index`'s registration includes before
`fn2-machine-index-events`. For example, extents can use
`(defcorechild fn2-core-extents fn2-extents :init (fn2-extents-init-for profile
fn2-extents) :profilep (fn2-extents-profilep profile) :why "Persistent allocator
state across commit yields.")`; B owns those profile/init adapters and replaces assembly's A-only profile
smoke assertions with the node profiles when it requires new keys.

`machines-all.lisp` includes A's kind declarations; `assembly-index` includes B's
`machines-b.lisp`, and later D's kind and child books, after it. That ordered
include list determines kind tags and global-ID ranges. Index generation runs
only after all registrations. Other layers' continuation event macros go in
`assembly-callbacks`, after the core/access events and before
`fn2-machine-dispatch-events`. Its run,
charge and observe arms, including `fn2-machine-refuse-phase`, receive the same
`fn2-core`; D continuations borrow D's registered children with `stobj-let`,
without extra stobj arguments or per-call allocation.

Pool, vocab, sched, machines, machines-a and machines-directory are library
books. Core, machine access, scribe/run, dispatch and reference-state provide
instance event macros; including them creates no core instance. Assembly expands
those macros once, through `assembly-index`, `assembly-core`, `assembly-access`,
`assembly-callbacks`, `assembly-dispatch`, and `assembly-reference` in that order.
`assembly.lisp` retains the public include and profile assertions. The separate
test instance uses the same six boundaries in `core-child-assembly-*` books.
Executor-access/executor and reference include assembly
(the reference through executor); simulator consumers follow those instance
books. Adding a D registration changes assembly and its consumers, without
recertifying the A library books. `tests/core-child-assembly.lisp` certifies a
separate test instance using the same events, since a certified assembly's
expansion is closed. Its external test registration never reaches the served
assembly.

The scheduler accepts the assembled row count, stores no connection/scribe IDs
or unused weights, and derives calendar length as `p + 4*ceiling(p/16)`. Runtime
probe IDs come from the directory's generated kind-base map. `fn2-init-executor`
sets listener admission mode through `fn2-listener-set-mode-all`; admission copies
that mode into each connection row. Both modes share the connection free list,
and there is no second bulk connection-mode initializer. Harvest captures the outstanding owner
before finishing its operation row, returns input ownership, then changes
machine state and wakes its continuation. Posted results retain FIFO order;
the clock mailbox follows, then sticky signals. One calendar visit selects one
bounded continuation. Resource waits remain separate from runnable links.

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

`books/reference.lisp` supplies the separate reference transition system.
Its ordinary lists hold the literal ROUND2 §C calendar, cursor, one FIFO per
principal and four service flags. `fn2-ref-transition` consumes one posted
result, clock mailbox or sticky signal, in that order; otherwise it visits
one calendar entry and runs its selected continuation or service. Empty
visits advance the cursor. Wakes returned by observation/run semantics append
at the tail, followed by the running machine's requeue; repeated wakes retain
position. It never reads the concrete scheduler's links or trace records.
`fn2-ref-turn` independently accumulates work and stops at H/K/Aturn, the turn
work allowance, or no eligible work. Machine observation, bounded runs, grants,
clock/ArmWake semantics and the scalar cost-ceiling predicate are shared.
Selection, ordering, bookkeeping and budget counters remain independent.

`fn2-ref-core` is congruent to `fn2-core`, including its nested children.
`reference-state.lisp` derives copy/comparison access from the column registry.
TRACE steps two persistent congruent cores at every turn. The reference
cursor, FIFOs, machine state, pool ownership/fills and control state advance
only through reference transitions. At the adapter boundary, the two sides
receive the same posted operation state (including submission acknowledgments,
clock and signals) and physically written input-loan bytes. Initialization and
process-death reset establish a fresh copy; no completed turn is copied back
into the reference. Four service flags start at zero; layer A only clears them.
A mismatch fails the scenario at that turn and prints the first differing
projection field.

`fn2-representation-relation(concrete, reference-core, reference-lists)`
compares ordered outbox entries and every operation field (including kind,
OpRef, owner, range, phase and reservations), every machine field, every pool
metadata field (including state/fill), readable bytes and input prefixes named
by pending successful/short completions, and control state including work
counters. It also compares concrete FIFO contents, links, tails, calendar
entries/position and service flags with the reference lists. Uninitialized/stale
bytes beyond those semantic prefixes, diagnostic trace records and the unused
reference intrusive scheduler are excluded. The refinement keystone is owed,
not proved; evaluated teeth compare real turns and swap one reference FIFO.

The fixed-width trace ring records per-run charges and selection. WORK checks
its cap/accumulator arithmetic and independently measures visible work (R5b):
outbox growth and the sum of newly emitted descriptor range lengths, plus the
successful receive/read ranges removed from the pre-turn posted FIFO. FIFO and
mailbox consumption supply the observation count. Scheduled and harvested byte
charges are checked separately, so fill work cannot mask an uncharged harvest.
The certificate is `(observations visits descriptors charged-bytes steps
outbox-bytes harvested-bytes)`. TRACE uses the independent reference scheduler.

## 6. Simulator and checkers (contract item 4)
Seeded xoshiro128** PRNG; profile, seed, observation order, fault choices
and revision recorded per run; the fault classes of the brief, each with a per-run probability
drawn from the seed (swarm testing); death at any action boundary and during the recovery stub.
**Recovery stub** (layer A only): the data file is sectors; a sector written by scribe carries
magic, its own address, a sequence number and a checksum; the stub classifies each sector as
never-written, valid, torn/corrupt or misdirected and the file as `intact / torn tail / damaged /
unknown` by ROUND2 §E.4's rules restricted to that format. Layer B replaces it.
Checkers implemented at bed9edc28: 3 of 11. OWN is an independent monitor. TRACE compares each concrete turn against the independent
list-scheduled reference transition system (repair R3). WORK compares per-run
charges against independent outbox/FIFO evidence (repair R5b), retaining all caps.
ACCOUNT is not implemented
(`fn2-check` returns `:not-yet`); it is owed in A6 before layer D. The other seven report
`:not-yet` until their layers. (Corrected 2026-10-28 after the Fable review, REVIEW-20261028.md
finding 2: an earlier revision of this paragraph claimed ACCOUNT was implemented.)

**Real read monitoring (R5b).** Acceptance installs `tests/own-read-hook.lsp`
around `fn2-core-read` and `fn2-core-write`. Each scenario binds its concrete core
and OWN monitor; reference-model reads are excluded. The hook checks scribe
verification reads against OWN's initialized-byte and loan provenance, and
records reads by machine kind. Listener and echo/null currently perform no core
reads. Controls first require the real reader to refuse past-fill and leased-in
reads safely, then mutate its result to `:ok`; OWN must reject both mutations.
A legal-read control and a separate-core control check the hook itself. This is
test instrumentation only; the served path has no hook. CPU figures printed
with `own-hook=ON` include its cost. **R6 must hook every new range-read primitive
and report its entire examined range to OWN.**

**Storage stamps and fence slots (S1).** `stamp` identifies the cached
completed-write version; `snapshot-stamp` freezes it at fence submission.
`durable-stamp` records the last version established by an honest fence or
completed FUA, not the provenance of arbitrary media bytes. A live tear changes
media bytes without advancing that stamp, so an honest fence still persists its
covered write. Dirty means `stamp > durable-stamp`; a reopened stale cache never
authorizes a crash landing over a newer durable version, even beside dirty bytes
in the same 512-byte unit. FUA persists only its own request.

`:fence-slots` defaults to 1 per simulated storage domain; both tiny and concrete
profiles specify 1, independently of `O`. Operation tokens map to occupied slots;
a second capture with no free slot returns `:exhausted` without changing the
first snapshot. The adapter retains the unacknowledged outbox action for retry.
Completion (honest, lying or failed) and cancellation release the slot; death and init
invalidate all slots. Each slot stores one full byte image and one u60 stamp
per byte: 147,456 bytes for tiny's four sectors, 589,824 for concrete's sixteen
sectors on SBCL (u60 arrays use 8 bytes per element), excluding array headers and
8 bytes of owner metadata per slot. `:sim-sectors` scales this cost linearly.

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

**Fault selection and landing coverage (R5d).** The simulator reserves 26 u8
probability cells, one per fault class. An enabled class draws a threshold in
`1..64` at initialization. Each advance chooses its flight first, then a class
applicable to that flight's kind and stage, and compares a `0..255` draw with
the threshold. A successful choice spends one fault-budget unit; it does not
increment coverage. `:broad` enables every class, `:none` disables them, and
`:crash-only` enables fragmentation, short sends, delay, tears, fail-slow,
process death and release ordering. IDs `0..25`, in order, are fragment,
short-send, delay, reset, half-open, nonreading, read-io, bitrot, misread,
miswrite, lying-flush, tear, no-space, dead, fail-slow, crash, monotonic-jump,
realtime-back, duplicate, stale, forged, overcount, malformed, flush-io,
short-write and release-order; `26` means no fault.

`fn2-sim-land` increments a class only at its effect: a shortened transfer,
changed network/storage state, delayed flight, changed clock, process death,
or injected observation. A full-length transfer selected as short, a cancelled
physical operation, an invalid capability or a wake that preempts the flight
does not earn the flight's physical-effect count. Broad acceptance prints and
requires at least one landing for each class, including storage classes;
matched fault controls separately test the counter's positive and negative
cases. Repeated fixed seeds remain the regression gate; swarm mode prints a
run-time seed for replay and runs additional pool scenarios and a short echo.
The fixed driver keeps 10,000 tiny and 1,000 near-limit pool runs and the
1,000-connection echo seed `20261028`. Its device phase runs 16,384 seeded
read/write/fence/receive trials, restarting devices between trials so a dead
device cannot starve later classes. Pending storage bytes permit actual tears;
queued network bytes permit a receive to reach its fragmentation limit. Broad
coverage sums echo and device landings; matched fault controls do not contribute.

Run the full fixed acceptance, including R1 coverage/liveness, R3 differential
checks and R5b WORK/OWN controls, from the repository root:
```sh
nohup env FN_ACL2_SLOT_DIR=/tmp/fn2-a4-acl2-slots FN_ACL2_SLOTS=6 timeout 3600 tools/acl2 < fn2/tests/sim-layer-a-a4-driver.lsp > build/r5b-acceptance.log 2>&1 &
echo $! > build/r5b-acceptance.pid
```
Keep `FN2_SWARM` and `FN2_SWARM_SEED` unset for this fixed gate. The liveness
bound applies to this driver's at most 1,024-byte clients and one round-robin
adapter service per turn. Its at most one receive exposure plus three
observations fits concrete's `H*24 = 3072` allowance, leaving all 64 visits
available; larger or more concurrent input needs a new bound. R4's machine
port and late-child composition controls are in `tests/machines-a-unit.lisp`
and `tests/core-child-unit.lisp`; certify those alongside `tests/work-controls.lisp`.

Run swarm mode from the repository root:
```sh
nohup env FN2_SWARM=1 FN_ACL2_SLOT_DIR=/tmp/fn2-a4-acl2-slots FN_ACL2_SLOTS=6 timeout 3600 tools/acl2 < fn2/tests/sim-layer-a-a4-driver.lsp > build/r5d-swarm.log 2>&1 &
echo $! > build/r5d-swarm.pid
```
It prints a clock-derived seed before loading scenarios, then runs the common
controls, 100 tiny and 20 near-limit pool scenarios, and a 20-connection echo
with the existing 200-connection liveness phase. Set `FN2_SWARM_SEED=<decimal>`
to replay that seed. Omit both swarm variables for fixed acceptance.

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
row in `fn2/docs/OWED.md` with its teeth. Teeth name zero-argument evaluating
functions; the corresponding unit books assert that each exists and returns exactly
`t`. `fn2/tools/certify.sh --export-owed` regenerates `OWED.md` from the admitted
world table after those units certify; edit registrations, never the generated file.
Layer A owes: pool generation/staleness, byte-fill,
no-reuse-while-borrowed, conservation; outstanding-table result reservation; turn bounds (WORK);
the refinement obligation of EXECUTION-MODEL §4 over `fn2-turn` and `fn2-ref-turn`.

## 9. Departures and open items
R5b retains W1's one-minute limit: all 73 books in the measured layer-A closure
certify below 60 s on the laptop with two jobs, including the new WORK controls.
The maximum is `sim/sim-adapter-base` at 48.16 s. `build/REPORT.md` lists every
book before and after; the 72-book before column is W1's source-identical baseline.

- Current pool generations use `:u60`; widths are chosen per column (§2).
- A send carries one range in layer A (ROUND2 D.3 allows four); the descriptor reserves the field
  width for four.
- A2 boundary details: the tiny calendar has 8 entries; row conservation includes retired rows; a release harvested before its terminal leaves the op submitted; ArmWake/Trace/ServicePosture finish at acknowledgment because they have no result event; clock bits 0/1 mean realtime-valid/negative and bits 2/3 record backward/malformed input, with a retained monotonic high-water and separate saturating rejected count.

## 10. DSL metatheory decisions

DM0a adds the internal `books/declare.lisp` library, included by `columns` and
`owed`. The existing four tables retain their payloads; qualified identities
and `fn2-decl-row`/`fn2-decl-rows` give them one read interface. Manifests record
actual admitted signatures, including DEFSTOBJ's generated names and local
facts inspected before their encapsulate closes. Conflicting identities or
definitions are soft refusals; identical declarations and shared artifacts
record reuse. No new author-facing form is introduced. Callback maps, staged
function resolution and per-input seals belong to DM0b; the obligation store
belongs to DM1. Current artifacts are emitted in `:declaration`; this manifest
does not claim the later assembly's artifacts as declaration emissions.

Ember's five DSL-METATHEORY §8 decisions are accepted:

1. Shared declarations are allowed for representation/compiler refinement, with recorded sharing, independent consequential-behaviour contracts and the shared-handler mutation control.
2. Complete arm-effect and cost checking requires a restricted arm language; outside calls have declared escapes whose contracts remain owed until discharged.
3. Export requirements, bound statements, admitted proofs and check coverage as separate counts; checked obligations remain owed.
4. Build each new form with its first real consumer; DM0a adds no user-facing form and `declare.lisp` remains internal.
5. Adopt the Opus timing position: DM1 precedes R7, creating its arm obligations in `fn2-squares` once, with their schema and contract.

The seat resolves §9's third open item in that order: **W1, R5b, DM0a, DM1,
DM0b, then the re-cut R5e and R7**. R7 is the first producer of `:bound` and
`:invariant` rows and D's first arm-contract consumer. Migrating those rows a
second time is pure churn; DM1's estimated five days are smaller than R7's
re-migration plus its review. This supersedes the design's still-written
“DM1 after R7” sequence, not its registry or contract requirements.
