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

The ABI's effect theory uses nondeterministic choice `⊕` (associative,
commutative and idempotent). These are its named equations:

- **E1 — posting order is free.** For outstanding operations `a`, `b` with
  no completed fence between them, `post_a ; post_b ⊕ post_b ; post_a`,
  whatever their submission order. This applies to socket and storage effects.
- **E2 — an overlapping read sees either.** While `write(l, v)` is outstanding,
  `read(l) = return old(l) ⊕ return v`, per declared write unit.
- **E3 — a read orders nothing.** `read(l) = return v` establishes no equation
  about the completion or durability of the overlapping `write(l, v)`.
- **E4 — a fence is the only order.** If all writes in `W` completed before
  submission of a successful `fence(W)`, every subsequent crash keeps `W`'s
  bytes, modulo the declared faults (including `lying-flush`).
- **E5 — death after acknowledgement.** Death between `fn2-outbox-ack` and
  posting the result chooses a subset of the submitted effects to survive,
  with tears per declared write unit: `crash = ⊕ survival(S)` over allowed
  subsets `S` of the writes since the last successful covering fence.

A lent input range being unreadable until harvest is a separate typing rule,
not an ordering equation. The simulator and native adapter must select outcomes
allowed by E1–E5; a particular schedule proves no stronger ordering guarantee.
Result reservation and generation checks tolerate E1; `harvest-byte-fill`
uses the input-loan typing rule and makes no E3 durability inference. Scribe's
`completed` frontier uses E4, while its `verified` frontier uses E2–E3 and
checksum evidence. Recovery's acknowledged frontier and uncertainty
classification use E4–E5: neither a valid sector nor readback alone establishes
acknowledgement. TRACE's storage projection compares a shared selected outcome
under E1–E5; it is not an independent storage implementation. WORK and OWN
bound or authorize accesses under any of those choices and assume no extra
posting order.

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

### 4.1 A5r: the native adapter redone *(design, statement first; the A5r commits rewrite it as built)*

A5r puts the served core (the listener admitting `fn2-conn`) on a socket, so that H's nntp S
form runs against a real TCP listener through the same session hook it uses for the simulator,
with no harness change. It replaces the parked `fn2/a5-native-wip` (6a6170a35, read as compost:
its FFI and mux are reused after review; its adapter structure is not, because it decided which
ops to start by kind inside the take loop and had no oracle). Four parts, landing in this order,
each under the whole-tree gate: the ABI change (4.1.1-4.1.2), the loop (4.1.3), the socket and the
session (4.1.4); the oracle (4.1.5) and the keystones (4.1.6) arrive with the loop.

#### 4.1.1 The Accept result carries the peer address
Today an Accept's terminal cell carries `count = 0`, `aux0 = cap index`, `aux1 = cap nonce`, and
nothing about the peer: D3's declared interim (d-machines-nntp.md §4.4, §8; the owed row
`fn2-conn-reader-only-interim`) is "every connection a reader, no per-address 400".

**Decision A5R-PEER-RECORD.** The peer address is a fixed-width *named record* posted with the
Accept's terminal cell, not two more aux words. Reasons: NNT-043 matches trusted ranges on up to
128 bits of the source address by family, so a word pair cannot carry an IPv6 source; aux0/aux1
already carry the capability; and widening every cell (or every observer's argument list) would
change every posting site and every observe callback for one event kind. D asked for "an
address word pair in the result's aux fields" (§8); this gives D the address with its family
and port instead, through the same cell and the same harvest.

- **Op-row columns** (vocab.lisp, cell 0 only): `peer-family` (`:enum fn2-peer-family (:none
  :inet :inet6 :local)`), `peer-port :u16`, `peer-w0 peer-w1 peer-w2 peer-w3 :u32` (the address
  in network order, most significant word first). `:inet`: `w0` is the IPv4 address and
  `w1 = w2 = w3 = 0`. `:inet6`: all four words. `:local` (a Unix-domain peer; its credentials
  are E6's) and `:none`: port and words zero. `fn2-ops-clear-row` zeroes them (family `:none`).
- **Posting.** `fn2-post-accept-result (slot gen outcome reason cap-index cap-nonce family port
  w0 w1 w2 w3 fn2-ops)`: bounded validation of the peer record (`fn2-peer-recordp`: family in
  the enum, port and words in width, the per-family zero rule, `:none` unless the outcome is
  `:done`), then exactly `fn2-post-result 0 slot gen :accept-result outcome reason 0 cap-index
  cap-nonce` on an op whose kind is Accept and whose cell 0 is unposted (checked first), then the
  record into the row's peer columns iff cell 0 became posted (acceptance is read from the cell,
  never from the stray counter, which saturates). Any refusal is a stray and changes nothing else
  (T6). The existing `fn2-post-result` with an
  `:accept-result` leaves the record `:none`: that is the simulator's fixed opaque value and
  every existing caller (the simulator, the cw adapter, the units) is unchanged, so A's drivers
  and D's scenario see identical cores.
- **Harvest.** `fn2-harvest-next`, on harvesting a cell 0, copies that row's peer columns into
  the ops child's observation latch (`fn2-ops-seen-peer-family`, `-port`, `-w0`..`-w3`, extra
  fields) before `fn2-op-finish` recycles the row; every delivered cell writes the latch, a
  release cell `:none`, so it always describes the observation being delivered. The reference
  turn runs the same `fn2-harvest-one` on its copied core and the columns' generated copy/diff
  carries the extra fields, so TRACE compares the latch too (shared code: TRACE checks
  composition here, not peer extraction, which the host unit checks). The latch is in
  `fn2-ops-nonstray-snapshot`, so a stray provably leaves it unchanged.
- **Observation.** `fn2-core-observed-peer (fn2-core) -> (mv family port w0 w1 w2 w3)`, a
  defcost'd core read. The listener gains six fields (`peer-family peer-port peer-w0 .. peer-w3`);
  `fn2-listener-observe-accept` writes them from the latch with the capability, and a failed
  Accept leaves them `:none`.
- **Into the connection.** Admission's `:copy` carries listener fields into the admitted row,
  from the listener's offer `*fn2-machine-listener-offer*`, which gains the six fields (and
  `fn2-machine-admit` six arguments, passed by `fn2-listener-admit`). A kind that copies none of
  them is unchanged. D carries the record by adding the six fields to `fn2-conn` and naming them
  in its `:copy`; the exact form goes to D through main with the commit. Carrying the address
  enables D's policy (per-address 400, the peer bit); it establishes neither, so D replaces its
  interim row when that policy lands, not when the fields arrive.

#### 4.1.2 The result cell format between core and adapter
One table, the adapter's contract per terminal event (cell 0) and the release (cell 1). "Sets"
are `fn2-event-statusp`'s per-primitive sets; "zero" means the adapter must post 0 (the core
validates widths and the listed relations; ENVELOPE, 4.1.5, checks every column).

| event | outcome / reason | count | aux0 | aux1 | peer |
|---|---|---|---|---|---|
| accept-result | done, cancelled / failed {exhausted, aborted} | zero | cap index (done), else zero | cap nonce (done), else zero | record if done, else `:none` |
| connect-result | done, cancelled / failed {refused, unreachable, timed-out, reset} | zero | cap index (done), else zero | cap nonce (done), else zero | `:none` until E4 |
| receive-result | done, cancelled / failed {reset, closed} | done: octets written at the loan's start, `1..range-len`, and 0 is EOF; failed or cancelled: zero | zero | zero | `:none` |
| send-result | done, short, cancelled / failed {reset, closed, pipe} | done: `range-len`; short: octets consumed, `< range-len`; failed or cancelled: what was consumed | release-pending (1 only if the op may release) | zero | `:none` |
| close-result | done | zero | zero | zero | `:none` |
| read-result | done, short, cancelled / failed {io} | done: `range-len`; short: `< range-len`; failed or cancelled: zero | zero | zero | `:none` |
| write-result | done, cancelled / failed {io, no-space, uncertain} | done: `range-len`; a partial write is failed/uncertain with its known progress | zero | zero | `:none` |
| fence-result | done, cancelled / failed {io} | zero | zero | zero | `:none` |
| cancel-result | done, cancelled, not-found, not-cancellable | zero | zero | zero | `:none` |
| tls-result | done, cancelled / failed {handshake, reset, timed-out} | zero | zero | zero | `:none` (E1) |
| entropy-result | done, cancelled | done: octets written, `<= range-len`; cancelled: zero | zero | zero | `:none` |
| borrow-released (cell 1) | done | zero | zero | zero | `:none` |

The core validates a superset (widths, the per-primitive status sets, `count <= range-len` for
transfers, the release flag's authority, the peer record); the table is the canonical production
the adapter must make. The simulator's normalizer `fn2-sim-terminal-values` produces a subset of
it: it never produces Accept `aborted`, Connect's failures, Send `pipe`, TLS `reset` or
`timed-out`, or Cancel `not-cancellable`. The native adapter normalizes through the same logical
function (4.1.3), so every native completion is one the simulator could post. A release may be
posted, and harvested, before its terminal (vocab.lisp's release-first rule); only the whole op's
history must agree (a release only where the terminal says release-pending).

Capabilities: a connection capability is `(index, nonce)` issued by the adapter at Accept; an
index is reused only with a strictly larger nonce, and a nonce never wraps (an index at
`2^32 - 1` retires). Unsolicited inputs are unchanged: the clock mailbox, the sticky signal word.

#### 4.1.3 The native event loop over the served core
`fn2/host/ffi.lisp` (syscalls, mux: epoll on Linux, poll(2) on darwin, a self-pipe for signals)
and `fn2/host/adapter.lisp` (the loop), raw SBCL loaded by a session script behind its trust tag;
`fn2/books/host-boundary.lisp` (certified) gives the loop scalar entry points over the live
core: outbox peek/ack, a descriptor's fields, the validated physical span of its loan
(`fn2-host-op-span`), the posts, the finish of a resultless op, the stop reason and idle
deadline, and the result normalization `fn2-host-result` (physical kind, syscall return, errno
class, length -> the cell's words, by the simulator's `fn2-sim-terminal-values`). The loop
implements physical scheduling and reports observations; ACL2 owns their interpretation.
One thread; per op slot a host record in one of `waiting`, `closed-waiting` (its capability was
closed under it: its loan is retained until the core cancels it, and no syscall result is
invented), `completed`; per capability index an fd, nonce, the physical peer (captured from
`accept(2)`'s sockaddr) and test counters. One iteration:

1. post the clock reading (the coalesced mailbox); post at most `H` completed results in
   completion order; post the sticky signal if a handler set it;
2. `fn2-turn`; `:stop` ends the loop;
3. take the outbox prefix (at most `Aturn`): peek, copy the descriptor and its validated span,
   `fn2-host-outbox-ack 1` (from here the op is submitted and the adapter owns its execution);
   ArmWake/Trace/ServicePosture are `done` at ack and the loop reclaims them with
   `fn2-host-op-finish` (no result event); every other kind waits;
4. interests to the mux: a waiting Accept/Receive wants readable, a Send writable, a Close and
   every non-socket kind is started now (Close: unregister, `close(2)`, then retire every other
   waiting op on that capability *without* inventing a syscall result: the core cancels and
   harvests them; storage kinds stop the host by name until the storage backend lands with
   B's durable POST, because the served core issues none yet; Connect and TlsStart complete
   `failed`/`refused` and `failed`/`handshake`: no facility, explicit, never simulated; Cancel
   checks its target's generation and state: a waiting or closed-waiting target gets its
   terminal `cancelled` result, then the Cancel `done`; else the Cancel `not-found`);
5. wait: timeout 0 if the turn said `:more` or completions are queued, else until the core's
   idle deadline (ArmWake) or a control/signal wake;
6. for each ready descriptor, one syscall for one of its waiting ops (one readiness report is
   one syscall, never a loop to EAGAIN; several Accepts on one listener share a report and the
   others stay waiting), its result queued for step 1. EAGAIN after readiness leaves the op
   waiting (the simulator's zero-progress would-block), never a failure; EINTR is retried at most
   a fixed number of times, then the op stays waiting. A Receive writes only inside its loan at the
   span's address; a Send reads only its borrowed span; neither touches the range after posting.

Death cuts: `FN2_KILL_AT=N` exits at the Nth boundary among take, ack, syscall, post (the
compost's `fn2-native-boundary`), so a kill at every boundary is a test row, not a claim.
This loop is the simulator's adapter with the physical world choosing the schedule: posting
order is the completion order (E1), a byte enters the core only at harvest, and nothing else is
observable.

#### 4.1.4 The socket and the session H speaks
`fn2/tests/native-session.lsp` (LD script: includes the served books and check-wire/check-envelope,
`:q`, loads `fn2/host/*.lisp`, initializes the core with `*fn2-conn-wire-profile*`, binds
`127.0.0.1:0`, prints `@@FN2SS ready <port> 0 0@@`, runs the loop) and
`fn2/tests/surface/fn2_native_session.py` (the hook
`FN2_SURFACE_SIM_NNTP=fn2.tests.surface.fn2_native_session:session`, the same `open / send /
close / stop` as `fn2_sim_session.py`; `sim_target.py` and the S form are untouched). The client
side is real TCP; a control line on the node's stdin (fd 0 is in the mux) is the only addition:

- `sync PORT SENT EOF` asks the node to answer `@@FN2SS quiet OUT CLOSED CAP@@` at
  *quiescence for that connection*: the capability whose physical peer port is PORT has posted
  Receive results for SENT octets (and its EOF when EOF is 1), or the node has closed it; and one
  whole iteration then ended (after its immediate ops and readiness handling) with no completion
  queued, the turn `:idle`, the outbox empty, and a zero-timeout wait reporting no descriptor
  ready for a waiting op. OUT is the cumulative count of octets the node's Sends moved on that
  capability, CLOSED whether the node closed it, CAP its incarnation (index and nonce).
- The client never trusts the marker's timing for the bytes: after `quiet` it reads its socket
  until it holds OUT octets in all (and EOF when CLOSED), so a marker overtaking the socket
  output cannot cut a reply. It drains its socket concurrently while sending, so the node's
  Sends never block on a full client queue.
- `open()`: connect, `sync PORT 0 0`, read what arrived (the greeting, or 400 and EOF).
- `send(id, octets, chunks)`: per chunk, `sendall` then `sync`: a chunk is a delivery barrier,
  as in the simulator session (which feeds bounded pipes and may also cut one chunk into several
  Receive results); TCP keeps no boundary within a chunk, so one chunk may reach the core as
  several Receives. Then the octets that arrived (read to OUT) and whether the node closed.
- `close(id)`: `shutdown(SHUT_WR)`, `sync PORT SENT 1`, the octets that arrived.
- `stop()`: `stop` on the control line; the loop ends; WIRE runs on each connection's client-side
  transcript (sent, received, closed) sent back as one REPL form, and ENVELOPE on the recorded
  boundary trace; the same `@@FN2SS wire ID VERDICT@@` lines as the simulator session (an
  ENVELOPE refusal is reported as every connection's verdict, so the case fails at cleanup).

Replies equal the simulator session's when the core's replies are fragmentation-invariant (T8,
owed, checked by conn-unit's every-split fixtures) and the schedule is fault-free; DATE reads the
real clock, so DATE lines (and nothing else: D's profile has no timing-dependent closure before
D7's deadlines) may differ.

#### 4.1.5 ENVELOPE: the oracle that the native loop refines the simulated one
`fn2/sim/check-envelope.lisp`, an execution checker. The native loop in test mode records its
boundary trace in a preallocated ring (overflow refuses the run, never truncates it):
`(:clock mono real flags)`, `(:signal bits)`, `(:turn status)`, `(:take op gen DESCRIPTOR)` with
the whole descriptor (kind, capability, range identity, offset and length, storage offset, fua,
may-release, cancel target, wake payload), `(:ack n)`, `(:finish op gen)`, `(:post cell op gen
event outcome reason count aux0 aux1 peer octets)` with `octets` the bytes the syscall moved (a
Receive's written prefix, a Send's sent prefix). ENVELOPE replays the trace into a fresh core
from the same profile (`fn2-envelope-replay`: each `:turn` a `fn2-turn`, each `:take`/`:ack` a
peek and ack, each Receive's octets written under its loan through `fn2-pool-adapter-write`,
each post through the core's own entry) and checks, at every step:

1. **The schedule is legal.** Each take's descriptor equals the replay's outbox head; each post
   answers a taken and acknowledged op of the replay, at most once per cell, is accepted by the
   replay's core (no stray), and is in the allowed relation `fn2-host-result-allowedp` (4.1.2's
   table); the release history agrees per op; Accept capabilities are fresh pairs; a capability
   posts nothing after its Close result except the core's cancellations.
2. **The bytes are the clients'.** Per capability, the concatenated Receive octets are what its
   client sent, in order (all of it and then EOF when the client closed and the node read on);
   the octets each Send moved are the replay's own borrowed range bytes (read from the replay's
   pool, not from the trace), and their concatenation is exactly what the client received; the
   Accept's peer port is the client's local port.

ENVELOPE's controls (each breaks one premise, keeps the others, and is refused): a take whose
descriptor differs from the replay's; a post to an unacknowledged op; a count over the loan; a
reused capability; a release on an op whose terminal said no release; one flipped octet in a
Receive (asserted as an input-transcript mismatch, since many inputs share a reply); a Send whose
recorded octets differ from the replay's range. What ENVELOPE cannot check is that an
uninstrumented process records its actions faithfully: that is the environment premise.

#### 4.1.6 Keystones (`fn2/books/owed-host.lisp`, `defthm-owed` with teeth)
- `fn2-accept-peer-delivered` (family port w0 w1 w2 w3): from the initialized served core, an
  Accept posted with a valid peer record and harvested leaves the listener row holding exactly
  that record (runner `fn2-accept-peer-run`). Teeth: the positive record for each family; a
  negative where an invalid record (an `:inet` with `w1 /= 0`) is a stray and the listener's
  record stays `:none`.
- `fn2-native-envelope-refines` (trace): a legal native schedule is, at the wire, the canonical
  simulated one: `(implies (and (fn2-envelope-steps-ok-p trace) (fn2-envelope-date-free-p
  trace)) (equal (fn2-envelope-replay-wires trace) (fn2-envelope-canonical-wires trace)))`, where
  `steps-ok` is ENVELOPE's item 1 (legality only, no byte comparison), `replay-wires` the octets
  each connection's Sends carry in the replay, and `canonical-wires` the wires of D's
  `fn2-conn-wire-run` (the subject of T1 and T8) over the same clients' octets and Receive cuts.
  It says the core's output does not depend on which legal schedule the physical world chose, so
  T1/T8 proved over the canonical view transfer to the native run; ENVELOPE's item 2 is the
  per-run evidence that the native process's bytes are the replay's. DATE is excluded because
  the canonical view posts no clock. Teeth: a recorded native trace (fixtures through the loop,
  Accept, Receive, a short Send and Close all exercised) where both sides agree; a negative where
  a post outside the allowed relation makes the replay's wires differ.
- `fn2-conn-reader-only-interim` is D's row; it is replaced by D when the conn row carries the
  peer (4.1.1's last item), not by A.

Acceptance of A5r, in order: the ABI commit with A's seven drivers at the 113 A4 blocks
identical, D's `sim-layer-d-evidence`, every unit book under 60 s; the loop commit with ENVELOPE
green on a native run of conn-unit's fixture transcripts over socketpairs and its controls
caught; the socket commit with H's nntp S form (`h8-run.py`, the hook pointed at
`fn2_native_session`) green against `127.0.0.1` and its WIRE and ENVELOPE verdicts ok.

## 5. Executor (contract item 5)
`fn2-turn` calls `fn2-concrete-turn` / `fn2-concrete-loop`, the bounded
dispatcher over `fn2-transition` and the intrusive scheduler;
there is no fusion. A turn stops at the first exhausted `H`, `K`, or `Aturn`
budget, or when nothing eligible remains. Results are `(mv status nobs nvisits
nactions fn2-core)`; `fn2-core-idle-deadline` supplies the accompanying sleep
bound (`*fn2-no-deadline*` means no requested deadline). `:more` preserves runnable work,
`:idle` permits adapter progress, and `:stop` records a sticky stop.

The scalar control field `stop-reason` uses the declared `fn2-stop-reason` enum;
`fn2-core-stop` retains the first reason. `:none` means no stop. The corruption
reasons are `:issue-unreserve`, `:issue-range`, `:issue-capability`,
`:issue-storage`, `:issue-cancel-target`, `:issue-wake`, `:issue-enqueue`, `:harvest-fifo`,
`:harvest-input`, `:harvest-output`, `:harvest-finish`, `:wake-bounds`,
`:wake-state`, `:machine-write`, `:machine-observation`, `:machine-phase`
and `:pool-release`. `:signal`, `:clock-exhausted` and `:work-overflow` name
the other stop paths; `:machine-contract` is a run beyond its arm's certificate, and `:account`
an invariant failure of the principal ledger (D7: an account operation's `:bounds`, `:underflow`,
`:state` or a charge overflow, turned into a stop, never absorbed). New reasons are appended, so
every earlier code is unchanged. Scenarios print the enum keyword and require `:none`
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
is idempotent. `fn2-sched-reattribute machine to` (D7's re-attribution) moves a queued
machine from its principal's FIFO, at any position, to the tail of `to`'s in one step and
only sets the principal column of an unqueued one; every link is checked before the first
write, so `:bounds` and `:state` leave the scheduler unchanged (`tests/sched-unit.lisp`). All A4 connections use anonymous principal zero. Listener rows
occupy `[0, accept-credits)`, followed by `C` connection rows and one scribe row.
The `fn2-echo` connection declaration has a per-row mode bit for echo or discard;
both modes share one free list and one admission count. A listener supplies the mode
to each admitted connection; the shared directory has no echo-mode flag. These disjoint global ID
ranges and their inverse are generated from the `defmachine` declarations.
L1 reserves row capacity before a listener issues Accept. The directory's
`admission-credits` starts at C; a successful issue consumes one, a failed
Accept or refused admission returns one, and echo reclamation returns one
unless the row retires. Free rows equal credits plus pending admission
reservations: issue moves a credit to a reservation, admission removes both
one reservation and one free row, and reclamation adds a free row and credit.
This preservation argument is an engineering derivation; R6b states it as an
owed keystone with teeth (no row is in fn2-squares yet). Listeners
without credits park on a separate FIFO, generated with the operation-wait
FIFO by `fn2-machine-wait-queue`; the grant service wakes them after reclamation.
R6b still owes pool/operation bundle reservation and the remaining refusal
postures. L1 reserves rows only; A4's echo profiles have enough class-0 pool
slots and generation headroom for their finite runs. Simulator listener Close
marks the capability `:admission-refused`; ordinary unexplained Close remains
`:unattributed`. A4 rejects any live drop and any unattributed safety drop.

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
Exhaustion returns `:more` with pending work retained. The caps are machine declarations, exported as `*NAME-RUN-BYTES*`,
`*NAME-RUN-STEPS*` and `*NAME-RUN-DESCRIPTORS*`; the profile has no
execution-quanta fields. Resident capacities and `:trace-capacity` remain
profile parameters. `fn2-control` contains scalar fields; the recovery image
contains a byte-array field without a dummy column.

`defmachine` owns phase dispatch, `:observes` event routing and the arm contracts (R7;
`build/coordinator/fn2/lanes/a-to-d-arm-contracts.md` is the full syntax layer D writes). Every
continuation and handler is `(TAG FN :cost (:bytes F :steps F :descriptors F) :writes (FIELD ...)
:tables (CHILD ...) :next (PHASE ...) :uses (OP ...) [:from ...] [:on-refusal ...]
[:language :unchecked])`; the bare `(TAG FN)` form is refused. `:holds ((PHASE KIND ...) ...)`
names each phase's resources in D0's order (`fn2/books/resources.lisp`). Outside calls declare
their work, the children they change, the row fields they write and their resource effects with
`defcost` (`fn2/books/machines-a-costs.lisp` for layer A's). `defmachine-callback` checks every
body in the restricted arm language (`fn2/books/arms.lisp`): scalar primitives, bindings,
`fn2-call` of contracted same-kind callbacks, the kind's `PUT-CORE` on its own row for declared
fields and declared successor phases, and declared operations; an undeclared write, an undeclared
move, a call outside `:uses` or without a defcost (a helper hiding a foreign-table write), a stale
row read and a cost citing an undeclared call are refused at expansion, each with its message
(`tests/core-child-assembly-callbacks.lisp` carries the controls). When a kind's run is generated
(the `:callbacks` section) every arm's evaluated cost must be within the declared caps, an arm
whose cost reaches a cap must name its own phase in `:next` (the row's fields are its continuation),
and its operations must make exactly the resource moves its phases imply (D0's
`fn2-resource-effects-p` checks the same rows). The run entry and each handler assert the arm's
certificate (`K-ARM-CHARGE-OK-P`, `K-ARM-NEXT-OK-P`, `K-OBSERVE-NEXT-OK-P`) and stop with
`:machine-contract` otherwise; each arm contributes owed `:bound` and `:invariant` (frame and
continuation) rows to fn2-squares with `:from (:machine K)` and evaluated teeth, each kind a
phase-totality row; `fn2-arm-cost-composition` and `fn2-arm-residual-budget` state the turn bound
as composition over the arms' certificates. The machine contributes its case catalogue (one label
per phase, then per observed event); correspondences (Q1) bind statements to it. The listener has
three phases so that its holds are a function of its phase: `:accepting` (the accept credit),
`:admitting` (plus a reserved connection row, while its Accept is in flight or ready) and `:closing`;
admission is the allocator operation `fn2-machine-admit-connection`, so no layer-A arm writes
another kind's columns. Declarations name functions, never pasted code forms. The fixed run
convention is `(id budget ROW-fields... fn2-core)`; observation handlers receive `(id event outcome
reason count aux0 aux1 ROW-fields... fn2-core)` and return `(mv wake fn2-core)`; `ROW-fields...`
are scalar values in declared column order, recorded in the machine row's `:calling-convention`.
The generated entry binds its own table once; per-kind writes bind that child once for the whole
field batch. Initial values are constants or named functions of `(slot base n gen)`. The router
validates the row's kind, generation and non-free state before invoking the handler, then performs
generic pending accounting; handlers see every completion before the pending decrement and own any
event-cell store. An unrouted event or a write to a field absent from the target kind stops the
executor. Per-kind phase-write macros reject another kind's constants. Global field setters guard
both the declared width and the presence of that field in the target kind.

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

The scheduler accepts the assembled row count and a weight list, stores no connection/scribe
IDs and no weights (they shape the calendar at init and are not read again), and derives
calendar length as `W + 4*ceiling(W/16)`, W the sum of the weights (`p + 4*ceiling(p/16)` when
every weight is 1). **Weights (D7's S3).** `fn2-sched-init profile weights n`; the core passes
`(fn2-profile-weights profile)`, slot I's `:weight` in the ledger's `:accounts` key, 1 when
unconfigured. A slot of weight w (1..255) appears w times per round: pass k lists, in slot
order, the slots whose weight exceeds k; after every sixteen principal entries and after the
last come the four services. With every weight 1 this is the unweighted calendar entry for
entry, at any P; a calendar with a weight above 1 has at most 4,096 entries
(`fn2-sched-profilep` refuses more, and a weight outside 1..255). The owed
`fn2-sched-starvation (principal weights fn2-sched)` holds over any weights: its hypothesis
`fn2-sched-calendar-validp weights` says the calendar is the weighted calendar of WEIGHTS, and
its teeth run every principal from every cursor on the concrete calendar and on a weighted
tiny one (weights 3 1 2 1, eleven entries). The reference builds the same calendar literally
(`fn2-ref-calendar weights`) and its relation recovers the weights from the literal calendar
(each slot's count) and refuses one not in the specified order (`:literal-calendar`). Runtime
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
successful fence (E4), and `verified` advances after complete readback
(E2–E3, without a further durability inference).

`fn2-request-wake` coalesces the earliest explicitly registered wake
requirement. The timer/grant service emits `ArmWake` with dedicated u60
deadline and observation-generation fields; each new clock view advances the
token, with stop at exhaustion. The simulator keeps one replaceable request,
retains the earliest deadline within a view, ignores stale views, and bounds
its virtual-time advance by that deadline. Layer A's machines do not yet use
a general timer heap. Trace and ServicePosture action payloads remain out of
scope.

`books/reference.lisp` supplies the separate reference transition system.
Its ordinary lists hold the literal ROUND2 §C calendar (weighted, `fn2-ref-lists weights`), cursor, one FIFO per
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
A mismatch fails the scenario at that turn and prints `:selection` with the
first differing transition field, or `:state` with the first differing
projection field when selections agree. The shared adapter outcome obeys E1–E5.

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

**TRACE per case and the Q1 evidence (DM3).** `fn2-check-trace-cases-turn`
(`sim/check-trace.lisp`) runs the same turn as `fn2-check-trace-turn`, stepped one
transition at a time by the two loops themselves (`fn2-concrete-loop` and `fn2-ref-loop`
with fuel 1, each continuing exactly when its named stop condition,
`fn2-concrete-loop-stop-p` / `fn2-ref-loop-stop-p`, is false), so the stepped turn is
`fn2-turn` and `fn2-ref-turn`. Before each transition `fn2-q1-label` names its Q1 case;
after it, that case's G1 square is checked: both loops continue together, the five
results agree, and `fn2-ref-difference` is empty with the reference's work counters
written by its loop exit (the contract's normalisation). A failure is a TRACE failure.
Per turn it returns the case counts and, for `(:run K P)`, the count of transitions
after which the core has no stop reason (the generated run entry asserted K's arm
certificate there non-vacuously). The A4 driver installs `tests/q1-case-hook.lsp`
(raw instrumentation, as the read hook) around every TRACE turn before the metered
echo run (the turn meter measures `fn2-turn` itself, so that run stays whole-turn),
then writes the sums to `tests/evidence/q1-a4-tally.lisp` with the run's revision.
`tests/q1-evidence.lisp` appends to every Q1 case row the record of the row's own
checker (`fn2-q1-check-case`) and to every `K-P-BOUND` row the run-time certificate's
record (`fn2-arm-certificate-check`); an unreached case or arm gets an `:unchecked`
record with zero exercised. The export lists each correspondence's cases with and
without a passing, exercised check. At `aa2604ac3` on forge: 21,100 turns, 180,838
transitions G1-checked, 34 of 54 cases exercised, none outside the catalogue; 19 arm
certificates exercised. Unexercised: echo and scribe `:free`, echo `:retired`, scribe
`:stopped`, the fourteen `fn2-commit` cases (B's machine; the A4 gate runs no commit
scenario), the router fallback and the sticky signal. The scope is the A4 gate's
scenarios; frame rows (`K-P-FRAME`) get no record: only their next-phase half is
asserted at run time.

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
in the same 512-byte unit. FUA persists only its own request. These frontiers
implement E4–E5; readback supplies no additional ordering (E3).

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
sector validity alone does not establish acknowledgement (E3–E5).
`fn2-recover-start` / `fn2-recover-step` retain only scalar scan progress;
each step reads one sector and writes no storage. A death discards that
progress and starts again. `fn2-recover-stub` uses the same step to scan the
whole supplied byte image.

Every public `:broad` echo, pool, device and scribe run also executes physical
ABI probes with two outstanding operations. Four counters must each reach one:
socket and storage completions posted against submission order (E1), and an
overlapping read returning the old and new values (E2). Counts require the
posted FIFO order and harvested bytes, not merely a requested schedule.

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

DM1 stores obligations in `fn2-squares`; `defthm-owed` is its author view.
`:schema` defaults to `:assertion`; A's migrated rows are explicitly classified.
The row retains the untranslated formula, its admitted `$OWED` body, variables,
teeth, owner (`:from`), contract, origin/case/source/boundary, sides and checker.
`:proof` is `(:owed)` or `(:proved THM)`; the table guard requires the admitted
formula to equal the translated body or its exact `$OWED` application.
`:checks` records contract, revision, profile, domain, horizon/unit, reached and
exercised counts, verdict and location. Appending evidence cannot discharge debt.
The export separately counts requirements, bound statements, proofs and rows with
passing exercised checks, by correspondence/owner, case source and schema.
A requirement without a statement counts only as a requirement. Case catalogues
and bindings arrive in DM2/DM3; the turn-composition row already names Q1.

`:shared` lists qualified declaration identities common to both sides.
The default `:claim :semantic` requires `:contract (:independent NAME ...)` and
`:shared-handler-mutation NAME` when sides share declarations. These are named
contracts/controls, not claims that they have been discharged. Representation or
compiler refinement may explicitly use `:claim :representation` or `:compiler`
with a refinement schema. Q1's existing turn row claims representation refinement
of independent selection over shared machine semantics, not independent behaviour.
Layer inference accepts absolute and ACL2 project-relative paths; `fn2/b/`, `c/`,
`d/` (also under `sprint/`) identify their layers, and `books/` and `sim/` default
to A. B adds one `(fn2-book-layer :b)` line at the head of each of its books,
after including the declaration machinery; every form in that book inherits B.
A conflicting second book-layer declaration is refused. An explicit `:layer`
in a registrar payload (including `defthm-owed :layer`) overrides the book's
recorded layer, which overrides the path default. Tests default to `:test`.

DM0b adds `fn2/books/operations.lisp`, the one carrier-parameterised emitter
below `columns` and `machines`. `defwide-columns`, `defmachine-callback`, the
generated run entries and the core's pool and issue wrappers all emit through
it, and each function is entered in its owner row's callback map (`:args
:returns :row-bindings :calling-convention :carrier :writes :cost :refusal
:section`). The core operations sit under `(:operation-set fn2-core-issue)` and
`(:operation-set fn2-core-harvest)`; L1's credit and wait-queue functions sit
under `(:operation-set fn2-machine-resources)`. `(fn2-call CALLEE extra...)`
expands from the callee's authoritative calling convention, and positional
`ROW-` forwarding is refused. After every binding that rebinds `fn2-core`, the
callback emitter re-snapshots the row from the returned core before any later
`ROW-` read, on refusal paths too; unsupported `b*` binders are refused.
`:writes` and `:cost` stay `:unchecked` until R7. Requirements resolve by `:at`
at `fn2-resolve` points (index, core, access, callbacks, dispatch, reference,
coverage). `fn2-input-seals` replaces `fn2-core-instance`: machines seal at
`:index` and children at `:core`. Obligations seal at `:coverage` only at the
top of the world, in `fn2/tools/owed-export.lsp` after every layer's unit and
checker books are included, never inside a library book: a seal in a library
would make include order refuse rows (B's commit keystones must include
`sim/sim` before they can be stated).

**Row read sets and assembly sections (2026-10-30, for D4).** A machine callback takes only the
row fields its body reads (inferred after `fn2-call` expansion) through per-field readers
`K-ROW-<field>`; the whole-row `K-SNAPSHOT` (one mv of every field) is deleted, so ACL2's 32-value
limit bounds a callback's read set, not a row (fn2-conn: 30 fields, widest read set 17). The
assembly's sections split further so no book nears the minute: the core's init (one guard over
every child's capacity arithmetic, 24 s alone) is `assembly-init`, and the commit kind's events
are two section books (`assembly-callbacks-b`, then `assembly-callbacks`). Forge, closure at -j 8
(load 4-7), before -> after: assembly-core 51.1 -> 25.6 (+ assembly-init 29.3), assembly-callbacks
56.6 -> 49.1 before the commit split, assembly-callbacks-d 29.9 -> 15.5, assembly-callbacks-a
24.2 -> 17.2, assembly-access 33.6 -> 40.4 (the per-field readers and their width lemmas live there).

