# fn2 layer D: the machines, the scheduler over real principals, accounting, and NNTP over them

Present state, rewritten whole by the layer-D seat. The contract is
`build/coordinator/briefs/FN2-LAYER-D-MACHINES-NNTP.md` over `FN2-SEAT-COMMON.md`. The decisions it
serves are `build/coordinator/fn2/EXECUTION-MODEL.md` (rules 1-5 and 7, §5, §7a items 2-3) and the
normative tables of `fn2/EXECUTION-MODEL-ROUND2-ASTRA.md` (§B machine catalogue, §C scheduler, §D
vocabulary, §E.2 commit batch, §F scenarios). This file records the choices the layer makes inside
those decisions, each with its reason. A departure from a decision that is not recorded here is a
defect. Sections marked *(design)* are written before their quest and are rewritten by it.

## 1. Where each piece lives

All D books sit in `fn2/books/` (or `fn2/tests/` for evidence) and open with
`(fn2-book-layer :d)` after including the declaration machinery, as B's do; every row they register
is attributed to layer D. Package `"ACL2"`, prefix `fn2-`; no `skip-proofs`, `defaxiom`, trust tag or
`:program`. Keystones are `defthm-owed` rows in `fn2-squares` with executable teeth.

| piece | file(s) | quest | owner |
|---|---|---|---|
| resource order, admission bundles, protected reserves, effects (data + checks; the acyclicity lemma, proved) | `fn2/books/resources.lisp`, negative fixtures `fn2/tests/resources-unit.lisp` | D0 | D (a library: includes only declaration machinery, so A's `defmachine` `:holds` can read it) |
| the owed deadlock keystone over the assembled core | `fn2/books/resources-owed.lisp` | D0 | D |
| acquisition and cancellation scenarios, per bundle | `fn2/tests/sim-acquisition.lisp`, `fn2/tests/sim-acquisition-driver.lsp` | D0 | D |
| machine DSL arm contracts (`:cost :writes :tables :next :uses :holds`, `defcost`) | `fn2/books/machines.lisp` | R7 (A's quest; D1's requirements are its seam request, §4) | **A** |
| T10, resident state bounded by the profile | `fn2/books/resident.lisp` (generator), `fn2/books/owed-d.lisp`, `fn2/tests/owed-d-unit.lisp`, `fn2/tests/owed-d-coverage.lisp` | D1a | D |
| the command-grammar DSL `defgrammar` (framer, block framer, validators, renderer, runner) | `fn2/books/grammar.lisp`, evidence `fn2/tests/grammar-unit.lisp` | D2a | D |
| the NNTP command and reply table | `fn2/books/nntp-grammar.lisp` | D2a | D |
| generator, mutator, fuzzer and its three mutation controls | `fn2/tests/grammar-gen.lisp` (a test library: it uses the simulator's PRNG, and nothing served includes it), `fn2/tests/grammar-fuzz.lisp`; the mutation controls are `*fn2-gram-faults*` in the grammar's logical runner | D2b | D |
| table check against H's model | `fn2/tests/grammar-export.lsp` (writes the table), `fn2/tests/grammar-oracle.py` (reads `fn2/tests/model/nntp_model.py`) | D2a | D |
| fuzz cases checked against H's model | `fn2/tests/grammar-fuzz-export.lsp` (writes the cases and the grammar's verdicts), `fn2/tests/grammar-fuzz-oracle.py` | D2b | D |
| connection machine `fn2-conn` (listener is A's) | `fn2/books/conn.lisp`, callbacks section `fn2/books/assembly-callbacks-d.lisp`, evidence `fn2/tests/conn-unit.lisp`, WIRE `fn2/sim/check-wire.lisp` | D3 | D |
| upload, transaction, cursor, TLS admission, wait | `fn2/books/{upload,txn,cursor,tls-admit,wait}.lisp` | D4-D8 | D |
| scheduler over principals, accounts | `fn2/books/sched.lisp` (extended through A's seam), `fn2/books/accounts.lisp` | D7 | D (sched.lisp changes go to A as a seam request) |
| layer-D simulator acceptance | `fn2/tests/sim-layer-d.lisp` | D3-D9 | D |
| serving | `fn2/host/` session script, `fn2/tests/native-nntp.py` | D9 | D |

Shared files D never edits directly: A's `machines.lisp`, `columns.lisp`, `core*.lisp`, `pool.lisp`,
`vocab.lisp`, `sched.lisp`, `declare.lisp` (exception: a purely additive line that certifies with A's six
drivers unchanged, reported to main as a seam note), `fn2/tools/owed-export.lsp` and the generated
`fn2/docs/OWED.md` (the seat adds D's include lines and regenerates after each merge, never a Codex
session, so two parallel quests do not collide on them).

## 2. What D stands on, and the seams it waits on

D starts on layer A alone (D0-D2; brief). A's queue at the time of writing (A continuation,
2026-10-29 04:20): R5e2 running, then R6a1, R6a2, R6b, DM2, R7, A5r, A6. Three of those are D's
foundations, and two of them overlap D's own contract items; the overlap is resolved by merging, never
by building both (seat-common "two additions that are one construction are merged"):

| D item | A quest | resolution |
|---|---|---|
| D0 the acquisition protocol | R6b item 1 (`fn2/docs/resources.md`: "a single global acquisition order, the admission bundle, protected reserves, release points, the deadlock-freedom argument") | **One protocol, D0's.** `fn2/books/resources.lisp` is the source; this file's §3 is its printed form. R6b item 1 is re-cut to "make A's code follow D0's order and bundles", and D0's per-bundle scenarios for A's bundles become R6b's acceptance. Seam request through main (§10). |
| D1 the machine DSL | R7 (arm contracts, restricted arm language, `defcost`, `:holds`, A4's three kinds ported) | **A owns `defmachine` (seat-common "one DSL owner").** D1's DSL content is a seam request with the exact forms D's machines need (§4); R7 builds it, and R7 item 2 *is* D1's "A4's three machines re-declared through the result". What D1 builds itself is the ownership matrix (§5) and T10 (§7), quest D1a. |
| D2 parser over pool ranges | R6a1 (`fn2-pool-scan`, `fn2-pool-drop-prefix`, `fn2-pool-compare` with two owners) | D2a builds the DSL, table, parser and renderer over the pool library's checked scalar exports (`fn2-pool-read`, `fn2-pool-write`), bounded by the 4 KiB run quantum; D2c ports line finding and prefix retention to R6a1's primitives once they land and deletes the scalar inner loop (the derived path only). |

C's identity and ordered schemas (C2/C3) gate D3 onward (brief). B's commit batch (B3b, on
`fn2/b-durability`) is the subject of D5's batch reference.

## 3. Acquisition (D0; `fn2/books/resources.lisp` is authoritative, this section is its printed form)

EXECUTION-MODEL §7a item 2, contract item 0 of the brief. The tables are data in
`fn2/books/resources.lisp` (a library: it includes only `owed`/`declare`, so `machines.lisp` can
include it for `:holds`), checked at certification by guard-verified predicates, each with a named
negative fixture in `fn2/tests/resources-unit.lisp`. The text below is printed by
`fn2/tests/sim-acquisition-driver.lsp` from those constants and pasted; regenerate it rather than
edit it.

**The order principle.** A resource is ranked by how long it is held: what a machine keeps across
many runs and external waits comes first, what it holds for one issue comes last. Every bundle
acquires in strictly ascending rank, and a holder waits only for a kind ranked above every kind it
holds. Changes from the draft of this section, each for a reason: RX and TX get separate ranks (one
total order, no ties); the principal reservation moves after RX/TX (a connection holds its windows
for its lifetime while a request waits for its charge, so the charge must rank above them; a machine
holds at most one request's charge); the storage job and the read/write slot are one kind (ROUND2
§B.1 gives them the same capacities `Jread`/`Jwrite`); `:storage-window` (a job's pool range) and
`:cancel-credit` (`Ncancel`) are added; `:service-work` goes first (a calendar visit is the frame in
which a service acquires and is never awaited).

**(a) The order** (`*fn2-resource-order*`).

| rank | kind | unit | bound | reserve | why |
|---:|---|---|---|---|---|
| 1 | `:service-work` | :visit | `(:calendar)` | :service-classes | One bounded run of a scheduled service; a visit is the frame in which a service acquires and is never awaited. |
| 2 | `:accept-credit` | :credit | `(:profile :accept-credits)` | none | A listener row: at most one pending Accept each, held for the listener's lifetime. |
| 3 | `:connection-row` | :row | `(:profile :c)` | none | Reserved as an admission credit at Accept issue, held for the connection's lifetime. |
| 4 | `:rx-range` | :pool-slot | `(:profile :pool-classes)` | none | The connection's receive window, held for its lifetime. |
| 5 | `:tx-range` | :pool-slot | `(:profile :pool-classes)` | none | The connection's reply window, held for its lifetime. |
| 6 | `:principal-reservation` | :quantity | `(:profile :p)` | :system | One request's charge on its principal account, held from request admission to its reply; a machine holds at most one. |
| 7 | `:durable-octets` | :quantity | `(:profile :dstore)` | :system | Octets a principal's appended articles keep durable (4,096-octet blocks, rounded up per article), charged in the append's transaction and released when retention reclaims them. |
| 8 | `:tls-slot` | :slot | `(:round2 :ltls 16)` | none | A handshake job, held for the handshake only. |
| 9 | `:upload-row` | :row | `(:profile :u)` | none | An article input in progress, held while its bytes arrive. |
| 10 | `:chunk-window` | :window | `(:round2 :large-upload-windows 16)` | none | Two 256 KiB chunk ranges of a large upload, held while it streams. |
| 11 | `:transaction-row` | :row | `(:profile :t)` | none | A posting transaction from admission to its outcome. |
| 12 | `:identity-reservation` | :reservation | `(:profile :t)` | none | The Message-ID and operation identity claim of one transaction. |
| 13 | `:cursor-row` | :row | `(:profile :x)` | none | A query cursor from its command to its last reply byte. |
| 14 | `:wait-row` | :row | `(:profile :w)` | none | A parked consumer wait from registration to its reply or cancellation. |
| 15 | `:subscription-edge` | :edge | `(:profile :esub)` (default 4,096, ROUND2) | none | One wait row's edge to a stream, reserved at registration. |
| 16 | `:control-output` | :bytes | `(:profile :w)` | none | The reply window a wake or control reply needs, reserved at registration so delivery never waits. |
| 17 | `:cache-pin` | :pin | `(:round2 :cache-profile)` | :recovery | An object lease under a pinned view, held while a reply streams it. |
| 18 | `:batch-membership` | :records-and-bytes | `(:round2 :batch 1024 4194304)` | none | A transaction's records in a commit batch until publish. |
| 19 | `:storage-job` | :job | `(:profile :jread :jwrite)` | :recovery | A read or write slot: a storage job row, held across its issue, completion and verification. |
| 20 | `:storage-window` | :pool-slot | `(:profile :pool-classes)` | :recovery | The pool range a storage job reads into or writes from. |
| 21 | `:fence-slot` | :slot | `(:profile :fence-slots)` | :fence | One fence in flight per storage domain. |
| 22 | `:cancel-credit` | :credit | `(:profile :ncancel)` | :cancel | One outstanding cancellation request. |
| 23 | `:operation` | :op | `(:profile :o :qa)` | (:close :cancel :arm-wake :fence) | One op row with its outbox descriptor and two result cells, reserved together (fn2-op-reserve); held for one issue. |
| 24 | `:sealable` | :overlay | `(:profile :identity-overlays)` | none | A pure wait, never held: the sealer parked until a published overlay is sealable; the grant service's fifth source wakes it. |

**(b, c) Bundles and held-while-waiting** (`*fn2-resource-bundles*`).

| transition | acquires (in order) | holds while waiting | reserve | status | why |
|---|---|---|---|---|---|
| `fn2-listener :accept` | `:connection-row :rx-range :operation` | `:accept-credit` | none | exists, owed-by :r6b | A takes the row credit and op at issue and the RX slot only at admission; an accepted capability without an RX slot is closed. |
| `fn2-listener :close` | `:operation` | `:accept-credit` | :close | exists, owed-by :r6b | A has no close reserve: the Close draws an ordinary op reservation. |
| `fn2-echo :receive` | `:operation` | `:connection-row :rx-range` | none | exists | Receive into the RX slot the connection already holds. |
| `fn2-echo :send` | `:operation` | `:connection-row :rx-range` | none | exists | Echo sends from its RX slot; D3's connection adds its TX range. |
| `fn2-echo :close` | `:operation` | `:connection-row :rx-range` | :close | exists, owed-by :r6b | A has no close reserve: the Close draws an ordinary op reservation. |
| `fn2-scribe :reserve` | `:storage-window` | `:storage-job` | none | exists | The probe's row is its storage job; it reserves its 4 KiB window. |
| `fn2-scribe :write` | `:operation` | `:storage-job :storage-window` | none | exists | Write from the held window. |
| `fn2-scribe :fence` | `:fence-slot :operation` | `:storage-job :storage-window` | :fence | exists, owed-by :r6b | A takes the fence slot adapter-side at take, after the op, and has no fence reserve. |
| `fn2-scribe :read` | `:operation` | `:storage-job :storage-window` | none | exists | Read back into the held window. |
| `:timer :arm-wake` | `:operation` | `:service-work` | :arm-wake | exists, owed-by :r6b | A has no ArmWake reserve: the wake draws an ordinary op reservation. |
| `:connection :accept` | `:connection-row :rx-range :tx-range :operation` | `:accept-credit` | none | planned :d3 | The connection machine's admission, whole at Accept issue. |
| `:connection :receive` | `:operation` | `:connection-row :rx-range :tx-range` | none | planned :d3 | Single-shot receive into the held RX range. |
| `:connection :send` | `:operation` | `:connection-row :rx-range :tx-range` | none | planned :d3 | Single-shot send from the held TX range. |
| `:connection :close` | `:operation` | `:connection-row :rx-range :tx-range` | :close | planned :d3 | Close from the close reserve. |
| `:connection :request` | `:principal-reservation` | `:connection-row :rx-range :tx-range` | none | planned :d7 | A command's charge on its principal, before any request row. |
| `:tls-admission :start` | `:tls-slot :operation` | `:connection-row :rx-range :tx-range :principal-reservation` | none | planned :d7 | STARTTLS: a handshake slot and the TlsStart op. |
| `:upload :admit` | `:upload-row :chunk-window` | `:connection-row :rx-range :tx-range :principal-reservation` | none | planned :d4 | POST/IHAVE/TAKETHIS article input. |
| `:transaction :admit` | `:transaction-row :identity-reservation` | `:connection-row :rx-range :tx-range :principal-reservation :upload-row :chunk-window` | none | planned :d5 | The transaction and its identity claim. |
| `:transaction :batch` | `:batch-membership` | `:connection-row :rx-range :tx-range :principal-reservation :upload-row :chunk-window :transaction-row :identity-reservation` | none | planned :d5 | Joining a commit batch. |
| `:cursor :select` | `:cursor-row :cache-pin` | `:connection-row :rx-range :tx-range :principal-reservation` | none | planned :d6 | ARTICLE/BODY and the other queries pin their view before the success line. |
| `:storage-job :read` | `:storage-job :storage-window :operation` | `:connection-row :rx-range :tx-range :principal-reservation :cursor-row :cache-pin` | none | planned :d6 | A cursor's page read. |
| `:storage-job :write` | `:storage-job :storage-window :operation` | `:connection-row :rx-range :tx-range :principal-reservation :upload-row :chunk-window` | none | planned :d4 | An upload's extent write. |
| `:wait :register` | `:wait-row :subscription-edge :control-output` | `:connection-row :rx-range :tx-range :principal-reservation` | none | planned :d8 | A consumer wait reserves its edges and its wake reply before it parks. |
| `:any :cancel` | `:cancel-credit :operation` | `:connection-row :rx-range :tx-range` | :cancel | planned :d7 | Cancel from the cancel reserve. |
| `:commit-batch :log-write` | `:storage-job :storage-window :operation` | `:batch-membership` | none | planned :b | B's batch writes its packed records. |
| `:commit-batch :fence` | `:fence-slot :operation` | `:batch-membership :storage-job :storage-window` | :fence | planned :b | B's batch fences from the fence reserve. |
| `:recovery :start` | `:cache-pin :storage-job :storage-window :operation` | none | :recovery | planned :b | Recovery takes its whole bundle from the recovery reserve. |

**(d) Release, descending** (`*fn2-resource-releases*`).

| holder, cause | releases |
|---|---|
| `fn2-listener :refusal` | none |
| `fn2-listener :failed-result` | `:operation :connection-row` |
| `fn2-listener :close` | `:operation :connection-row` |
| `fn2-echo :refusal` | none |
| `fn2-echo :failed-result` | `:operation` |
| `fn2-echo :close` | `:operation :rx-range :connection-row` |
| `fn2-scribe :refusal` | none |
| `fn2-scribe :failed-result` | `:operation` |
| `fn2-scribe :cancellation` | `:operation :storage-window` |
| `:connection :refusal` | none |
| `:connection :close` | `:operation :control-output :subscription-edge :wait-row :cursor-row :principal-reservation :tx-range :rx-range :connection-row` |
| `:request :cancellation` | `:operation :storage-window :storage-job :cache-pin :cursor-row :identity-reservation :transaction-row :chunk-window :upload-row :principal-reservation` |
| `:request :failed-result` | `:operation :storage-window :storage-job :cache-pin :cursor-row :chunk-window :upload-row :principal-reservation` |
| `:wait :cancellation` | `:operation :control-output :subscription-edge :wait-row` |
| `:commit-batch :publish` | `:batch-membership` |
| `:commit-batch :failed-result` | `:operation :fence-slot :storage-window :storage-job` |

**(e) Protected reserves** (`*fn2-resource-reserves*`).

| reserve | covers | drawn as | why |
|---|---|---|---|
| `:close` | `:operation` | issue | Close always issues: a connection or listener full of idle receives can still time out and close. |
| `:cancel` | `:cancel-credit :operation` | issue | Cancellation of an outstanding operation never waits for the operations it cancels. |
| `:arm-wake` | `:operation` | issue | The timer service can always arm the earliest deadline. |
| `:fence` | `:fence-slot :operation` | issue | A batch or probe holding its writes can always fence them. |
| `:recovery` | `:cache-pin :storage-job :storage-window :operation` | whole bundle | Recovery acquires its whole bundle from this reserve at start and never waits for ordinary holders. |
| `:system` | `:principal-reservation` | whole bundle | Recovery and control are charged to the system reserve of every account dimension. |
| `:service-classes` | `:service-work` | whole bundle | The four protected service classes of the calendar (ROUND2 section C.2). |

**(f) Commit-batch phases** (`*fn2-resource-batch-phases*`; per-recipient kinds `:connection-row :rx-range :tx-range :principal-reservation :transaction-row :wait-row :subscription-edge :control-output :batch-membership`).

| phase | holds |
|---|---|
| `:collect` | `:batch-membership` |
| `:seal` | `:batch-membership` |
| `:dependencies` | `:batch-membership` |
| `:log-write` | `:batch-membership :storage-job :storage-window` |
| `:fence` | `:batch-membership :storage-job :storage-window :fence-slot` |
| `:durable` | `:batch-membership :storage-job :storage-window` |
| `:install` | `:batch-membership :storage-window` |
| `:publish` | `:storage-window` |
| `:notify` | none |
| `:uncertain` | `:batch-membership :storage-window` |
| `:draining` | none |

**Effects across rows** (`*fn2-resource-effects*`).

| operation | holds before | effects |
|---|---|---|
| `fn2-listener :accept-issue` | `:accept-credit` | `(:acquire (:connection-row :operation))` |
| `fn2-listener :admit` | `:accept-credit :connection-row` | `(:transfer (:connection-row) :to fn2-echo) (:acquire (:rx-range) :for fn2-echo)` |
| `fn2-listener :admit-refused` | `:accept-credit :connection-row` | `(:release (:connection-row))` |
| `fn2-echo :reclaim` | `:connection-row :rx-range` | `(:release (:rx-range :connection-row))` |

**Interim, layer A only.** `*fn2-resource-a-holds*` lists the kinds each phase of `fn2-listener`,
`fn2-echo` and `fn2-scribe` may hold. Pending operations are not listed there, because they belong to
the outstanding table, and waiting for a completion is not a resource wait. R7 moves this table into
each `defmachine`'s `:holds` and then deletes it here, as it will `*fn2-resource-effects*` once R7
declares those effects on its allocator operations. The wait-reason enum is now `(:none :completion`
followed by the 23 kinds by name, read from `*fn2-resource-order*` (R7 2/n, 80458ea94). The wait
projection therefore reads the awaited kind directly, and no translation table remains. R7 also
splits the listener into `:accepting` (`:accept-credit`) and `:admitting` (`:accept-credit
:connection-row`): with one phase spanning both states, per-phase holds could not state the
difference (A/D DSL seat, 2026-10-29).

**What the certification checks enforce.** The order has ranks exactly 1..22 in listed order with
distinct keywords; every bundle acquires in strictly ascending rank and names only known kinds; its
held-while-waiting set ranks strictly below its first kind (rule (c)); a `:close`, `:cancel`,
`:fence` or `:arm-wake` transition names a reserve that covers its whole bundle; no kind an issue
reserve covers (`:operation`, `:cancel-credit`, `:fence-slot`) appears in any held-while-waiting set;
every release list descends and a refusal releases nothing; no commit-batch phase holds a
per-recipient kind, and from `:publish` on none holds batch membership; an effect acquires above
everything its row still holds and releases or transfers only what it holds.

**(g) Why no cycle.** A wait-for edge `m → n` exists only when `m` waits for a kind `k` that `n`
holds. By rule (c) every kind `m` holds ranks below `k`; `n` holds `k`, so if `n` waits, it waits for
a kind above `k`. Ranks of awaited kinds strictly increase along every path, so no path returns to
`m`. This is **proved**, not owed: `fn2-resource-ranked-no-cycle` (resources.lisp) says that a list
of waiters `(held . awaited)` in which every waiter's held kinds rank below its awaited kind is never
a cycle (a chain whose last awaited kind is held by its first waiter). Reserve-drawn units are never
held while waiting (checked above), so release paths add no edge; a transfer between rows adds none
(neither row waits during it, the target is a free row). The keystone over the real core is owed:
`fn2-resource-no-deadlock` (`fn2/books/resources-owed.lisp`, `:schema :invariant`, `:from
(:operation-set fn2-resources)`): initialization establishes, and every `fn2-turn` preserves, that
the core's wait projection `fn2-resource-waiters` (per row: kind, phase and wait reason through the
tables above) is ranked. Teeth (`tests/sim-acquisition.lisp`): positive, real reached cores with a
listener parked on admission and a scribe parked on its window, nonempty and ranked, still ranked
after a real turn; negative, a connection holding its row and RX slot made to wait for a connection
row, refused. Its step is stated over `fn2-core-wfp` plus the ranked projection; a proof may need
A's conservation invariants as further hypotheses, recorded here when it is attempted.

**Scenarios.** `fn2/tests/sim-acquisition.lisp` (certified) drives every `:exists` bundle through
the real assembled core at the adapter boundary the simulator drives (`fn2-outbox-ack`,
`fn2-post-result`, harvest and observation routing, `fn2-machine-run`, the grant service), in tiny
profiles, exhausting each kind of the bundle in turn by profile capacity (`:c 1`, `:o 1`) or by
pre-occupying its units through the pool's reserve export; each boundary checks that nothing was
acquired (every core free count unchanged, the holder waiting with the reason naming the kind), then
lifts it and checks the bundle is acquired whole, then completes or closes and checks every count
comes back. The random simulator is not used: these are deterministic schedules at the boundary it
calls, and they add a boundary per kind it would only reach by chance. Today's verdicts: the echo
Receive/Send and scribe Reserve/Write/Read bundles pass; the five bundles owed by R6b fail exactly
on their owed checks (listener Accept: the RX slot is taken at admission, not at issue; listener and
echo Close, scribe Fence and ArmWake: no protected reserve, so with the operations exhausted they
cannot issue). The driver and the book fail if an owed bundle passes (the marking must then go), if
an un-owed bundle fails, or if an `:exists` bundle has no scenario; three controls on the verdict
rule check all three. Planned bundles print `pending` with their quest. Not covered by a scenario:
the fence slot is adapter-side in A (no core count to observe), and scribe has no cancellation in A
(its release row is R6b item 2's posture).

## 4. The machine DSL as landed, and D3's connection machine *(design; D3 rewrites it as built)*

### 4.1 What R7 gave D (926b09328; read from the commit, not the plan)

D's machines declare through A's `defmachine` with R7's arm contracts (syntax:
`build/coordinator/fn2/lanes/a-to-d-arm-contracts.md`; source `fn2/books/arms.lisp`,
`fn2/books/machines.lisp`; worked examples `fn2/books/machines-a.lisp`, `machines-a-costs.lisp`,
`machines-a-run.lisp`). Every item of the seam request this section used to carry is built: per-arm
`:cost :writes :tables :next :uses [:from] [:on-refusal]`; `defcost` for outside calls with D0's
effect forms (`:per-use` for pool ranges, `:target` for cross-row admission); `:holds` per phase in
D0's kinds, with each arm's operations checked to make exactly the phase deltas; the continuation is
the row's fields, and an arm whose cost can reach a cap lists its own phase in `:next`; per-arm owed
rows `K-PHASE-BOUND`, `K-PHASE-FRAME`, `K-OBSERVE-EVENT-FRAME`, `K-PHASE-TOTALITY` in `fn2-squares`
with generated teeth; run-time certificates that stop the core with `:machine-contract`; postures
`:close-and-release :discard-to-terminator :refuse-by-word :stop`. D0's interim
`*fn2-resource-a-holds*` / `*fn2-resource-effects*` are gone (resources-owed derives both from the
machine rows). D declares no arm `:language :unchecked`: the restricted language is the point.

Not built by R7 and owned here or later: the line-scanner/compaction worked example (D3, below);
per-path resource checks (per arm only); per-row accounting (A6); `*fn2-turn-transition-max*` from
arm bounds.

### 4.2 D3: the connection machine `fn2-conn` (`fn2/books/conn.lisp`)

ROUND2 §B.2 row 1 is "listener/connection". R7 made the listener its own kind (A's `fn2-listener`,
`:accepting :admitting :closing`), because a listener row and a connection row are different rows
(one listener, `C` connections) and per-phase holds could not state both. **Departure, recorded:**
row 1 is two kinds. The brief's `accepting` phase is the listener's; `fn2-conn` starts where the
listener's admission puts it. Its phases, all declared in D3 so the enum is stable (phases are
compared by name only, so later additions would also be safe), each arm landing with the quest that
can serve it:

| phase | holds (D0 kinds) | arm (quest) | does |
|---|---|---|---|
| `:free` | none | `fn2-conn-idle` (D3) | an unadmitted row on the connection free chain |
| `:greeting` | `:connection-row :rx-range :tx-range` | `fn2-conn-greet` (D3) | renders the greeting, or the capacity 400 when admitted into the refusal reserve, into TX; `:next (:reply)` |
| `:command` | same | `fn2-conn-command` (D3) | the parser continuation over RX; at a line, parse, decide, render into TX; else Receive |
| `:article-input` | same | `fn2-conn-block` (D4) | the block framer for POST/IHAVE after 340/335 and TAKETHIS's immediate block, handing data lines to the upload machine; discard-to-terminator for a refused block |
| `:reply` | same | `fn2-conn-reply` (D3) | Send `[tx-off, fill)` of TX by loan; when sent and released, reset TX, move to `after` |
| `:upgrading` | same (+ `:tls-slot` is the TLS row's, not this row's) | `fn2-conn-upgrade` (D7/E1) | nothing framed; waits for the TLS admission machine's result |
| `:closing` | same | `fn2-conn-close` (D3) | Close (from the `:close` reserve once R6b has it) |
| `:draining` | same | `fn2-conn-drain` (D3) | wait for pending 0 and borrows 0; release TX, RX; reclaim the row |
| `:retired` | none | `fn2-conn-idle` (D3) | generation exhausted (A's retirement rule) |

Until D4 and D7, no D3 arm moves a row into `:article-input` or `:upgrading` (no `:next` names them).
`defmachine` requires an arm per phase, in phase order, so in D3 both carry `fn2-conn-unreached`
(`:next` its own phase, cost `(:cost fn2-machine-refuse-phase :steps)`): reaching it means the row is
inconsistent and the core stops (assert, never absorb). POST, IHAVE and the block commands answer
their interim refusals (below) without opening a block, and STARTTLS answers 580.

**Fields** (beyond the common row: phase, generation, principal-slot, account-ref, ready-prev/next,
wait-reason, deadline):

| field | kind | meaning |
|---|---|---|
| `cap-index cap-nonce` | u32 u32 | the capability token (A's Accept result) |
| `rx-slot rx-gen tx-slot tx-gen` | link u60 link u60 | the RX and TX pool ranges (whole slots; offsets below) |
| `start pos overflow` | u32 u32 bool | the framer's whole state over `[start, fill)` of RX (`fn2-gram-frame`) |
| `compacting cursor` | bool u32 | a drop-prefix compaction in progress and its continuation |
| `tx-off` | u32 | the sent prefix of TX |
| `after` | u8 | the phase `:reply` moves to when TX is drained: an enum of `:command :article-input :upgrading :closing` (by name) |
| `pending borrows` | u32 u32 | outstanding ops; TX bytes lent to a Send |
| `mask` | u8 | the grammar state mask (`*fn2-nntp-state-reader*` etc.): reader or peer, anonymous or authenticated |
| `ordinal` | u32 | commands answered on this connection |
| `access-ref` | u32 | the pinned access rule (W01): the anonymous rule (0) at admission, re-pinned only by E2's authentication arm |
| `auth-pending` | u8 | H's shared pending slot: none, AUTHINFO USER, SASL, XREDEEM (starting any replaces the others) |
| `refused stopped next-free` | bool bool link | admitted into the refusal reserve; the row's stop bit; the partition's free chain (A's admission) |

**The 32-value limit, and the fields that wait for their quests.** The arm calling convention
passes every row field as a scalar argument and the snapshot returns them through `mv`, which ACL2
caps at 32 values: the common row (8 with the phase) leaves 24 fields to a kind. fn2-conn uses 22.
So the fields whose subjects are later quests are added by those quests, not declared empty now:
the selected view (D6), the authentication and configuration references (E2, D7), the active request
reference and outstanding-use count (D4-D6). Seam note to A (sent with this commit): a kind with more
than 24 fields (D4's upload and D5's transaction rows will be) needs the snapshot to pass only the
fields an arm reads, or the row split into two tables.

**Budget** `(:bytes 4096 :steps 32 :descriptors 4)` (ROUND2 §B.3). **Capacity** `(fn2-profile-c
profile)`. **Pool class**: RX and TX are each one slot of the smallest class of at least
`*fn2-conn-range-min*` = 1,024 octets (twice the 512-octet line cap, so a retained partial line and a
whole Receive quantum fit; the concrete profile's 4,096 class). A profile whose pool cannot give
every connection row two such slots fails the kind's profile check by name (the tiny profile's 64
and 256 classes cannot; D's tests use `*fn2-conn-profile-tiny*`, the tiny profile with `:pool-classes
((8 . 1024))`).

**The parser as a continuation under the byte budget.** `fn2-conn-command` charges at most 4,096
octets per run, split statically: the framer gets `*fn2-conn-frame-bytes*` = 2,048 per run (it
examines at most that many octets, resuming from `(start pos overflow)` at `:budget`); a framed line
is re-read once by `fn2-nntp-parse-line` (at most 512); the decision renders one status line (at most
512) and at most `*fn2-conn-body-bytes*` = 1,024 of fixed body (HELP, CAPABILITIES). Multi-line
bodies beyond that are the cursor's (D6), which renders and sends in its own quanta. So the arm's
declared cost is `(:bytes (+ *fn2-conn-frame-bytes* 512 512 *fn2-conn-body-bytes*))` = 4,096, it
reaches the cap, and its `:next` includes `:command`. Framer outcomes:

| status | the run then |
|---|---|
| `:line` | parse, decide (4.3), render the reply into TX, set `after`, move to `:reply`; `ordinal` + 1 |
| `:overflow` (a line over 512) | render 501, `after` = `:closing` (RFC 3977 §3.1; H's `_malformed(overlong)`) |
| `:need-more` | compact if needed (below), then issue Receive of `cap - fill` octets; stay `:command`, pending |
| `:budget` | stay `:command`, runnable (the continuation is the row) |
| `:fault` | the pool refused a read of a filled octet: stop the core (assert, never absorb) |

Compaction (GD4): when every filled octet is consumed (`start = fill`) the RX range is reset
(`fn2-core-reset`) and `start = pos = 0`; when a partial line is retained and the slot is full, its at
most 511 octets move to the front with R6a1's `fn2-core-drop-prefix`, a bounded continuation over the
row's `cursor` (`compacting` set; at most `*fn2-conn-compact-bytes*` = 1,024 per run). A slot smaller
than the line cap that fills with one unfinished line is refused as overlong (501, close): only a
profile below `*fn2-conn-range-min*` can reach it.

Pipelining is preserved by construction: the framer resumes at `pos`, so lines that arrived together
are answered in order, one reply per run of `:command` → `:reply` → `:command`. Fragmentation
invariance is the grammar's (`fn2-nntp-fragmentation`) lifted to the machine (T8 below).

**Arms, contracts, costs** (each a `defmachine-callback` in the checked language; sub-callbacks
forwarded with `fn2-call` carry `:contract`):

| arm | cost (bytes / steps / descriptors) | writes | next | uses (each a defcost or contracted callback) |
|---|---|---|---|---|
| `:free`, `:retired` `fn2-conn-idle` | 0 / `(:cost fn2-machine-idle :steps)` / 0 | none | own phase | `fn2-machine-idle` |
| `:greeting` `fn2-conn-greet` | 512 / transition / 0 | `tx-off after` | `:greeting :reply` | `fn2-conn-run-greeting`, `fn2-machine-refuse-phase` |
| `:command` `fn2-conn-command` | max of its two forwards: 4,096 / 32 / 1 | the framer state, `compacting cursor tx-off after auth-pending ordinal` and the issue set | `:command :reply` | `fn2-conn-frame-run`, `fn2-conn-compact-run` |
| (contracted) `fn2-conn-frame-run` | 4,096 / transition / 1 | as `:command` | `:command :reply` | `fn2-conn-frame`, `fn2-conn-run-answer`, `fn2-conn-run-overflow`, `fn2-conn-input`, `fn2-machine-refuse-phase` |
| (contracted) `fn2-conn-input` | frame + max(receive, overflow) / mailbox / 1 | `start pos compacting cursor tx-off after` and the issue set | `:command :reply` | `fn2-conn-room`, `fn2-core-reset`, `fn2-issue-receive`, `fn2-machine-issue-result`, `fn2-conn-run-overflow`, `fn2-machine-refuse-phase` |
| (contracted) `fn2-conn-compact-run` | 1,024 / transition / 0 | `start pos compacting cursor` | `:command` | `fn2-core-drop-prefix`, `fn2-machine-refuse-phase` |
| `:article-input`, `:upgrading` `fn2-conn-unreached` | 0 / refuse / 0 | none | own phase | `fn2-machine-refuse-phase` |
| `:reply` `fn2-conn-reply` | 4,096 (the send length) / 2 mailbox / 1 | `tx-off borrows` and the issue set | `:reply :command :closing` | `fn2-conn-room`, `fn2-issue-send`, `fn2-core-reset`, `fn2-machine-issue-result`, `fn2-machine-refuse-phase` |
| `:closing` `fn2-conn-close` | 0 / transition / 1 | the issue set | `:closing` | `fn2-issue-close`, `fn2-machine-issue-result` |
| `:draining` `fn2-conn-drain` → (contracted) `fn2-conn-release` | 0 / release / 0 | the release set (generation, ranges, capability, framer state, offsets, next-free, wait-reason) | `:draining :free :retired` | `(fn2-core-release :effects ((:release (:tx-range))))`, `(fn2-core-release :effects ((:release (:rx-range))))`, `fn2-machine-gen-limit`, `fn2-machine-reclaim-fn2-conn` (4.5), `fn2-core-stop` |

("The issue set" is `pending stopped wait-reason ready-prev ready-next`, what A's
`fn2-machine-issue-result` writes.)

Observation handlers, mirroring echo's: `:receive-result` (from `:command`; a positive count stays in
`:command`, EOF or failure moves to `:closing`), `:send-result` (from `:reply`; advances `tx-off`, a
failure moves to `:closing`), `:borrow-released` (writes `borrows`), `:close-result` (from
`:closing`, to `:draining`). Postures: `:command`'s declared `(:close-and-release :to :closing
:releases ())` (the row keeps its ranges until `:draining`; a refused Receive closes); `:reply` the
same.

The connection's own operations have their defcosts in conn.lisp (D's layer, as the arm-contract
doc asks); each is a thin `stobj-let` wrapper over the pool child, never copying octets into a list:

| op | over | declared |
|---|---|---|
| `fn2-conn-frame` | `fn2-gram-frame` on RX (since D2c one `fn2-pool-scan` for LF) | `:bytes *fn2-conn-frame-bytes*` (reads only) |
| `fn2-conn-run-answer` | `fn2-answer` (conn-answer.lisp): parse, sub-form checks, decide, render into TX; reads the clock mailbox | `:bytes *fn2-conn-answer-bytes*`, `:tables (fn2-core-pool)` |
| `fn2-conn-run-greeting`, `fn2-conn-run-overflow` | `fn2-answer-greeting`, `fn2-answer-overflow` | `:bytes 512`, `:tables (fn2-core-pool)` |
| `fn2-conn-room` | a held slot's fill and capacity | reads only |

### 4.3 The decision table (command tag → reply), D3's half

The decision is `fn2-answer` (`fn2/books/conn-answer.lisp`), a pool-level library the arm reaches
through the one declared operation `fn2-conn-run-answer`; it never reads a live configuration or
access rule, only the row's `config-ref`, `access-ref`, `auth-ref` and `mask`
(**the pinned access rule, H ruling HZ3 / fn1 W01**: one rule per connection, pinned at admission for
the anonymous principal and re-pinned only by the authentication arm; checked structurally, because
no arm but authentication lists `access-ref` in `:writes` and no defcost reads a live rule, and by
E2's W01 differential row once rules change at run time).

| parse code / command | D3 answers |
|---|---|
| `:malformed` | 501, `after` = `:closing` (H pin P-UTF8-WS) |
| `:syntax` | 501, stay |
| `:unknown` | 500 |
| `:state` | the command's declared state refusal (502 transit on a reader connection; 502 AUTHINFO/XREDEEM once authenticated; 480 COMPRESS before authentication) |
| CAPABILITIES | 101 and the always-on labels `VERSION 2`, `READER`, `IMPLEMENTATION`, `LIST ACTIVE ACTIVE.TIMES COUNTS HEADERS MOTD NEWSGROUPS OVERVIEW.FMT`, `OVER MSGID`, `HDR`, `XPAT`, `NEWNEWS`; the conditional slots (`POST` from D5, `IHAVE`/`STREAMING` with the peer bit, `STARTTLS` from E1, `AUTHINFO`/`SASL` from E2, `COMPRESS DEFLATE` only when authenticated, from E2) render nothing until their quest; a label argument must be a keyword-shaped token else 501 |
| HELP | 100 and `*fn2-nntp-help-text*`, dot-terminated |
| QUIT | 205, `after` = `:closing` |
| MODE READER | 201 while posting is not served (D5 turns it to 200 by the same predicate as the greeting); MODE STREAM: 203 on a peer connection, **501 on a reader connection** (deferred sub-form check, RFC 4644 §2.3) |
| DATE | 111 `YYYYMMDDhhmmss` from the clock mailbox's realtime reading (UTC civil date by scalar arithmetic); 503 `:no-observation` before any reading, `:no-wall` when the realtime flag is invalid, `:out-of-range` past year 9999 |
| AUTHINFO | sub-form arity first (USER 1 token, PASS 1, SASL 1 or 2: else 501); then, with no credential store until E2: USER → 381 and the pending slot; PASS after USER → 481; PASS without USER → 482; SASL → 503 `:no-mechanism` |
| XREDEEM | arity (2 tokens) else 501; with no invitations until E2: 482 `:refused` |
| STARTTLS | 580 `:cannot` (no TLS context until D7/E1) |
| GROUP LISTGROUP LIST NEXT LAST NEWGROUPS NEWNEWS ARTICLE HEAD BODY STAT OVER XOVER HDR XHDR XPAT XFN-ZARTICLE XFNCATCHUP | the sub-form checks first (LIST variant arguments: none for MOTD, DISTRIB.PATS, DISTRIBUTIONS, OVERVIEW.FMT, a Message-ID or range for HEADERS, a wildmat for the others; XPAT's patterns as wildmats; HDR/XHDR field-name syntax; XFN-ZARTICLE's 64-hex digest; XFNCATCHUP's field values), each 501 on failure; then the command's declared `:no-projection` 503 until D6 serves it (NEXT/LAST have no projection reply: 412, no group selected, which is true of every D3 connection) |
| POST | 440 `:not-permitted` (the greeting said 201) until D5 |
| IHAVE CHECK TAKETHIS | reader connections: the grammar's 502 state refusal; peer connections arrive with E4 |

Every interim row names the quest that replaces it; the set is a constant
(`*fn2-conn-interim-tags*`) whose emptiness is a D9 acceptance check, so the interim cannot
outlive its quests.

**The deferred fixtures from D2b's oracle** (§6, `DEFERRED` in `tests/grammar-fuzz-oracle.py`)
become D3 fixtures in `fn2/tests/conn-unit.lisp`, one per sub-form, each with a positive and a
negative line, and the oracle's `DEFERRED` list shrinks to nothing as each lands (the oracle then
compares those lines too, through the machine's transcript runner instead of the grammar's).

### 4.4 Timers, refusals, the anonymous principal

The first-command, idle and send deadlines are configured limits (`exposure-first-seconds`,
`exposure-idle-seconds`, specs/nntp.md:2318-2326), and no limit configuration exists before D7's
configuration generations; the row's `deadline` stays `*fn2-no-deadline*` in D3. D7 sets it at the
greeting, after each reply and while a Send is pending, enforces it on the row's run (close without a
reply), and adds the earliest-deadline `ArmWake` from the `:arm-wake` reserve (ROUND2 keeps one
replaceable wake, not one per connection; scenario 18). Capacity refusal (NNT-031/043): the connection
partition keeps one row in reserve; an admission that leaves no other row free is admitted with
`refused` set (the admission seam of 4.5 exposes the partition's free count for this), and `:greeting` renders 400 `:busy` with `after` =
`:closing`. The per-address 400 needs the peer address, which the Accept result does not carry
(ABI row, §8). Every D3 connection is the anonymous principal (`principal-slot` the anonymous slot,
`auth-ref` none) under `anonymous open` on a plaintext listener (§11).

### 4.5 The seam D3 needs from A (sent through main)

A's connection partition is echo's: `fn2-machines-free-head`, `-connection-count`,
`-admission-credits`, `-active-count` and the admission FIFO are initialized from
`*fn2-echo-kind*` (`machines-directory.lisp`), `fn2-machine-admit-connection` installs an echo row
(`:target (fn2-echo :free :command)`), and `fn2-machine-reclaim-connection` returns an echo row.
`fn2-conn` needs the same partition, and A's drivers need echo's unchanged. The exact form asked:

```lisp
;; a kind admitted by the listener declares it:
(defmachine fn2-conn ... :admission (:phase :greeting :ranges (:rx-range :tx-range)) ...)
;; A generates, per admitted kind K (echo and conn), in the directory: the partition scalars as
;; arrays indexed by the admitted-kind ordinal; the operations
;;   fn2-machine-admit-K (index nonce fn2-core)   :target (K :free PHASE)
;;     :effects ((:transfer (:connection-row) :to K) (:acquire RANGES :for K))
;;   fn2-machine-reclaim-K (id retire fn2-core)   :effects ((:release (:connection-row)))
;; and a listener field TARGET (the admitted-kind ordinal), initialized from the profile key
;; :listener-targets (default: every listener admits echo, so every existing profile, driver
;; and A4 summary is unchanged); fn2-listener-admit dispatches on row-target.
```

D's served-node profile then sets `:listener-targets` to `fn2-conn`. Until it lands, D3's tests
install a connection row at the adapter boundary with a test fixture that does what
`fn2-machine-admit-fn2-conn` will (reserve RX/TX, set the row, wake it), and `fn2-conn-drain` uses
the requested reclaim name, so the served path is the requested one from the first commit. The same
request covers D0's planned `:connection :accept` bundle (RX and TX at Accept issue rather than at
admission) as R6b's item, unchanged.

### 4.6 Acceptance of D3 (the checks, before any number)

- `fn2/books/conn.lisp` declares `fn2-conn` through `defmachine` with every arm contracted, none
  `:unchecked`; registered by `assembly-index` after B's books; its continuations in their own
  section book `assembly-callbacks-d.lisp` after `assembly-callbacks` (A's section is at 49 s of the
  60 s rule).
- `fn2/tests/conn-unit.lisp`: transcripts through the real core at the adapter boundary (Receive
  results carrying the client's octets in every chunking, Sends harvested into a wire record):
  greeting; every D3 command, positive and negative; pipelined lines; every split point of every
  transcript (T8's teeth); overflow, malformed and EOF closes; the compaction boundary; drain and
  reclaim with every count back; the deferred sub-form fixtures.
- **WIRE** (`fn2/sim/check-wire.lisp`, built): an independent checker over one connection's client
  octets, server octets and close. Its reply-code table by command keyword is written from RFC 3977,
  4643, 4644, 8054 and specs/nntp.md (it reads neither the grammar nor the core). It checks the
  greeting (200/201, or 400 then close), one reply per client line in order with an admitted code,
  status-line framing, multi-line bodies by command (dot-stuffed, `.CRLF`-terminated), 501 as the
  last reply to a line the spec makes malformed (a NUL, over 512 octets), nothing after a closing
  reply, a closing reply only on a closed stream, and an unfinished body only on a closed stream. In
  `tests/conn-unit.lisp` it passes every fixture and the 24 random transcripts, and catches its three
  mutation controls (a wrong status byte, a missing reply, a reply after the close).
- Scenario 1's plaintext anonymous-reader half under the simulator (`fn2/tests/sim-layer-d.lsp`, an
  LD module; built): the served core with `:listener-targets fn2-conn`, the simulator's adapter
  (`fn2-sim-take-one`, `fn2-sim-advance-with-clients`) and network pipes, clients writing their
  transcripts in seeded chunks (1-37 octets per round) and reading everything the node sends; WIRE over
  every client, and for conn-unit's fixtures the exact reply bytes (the DATE line excepted, which the
  simulator's clock makes 111 and a date). 15 clients per run (7 fixtures, 8 random) on 4 connection
  rows; 3 seeds without faults and 8 with network faults (short sends, delays, reordered releases;
  process death excluded): all quiescent, all WIRE-clean, all fixture bytes exact; 37 s. It found one
  defect, fixed in conn.lisp: a short send that moved zero octets was taken as a failure and closed the
  connection; it is progress deferred (ROUND2 D.1: the remainder is a new Send).
- The surface session (`fn2/tests/sim-session.lsp` with `fn2/tests/surface/fn2_sim_session.py`, the hook
  `FN2_SURFACE_SIM_NNTP=fn2.tests.surface.fn2_sim_session:session` for H's `sim_target.py`): a
  long-lived ACL2 process over the same core and network; open, send in chunks (each delivered, then the
  node runs to quiescence), close (client EOF), stop (WIRE per connection). The interim table as data:
  `fn2/tests/surface/fn2_conn_interim.json` (from `tests/conn-interim-export.lsp`), each command's
  interim reply and the quest that replaces it.
- Keystones admitted (§7): T1 `fn2-turn-served-safety` and T8 `fn2-reply-trace-fragmentation-
  invariant` / `fn2-connection-privacy`, `defthm-owed` over `fn2-conn-wire-run` (the logical view:
  octets and chunk sizes per connection in, the wire record per connection out), with executable
  teeth from conn-unit.
- A's six drivers, `sim-acquisition-driver` and B's `sim-layer-b` exit 0 with the 113 A4 blocks
  identical; every book under 60 s; OWED.md regenerated.

## 5. Catalogue: the machine ownership matrix

Every kind of ROUND2 §B.2, with its owner, phases, retained fields, capacity (§B.1) and simultaneous
per-run budget (§B.3; work stops at any limit). All are declared through A's `defmachine`.

| kind | owner (quest) | phases | retained fields beyond the common row | capacity | per-run budget |
|---|---|---|---|---:|---|
| listener (A's `fn2-listener`) / connection (`fn2-conn`) | D3 | listener `accepting admitting closing`; connection `free greeting command article-input reply upgrading closing draining retired` (§4.2) | capability token; RX/TX ranges; parser offset u32; command ordinal; selected view (version + leases); auth/config refs; active request refs; outstanding-use count u32 | `C` 256, accept credits 8 | 4 KiB parsed/rendered, 32 steps, 4 descriptors |
| TLS admission | D7 | `requested reserved running result-ready cancelling draining done` | connection MRef; config generation; job OpRef; evidence range; negotiated flags; channel-binding digest | `Ltls` 16 | 32 metadata operations |
| upload | D4 | `head identity receiving validating discard sealed aborting draining` | connection/request; source and stored lengths u64; BLAKE3 scan continuation; two chunk ranges; manifest cursor; Message-ID range; transaction ref; TAKETHIS ordinal | `U` 128; windows 16 | 4 KiB scanned/hashed/copied, 32 manifest entries |
| transaction | D5 | `admit lookup reserve prepare ready batched accepted refused uncertain draining` | operation identity (principal-id, operation-id); authority/config version; identity reservation; membership cursor; dependency-manifest root; proposed index root; batch ref; outcome | `T` 128 | 32 index entries/comparisons/units; 4 KiB comparison |
| query cursor | D6 | `select seek need-page inspect render send finish failed` | request kind; pinned view/root; article/group refs; index position; source offset u64; render offset u32; framing state; pending ranges | `X` 256 | 32 examined entries, 4 KiB inspected/rendered |
| consumer wait | D8 | `registering checking parked eligible polling replying cancelling` | consumer/history/incarnation ids; registration epoch; principal/query/view versions; acked and scanned positions; edge head/count; pending-wake bit | `W` 256; `Esub` 4,096 (separate row) | 32 edges or entries, 4 KiB output |
| cache/storage job | D4 (first consumer: upload extents), D6 (reads) | `reserve issue waiting verify ready failed cancelling draining` | expected block identity/address/digest; pool range; OpRef; verification offset; owner/waiter refs | `Jread` 64, `Jwrite` 16 | 4 KiB verify/copy, 32 metadata ops, 4 descriptors |
| timer/grant/wake services | D7 | `idle scanning dispatching pending` | heap/list cursors; resource-wait heads; dirty-subscription cursor; latest clock observation | one each | 32 timers, grants or edges |
| commit batch | **B** (B3b), migrated into the arm contracts by B after R7 | `collect seal dependencies log-write fence durable install publish notify uncertain draining` | batch identity; predecessor head; members; dependency cursor/count; outstanding counts; packed ranges; proposed root; fence OpRef; publication cursor | `B` 2 | 32 members/dependencies or 4 KiB, 4 descriptors |
| cleaner, checkpoint, recovery | **B** | per §B.2 | per §B.2 | one each | 32 entries or 4 KiB |

## 6. The grammar DSL (D2a; `fn2/books/grammar.lisp`, `fn2/books/nntp-grammar.lisp`)

`defgrammar NAME` declares a wire grammar once. It is D's DSL, the third of EXECUTION-MODEL §5. Each
of its entries is DSL-METATHEORY's `command` kind, registered as a `(:command NAME-CMD)` row through
`fn2-declare` (table `fn2-commands`, the one `declare.lisp` clause, carried into dev by the DSL seat
in 5d809cb94). The row's payload is `:grammar :keyword :syntax :protocol-states :state-refusal :block
:block-refusal :hand-off :help :spec :replies`, and its `:generated` manifest is the command's argument parser.

**The declaration.** It gives `:line-cap 512 :args-cap 497 :block-line-cap 1000` (RFC 3977 §3.1;
RFC 5322 §2.1.1) and `:states (:reader :peer :authenticated :anonymous)`, where each state is one bit
of the connection's state mask. A connection is reader or peer, and anonymous or authenticated.
AUTHINFO and XREDEEM are admitted only in `:anonymous`; once a connection is authenticated, the
state refusal answers them 502 whatever their arguments (RFC 4643 §2.2). COMPRESS is admitted only
in `:authenticated`. It also gives `:layers`, which says which state a reply's layer needs
(`:peer` replies need `:peer`). Then come `:fields`, the template field words of the reply texts
(`NUMBER`, `MESSAGE-ID`, `COUNT LOW HIGH GROUP`, `REASON`, `YYYYMMDDhhmmss`, ...); `:general`, the
replies of no command (500, 501, the greetings, the 400s, the 403); and `:commands`. A command entry
has a keyword, typed arguments, admitting states, the reply that refuses it in another state, a block
opening (`(:after 340)`, `(:after 335)` or `(:immediate)`; an immediate block names its
`:block-refusal`, TAKETHIS's 439), a hand-off (`(:tls 382)` or `(:compress
206)`), its HELP row, its spec citation and its replies `(KEY :code :class :layer :text)`.
Argument kinds are `:number` (an article number, 1..2^31-1), `:digits`, `:range` (`n`, `n-`, `n-m`,
with the open end `*fn2-none*`), `:msgid`, `:ref` and `:ref-range` (a Message-ID when the token opens
with `<`), `:wildmat`, `:label`, `:date`, `:time`, `:gmt`, `:token`, `:rest` and `(:keyword W ...)`,
each optional under `(:opt K)`, with at most four per command.

**Generated, scalar, over pool slots.**
- The command-tag and reply-tag enums and the state bits, all as named constants.
- The keyword matcher, which is case-insensitive.
- Per-command argument parsers, plus the state, block and hand-off tables.
- `NAME-parse-line`. It takes one complete line `[s, e)` and returns `(mv code tag nargs f0 a0 b0 ...
  f3 a3 b3)`, where CODE is `:ok`, `:malformed` (empty line, bare LF or CR, NUL, ill-formed UTF-8:
  reply 501 and close), `:syntax` (501), `:unknown` (500), `:state` (the command's state refusal),
  or `:discard`. `:discard` applies to a command whose block follows at once (TAKETHIS, RFC 4644
  §2.5.2) and whose line would otherwise be malformed or a syntax error. It applies only when the
  keyword stands first, a state admits the command, and the line is framed structurally (it ends
  in CRLF and holds no other NUL, CR or LF). There is no reply to the line. The block that follows
  is framed and discarded, and the `:block-refusal` reply is due after its terminator. The rule
  exists because without it a malformed TAKETHIS would have its article read back as commands
  (NNT-003). H's model over the fuzz cases found it.
  Each argument is a descriptor: a value, a range, a keyword index or an `(offset, length)` span in
  the RX slot, never copied.
- `NAME-render`. It is typed: a reply is written only for its own command, in a state its layer
  admits. It appends `NNN text CRLF` to a TX slot from the compiled template, with numbers and one
  span.
- The generic framer `fn2-gram-frame`, a bounded continuation over `[pos, fill)` whose whole state
  is `(start pos overflow)`. A line over the cap stops being retained, so retention never exceeds
  the cap. The framer is shared by command lines and by `fn2-gram-block-step` (dot-unstuffing, the
  terminator, a bare LF / NUL / unescaped leading dot as `:bad-line`, discard to the terminator by
  the caller).
- The two hand-offs. After 382 (STARTTLS) or 206 (COMPRESS, which is admitted only in
  `:authenticated`, per NNT-054 and H's ruling) the grammar frames nothing more.

Bytes are read and written only through `fn2-pool-read` / `fn2-pool-write`. No served path builds a
list of octets.

**Obligations** (`defthm-owed`, teeth in `fn2/tests/grammar-unit.lisp`). The five grammar
obligations are covered by four rows:

| row | covers | teeth |
|---|---|---|
| `fn2-gram-frame-total-linear` | framer totality, linear consumption, bounded retention | every `(start, pos)` of six transcripts (one holds all 256 octet values) at budgets 1 and 4096 and caps 512 and 4; negative: four wrong outcomes |
| `fn2-nntp-parse-total` | parse totality over arbitrary octets (guard only) | the same probe; negative: shapes a wrong parser would produce |
| `fn2-nntp-fragmentation` | fragmentation invariance | 29 transcripts × 3 state masks, every split point, every pair for those of at most 64 octets, and bytewise arrival, equal on events and on rendered reply bytes; negative: a chunker that forgets the retained line |
| `fn2-nntp-reply-typing` | reply typing | every reply × every command tag × 3 masks; negative: an untyped renderer |

The fragmentation statement is about the transcript runner `fn2-nntp-run`, a logical view over an
octet list. It drives the real framer, parser and renderer over a local pool, assuming each
block-opening reply is granted. Twenty-five transcripts have independently written expected outcome
codes, so a parser that is split-invariant but wrong still fails them.

**Checked against H's model.** `fn2/tests/grammar-export.lsp` writes the declared table and the
validators' verdicts on a 90-string seeded sample. `fn2/tests/grammar-oracle.py` checks four things:
the keyword set equals `KEYWORDS`; the HELP text equals `HELP`; every citation is the model's
`SPECS` entry; and every Message-ID, range and wildmat verdict agrees with `msgid`, `number_range`
and `wildmat`. Result: 0 disagreements. The oracle catches a mutated row or verdict.

**Resolved disagreements and departures.**
- HELP is the six rows of `specs/nntp.md:51-93` and of H's `HELP`. XFNCATCHUP and XFN-ZARTICLE are
  recognized but have no HELP row (`:help nil`). fn1's served table has a seventh row with them,
  which contradicts the spec text, and the spec text wins.
- Overlength is checked in two places, as RFC 3977 §3.1 has it. A line of 513 octets or more is
  `:overflow`: reply 501 and close (H's `_malformed(overlong=True)`). Within the cap, arguments
  longer than 497 octets get 501 and the connection stays.
- fn1's "done|more" XFNCATCHUP reply becomes two replies.
- The parser reads through the pool library's `fn2-pool-read`, not `fn2-core-read`. The grammar is a
  library over `fn2-pool` and needs no core instance. OWN's read hook must cover `fn2-pool-read` (or
  the range primitives of D2c) when D3 serves it; R5b's rule.
- What depends on a sub-form or on the connection kind is D3's decision table
  (`books/conn-answer.lisp`, section 4.3): AUTHINFO arity, XFN-ZARTICLE's digests, MODE STREAM on a
  reader connection, LIST variant arguments, XPAT's wildmat, HDR/XHDR field names (XREDEEM's code is
  any token, per H's model; XFNCATCHUP's fields are the grammar's own kinds). Each has a fixture in
  `tests/conn-answer-unit.lisp`, and the fuzz oracle no longer defers them: the export carries each
  line's decision-table status code, and the model's 501 and D3's 501 must agree both ways on every
  parsed line (4,416 cases, 13,501 lines, 0 disagreements).
- XOVER takes a range only (RFC 2980 §2.8). The table had `:ref-range`, copied from OVER; H's model
  over the fuzz cases found the difference.
- H's pin P-UTF8-WS (whitespace on an ill-formed UTF-8 line is still malformed: 501 and close) is
  the oracle's rule; its former exception for the model's whitespace-first order is deleted.
- The framer finds line ends with one R6a1 `fn2-pool-scan` per run (D2c): the octet loop is gone
  from the served path and survives only in `tests/grammar-unit.lisp` as the reference the scan-based
  framer must equal at every (start, pos), budget, cap and overflow state of the probe transcripts.
  Prefix retention is the connection's: R6a1's `fn2-core-drop-prefix` (section 4.2).

**The fuzzer (D2b; form F of RELEASE-PLAN §2.4).** `defgrammar-generator NAME`
(`fn2/tests/grammar-gen.lisp`) reads NAME's `(:command ...)` rows from the declaration table, so
the generator works from the same declared table as the parser. It emits `NAME-generate seed mask
budget` and `NAME-mutate seed class mask budget spec`. A case is `(octets events replies mode)`: the
transcript, the events the transcript runner must report, the reply codes it must render, and the
mode it must end in. Randomness comes from the simulator's PRNG (`sim/prng`), so every case replays
from `(seed, class, mask, budget)`.

- **Generated.** A generated transcript holds one to six pipelined command lines, all admitted by
  the mask. Keywords come in random case, and separators are runs of SP/TAB. Every argument kind has
  its own generator: numbers at their edges, `n`, `n-` and `n-m` ranges, Message-IDs over RFC 3977
  §3.6's octets, wildmats with negated alternatives, labels, calendar dates of six or eight digits,
  times, GMT, tokens and rests. Block commands carry a dot-stuffed block that contains empty lines,
  dot-led lines, 8-bit octets and long lines of up to 998 octets. A hand-off command (STARTTLS, or
  COMPRESS when authenticated) ends the transcript. The expected event of each line is exact: its
  tag, its argument count, and every argument descriptor, spans included.
- **Mutated.** Twenty-one operators each change one line or one block line inside a transcript that
  has valid commands before and after it, so the case also observes what follows a refusal. The
  line operators are NUL, bare CR, bare LF, ill-formed UTF-8, the empty line, a control octet,
  leading or trailing whitespace, a line over 512 octets, arguments over 497 octets, an unknown
  keyword, an extra argument, a missing argument, an argument invalid for its kind, and a command in
  a state that refuses it. The block operators are an unstuffed leading dot, NUL, bare CR, bare LF,
  a line over 1,000 octets, and a missing terminator. The reply that each mutation must receive
  comes from the spec table `*fn2-gf-spec*` (`tests/grammar-fuzz.lisp`). That table is written from
  RFC 3977 §§3.1, 3.1.1, 3.2.1, RFC 5322 §2.1.1, `specs/nntp.md` and H's COMPRESS ruling, one
  citation per row, and is never read from the grammar. For example: 501 and close for a malformed
  line, 501 for a syntax error, 500 for an unknown keyword, 502 for transit commands on a reader
  connection, 480 for COMPRESS before authentication, and a `:bad-line` event for a block line.
- **Random.** One to three byte operations are applied to a valid transcript: a flip, an insertion
  of CR, LF, NUL, `.`, SP, TAB or an 8-bit octet, a deletion, or a truncation. A random case has no
  expectation of its own.
- **Checked on every case.** Every case runs through the real framer, parser and renderer, both
  unsplit and in a seeded chunking whose deliveries are bounded by the simulator's network capacity
  (`*fn2-sim-network-capacity*`, 4,096). Each framer call runs within the 4 KiB run quantum. A case
  must match its expectation if it has one. It must also be sound: every event is declared and
  well formed, every reply passes its type check, there is one reply line per command or overflow,
  and the run stops exactly where the grammar stops. And it must be invariant under fragmentation:
  the chunked run equals the unsplit run, and for the first four seeds every split point is checked.
- **Result.** 256 seeds × 3 masks (anonymous reader, anonymous peer, authenticated reader) × 23 classes (valid, 21
  operators, random) give 17,664 cases. None fails and no class is skipped. The run is
  `tests/grammar-fuzz.lisp`, certified in 12.2 s; its tallies are in the `.cert.out`.
- **Mutation controls.** The grammar's logical runner takes `fault`, which is nil in every statement
  (`NAME-run` is `NAME-run-fault` with no fault). Each of the three faults makes the runner a
  deliberately wrong grammar:
  - `:accept` takes an argument that its syntax refuses (a wrong acceptance);
  - `:reply` answers a syntax refusal with 500 (a wrong reply);
  - `:drop` keeps the connection open after a malformed line (a dropped effect: the close).

  The same campaign (16 seeds) catches all three, and the book asserts which classes catch each one.
  `:accept` is caught by extra-arg, missing-arg and bad-arg. `:reply` is caught by every class whose
  spec reply is 501. `:drop` is caught by the five malformed classes, and by random mutations.
- **Not yet covered.** D2b exercises the grammar layer only: the framer, the parser, the typed
  refusals and the hand-offs, through the transcript runner and its test responder (a line that
  parses gets the command's first declared reply). The served replies, the WIRE and WORK checkers,
  and the scenario `fuzz-nntp` under the simulator wait for D3's connection machine. Running against
  a live node (`tests/test_fuzz_nntp.py` with fn1's nine reproducer sets) waits for D9.
- **H's model as the second oracle.** `tests/grammar-fuzz-export.lsp` writes the cases of 64 seeds,
  4,416 in all, together with the grammar's verdict on every framed command line.
  `tests/grammar-fuzz-oracle.py` sends each line alone to a fresh model connection in the case's
  state and compares the two on the syntax layer: malformed means 501 and close; syntax means 501;
  unknown means 500; state means 480 or 502; discard means no reply and the article read; and a
  line that parses must not get 500, or 501 alone. On its first run the oracle reported 382
  disagreements. Three of them were grammar defects, all now fixed: TAKETHIS's refused line (the
  `:discard` rule), AUTHINFO and XREDEEM after authentication (the `:anonymous` state), and XOVER's
  Message-ID. The rest were sub-form checks that belong to D3, which are now named. Result: 13,501
  lines, 0 disagreements.

## 7. Keystones, phased

| statement | admitted with | over |
|---|---|---|
| T10 `fn2-core-state-bounded` | D1a (owed, with teeth) | the assembled core's children and their `fn2-columns` rows: a generated resident measure, the same for every core initialized from one profile, and unchanged by `fn2-turn` and by the adapter-boundary entries `fn2-outbox-ack`, `fn2-post-result`, `fn2-post-clock` (no array grows after init) |
| T1 `fn2-turn-served-safety`, T8 `fn2-reply-trace-fragmentation-invariant` / `fn2-connection-privacy`, and the interim `fn2-conn-reader-only-interim` | D3 (owed, with teeth: `fn2/books/owed-conn.lisp`, `fn2/tests/conn-unit.lisp`) | `fn2-conn-wire-run`, the served core at its adapter boundary with scripted clients (octets in chunks in, wire and close out, stop reason) |
| T6 `fn2-refusal-no-committed-mutation` / `fn2-outcomes-three`, T9 `fn2-exact-identity` | D5 | the transaction machine, C's identity schema, B's commit batch |
| closure audit `fn2/tests/turn-guards.lisp` | D9 | `fn2-turn`'s executable closure |

**T1 and T8 as built (D3).** `fn2/books/owed-conn.lisp` defines the logical view
`fn2-conn-wire-run`: the served core (`fn2-init-executor` with `:listener-targets fn2-conn` and a
pool of 1,024-octet slots) driven by real turns, with an adapter that completes the outbox head:
Accepts in client order (capability index = client index), each Receive with the client's next
chunk (left pending once the client has sent everything), each Send recorded on the client's wire
with its terminal and release, each Close. It returns, per client, the wire and whether the core
closed it, plus the status (`:quiet` after three idle rounds) and the core's stop reason. T1:
any client octets in any chunks on up to four connections end quiescent with the core never
stopped (every run, handler and reached call kept its contract and guard, since a violation stops
the core by name). T8 fragmentation: a client's wire and close do not depend on its chunking. T8
privacy: a client's wire and close in a two-client run are those it gets alone (D3's only shared
input is the clock, not posted in these runs). The peer-address interim is owed too: a first
`MODE STREAM` gets the reader greeting and 501, whatever follows; lifting it (A5r's address words,
E4's peer records) replaces the row. Teeth (`tests/conn-unit.lisp`): seven spec-written transcripts
(the greeting alone, pipelined CAPABILITIES/HELP/QUIT, DATE/MODE, unknown/interim/NEXT, a NUL, a
600-octet line, 150 lines across the slot); every split point and bytewise arrival of the short
ones and 7- and 300-octet chunkings of the long ones; four two-client pairs; 24 seeded random
transcripts in seeded chunks; each negative tooth refuses a wrong runner or result.

**T10 as built (D1a).** `fn2/books/resident.lisp` is a library over the core-child registry. Its
generator, `fn2-resident-measure-events`, emits one measure per registered child: the rows scalar
(sized by `:rows-bound`), every column array's actual length times its declared width in bytes
(`fn2-columns-width`, rounded up to whole bytes), and every extra field, whether an array (actual
length × element bytes) or a scalar. It also emits their sum, `fn2-core-resident-measure`, and a
per-child breakdown. A field it cannot measure (a hash table, a nested stobj, an untyped array) is
refused at expansion by name unless the child's `:why` states its bound. Today no field is refused
(`*fn2-resident-refused*` is nil). `fn2/books/owed-d.lisp` expands the generator once over the served
assembly and states T10. `tests/owed-d-unit.lisp` holds the teeth. The positive tooth covers the
tiny, near-limit and concrete profiles: each is initialized twice, then driven for 40 steps through
the real executor (turns, outbox acknowledgements, Accept results, clock observations), and the
measure must not change at any step. The negative tooth grows the pool's byte array after init.
`tests/owed-d-coverage.lisp` expands the same generator in the separate test instance and checks
that it measures that instance's test-only child and machine, and that four more test-child rows
add exactly 16 bytes.

The measured resident bytes, at declared widths:

| child | tiny | concrete |
|---|---:|---:|
| fn2-core-pool | 2,705 | 7,387,601 |
| fn2-core-ops | 1,324 | 161,900 |
| fn2-core-sched | 177 | 4,023 |
| fn2-core-machines | 1,123 | 2,413 |
| fn2-core-trace | 3,813 | 60,693 |
| fn2-core-control | 70 | 70 |
| fn2-listener-table | 98 | 380 |
| fn2-echo-table | 300 | 18,948 |
| fn2-scribe-table | 92 | 92 |
| **total** | **9,702** | **7,636,120** |

T10 does not cover the adapter, the SBCL runtime (u60 arrays take 8 bytes per element there, which
the declared width matches; headers are excluded) or the simulator's own state; that is W13's
guardrail. Layer B's children join the table when B registers them in the assembly; the generator
reads the registry, so nothing here changes.

## 8. The ABI reconciled *(D3 design; the D3 commits fill the last column)*

ROUND2 §D against A's `a-pool-host-sim.md` §4 as built, for what D's machines use. A difference is
resolved here or sent as a seam request; none is silently absorbed.

| ROUND2 §D | A as built | D's resolution |
|---|---|---|
| `AcceptResult` carries a fixed-width peer address/credentials | capability `(index, nonce)` only | per-address 400s (NNT-043) and the peer bit need the address: seam request to A (an address word pair in the result's aux fields, filled by the adapter, a fixed opaque value in the simulator); until then no per-address refusal and every connection is a reader |
| `Send` with at most 4 immutable ranges | one range | D3 renders status line and fixed body into one TX range, so one range suffices; the cursor (D6) streams a stored body by successive single-range sends (a short send is terminal, ROUND2 D.1); the four-range form is a later performance change, not a semantic one |
| `Accept` takes a reserved connection slot (and its windows) | the row credit at issue, the RX slot at admission (owed R6b) | D0's planned `:connection :accept` bundle (row, RX, TX at issue) is R6b's; D3 works with A's current split, where an admission without its ranges closes the capability (A's posture) |
| `Close` from a protected reserve | ordinary op reservation (owed R6b) | D3's `:closing` uses `fn2-issue-close` as echo does; it gains the reserve with R6b, no D change |
| `Connect` (E4's peers) | absent | E4's; recorded so E4 asks A for it with the peer quest |
| `ControlObserved` / `Qc` | absent (a sticky signal word only) | D9 (shutdown and reload); the seam request goes to A with D9 |
| `EvidenceObserved` | absent | E2/E6 (evidence for authentication and key statements) |
| `ServicePosture` | absent | B's recovery posture and D9's serving posture; requested with D9 |
| `Trace` payloads | A's bounded trace child | D's machines add no trace kinds in D3 |
| `ClockObserved` (one coalesced mailbox) | `fn2-ops-clock-mono/-real/-flags` | DATE and the deadlines read it through `fn2-conn-clock`; no difference |
| `ArmWake` (one replaceable wake) | `fn2-issue-arm-wake` | D7's timer service owns it; no connection issues one |

## 9. The sprint's gaps, and how D plans around them

The sprint (`origin/fn2/sprint-cd` 8e3488fcb) is compost; its gaps are the seams.

| gap | state | plan |
|---|---|---|
| G1 closed machine registry | closed by R5c's open registry (`defcorechild`, assembly sections) | D's kinds register in D books included by `assembly-index` after B's |
| GD1 dispatcher fallback hardwired to A's core | closed by the same: the generated dispatch's refusal arm receives the assembled `fn2-core` | none |
| GD2 no commit/recovery machine | B3b on `fn2/b-durability` | D5 references B's batch; no stand-in persistence |
| GD3 no arm cost/frame contract | R7 | §4's seam request; D3 builds on R7 (landed) |
| GD4 no retained-prefix compaction | R6a1 `fn2-pool-drop-prefix` | closed: D3's connection compacts with `fn2-core-drop-prefix`; D2c put the framer on `fn2-pool-scan` |
| GC1 no two-owner range compare | R6a1 `fn2-pool-compare` | C's and D5's consumer |

## 10. Departures, seam requests and open items

- Row 1 of ROUND2 §B.2 is two kinds: A's `fn2-listener` (`:accepting :admitting :closing`) and D's
  `fn2-conn`; the brief's `accepting` phase is the listener's (§4.2).
- D4/D5 seams (§14.7, sent through main 2026-10-30): A-S7 taken kinds, A-S8 cross-owner copy, B-S1
  hasher rows by profile, B-S2 the transaction member, C-S1 identity in the served assembly, C-S2 the
  private successor overlay.
- Seam request to A (through main, 2026-10-30): the connection partition per admitted kind and the
  listener's target (§4.5, exact form); the Accept result's peer address (§8).
- R6b item 1 re-cut onto D0 (§2); R7 carried §4's forms (done, 926b09328).
- `declare.lisp` gained the `command` kind's table entry (D2a), purely additive.
- D3's interim replies (§4.3) are a named constant whose emptiness is a D9 check.
- D7's interim booking point (§13.4): a connection books its principal's `:connection-row` at the
  greeting, not at Accept issue, so the rows between Accept and greeting are unattributed; S1 closes it.
- Echo stays A's test workload in the served instance (A4's drivers); the served listener admits
  `fn2-conn` once §4.5 lands. Whether echo leaves the served instance is A's call.

## 11. Deferred assertions E must restore

D gates only what it can execute without authentication, access rules, the TLS adapter or the CLI
(brief, "Acceptance"). Every assertion it cannot gate is listed here, per command or behaviour. Each
row gives the D quest that builds the half D owns, the reason D cannot assert the rest, and the E
quest that restores it, with its test (RELEASE-PLAN §1.1). Until E restores a row, D's simulator
scenarios run with an anonymous principal under `anonymous open` on a plaintext listener, and its
natives skip the row by name. A row leaves this table only when E's test is green.

| command or behaviour | D builds (quest) | what D cannot assert | E restores (quest): test |
|---|---|---|---|
| every reader and posting command under `anonymous none` / `auth required`: 480 | D2 (480 replies declared; COMPRESS's 480 is grammar-level), D3 (the connection carries its auth reference, anonymous until set) | that an unauthenticated session gets 480 for every command but the public set (`specs/nntp.md:2322`), and that the pinned configuration decides it | E2: `auth`, `public_exposure`; the H model's `_requires_auth` |
| the pinned access rule (H ruling HZ3, fn1 bug W01) | D3 (one access-rule reference per connection, pinned at authentication and re-read only at re-authentication; every command reads that one reference) | that LIST ACTIVE, GROUP, ARTICLE and POST apply the same pinned rule after an `account access` change on an open connection | E2: `group_access`; a W01 differential row in H |
| GROUP/LISTGROUP/ARTICLE/... on a group the login cannot read: "no such newsgroup" (411/430), never a distinguishing refusal | D6 (the cursor answers from the visibility the connection's view grants) | the visibility itself: read wildmats, private groups, moderation queues | E2: `group_access`, `visibility_join` |
| POST 440 (`:principal`, `:not-permitted`), read-only and moderated groups, `Approved` from a moderator only, signed-post bindings | D5 (the transaction's typed refusals, each a fixture) | which principal may post where, who moderates, the hybrid-signature binding | E2, E6: `moderation`, `hybrid_author`, `key_statements` |
| CAPABILITIES conditional labels (POST, IHAVE, STREAMING, STARTTLS, AUTHINFO, SASL, COMPRESS, XFN-DICT) | D3 (the always-on labels; the slots for the conditional ones) | the conditions: TLS state, the auth profile, the peer record, the shipped dictionaries | E1, E2, E4: `conformance`, `auth`, `sasl`, `compress`, `implicit_tls` |
| AUTHINFO USER/PASS, SASL PLAIN/SCRAM/SCRAM-PLUS (381/281/481/482/483/383/283/503/504) | D2 (the grammar; 502 once authenticated, fuzz-checked against H's model), D3 (sub-form arity, the auth reference, the 483 slot) | the credential check, the verifier `:fn-authsec-v2`, SCRAM, channel binding, the third failure's 481 + 400 + close (NNT-1002) | E2: `auth`, `sasl`, the RFC 7677 vectors |
| XREDEEM (381/281/482/483) | D2 (the grammar; 502 once authenticated), D3 (arity) | invitation codes and account binding | E2: `friends_accounts`, `consumer_identity` |
| STARTTLS (382; nothing framed during the handshake; 502 after auth, twice, or after COMPRESS; 580) | D2 (the hand-off), D7 (the admission machine, `Ltls` 16, the simulator's TLS stub; scenario 18's admission half) | the handshake, the reset of group and cursor after it, key exchange, certificate reload | E1: `starttls`, `tls_handshake_budget`, `tls_key_exchange`, `tls_reload` |
| implicit TLS listener, protected-only (483 before TLS), the PROXY header | D3 (a listener kind field) | everything: E's listener and adapter | E1: `implicit_tls`, `tls_transport`, `tls_proxy` |
| COMPRESS DEFLATE (206; the bomb and BFINAL close rules) and XFN-DICT / XFN-ZARTICLE (229) | D2 (the grammar: 480 before authentication, the hand-off after 206; XFN-ZARTICLE's line), D3 (the digest syntax) | the inflate and deflate streams, the dictionaries, the stored-payload carriage | E2: `compress`, new native `compress_dict` |
| IHAVE/CHECK/TAKETHIS identity of the peer; transit body bound from the peer record's `inbound-max-octets` | D3 (the peer bit of the connection), D4 (the bound as a parameter; 437/439 then close; scenario 4), D5 (offer/transfer decisions; scenario 5) | which addresses are peers and their records' limits and max-inflight | E4: `peering`, `peer_misbehaving`, `peer_hostile_feed` |
| XFNCATCHUP (291/423/501) | D2 (the grammar; 502 on a reader connection), D3 (field values) | the catch-up log and its chain | E4: `peer_catchup` |
| live limits and `policy set` (capacity 400s, pacing, posts per minute, timers) | D7 (the limits as configuration generations in the simulator; scenarios 10, 11, 18) | the operator verbs that change them on a live node | E6: `limits_live`, `live_reconfiguration`, `public_limits` |
| the Qc control inbox's operator sources (shutdown, reload) | D9 (Qc delivered by the simulator and the adapter) | the CLI and signals that write it | E6: `operator_verbs`, `operator_cli` |

## 12. Quests

| quest | contents | waits on | state |
|---|---|---|---|
| D0 | resources.lisp, the tables of §3 as data with certification checks, the owed deadlock-freedom keystone, per-bundle exhaustion and cancellation scenarios for A's existing bundles | A only | done |
| D1a | T10 in owed-d.lisp with teeth | A only | done |
| D2a | defgrammar, the NNTP table, parser, renderer, obligation stubs, every-split test, H-model table check | A only | done |
| D2b | generator, mutator, fuzzer, the three mutation controls, H's model over the cases | D2a | done |
| D2c | framer onto R6a1's scan (drop-prefix is the connection's compaction) | R6a1 | done |
| D3 | connection machine (§4.2-4.6): conn.lisp, the decision table, the deferred sub-form fixtures, WIRE, T1 and T8, scenario 1's plaintext half, the surface session hook | R7, the admission seam a20fac18f | done (ec9b96173) |
| D7 | the ledger, the scheduler over principals, the services, TLS admission (§13, six slices) | A's seam S1-S5 for 4/n | 1/n design, 2/n ledger, 3/n served booking and ACCOUNT |
| D4, D5 | designed together (§14): the article input path, the upload machine, the transaction machine; six slices | §14.7: A-S7, A-S8, B-S1, B-S2, C-S1, C-S2 | §14 design |
| D6, D8, D9 | per the brief | D6: C3 (C3a on dev 654d1fd39) | |

## 13. D7: principals, the ledger and the scheduler over them *(design; D7's commits rewrite it as built)*

The contract is brief item 7 over EXECUTION-MODEL rule 5, ROUND2 §B.2 (principal accounts are shared
ledger rows), §C (the calendar, turn bounds, starvation) and D0's `:principal-reservation` (rank 6,
reserve `:system`) and `:connection :request` bundle. Reviewed with Astra before the first line of
code (`build/d-seat/d7-astra-1.md`); every change it asked for is taken below, and where it named a
choice D defers, both positions are recorded. The slices, in the order they land:

| slice | contents | waits on |
|---|---|---|
| D7 1/n | this section; the seam request to A (13.6) | nothing |
| D7 2/n | `fn2/books/accounts.lisp`: the ledger as a library (columns, configuration, operations, the local keystones proved), `fn2/tests/accounts-unit.lisp` | nothing |
| D7 3/n | the ledger registered as a core child; `fn2-conn` booked at its greeting (interim, 13.4) and charged from its first byte; the ACCOUNT checker `fn2/sim/check-account.lisp`; scenario 11's anonymous-flood half under the simulator | 2/n |
| D7 4/n | booking at Accept issue; the request bundle with its wait and the grant service; run charges; calendar weights; re-attribution (S1-S5 landed by A; D's half is 13.8: 4/n-a the ledger's request operations and grants, 4/n-b the connection's bundle at its port) | 4/n-a nothing; 4/n-b the form (P4) |
| D7 5/n | the timer service: the deadlines of 4.4 and the earliest-deadline `ArmWake`; scenario 18's expiry half | 3/n |
| D7 6/n | the TLS admission machine (`fn2/books/tls-admit.lisp`, `Ltls` 16, the simulator's TLS stub); scenario 18's admission half; scenario 10 | 5/n |

### 13.1 What stands (A4's scheduler, `fn2/books/sched.lisp`)

The calendar of `L = P + 4·ceil(P/16)` entries (16 principal slots, then commit, timer/grant, wake,
maintenance), one cursor, a FIFO of runnable machines per principal slot keyed by the row's common
`principal-slot`, four service bits, and the owed `fn2-sched-starvation` (a continuously eligible
principal is visited within L visits). Every machine today runs on slot 0. Missing: the ledger, any
attribution, any charge, weights, the request bundle and its wait, protected reservations.

### 13.2 The ledger `fn2-accounts` (`fn2/books/accounts.lisp`, D's core child)

One row per principal slot, `P + 1` rows: slots `0 .. P-1` are the calendar's principal slots (slot 0
is the anonymous principal every unauthenticated connection shares, ROUND2 §C.2); row `P` is the
**system row**, never in the calendar: recovery and control book there, and the system reserve
(D0's `:system`) is simply its reserve. The scheduler's runnable heads, tails and counts are already
indexed by the same slot; the ledger does not copy them (ROUND2 §B.2's "runnable-list heads" are
sched's arrays read through the slot).

Per row: `state` (`:free :anonymous :configured :system`; E2 adds `:authenticated`), `weight` (u8,
calendar entries per round, at least 1), `wait-head wait-tail` (the request FIFO, 4/n), and, in
dimension-major arrays, per **holding dimension** `d` a `limit`, `reserve` and `hold` (u32), per
**charge dimension** `c` a `charge` (u60, monotone). Per dimension: `capacity` N and `committed`. The
dimensions are data (`*fn2-account-holdings*`, `*fn2-account-charges*`), and every use names its
dimension by keyword through `(fn2-account-holding :connection-row)` / `(fn2-account-charge-dim
:rx-octets)`, resolved at expansion (an unknown name is refused):

| holding dimension (a D0 kind) | unit | capacity N | booked by | why it is its own dimension |
|---|---|---|---|---|
| `:connection-row` | row | `C` | `fn2-conn` (13.4) | the entitlement to a connection; RX and TX ranges are held one each per row for its lifetime, so this dimension accounts them too; they get their own dimension when a holder can hold a varying amount (D6's output windows) |
| `:principal-reservation` | request | `C` (one per holder; today only connections hold one) | the request bundle (4/n) | concurrent requests of a principal; D0's bound column says `(:profile :p)`, which counts principals, not requests; corrected with 4/n |

D4-D6 add `:upload-row :chunk-window :transaction-row :cursor-row :cache-pin :storage-job`, one line
each. Charge dimensions: `:rx-octets` and `:tx-octets` (settled from completion counts), `:requests`
(replies rendered for framed lines), `:run-steps` and `:run-bytes` (per scheduled run, 4/n).
Maintenance debt joins with the cleaner's quest (13.3's rule (c)), not before.

**Configuration.** Profile key `:accounts` (optional, read with `fn2-profile-get`; A's `profile.lisp`
is untouched): `((SLOT :state S :weight W :limits ((DIM . N) ...) :reserves ((DIM . N) ...)) ...)`,
SLOT a slot below P or `:system`. Unconfigured: slot 0 `:anonymous` and the system row with every
limit the dimension's capacity and no reserve, every other slot `:free` with limits 0.
`fn2-accounts-profilep` refuses an unknown dimension, a slot outside P, a duplicate slot, a reserve
over its limit, a weight outside 1..255, and reserves summing over a capacity.

**The admission rule** (protected reservations). `committed-d = Σ_{q=0..P} max(hold_q, reserve_q)`,
the system row included; the invariant `fn2-accounts-conservedp` is, for every dimension, `committed =`
that sum `≤ N` and `hold_q ≤ limit_q` on every row. `acquire(p, d, a)`: with `h' = hold_p + a`,
refuse `:limit` when `h' > limit_p`; with `extra = max(h', reserve_p) − max(hold_p, reserve_p)` (the
part above p's own reserve, exactly the change in committed), refuse `:shared` when `committed + extra
> N`; else hold and committed move together. `release(p, d, a)` subtracts `max(h, r) − max(h − a, r)`
from committed: releasing below one's reserve frees no shared capacity. A release of more than is
held is `:underflow`, and the caller stops the core (assert, never absorb). `acquire2` takes two
dimensions whole or not at all. Codes are keywords; `:bounds`, `:underflow` and `:state` are
invariant failures the caller turns into a stop.

### 13.3 Rule 5, operation by operation

| rule 5 clause | where it is enforced |
|---|---|
| reserve before issuing work | a holder books or reserves before the transition that uses the resource; on refusal it holds nothing new |
| settle on completion | charges are added from completion counts (`count` of a Receive or Send result), never from requested lengths |
| disconnecting erases no charge | `release` touches holdings only; no operation decreases a charge (proved, 13.5); a drained connection's charges stay on its principal |
| authentication transfers attribution without laundering | `fn2-account-attribute (from to ...)` is **one net change**: release on FROM, acquire on TO, and on TO's refusal acquire back on FROM (which cannot be refused), so a capacity-neutral transfer is never refused for want of shared room (Astra) and a refused one leaves the ledger as it was; charges stay on FROM. The machine's `principal-slot` and its scheduler membership, runnable or parked, move with it (S4). E2's authentication arm calls it |
| shared costs have an explicit allocation rule | stated here, implemented by the quests that create the costs: (a) a commit batch's padding and fence work is divided among its members in proportion to their packed bytes, the rounding remainder to the system row (B, D5); (b) cache occupancy is `:cache-pin` holdings of the pinning principal while pinned and the system row's when unpinned (D6); (c) cleaning, relocation and checkpoint work is maintenance debt of the principal whose live extents it moves or covers, executed by the maintenance service class; a principal whose debt exceeds its debt limit is refused new storage writes with the transient refusal (backpressure, never loss) |
| a system reserve covers recovery and control | recovery and control book on the system row; its reserve is the system reserve; no principal can draw it |

### 13.4 The connection, charged from its first byte

`account-ref` (a common row field, unused until now) names the ledger row the row's holdings are
booked on, `*fn2-none*` while nothing is booked; `principal-slot` names the calendar slot it runs
under. They are equal once booked.

- **Where the booking belongs (Astra; adopted for 4/n).** A booking at the greeting leaves a hole:
  the listener has already spent a physical connection row and RX/TX ranges before `fn2-conn-greet`
  runs, so unbooked admissions and refused connections draining their 400 occupy capacity no principal
  was charged for. The right point is the listener's Accept issue: the listener's accept bundle
  reserves its principal's `:connection-row` entitlement beside the physical credit, the admission
  transfers that booking to the admitted row, a failed Accept releases it (S1). A listener labelled
  with a protected principal must itself be a trusted entrance (an operator socket, a configured peer
  address), or anonymous callers spend that principal's reserve.
- **3/n, the interim.** Until S1 lands, `fn2-conn-greet` books `:connection-row 1` on its slot (0)
  before rendering; refused (`:limit` or `:shared`) it renders the capacity 400 exactly as the
  partition's reserve row does today (A keeps one physical row for it) and books nothing. The hole
  above is open by at most the physical rows between Accept and greeting; it is listed in section 10
  and closed by S1.
- **Charges.** The receive-result handler adds the completion's `count` to `:rx-octets` of the row's
  principal (before the greeting too: the first byte is charged); the send-result handler adds to
  `:tx-octets`; the frame run adds 1 to `:requests` per answered line.
- **Drain.** `fn2-conn-release` releases `:connection-row 1` from `account-ref` and resets it to
  `*fn2-none*` before reclaiming the row; its charges stay.
- **The request bundle (4/n).** D0's `:connection :request`: `:principal-reservation`, held from the
  framed line to the reply's last octet. Two positions on the reply that carries no request (the
  greeting, the capacity 400): Astra would give it its own phase `:control-reply`, charged to a
  bounded control allocation, sharing the send continuation with `:reply`; D's first draft made the
  greeting request-bearing and gave only the 400 a phase `:refusing`. Either is exact under per-phase
  holds; D takes `:control-reply` (it also bounds refusal traffic, which `:refusing` left unaccounted).
  **The wait:** a refused reservation parks the row on its principal's FIFO in the same transition
  that refused it (failed acquisition and enqueue are one step; the framed line's `start pos` are kept
  as the continuation). A direct hand-off from the releasing row is not enough (Astra's example:
  request capacity 3, B holds 2, C reserves 1, A waits on `:shared`; B's release must reach A), so
  grants are the timer/grant service's: a release that lowers committed marks the service, which
  visits blocked principal heads in calendar order and, for each head whose acquisition now fits,
  acquires on its behalf, dequeues it and makes it runnable in one transition (no barging). A zero
  request limit is refused by name, never parked. Cancellation unlinks a parked waiter before its links
  or row are reused, and settles a granted reservation exactly once. This needs S5.

Ledger operations used by arms have defcosts beside their core wrappers. Booking operations declare no
D0 effect (they attribute a resource the admission already acquired); the request operations (4/n)
declare `(:acquire (:principal-reservation))` / `(:release (:principal-reservation))`. fn2-conn gains
no field (22 of 24 stay used).

### 13.5 Keystones

| statement | status | over | teeth |
|---|---|---|---|
| `fn2-account-acquire-protected`: from a ledger with committed ≤ capacity, `acquire(q, d, a)` with `hold_q + a ≤ reserve_q` and `≤ limit_q` is `:ok`, whatever every other row holds | **proved** (2/n) | the ledger stobj | the unit exhausts shared capacity first, then acquires positive amounts within a reserve (slot 1 and the system row) |
| `fn2-account-{acquire,release,attribute}-charges`, `fn2-account-charge-monotone`: holding operations leave every charge unchanged; a charge only adds | **proved** (2/n) | the ledger stobj | the unit's disconnect and attribution keep the 100 charged octets on slot 0 |
| `fn2-account-ops-conserve`: acquire, release, charge, acquire2, release2 and attribute preserve `fn2-accounts-conservedp` | owed (2/n): the sum over the dimension-major array under one update | the ledger stobj | positive: 600 pseudo-random operations of every kind, conserved after each; negative: committed off by one, a holding over its limit |
| `fn2-account-ledger-matches` (`fn2/books/owed-conn.lisp`, over `fn2-conn-wire-run`, the T1 view): after any client octets in any chunks on up to C connections, the anonymous row is conserved, holds exactly the connections greeted and not closed, and is charged exactly the octets the adapter delivered by Receive results and took by Send results. With S1 it gains listener-owned admission bookings, with 4/n each request token by its holding phase | owed (3/n) | the served core at its adapter boundary | `tests/conn-unit.lisp`: three mixed clients and eight random pairs in varied chunkings (positive, nonzero charges); a view off by one in holding, received or sent, or unconserved (negative). ACCOUNT checks the same over the simulator's runs |
| the weighted starvation bound | A's `fn2-sched-starvation`, its hypothesis `fn2-sched-calendar-validp` generalised to the weighted calendar (otherwise weighted cases are vacuous); still a visit bound, not request completion (4/n) | sched | A's teeth |

### 13.6 The seam request to A (sched.lisp, machines-a*.lisp, executor.lisp are A's; sent through main)

- **S1, booking at Accept.** Profile key `:listener-principals` (one slot per listener, default 0)
  sets each listener row's `principal-slot` at init. `fn2-listener-accept` acquires `:connection-row 1`
  on that slot through `fn2-account-book` (D's core wrapper, `(mv code fn2-core)`) with the credit;
  refused, the listener parks on the admission FIFO as for a missing credit. The admission copies
  `principal-slot` and `account-ref` into the row (`fn2-conn`'s `:admission` gains `:copy
  (principal-slot account-ref)`), and a refused admission or failed Accept calls `fn2-account-unbook`.
- **S2, run charges.** In `fn2-exec-principal`, after `fn2-machine-run`: `(fn2-account-charge-run
  principal bytes steps fn2-core)` (D's wrapper: `:run-bytes`, `:run-steps`, a stop on u60 overflow);
  in `fn2-exec-service`, the same on the system row.
- **S3, weights.** `fn2-sched-init` takes a weight list; a slot of weight `w` appears `w` times per
  round, groups of 16 principal entries keep the four service entries between them, `L = Σw +
  4·ceil(Σw/16)` at most 4,096; with every weight 1 the calendar is today's, entry for entry;
  `fn2-sched-calendar-validp` and the starvation hypotheses follow the weighted geometry.
- **S4, re-attribution.** `(fn2-sched-reattribute machine to fn2-sched) → (mv code fn2-sched)`: a
  queued machine is unlinked from its FIFO and appended to `to`'s tail; its `principal` column is set.
- **S5, ledger grants.** `fn2-machine-grant-ready-p` and `fn2-machine-grant-one` gain a fourth source
  after admission: `(fn2-account-grant-ready-p fn2-core)` and `(fn2-account-grant-one fn2-core) → (mv
  id fn2-core)` (D's: one blocked principal head whose reservation now fits, acquired, dequeued, its
  wait reason cleared). The grant is persisted work, drained by the service class, never the
  observation path's single wake id (Astra: a release in a send-failure handler would overwrite it).

### 13.7 ACCOUNT (`fn2/sim/check-account.lisp`) and scenario 11

ACCOUNT reads none of the ledger's code. Its inputs are the simulator's own records per connection
(octets delivered by Receive completions, octets reported by Send completions, its greeting or 400,
when it closed), WIRE's parse of each client's replies, and the ledger rows read through their column
readers at every boundary the scenario stops at (after admission, after each delivery, after drain),
not only at quiescence. It checks: (1) per principal, `:rx-octets` equals the octets delivered to its
connections and `:tx-octets` the octets reported sent; `:requests` equals the rendered replies, which
the simulator records independently of what reached the client (a reply lost on a failed Send was
still rendered); (2) the `:connection-row` holding equals the principal's booked connections, counted
from the simulator's records (greeted and not yet reclaimed, draining included); (3) per dimension,
`Σ max(hold, reserve) ≤ N` and `hold ≤ limit`; (4) a connection of a principal below its reserve is
never refused the 400 by the ledger; (5) after every connection has closed and drained, every holding
is 0 and every charge equals (1)'s totals. Mutation controls: a reading with a charge dropped, a drain
that also clears charges, a refusal of a protected principal; each must be caught.

Scenario 11's half that 3/n can run: anonymous clients beyond slot 0's connection limit get the 400
and close while every greeted one is served; a principal with a connection reserve (attributed by the
test fixture standing for E2) keeps it while the anonymous flood holds the shared remainder. WIRE and
ACCOUNT over every client. The request-wait half and FAIR join with 4/n.
### 13.8 D7 4/n, statement first (2026-10-31): the request bundle and the ledger's grants

**What stands.** A's seam is on dev whole:
- S1: the listener books `:connection-row` at Accept issue (`fn2-account-book` in the listener's
  arm), and the admission copies `principal-slot account-ref`.
- S2: `fn2-exec-charge-run` charges `:run-steps`/`:run-bytes` per principal run.
- S3: the weighted calendar in sched.lisp.
- S4: `fn2-sched-reattribute`.
- S5: the grant service's ledger source, `fn2-account-grant-ready-p` / `-grant-one`. Its bodies are
  `nil` / `(mv *fn2-none* fn2-core)` in accounts-core.lisp: "no row parks on a principal's request
  FIFO before 4/n".

The grant service now has six sources: operation credit, pool, admission, ledger, sealable and
batchable. What 4/n adds is D's own, in two commits:
- **4/n-a, the ledger's request operations and the grant pair's bodies.** These are core operations,
  so they land now, under the machine-form ruling.
- **4/n-b, the connection's request bundle.** These are arms, so they land at fn2-conn's port, in
  the new form (d-continuation.md P.1). The changed arms are written below in the form's syntax.

**The ledger's request operations** (accounts.lisp over the stobj, accounts-core.lisp the core
wrappers, each with a defcost). The FIFO links are the parked rows' directory links (`ready-prev
ready-next`, P1). The FIFO's ends are the ledger row's `wait-head wait-tail`.

| operation | answers | effect |
|---|---|---|
| `fn2-account-request (p id)` | `:ok` | acquired: `hold(p, :principal-reservation) + 1`, committed per 13.2 |
| | `:queued` | p's FIFO is non-empty: nothing acquired (no barging, even when it would fit) |
| | `:limit` / `:shared` | does not fit: nothing acquired |
| | `:refused` | p's request limit is 0: refused by name, never parked |
| | `:bounds` `:state` | an invariant failure; the caller stops |
| `fn2-account-request-park (p id)` | `:ok` `:bounds` | ID joins p's FIFO tail with wait reason `:principal-reservation`, in the transition that was refused (the park step of F4) |
| `fn2-account-request-release (p)` | `:ok` `:underflow` | the hold leaves; when committed or p's hold dropped, the ledger's grant source becomes ready (persisted, never a wake id) |
| `fn2-account-request-cancel (p id)` | `:ok` `:absent` | ID unlinked before its links or row are reused (the timer's deadline, 5/n); nothing acquired or released |

**The grant pair.** It visits the principals in calendar order from a grant cursor (`grant-at`, a
field of the ledger's configuration row) for a head whose acquisition now fits.
- `fn2-account-grant-ready-p` holds when some principal p has a non-empty FIFO whose head's
  acquisition would answer `:ok` with the FIFO ignored.
- `fn2-account-grant-one`, for the first such p from the cursor:
  - acquires on the head's behalf;
  - dequeues it and clears its wait reason;
  - moves the cursor past p;
  - returns the head's id.
- It does all of that in one transition, as 13.4's Astra example needs. The example has request
  capacity 3, where B holds 2, C reserves 1, and A waits on `:shared`. B's release reaches A through
  the source, not through B.

**As built (4/n-a).**
- **accounts.lisp.** `fn2-account-request` (`:ok :queued :limit :shared :refused :bounds`), with
  `fn2-account-request-no-barging` **proved**. `fn2-account-fits` (and `fn2-account-fits-acquire`,
  proved), `fn2-account-grant-scan` / `-grant-next`, and the cursor column `grant-at`, read and
  written on the system row.
- **accounts-core.lisp.** `fn2-account-request-core`, `-request-release` and `fn2-account-core-ends`
  / `-set-ends` / `-grant-next` / `-grant` / `-headed-fits` in `fn2-account-events`. Then
  `fn2-account-request-events` (materialized in assembly-access after the machine access events)
  holds `fn2-account-request-park`, and the source `fn2-account-grant-ready` /
  `fn2-account-grant-take`.
  - The source is attached by `defattach` to the constrained pair `fn2-account-grant-ready-p` /
    `-grant-one`, which A's machines-a-access.lisp now declares like the sealable and batchable
    sources. That is a foundation edit to A's book: the stubs moved out of D's events.
  - `fn2-account-grant-take-live` is **proved**, so the liveness constraint holds by construction: a
    grant whose FIFO and ledger disagree stops the core (`:machine-write`) and still answers its head.
- **Teeth.** `tests/request-unit.lisp`, in the owed export, covers:
  - Astra's example, scaled to capacity 8;
  - the bounded wait: id 7 on slot 2 is granted within the 4 rows, and a cursor that restarts at 0
    serves slot 0 four times and never reaches it;
  - settled once, with a re-park as the negative;
  - `:refused` for a request limit of 0.
- `fn2-account-request-cancel` comes with 5/n, its only caller.
- `grant-ready-exact` is definitional (`fn2-account-grant-ready` is "the scan finds a fitting head"),
  so it is not a separate row.
- **E's dimensions** (e-surface.md §11): `:durable-octets`, a new D0 kind at rank 7 (the kinds after
  it renumbered 8..24, so every wait-reason code above `:principal-reservation` moves by one),
  `:wait-row` and `:subscription-edge`, the last bounded by the profile key `:esub` (default 4,096).
  Each is a holding dimension of the ledger. A missing profile key takes the dimension's `:default`.

**Keystones** (owed, `fn2/books/owed-accounts.lisp`; teeth in `fn2/tests/request-unit.lisp`, over a
served core with no machine run):

| statement | teeth |
|---|---|
| `fn2-account-grant-live`: `(fn2-account-grant-ready-p c)` implies the id `fn2-account-grant-one` returns is not `*fn2-none*`. This is the shape the sealable and batchable sources already export to A's service | positive: Astra's example. Negative: a ready-p that answers t on an empty FIFO |
| `fn2-account-grant-exact`: the granted id was the head of some principal p's FIFO. The ledger after the grant equals `acquire(p, :principal-reservation, 1)` with that head dequeued and its wait reason none. No other row, hold or charge changes | positive: two principals queued, each granted its head. Negative: a grant that skips a head, and a grant that acquires twice |
| `fn2-account-grant-ready-exact`: `ready-p` holds exactly when some p has a non-empty FIFO whose head fits | positive: a FIFO that fits and one that does not. Negative: ready-p true for a head over its limit |
| `fn2-account-request-no-barging`: while p's FIFO is non-empty, `fn2-account-request p id'` answers `:queued` for every other id' | negative: a request that acquires past a queued head |
| `fn2-account-request-bounded-wait` (the liveness statement). Take any state in which p's head h fits, and every later step is a grant, a release, or a request that answers `:queued`/`:limit`/`:shared`/`:refused`, so nothing else acquires. Then h is granted within P calls of `fn2-account-grant-one`, P the number of principals, because the cursor passes each principal at most once before reaching p. With A's weighted starvation bound (the grant service is visited within L calendar entries), a fitting head is granted within P·L entries. This is a bound on visits, not on request completion, as 13.5 says of the starvation bound | positive: P principals with full FIFOs, every head granted within P grants. Negative: a cursor that restarts at slot 0 starves slot P-1, and the bound must fail |
| `fn2-account-request-once`: each parked request is settled once, granted (`hold + 1`) or cancelled (unlinked, hold unchanged), never both and never twice | negative: a cancel after a grant that releases, and a second grant of one id |
| `fn2-account-ledger-matches` (13.5) gains the request dimension: `hold(p, :principal-reservation)` equals the number of p's connections in a request-holding phase, `:command` while `reserved = 1`, `:article-input`, `:reply` or `:query` | as 13.5's, with a conn granted while parked |

**4/n-b, the connection's request bundle** (written for fn2-conn's port). It uses D0's
`(:connection :request)` bundle, held from the framed line to the reply's last octet.
- **Fields and phase.** The connection gains the field `reserved (:enum fn2-conn-reserved (:none
  :waiting :held))` and the phase `:control-reply`.
  - `:control-reply` holds `:connection-row :rx-range :tx-range`, with no `:principal-reservation`.
    It is 13.4's choice for the greeting and the capacity 400.
  - It shares `:reply`'s send sub-arm. Only `:reply`'s end releases the reservation.
- **Acquiring at a framed line.** The frame sub-arm's `:line` branch acquires before it answers:
  ```lisp
  (:if (equal row-reserved *fn2-conn-reserved-held*)
       ((:goto answer))                ; a grant acquired it while this row was parked
       ((:do (rcode) (fn2-account-request row-principal-slot id)
         :accept ()
         :case (((:ok) (:set (reserved *fn2-conn-reserved-held*)) (:goto answer))
                ((:queued :limit :shared)
                 (:set (reserved *fn2-conn-reserved-waiting*))
                 (:park :principal-reservation row-principal-slot :steps *fn2-work-transition*))
                ((:refused) (:goto refuse-request))))))
  ```
  The line's `start pos` are kept, so the woken row re-frames the same line. A row parked on
  `:principal-reservation` is woken only by its grant: it has nothing pending, and the grant source
  is the only waker of that reason. So `reserved = :waiting` in a running row means the grant
  acquired for it. The frame's first step turns `:waiting` into `:held` without a second acquire:
  that is the "settled exactly once".
- **`:refuse-request`.** Renders `400 request limit` (a new `fn2-answer-request-refused`), with
  `after :closing`, `:next :control-reply`.
- **Releasing.** The end of `:reply`, where TX is reset and the row moves to `after`, gains
  `(:do (qcode) (fn2-account-request-release row-principal-slot) :case ((:otherwise (:stop
  :account))))` and `(:set (reserved *fn2-conn-reserved-none*))`, on the paths that do not return to
  `:article-input` or `:query`. A block or a query keeps its request until its own last reply.
- **Draining.** `:draining` releases a held reservation (a failed Send left it) before the booking.
  A `:waiting` row cannot drain, because it is parked. Its cancellation is 5/n's deadline, through
  `fn2-account-request-cancel`.
- **Holds** (D0's bundle per phase):
  - `:command` holds the reservation only while `reserved = :held`;
  - `:reply`, `:article-input` and `:query` hold it;
  - `:greeting`, `:control-reply`, `:closing` and `:draining` do not, after the release.
  `:command`'s split hold is per path, not per phase. That needs the form's per-path holds, which
  D0 checks per arm today (a-to-d-arm-contracts.md:107): D asks the form seat (F14, through main)
  for path postures. The fallback is a second phase `:requesting` for the parked line, which is
  exact under per-phase holds and costs one phase.

**ACCOUNT and FAIR.**
- ACCOUNT's check (2) gains the request dimension, from the simulator's own record of which
  connections have a line framed and its reply not yet fully sent.
- FAIR, scenario 11's request half: one principal floods requests past its limit while another
  holds a request reserve. The reserved principal's requests are never refused `:shared`, and every
  parked request of the flooder is granted within the bound above.

## 14. D4 + D5: article input, the upload machine, the transaction machine *(design; the D4/D5 commits rewrite it as built)*

The contract is brief items 4 and 5, ROUND2 §B.2 rows 3-4, §B.3, §E.1-E.2 and scenarios 4, 5 and 13,
D0's bundles `:upload :admit`, `:transaction :admit`, `:transaction :batch` and `:storage-job
:write`, C's identity decision (`fn2/docs/c-ordered-runs.md` §4-5, `fn2/books/identity.lisp`), B's
commit batch (`fn2/docs/b-durability.md` §10) and fn1's POST contract (`specs/nntp.md:681-1044`, the
oracle being H's model `fn2/tests/model/nntp_model.py` `_article_block`). D4 and D5 are designed
together because a POST needs the input path before a transaction exists: the reply to POST's body
is the transaction's outcome, and the transaction's identity key is the upload's digest.

### 14.1 The path, as one picture

```
POST line ─► fn2-conn :command ── take an upload row and its window (bundle :upload :admit) ──► 340
                │ refused (no row / no window): park on the upload FIFO, the line kept unconsumed
                ▼
fn2-conn :article-input ── frame block lines from RX, unstuff, append to the window ──► upload wakes
                │ :terminator                                     │ (hash + header scan, 4 KiB/run)
                ▼                                                 ▼
fn2-conn :article-input (waiting, no work)              fn2-upload :validating ── a definite refusal
                ▲                                                 │            posts its word to the
                │                                                 │            connection, drains
                │   outcome word posted to the row, conn wakes    ▼
                └──────────────────────────────  fn2-txn admit ► reserve ► lookup ► prepare ► ready
                                                                   │ batched ► accepted | refused | uncertain
                                                                   ▼
fn2-conn :article-input renders 240 / 441 WORD (POST), 235 / 437 / 436 (IHAVE), 239 / 439 / 436
(TAKETHIS) into TX ─► :reply ─► :command
```

IHAVE is the same path after `335` (its Message-ID is the command's argument, checked equal to the
article's: a mismatch is a definite refusal). TAKETHIS has no reply before its block (RFC 4644 §2.5):
its block is framed at once (`:immediate`), and an upload that cannot be taken discards the block to
its terminator and answers `439` (the model's pattern admits it; the window credit is the peer
window's, E4). CHECK answers from the identity reservation table and C's decision without a block
(D5 2/n). On a reader connection IHAVE, CHECK and TAKETHIS stay the grammar's 502 (§4.3) until E4
admits peers; D's tests drive the peer path by setting the peer bit at the adapter boundary, as the
ACCOUNT test fixture stands for E2.

Three machines, one per resource lifetime: the connection holds the wire for its lifetime, the upload
holds a window while octets arrive, the transaction holds the identity claim until its outcome is
known. They meet only through declared operations on each other's rows (a `:target` move, or a
contracted cross-row write listed in `:tables`), never through shared fields.

### 14.2 The connection's article input (`fn2-conn`, D4)

New fields (fn2-conn has 22 declared; the read-set snapshot of 6b2f6ef5b removed the 32-value cap on a
row, so this adds what the path needs): `upload :link` and `upload-gen :u60` (the upload row this
connection feeds, `*fn2-none*` otherwise), `rule (:enum fn2-conn-rule (:none :post :ihave :takethis))`,
`word :u8` (the outcome word the transaction or the upload posts, `0` while none is due; the words are
the enum of 14.5), `outcome-ready :bool`, `request :u32` (the ordinal of the request awaiting its
outcome: a word is accepted only with the matching connection generation **and** request ordinal, so a
late or recovered outcome never answers a later request on the same row; Astra), `token-off token-len
:u32` (IHAVE/TAKETHIS: the command's Message-ID, see below).

**Opening the block.** `fn2-answer` gains one answer code, `:block` (no reply rendered): POST (in a
posting-served state), IHAVE (peer, 335 due) and TAKETHIS (peer). `fn2-conn-frame-run` on `:block`
calls `fn2-upload-take` (the generated taken-kind operation of seam A-S7, 14.7): `:ok` gives the row;
the arm renders the opening reply (`340`, `335`; nothing for TAKETHIS) through
`fn2-conn-run-block-open`, consumes the line, sets `upload upload-gen rule`, `after = :article-input`
and moves to `:reply` (TAKETHIS straight to `:article-input`). `:no-row` or `:pool`: the generated
take has appended the connection to the upload kind's FIFO (`wait-reason :upload-row`), and the line
stays unconsumed (`start pos` unchanged), so the grant re-runs `:command` and re-frames the same line
(at most 512 octets re-read: the continuation is the row). A TAKETHIS whose take is refused does not
park (its block follows on the wire whatever we do): the row moves to `:article-input` with `upload =
*fn2-none*`, which is discard-to-terminator, and answers `439 <message-id>` after the terminator.
Every TAKETHIS reply carries its offered Message-ID (RFC 4644 §2.5; the oracle's pattern), so the
token is copied out of RX at the command (to a connection-owned range: `token-off token-len` in a
reserved 256-octet tail of TX, which the reply renderer reads first and which no compaction moves)
and survives RX reuse and an upload that never existed (Astra).

**The block arm.** `:article-input fn2-conn-block` (replacing `fn2-conn-unreached`), at most 4,096
octets per run:

| condition | the run |
|---|---|
| `outcome-ready` | render the reply for `(rule, word)` into TX (14.5), clear `upload rule word outcome-ready`, `after = :command` (or `:closing` for a transit body over its bound, H's `close_after_reply`), move to `:reply` |
| the upload is terminated and no outcome yet | nothing: the row is parked on its upload (`wait-reason :completion`); the outcome wakes it |
| otherwise | `fn2-upload-feed` (below) over `[start, fill)` of RX; at `:need-more` compact or Receive exactly as `:command` does (`fn2-conn-input` is shared); at `:terminator` wake the upload and park |

`fn2-upload-feed (left i mode discard rslot rgen rk rs rg dslot dgen dk ds dg fn2-pool) → (mv status
i mode discard copied fn2-pool)` (`fn2/books/upload-feed.lisp`, landed with D4's input library) is a
**streaming octet machine, not a line framer** (a change from the first draft and from
`fn2-gram-block-step`): a body line may be longer than the connection's 1 KiB RX slot, since H's model
sets no body-line bound, so nothing is retained between octets but a five-valued `mode` (line start,
inside a line, after CR, after a leading dot, after ".CR"). Each RX octet is read once under the
connection's owner and each released octet written once under the upload's (`fn2-gram-read`,
`fn2-gram-put`), so the declared cost is `:bytes 2 × left` with `left` ≤ 2,048, and there is no rescan
(Astra's accounting point disappears with the line framer). Statuses: `:terminator` (the octet after
its LF), `:need-more`, `:budget`, `:full` (the next octet releases more than the chunk holds: switch to
the other chunk and resume, nothing consumed), `:fault`. The framing is H's `framing.py`
`decode_block`: a bare CR, a bare LF, a NUL or an unescaped leading dot sets `discard`, after which the
block is drained to its terminator and nothing more is written. The upload keeps a producer offset
(`filled`, written only by the feed) and consumer offsets (`hashed`, `scan-off`, written only by the
upload), so neither machine reads a half-written line. The arm records why: a framing `discard` becomes the upload's
reason `:framing` (14.5); a `:full` with both chunks full, or a source past the article bound, makes
the arm pass `discard` t from then on with reason `:too-large` (RFC 3977 §3.1.1, scenario 4: "bounded discard", never buffered). A
block over the bound keeps the connection open for POST (the model drains it) and closes it after the
reply for IHAVE/TAKETHIS (`specs/nntp.md:530-534`). EOF or a failed Receive in `:article-input` moves
the connection to `:closing`; the upload sees its connection gone (14.3 `:aborting`) and the
transaction, if any, completes or stays uncertain on its own (a disconnect undoes nothing, ROUND2
§E.2 `durable`).

`:holds` of `:article-input` is unchanged (`:connection-row :rx-range :tx-range`): the upload's row
and window are the upload's holdings, not the connection's (D0 row `:upload :admit`: the connection
holds its own kinds while the upload is acquired on its behalf, `(:acquire (:upload-row :chunk-window)
:for fn2-upload)`).

### 14.3 The upload machine `fn2-upload` (`fn2/books/upload.lisp`, D4)

ROUND2 §B.2 row 3. Capacity `:u`. Phases (the brief's, each with a reason to exist):

| phase | holds | arm | does |
|---|---|---|---|
| `:free` | none | `fn2-upload-idle` | on the kind's free chain (A-S7) |
| `:head` | `:upload-row :chunk-window` | `fn2-upload-scan` | octets arrive from the connection; each run hashes `[hashed, fill)` of the current chunk (≤ 4,096) and advances the header scan (14.3.2) until the blank line |
| `:identity` | same | `fn2-upload-claim` | the header is complete: the Message-ID range is known exactly (for a transit offer compared with the command's). The upload takes its transaction row here (`fn2-txn-take`, bundle `:transaction :admit`), and the transaction claims the Message-ID (14.4.2) before the body is stored, so a same-Message-ID offer serializes early. A POST without a Message-ID claims after the transaction generates one (14.4.1), which needs no body |
| `:receiving` | same | `fn2-upload-scan` | body octets: hashing only, 4,096 per run |
| `:validating` | same | `fn2-upload-validate` | the terminator was framed and every octet is hashed: finalize the digest, apply the definite refusals (14.5) in the model's order, then wake its transaction with the digest |
| `:discard` | same | `fn2-upload-discard` | a refused or oversized block: nothing is copied; at the terminator post the refusal word to the connection and move to `:draining` |
| `:sealed` | same | `fn2-upload-idle` | complete, hashed and owned by a transaction; the window holds the article octets the batch packs (until D4 3/n) or the extents hold them (D4 3/n) |
| `:aborting` | same | `fn2-upload-abort` | the connection left before the terminator: release the reservation if held, post nothing, move to `:draining` |
| `:draining` | same | `fn2-upload-drain` | release the window (both chunk slots, then the hasher row) and the row (`fn2-machine-reclaim-fn2-upload`) |

Fields: `conn :link conn-gen :u60` (the connection fed by and replying for this upload),
`c0-slot :link c0-gen :u60 c1-slot :link c1-gen :u60` (the two chunks), `cur :bool` (the chunk being
filled), `window :u8` (the window index: it names the hasher row, 14.3.1), `source-len :u60`,
`hashed :u60`, `head-state` and the header-scan continuation (14.3.2: `scan-off :u32 line-start :u32
fields :u16 lines :u16 seen :u16` and the ranges `mid-off mid-len ng-off ng-len path-off path-len`,
`:u32` each), `discard (:enum fn2-upload-why (:none :malformed :too-large :missing :duplicate-field
:path :message-id :mismatch :injected))`, `terminated :bool`, `bound :u60` (the article bound, from
the profile and, for transit, the peer record's `inbound-max-octets`, E4), `rule`, `ordinal :u32`
(TAKETHIS), `txn :link txn-gen :u60`. Budget `(:bytes 4096 :steps 32 :descriptors 4)` (ROUND2 §B.3:
4 KiB scanned/hashed/copied, 32 manifest entries).

**14.3.1 Windows.** A window is two chunk slots of the profile's chunk class and one hasher row. The
chunk class is profile key `:upload-chunk-bytes` (the smallest pool class at least that size; 65,536
in the concrete profile, whose largest class is 64 KiB today; ROUND2's 256 KiB is a profile change
with its T10 row), and `:large-upload-windows` (16) windows exist. The hasher row of window `w` is
row `3 + w` of B's `fn2-b3` table and its digest stripe (B's `fn2-b3` rows are sized by
`:format-slots`; the served profile sets it to `3 + windows`, rows 0-1 staying the commit kind's and row 2
recovery's checker (`*fn2-rec-checker-row*`, B5-3);
seam B-S1 is this convention plus a profile check, no code). The upload kind's partition (A-S7)
grants a row and a window whole or not at all, so `U` rows serve at most 16 concurrent inputs
until D4 3/n; rows beyond 16 matter once a sealed upload gives its window back after writing temporary
extents (D4 3/n).

**Article bound.** Until D4 3/n the whole article stays in its window, so the bound is `min(profile
:article-max, 2 × chunk)`; `:article-max` defaults to 32,768 (fn1's source bound,
`specs/article-parser.md`). Above two chunks the article must leave the window as it arrives: D4 3/n
writes each full chunk to a temporary extent through a storage job (`:storage-job :write`, D0) under
B's allocator, records the extent in the manifest cursor, and frees the chunk; the transaction then
references extents, not chunks. Until 3/n an article over the bound is `:too-large` (definite, scenario
4's oversized row), never a false durable refusal.

**14.3.2 The header scan** (`fn2/books/upload-scan.lisp`, a pool-level library like conn-answer.lisp,
D4 1/n). A bounded continuation over chunk 0 (the header section must lie in chunk 0: `:upload-chunk-
bytes` ≥ `max-header-octets` + 2 is a profile check, so a header longer than the cap is refused by its
limit before chunk 0 fills). Per physical line it checks fn1's header syntax
(`specs/article-parser.md` "Header syntax": `field-name ":" (WSP body / "")`, continuations start with
WSP, US-ASCII SP/HTAB/VCHAR only, ≤ 998 octets per line, the field/line/octet limits), counts fields,
and records for the fields the decision needs the exact value range of their first occurrence and the
occurrence count: `message-id` (one physical line, value trimmed of WSP: a folded Message-ID is
`:message-id`), `newsgroups` (whole folded value), `path`, and presence bits for `from subject date
xref injection-date injection-info approved control`. Its state is scalars only (the row's fields),
and each call examines at most the run's remaining budget. Outcomes: `:more`, `:header-done` (offset
of the body), or a refusal word. Message-ID syntax is the grammar's `fn2-gram-arg-msgid` over the
recorded range (one definition of a Message-ID for the command line and the header).

**The identity, exactly.** The Message-ID is the octets of that range in chunk 0 under the upload's
owner: no copy, no list. The content identity is BLAKE3 of the **source** (the unstuffed octets the
poster sent, without the terminator): D25 compares sources (`specs/nntp.md:952-1040`), and for
transit the received octets are the source. B's `fn2-b3-init`/`fn2-b3-update`/`fn2-b3-finalize` over
the chunks in order; the digest lands in the hasher row's result slot and is stored into the window's
digest field with B's `fn2-digest-store` (C's seam 1, landed 810a4c376). Injection (RFC 5537 §3.5:
Path, Injection-Info, generated Message-ID/Date/Injection-Date) changes the **stored** octets, not the
source; it is the transaction's `prepare` (14.4) and the stored length is its field.

### 14.4 The transaction machine `fn2-txn` (`fn2/books/txn.lisp`, D5)

ROUND2 §B.2 row 4. Capacity `:t`. Phases:

| phase | holds | arm | does |
|---|---|---|---|
| `:free` | none | idle | free chain (A-S7) |
| `:admit` | `:transaction-row` | `fn2-txn-admit` | bind the operation identity (14.4.1) and the authority/configuration version pinned on the connection (W01: the connection's `access-ref`, never a live rule); move to `:lookup` |
| `:reserve` | `:transaction-row` | `fn2-txn-reserve` | claim the Message-ID, or wait on the holder's FIFO holding no claim (14.4.2); a same-Message-ID waiter holds no claim and no membership, so the wait is upward in D0's order |
| `:lookup` | `:transaction-row :identity-reservation` | `fn2-txn-lookup` | C's identity decision under the stale rule (14.4.3), at most 32 entries and 4,096 compared octets per run |
| `:prepare` | same | `fn2-txn-slots` | injection for POST (stored octets, stored length), membership assignment `(group-id, group-number)` (C3), the records the batch packs, the dependency manifest root (D4 3/n's extents) |
| `:ready` | same | `fn2-txn-ready` | `fn2-identity-stage` (C-S2; `:full` and batch capacity are backpressure: stay `:ready`), then `fn2-commit-admit-txn` (B-S2), then on `:ok` `fn2-identity-bind` in the same transition |
| `:batched` | `+ :batch-membership` | `fn2-txn-batched` | no work: waits for the batch's member outcome (an observation from the commit kind) |
| `:accepted` | `:transaction-row :identity-reservation` | `fn2-txn-reply` | post the success word to the connection; release the reservation (waking its FIFO), the upload (→ `:draining`) and the row |
| `:refused` | same | `fn2-txn-reply` | post the refusal word; release as `:accepted` does |
| `:uncertain` | same, persistent | `fn2-txn-uncertain` | post the uncertain word once; the row, its reservation and its records stay until recovery resolves the batch (ROUND2 §E.2): the Message-ID stays reserved, so a resend waits rather than racing an unresolved write |
| `:releasing` | same | `fn2-txn-unclaim` | release the claim (its FIFO's head takes it and is woken) |
| `:draining` | none after release | `fn2-txn-drain` | wake the upload, reclaim |

The outcome is exactly one of accepted, refused, uncertain, decided by the batch, never by the
transaction alone: `uncertain` is entered as soon as a recoverable committing record may exist (the
batch reached `log-write`, ROUND2 §E.2) and its write's fate is not known; `accepted` only on the
batch's durability evidence (B's `durable`, then install and publish: the reply follows publication,
so a 240's poster reads its own article); `refused` only while no record of it can exist (before the
batch's `log-write`, or a definite refusal before `ready`). Known-durable but unpublished work is an
obligation, never a refusal; the batch hands each member its outcome with the evidence it rests on
(B-S2), so the transaction never infers it from the batch's current phase. A disconnected connection
changes none of this: `fn2-conn-post-word` checks the connection's generation and request ordinal and
drops the word for a row that has moved on (the one place a word is legitimately not delivered; it is
counted).

**14.4.1 Operation identity.** `(principal-id, operation-id)` beside the Message-ID (STORAGE §4
decision 1). On NNTP the retry identity is the Message-ID (NNT-005: a supplied Message-ID is the
retry identity; a generated one is a new article), so the operation id is fresh per attempt: the
node's operation counter (u60, persisted with the batch; exhaustion refused by name, never wrapped),
and the principal is the connection's `principal-slot` (attribution, D7). The outcome of
`(principal, operation)` is a record of the batch (C4's operation-outcome schema): an API caller (E)
that retries with the same operation id gets the original outcome without re-execution, and a
contradictory reuse (same id, different request digest) is refused `:operation-reused`; the NNTP
path never retries by operation id, so D5 builds the record and E's API is its first reader.

**14.4.2 The identity reservation** (D0 rank 12, `:identity-reservation`). *As built
(`fn2/books/claims.lisp`, `tests/claims-unit.lisp`): the table is its own stobj `fn2-claims` (a D core
child with D5 1/n), one row per transaction slot whose `head`/`stamp` columns are also bucket `r`'s;
`fn2-claim-begin`, `fn2-claim-walk` (budgeted, restarting when its bucket's stamp moved),
`fn2-claim-release` (unlink, then hand the claim to the FIFO head in the same step). Owed with the
machine: a waiter's cancellation (an upload aborting while its transaction waits) unlinks it from its
holder's FIFO.* The design: One claim per transaction
on its Message-ID's exact octets: a D core child `fn2-txn-claims` holding `2^k ≥ 2T` bucket heads;
each transaction row carries `mid-hash :u32` and `claim-next :link`, and the Message-ID range it
claims (the upload's chunk, under the upload's owner). `fn2-txn-claim (t fn2-core) → (mv code holder
fn2-core)` walks the bucket chain comparing hashes and, on a hash match, the octets
(`fn2-core-compare`, two owners): a free Message-ID is claimed (`:ok`); a held one returns its holder
and the transaction parks on the holder's FIFO (`claim-wait-head`), in the same transition (no
lost wakeup: the release that unlinks the holder grants the head). Its declared cost: at most 32
chain steps and one 250-octet comparison per hash match, at most 4,096 compared octets per run; a
longer walk is a continuation (`claim-cursor`). Claims are taken at the upload's `:identity` (14.3)
and released only at the outcome: same-Message-ID offers on one node never race, so C's decision for
a claimed Message-ID can be stale only through **other** Message-IDs sharing its stamp bucket or
through a run installation (14.4.3).

**14.4.3 C's decision, with the stale rule.** `:lookup` stages the offer (Message-ID range and digest,
both under the upload's owner) into the transaction's decision row (decision row = transaction row
index, C-S1) and steps it to an answer: `:stored` (new), `:duplicate` (this content is recorded),
`:conflict` (another content is). The fact is never recorded into a public overlay at lookup (a
refusal or a crash would leave a phantom fact), and not discovered at install either (a durable batch
must never become unpublishable because a record is stale or an arena is full; Astra). The
transaction's `:ready` arm stages the fact for its batch's **private successor overlay** (C-S2, as C
amended it): `fn2-identity-stage` validates the decision against published state (re-deciding on
`:stale`, under the claim) and reserves room, the batch admission follows, and `fn2-identity-bind`
copies the offer's octets into the successor in the same transition, which cannot fail; all before B
seals the batch's records and root. Publication exposes the successor atomically, with no
admission or lookup at install. A private successor is invisible to every decision until
publication (C enforces it: today `fn2-id-decide-step` visits every active and frozen overlay). **Claim stability (keystone
`fn2-txn-claim-stabilizes-decision`, 14.6), as Astra restated it:** for an immutable offer, while its
transaction holds the claim and before the offer's own publication, every validated decision returns
the same answer, provided every identity writer respects claims and every representation change
(seal, merge) preserves facts. Claims do not validate C's traversal (the stamp and version do), and
the retry argument below gives no per-request starvation bound; the retry count is
bounded by the records and installations that touch its bucket while it is in flight (lock-free, not
wait-free: each stale retry means another transaction or installation progressed), which is what C
measured (~45 stale per 30 offers under contention with no claims; the claims remove the same-Message-
ID share of them). D's IDENTITY run (14.8) reports retries per decision.

Answers to replies, under IDENTITY-ACROSS-PEERS rulings 6, 7, 8 and 11 (2026-10-30). This text
replaces the earlier D25 reading, where a POST conflict wrote nothing, a fifth content was refused by
a per-name bound, and transit decided by Message-ID alone.
- **The decision's facts decide the reply** (ruling 8; C §4a). The reply is chosen from the selection
  relation, the evidence status and the coverage, never from a verdict word alone (d-continuation.md
  P.4).
- **POST and IHAVE.**
  - **Selected here.** The name is selected here under this content: POST answers 441 "this article
    is already stored here" and IHAVE answers 437.
  - **A valid competing binding.** This takes ruling 6's evidence-only committed transaction: the
    evidence is framed, charged and committed with no membership and no retention promise, the reply
    waits on that commit, and the article refusal (441 or 437) and the evidence outcome (committed,
    uncertain or refused) are reported separately.
  - **Evidence that is known already** is idempotent: it commits nothing new and is not
    double-charged on replay.
  - **Three evidence classes.** An invalid signature, an out-of-scope object and a valid competing
    binding are distinct, each with its own word.
- **No per-name ceiling** (ruling 7). `:identity-conflict-bound` and its "fifth content" refusal are
  deleted with C's four-per-id constant. Evidence admission is funded instead: charged against the
  offerer and reserved. A refused admission leaves coverage explicitly incomplete, which the typed
  read result reports, and the article's reply is unchanged by it.
- **Transit** (ruling 11).
  - CHECK and IHAVE keep Message-ID-only suppression (435/438) as a declared loss. Per E's §13.2,
    suppression happens only on local acceptance history for the name (accepted, withdrawn or
    reclaimed) or a local not-wanted decision, never on evidence alone.
  - A fully received TAKETHIS that carries a new admissible conflict takes ruling 6's path and
    answers 439 with the conflict word, with its evidence committed. Transit decides after receipt,
    not by Message-ID alone.
- **The refused article contributes no mutation** (T6). The committed evidence is a separate operation
  with its own record and outcome in the same batch, and T6 counts the two apart. A later re-offer of
  evidence-only content never hears "already stored here": `:duplicate` is only for selected content.

**14.4.4 The batch.** `:ready` admits the transaction to B's commit batch (B-S2): one member whose
records are (a) the article record (stored octets by reference: the window today, extents with D4
3/n; the content digest; the source digest; the stored length), (b) the identity fact `(mid, content,
article, binding = batch event, principal)`, (c) the membership rows `(group, number, article)` (C3),
(d) the operation outcome `(principal, operation, request digest, outcome, event)` (C4). Batch
membership is acquired here (`:transaction :batch`, holding everything below rank 18); a full batch is
backpressure (`:ready` stays, a retry, the transaction holds no batch resource). The member outcome
comes back as an observation (`:member-result`) carrying accepted / refused / uncertain by the batch's
own phase at the time it settled, so the transaction never infers its outcome from time or from a
readable byte. Unfinished uploads are excluded from sealing (ROUND2 §E.1): only `:ready` transactions
join, so a stalled uploader holds no batch.

### 14.5 Replies: the typed refusal set

Every word is a value of `fn2-txn-word` (the row's `word` field) and every reply is one row of
`nntp-grammar.lisp`'s catalogue, rendered by the connection; each is a fixture in the units:

| word | POST | IHAVE | TAKETHIS | decided by |
|---|---|---|---|---|
| `:accepted` | 240 | 235 | 239 | batch (durable, published) |
| `:uncertain` | 441 "...the outcome is uncertain; do not repost (uncertain)" | 436 "...outcome uncertain" | 436 `<id>` "...outcome uncertain" | batch (log-write reached, fate unknown); the oracle classifies by the word `uncertain` in the text, never by 436 alone |
| `:duplicate` | 441 "this article is already stored here" | 437 | 439 | C's decision |
| `:conflict` | 441 "a different article with this Message-ID is stored here" | 437 | 439 | C's decision |
| `:too-large` | 441 "...too large (bound)" | 437 + close | 439 + close | upload |
| `:malformed` | 441 "...malformed" (header syntax, missing separator) | 437 | 439 | upload |
| `:framing` | 441 "...malformed block" (a bare CR or LF, a NUL, an unescaped dot: the block is drained to its terminator; H's model closes after it) | 437 + close | 439 + close | conn |
| `:line-length`, `:header-fields`, `:header-lines`, `:header-octets` | 441 "...malformed: a header field line is longer than 998 octets" / "...header limit" | 437 | 439 | upload (fn1's names, specs/article-parser.md) |
| `:missing` | 441 "...missing a required field (From, Subject, Newsgroups)" | 437 | 439 | upload (transit also Message-ID, Date, Path) |
| `:duplicate-field` | 441 "...duplicate field" | 437 | 439 | upload |
| `:path` | 441 "...Path is not a valid path" (POST: POSTED, syntax) | — | — | upload |
| `:message-id` | 441 "...Message-ID is malformed" | 437 | 439 | upload |
| `:mismatch` | — | 437 | 439 | upload (header vs command Message-ID) |
| `:injected` | 441 "...Xref or Injection fields are the server's" | — | — | upload |
| `:no-clock` | 441 "posting failed; this server has no usable clock reading" | — | — | transaction (injection) |
| `:group` | 441 "...no such newsgroup here (group)" | 437 | 439 | transaction (C3 membership) |
| `:identity-conflict-bound` | conflict line | 437 | 439 | C's record; deleted with C §4a (ruling 7: no per-name ceiling), served until then |
| `:unaffordable` | 441 "...unaffordable" | 436 | 436 | a capacity the profile cannot grant (a zero `:t`, an article over the window with no extents) |
| `:control-malformed` | 441 "the Control header field is malformed" | 437 | 439 | transaction (control, RFC 5537) |
| `:refused` | 441 "posting failed; the article was refused" | 437 | 439 | the generic refusal |
| `:not-stored` *(interim, D5 until B-S2)* | 441 "posting failed; the article was refused (storage is not served yet)" | 436 | 436 | a transaction that reached `:ready` before the batch carries articles |

The definite order is the model's (`_article_block`): bound, separator and required fields, duplicate
fields, Path (POST), Message-ID mismatch (transit), Message-ID syntax, clock (POST), identity, group,
read-only/moderation (E2), Xref/Injection (POST). fn1's index-specific words (`:mpx-saturated`,
`:history-exhausted`) are retired by name: fn2 has no keyed Message-ID table that can fail to place an
article (C's runs have no placement failure) and its capacity refusal is `:unaffordable` and
backpressure. `:storage-failed` is not a word: a write that fails before `log-write` is a refusal only
if nothing of it can be recovered, which B's batch decides, so it is `:refused` (before) or
`:uncertain` (after).

Posting is advertised (greeting 200, MODE READER 200, CAPABILITIES `POST`, POST answering 340) by
one predicate, `fn2-answer-posting-p mask`. **Two positions, Astra's taken:** D's draft turned it on
with D4 2/n, so POST's definite refusals would be served while every valid article got the interim
`:not-stored`; Astra would keep the public posting capability off until a POST can succeed, exercising
the interim path only in fixtures (the units and sim-layer-d with a test profile key
`:posting-interim t`). Advertising posting that cannot succeed misleads a client; so the predicate
turns on with D5's first durable POST, and H's 713 POST interims leave then, all at once. E2 adds the
authentication cases.

### 14.6 Keystones (statement first; each a `defthm-owed` in `fn2/books/owed-txn.lisp` with teeth)

The logical view is `fn2-conn-wire-run` (§7) extended with posting clients and an adapter whose
storage completes in a scripted order with scripted faults, so every keystone states a property of
the served core at its adapter boundary, not of a model.

| name | statement | teeth |
|---|---|---|
| T6 `fn2-outcome-safety` (unconditional) | for every request the core ever admitted (POST/IHAVE/TAKETHIS line framed, whether or not it got an upload or a transaction row): at most one outcome word is ever posted for it, correlated by connection generation and request ordinal; the word is accepted only if a batch holding its records reached durable and was published; uncertain only if such a batch reached log-write and did not reach durable; refused otherwise. Disconnects, death cuts and recovery included | positive: transcripts with faults at every batch phase and a disconnect at every point from the line to the outcome; negative: a runner that answers 240 at `log-write`, one that answers refused after `log-write`, one that delivers a recovered outcome into a later request on the same row |
| T6 `fn2-outcome-delivery` (under stated progress) | under a declared bounded-completion environment (the scheduler visits, the device completes, recovery finishes, the transport sends), a request whose connection stays open gets exactly one reply, and requests that never got an upload or a transaction row (a no-row TAKETHIS, a refused take) are among them | positive: the same transcripts with faults stopped; negative: a no-row TAKETHIS that gets no 439 |
| T6 `fn2-refusal-no-committed-mutation` | a refused transaction's operation contributed no article, membership or identity record to any batch that reached log-write; an evidence operation's records are its own (14.4.3) and are counted apart | positive: refusals of every word beside accepted posts and transit conflicts with evidence; negative: a runner that packs a refused member's article record |
| T9 `fn2-exact-identity-served` | over the served core, for eligible offers (otherwise valid, under the bound) and **an accepted witness** (the first offer is accepted, so the statement is not vacuous under an all-refusing node): a later offer with equal Message-ID octets and equal source digest is answered duplicate, an unequal digest conflict, evidence content never duplicate; equality is of exact octets, and the answers are unchanged after the first's window is released | positive: the M3 shapes through POST and TAKETHIS with accepted witnesses; negative: an upload that lower-cases the Message-ID, a digest over the stored rather than the source octets (a resend at another clock then conflicts), an all-refusing node (refused by the witness premise) |
| `fn2-txn-claim-stabilizes-decision` | Astra's statement (14.4.3): for an immutable offer, while it holds its claim and before its own publication, validated decisions agree | positive: decisions re-taken after other Message-IDs publish into the same bucket; negative: claims disabled and two same-Message-ID offers interleaved |
| `fn2-upload-source-exact` | the window holds exactly the dot-unstuffed source of an accepted-for-validation block, for every fragmentation, while the article fits the window | positive: every split point of the block transcripts; negative: a framer that does not unstuff |
| `fn2-upload-discard-bounded` | a block refused **by framing or by the bound** is consumed to its terminator with no octet copied after the refusal and at most the block's length of framing work; a block refused by a header check after octets were copied keeps them only until its upload drains (no claim that no prefix was copied; Astra) | positive: scenario 4's shapes; negative: a feeder that keeps buffering an oversized block |

Owed with the existing identity keystones' D side: C's `fn2-exact-identity` and
`fn2-identity-linearizable` are over C's adapters; `fn2-exact-identity-served` is the same claim over
the served path, and `fn2-identity-linearizable` gains the D-side runs (IDENTITY over sim-layer-d's
traces, 14.8).

### 14.7 Seams (sent through main, exact forms)

- **A-S7, taken kinds** (the admission partition, generalized; D asks rather than build a twin):
  ```lisp
  (defmachine fn2-upload ...
    :taken (:phase :head :rows :upload-row
            :ranges ((:chunk-window :slot c0-slot :gen c0-gen :class 1)
                     (:chunk-window :slot c1-slot :gen c1-gen :class 1))
            :copy (conn conn-gen rule) :clear (...)))
  ;; generated, per taken kind K, beside the admission events, sharing the directory's
  ;; per-ordinal partition arrays (capacity, free head, credits, active count, FIFO):
  ;; (fn2-machine-take-K waiter COPIES... fn2-core) -> (mv code id fn2-core)
  ;;   :ok, or :no-row / :pool with WAITER (a machine id, or *fn2-none*) appended to K's FIFO,
  ;;   wait-reason the row kind; ranges all or none
  ;;   defcost :target (K :free PHASE)
  ;;   :effects ((:acquire (ROWKIND) :for K) (:acquire RANGES :for K))
  ;; (fn2-machine-reclaim-K id retire fn2-core): free chain, then grant the FIFO head (wake it)
  ```
  `fn2-txn` declares `:taken (:phase :admit :rows :transaction-row :copy (upload upload-gen conn
  conn-gen))`. If A prefers, D writes it as a foundation commit in a worktree with the whole-tree gate.
- **A-S8, the cross-owner copy** (a performance item, not a correctness one, since the feed reads and
  writes octet by octet under each owner through checked exports; pool-ranges.lisp, the sibling of
  `fn2-pool-compare`):
  `(fn2-pool-copy-across src sgen soff sk ss sg dst dgen doff dk ds dg len fn2-pool) -> (mv code
  fn2-pool)`: `[soff, soff+len)` readable under `(sk ss sg)` copied to `doff` of a workspace of `(dk ds
  dg)`, `doff ≤ fill`, with `fn2-core-copy-across` and a defcost; the feed would then copy the runs
  between line boundaries in one call.
- **B-S1, hasher rows** (no code): the served profile sets `:format-slots` to `3 + :large-upload-
  windows`; rows 0-1 are the commit kind's, row 2 recovery's checker, row `3 + w` window `w`'s
  (B's ruling, 2026-10-30; C1c's sealer claims a checker row of its own after the windows). B confirms nothing else indexes
  `fn2-b3` rows by count.
- **B-S2, the transaction member** (with GC2 inside B5, the same admission shape):
  `(fn2-commit-admit-txn member-slot member-gen bytes okind oslot ogen fn2-core) -> (mv code batch
  fn2-core)`: a D-prepared workspace holding the member's records (14.4.4) in B's record encodings;
  `:ok` (handed to the commit kind; the batch notifies the member row with `:member-result` carrying
  the outcome **and its evidence**: accepted with the durable and published batch, uncertain with the
  log-write reached, refused before it; known-durable-unpublished is never refused), `:exhausted`
  (backpressure), `:admission`. An unresolved batch fences its storage scope, not only its
  Message-IDs; recovery resolves retained claims with protected resources, never waiting for them. Records over the batch's packing room go as payload blocks referenced
  from the record (D4 3/n).
- **C-S1, identity in the served assembly** (agreed by C, 2026-10-30; lands with C's move onto the
  production assembly, `books/machines-c.lisp`, section `assembly-callbacks-c` between `-a` and `-d`):
  `(fn2-identity-offer d mslot mgen moff mlen dslot dgen doff okind oslot ogen fn2-core)`,
  `(fn2-identity-step d budget fn2-core)` → `:more | :stored | :duplicate` (accepted content) `|
  :evidence` (content recorded only as evidence) `| :conflict`, `(fn2-identity-release d fn2-core)`;
  one decision row per `:t`, each with a 128-row field stripe (B's `fn2-fields` default grows to 128 ×
  (format-slots + t), the stripes after B's format stripes).
- **C-S2, the private successor, as C amended it** (a transaction joins a batch only at `:ready`, so a
  stage cannot name its batch earlier, and nothing may fail after admission): both steps are in the
  `:ready` arm. `(fn2-identity-stage d fn2-core) → (mv code fn2-core)` immediately before
  `fn2-commit-admit-txn`: validates the decision against published state (`:stale` re-decides under the
  claim), guarantees room for one fact in a private successor (`:full` is backpressure: stay `:ready`),
  or answers `:duplicate` / `:evidence` (reply, nothing to record) / `:identity-conflict-bound`. Then
  `(fn2-identity-bind d batch article binding principal fn2-core) → (mv code fn2-core)` right after the
  admission's `:ok`, in the same arm: copies the offer's octets into the batch's private successor
  (stored → accepted, conflict → evidence); it cannot fail after an `:ok` stage, so a non-`:ok` is an
  invariant failure (stop). For B's commit kind: `(fn2-identity-publish batch fn2-core)` after the root
  swap and before any member result (private → frozen in one step; the buckets' stamps move so
  in-flight decisions go `:stale`; bounded by members per batch), `(fn2-identity-drop batch fn2-core)`
  for a refused batch; an uncertain batch calls neither (recovery resolves it); `fn2-id-decide-step`
  skips private overlays. Until C1c's sealer, identity capacity is overlay rows × arenas, and exhaustion
  shows as `:full` at stage. So `:prepare` does injection and membership only, and the identity staging
  moves into `:ready`.
- **A-S7 as landed** (DSL seat's read taken): `:class` is a pool class index (class 1, the profile's
  second; the upload's profile check requires it), not a profile expression; a take refused by the pool
  parks its waiter on the partition FIFO, and the grant service wakes the head only when the pool holds
  the rows the take reserves (`fn2-machine-partition-classes`, `fn2-machine-pool-has-p`), so a pool
  shortage is a wait, not a re-park loop; a waiter that is neither `*fn2-none*` nor an idle machine is
  refused (`fn2-machine-refuse-write`). A taken kind owns `next-free` and `stopped`.
- **A-S7 ruling (DSL seat, 2026-10-30):** D writes taken kinds itself as a foundation commit in a
  worktree on top of S1 (S1 touches the admission generator), under the whole-tree gate (every layer's
  unit books, A's seven drivers with the 113 A4 blocks identical, B's units); the DSL seat reads the diff
  before it lands.
- **S1's refusal semantics (A as built; D accepts):** a booking refused at Accept does not park the
  listener; the connection is admitted unbooked and its greeting renders the 400, which keeps the
  flood's refusals as 400s rather than an accept backlog.

### 14.8 Slices, acceptance, scenarios

Astra's order is taken: the seams that decide semantics are settled together first, then ingestion,
then one real durable POST with its read-back, before anything is widened.

| slice | contents | waits on |
|---|---|---|
| D4 1/n | `upload-scan.lisp` (header scan, Message-ID range, definite refusals), `tests/upload-scan-unit.lisp`; `upload-feed.lisp` (the streaming unstuffing feed), `tests/upload-feed-unit.lisp` | nothing (landed 92a31a6dd and the feed commit) |
| seams | A-S7, A-S8, B-S1, B-S2, C-S1, C-S2 agreed together, with this section's claim, successor-visibility and evidence semantics | main, A, B, C |
| D4 2/n | ingestion: `fn2-upload` declared, `fn2-conn` article input (fields, `:block`, `fn2-conn-block` over `fn2-upload-feed`), BLAKE3 over the window, the TAKETHIS token and no-row discard, conn-unit transcripts; POST answered only under `:posting-interim t` (fixtures and sim-layer-d), the public capability off | A-S7, B-S1 |
| D5 1/n | `fn2-txn` with `fn2-txn-claims`, the claim and its FIFO, a generated Message-ID path for POST, lookup through C-S1 | D4 2/n, C-S1 |
| D5 2/n | one real durable POST: prepare into the private successor (C-S2), the batch member (B-S2), 240 after publication, uncertain; read-back through D6's ARTICLE by Message-ID or the IDENTITY checker; stale-decision, disconnect and death-cut controls; posting capability on; H's POST interims leave | B-S2, C-S2 |
| D5 3/n | IHAVE, CHECK, TAKETHIS on the peer path with request/reply queuing (a connection keeps framing the next TAKETHIS while earlier outcomes are pending, replies in request order), evidence operations; scenario 5 | D5 2/n |
| D4 3/n | temporary extents through storage jobs (articles over two chunks; chunk reuse once its octets are durable; the Message-ID keeps its own range when chunk 0 is recycled); scenario 4 whole | B's allocator in the core, a storage-job kind |

**D4 2/n as built.** POST only (IHAVE, TAKETHIS's token and its no-row discard move to D5 3/n with the
peer path, which needs the request/reply queue anyway). The connection answers POST `:article-input`
(`rule :post`), its next `:command` run takes the upload (`fn2-machine-take-fn2-upload`, copies `conn
conn-gen request rule principal-slot`) and renders 340; `:reply` moves to its `after` phase, now
including `:article-input`. The feed state lives on the connection row (`fed`, `feed-mode`,
`feed-discard`), written only by the connection; the upload reads it (a cross-row read, no cross-row
write) and aborts when the connection's generation, `upload` or `upload-gen` no longer name it (the
connection's phase is not read: the take wakes the upload while 340 is still being sent). A full second
chunk or a source past the bound is `:too-large` and the block drains. The upload hashes into hasher row
`3 + slot` (B-S1), scans the header, and at the terminator gives the verdict and posts its word
(`fn2-conn-post-word`, generation and request checked); a valid article gets the interim `:not-stored`
until D5. Layer D's section is four books, each under the one-minute rule: `assembly-callbacks-d` (the
operations the connection and the upload share, the connection's helpers), `-d-conn` (greeting and
input), `-d-conn2` (the rest of the connection) and `-d-upload`; the upload's finish is three
preserved steps (two minutes inline). WIRE requires a reply for every complete command line received
before a close: only a closing reply (205, a malformed line's 501) or an article block's refusal may
be followed by the close with lines unanswered (the dropped-205 wire is its mutation control in
`tests/conn-unit.lisp`). Evidence: `tests/upload-unit.lisp` (every POST shape whole, by 7 and by 1
octet, each expected wire also passing WIRE; three clients over two windows, the third parked and
granted; WIRE's two-phase controls) and sim-layer-d's POSTING set (four seeds under network faults).
WIRE now reads POST and IHAVE in two phases (`POST` 340/440, `POST-BLOCK` 240/441; `IHAVE`
335/435/436, `IHAVE-BLOCK` 235/436/437).

**D5 1/n as built.** `fn2-txn` (`fn2/books/txn.lisp`, section book `assembly-callbacks-d-txn` for its operations and arms) is a
taken kind (`:taken (:phase :admit :rows :transaction-row :ranges () :copy (upload upload-gen conn
conn-gen request rule principal-slot))`, capacity `:t` under `:posting-interim`), with the claim
table `fn2-claims` as a D core child (`fn2-core-claims`, one row per transaction slot). The upload
whose header scan reaches `:header-done` moves to `:identity` and takes the transaction there
(`fn2-machine-take-fn2-txn`; refused, it parks on the kind's FIFO), then keeps receiving. At its
terminator it appends the source's BLAKE3 to the window right after the source (chunk 0 when it
fits, else chunk 1; a pool workspace is written at its fill; the article bound leaves the room:
`min(:article-max, cap0 + cap1 - 33)`), writes its verdict on its own row (`word` the
definite refusal or 0, `inj` the injected-field refusal or 0), wakes the transaction and waits in
`:sealed` until the transaction lets go of it (an upload aborting with a live transaction waits
the same way). One writer posts the word: the transaction. Its arms: `:admit` hashes the
Message-ID (FNV-1a, 250 octets) and begins the claim (a POST without one waits for the verdict
and gets the interim); `:reserve` walks the claim (16 chain steps a run; a held Message-ID parks
the transaction in its holder's FIFO, the holder's release hands it over and wakes it); `:lookup`
applies the upload's verdict first, then offers the Message-ID and digest (C-S1) and steps the
decision (`:duplicate` and `:conflict`/`:evidence` refused by word); `:prepare` counts the body's
lines, looks each Newsgroups name up (S-GROUP, one source a run; none carried is `:group`), applies
the injected fields, and declares the slots: the identity fact (article = binding = `:event`),
the article row (key and birth `:event`), the operation outcome (`(principal, operation)` with the
operation `:event`: fresh per NNTP attempt, NNT-005) and one group-count accept per carried group
(at most 6, else `:unaffordable`); then resolves. `:ready` is one transition: stage, the admission
(`fn2-commit-admit-txn`, B-S2's interim answering `:not-served` until B lands the member: the
transaction is refused `:not-stored`), bind on `:ok`; `:stale` decides again. `:accepted` and
`:refused` post the word and release the successor, `:releasing` releases the claim (its FIFO's head
takes it), `:draining` wakes the upload and reclaims the row: a run has one wake slot, so each wakes
one row. Departures: the kind's
budget is 16 KiB, not B.3's 4 KiB, because stage (4 KiB), bind (8 KiB) and the admission are one
run by C-S3's design; `:full` and an exhausted batch re-run the arm (no wake source until C1c and
B-S2: owed with them). Owed rows (`fn2/books/owed-txn.lisp`, teeth in `tests/txn-unit.lisp`):
`fn2-txn-admission-interim` (B-S2), `fn2-txn-generated-message-id-interim` (injection, D5 2/n).
Also owed: a waiter's cancellation in a claim FIFO (an aborted upload's transaction waits for the
hand-over, then releases at once); the overview row and the addr entries (D5 2/n, with the
overview line). Evidence: `tests/txn-unit.lisp` (refused, duplicate and conflict over facts seeded
through C-S3, the model's order of verdict, identity, group and injected fields, pipelined posts,
two clients on one Message-ID, every transcript whole, by 7 and by 1).

**sim-layer-d** gains a posting client (POST blocks in seeded fragmentations, valid and each refusal
shape, duplicate and conflicting resends) on every run of the existing four sets, with WIRE (reply
codes by the model's table for POST's two phases), ACCOUNT (an upload's and a transaction's holdings
booked on its principal, D7's `:upload-row`/`:transaction-row` dimensions), and from D5 2/n
`check-identity` (C's checker over the offers, answers and recorded facts) and HISTORY. Mutation
controls: a feeder that drops one data line (WIRE/IDENTITY catch the digest), a transaction that
answers 240 before durable (HISTORY), a claim table that admits two holders of one Message-ID
(IDENTITY). H's interim table shrinks as each slice lands: `fn2/tests/surface/fn2_conn_interim.json`
is regenerated from `*fn2-answer-interim*` at each slice (POST's row leaves at D5 2/n, when posting
is advertised and a POST can succeed).

### 14.9 The design review (Astra, `build/d-seat/d45/astra-1.md`)

Astra would build the three machines as designed and changed six things, all taken above: the feed's
work accounting counts the block line's rescan and keeps producer and consumer offsets (14.2); the
transaction row is taken before the claim, `:reserve` holds no claim, and POST's generated Message-ID
path precedes the claim (14.3, 14.4); claim stability is stated for an immutable offer before its own
publication, with no starvation bound claimed (14.4.3); identity facts are staged into a private
successor overlay before the batch seals, never recorded at lookup and never discovered at install
(C-S2); evidence is its own operation, and C's decision distinguishes accepted content from evidence
(14.4.3, C-S1); outcomes carry their evidence, are correlated by request ordinal, and the keystones
split unconditional safety from delivery under stated progress, with an accepted witness for T9
(14.6). Two positions were recorded and Astra's taken: the posting capability stays off until a POST
can succeed (14.5); the slice order puts the seams first and one durable POST before widening (14.8).

## 15. D6: the query cursor machine `fn2-cursor` *(design, statement first; the D6 commits rewrite it as built)*

The contract is brief item 6, ROUND2 §B.2 row 5 and §B.3, D0's bundles `(:cursor :select)` and
`(:storage-job :read)`, scenarios 2, 3 and 6, C's read contract and range reads
(`fn2/docs/c-ordered-runs.md` §6, `fn2/books/range.lisp`) over the schemas of `ordered.lisp` and
`folds.lisp`, and fn1's reader contract (`specs/nntp.md:182-505`; the oracle is H's model
`fn2/tests/model/nntp_model.py` `_select_group`, `_move`, `_lookup`, `_retrieve`, `_over`, `_hdr`,
`_cmd_list`). The connection's decision (§4.3) answers the reader commands with interim 503s today
(`*fn2-answer-interim*`, rows `:d6`); H's oracle has 15,028 interim replies over seventeen verbs
waiting on this machine.

### 15.0 As built: D6 1/n (`fn2/books/cursor.lisp`, the first kind in the machine form's child form)

This subsection is the present state; 15.1-15.9 are the design it was built from, and where they
differ this one holds.

- **The kind.** `fn2-cursor` is a taken kind (`(defmachine-registry fn2-cursor)`, P4). Its rows are
  the read rows: `:capacity (fn2-b-read-rows profile)`, so read row X is the row's slot (`row-slot`).
  Phases are `:free :select :seek :render :send :finish :draining :retired`, and it holds
  `:cursor-row`. Its arms are child form over C-S4's read children; 15 sub-arms carry the branches
  of `:seek` and `:render`.
- **TX is written under the connection's owner, not handed.** The take copies the connection's
  owner triple (`conn conn-gen conn-kind`), its RX place (`rx-slot rx-gen line-s line-e`), its TX
  range, its mask and its selection (`group current pin`).
  - The cursor reads the line and renders every page into the connection's TX under that triple.
    Nothing is handed: the connection touches neither RX nor TX while it is in `:query`.
  - `turn` says whose move it is. The cursor clears it and wakes the connection when a page is ready
    (`roff` is where the page starts). The connection sends the page and sets `turn` again, waking
    the cursor, which renders the next page or, once `done`, finishes.
  - The connection copies the selection back (`update sel ncurrent spin`) after the last page.
  - `cancel`: a connection that drains with a cursor waiting sets it and wakes the cursor (one wake:
    an upload and a query are never both live).
- **Selection.** The view is `pin`, set to C's published frontier at GROUP/LISTGROUP (15.1's `view`;
  `view` is a reserved column name).
- **Served:** GROUP, LISTGROUP name [range], NEXT, LAST, STAT [n | <id>] and OVER/XOVER [range],
  with their 411/412/420/421/422/423/430 refusals.
  - STAT <id> answers `223 0 <id>` through `fn2-read-identity`, visible when its article is at or
    below the pin.
  - LAST walks [1, current-1] forward and reads the last entry again. That is linear in the articles
    before current; a positioned seek replaces it.
- **Not yet served (1/n-b), each answering 503 meanwhile:**
  - LISTGROUP with no name: the selected group's name is not read back from `fn2-groups`.
  - OVER <id>: the article's number in the group comes with D5 2/n's address entries.
  - The LIST variants.
  - ARTICLE/HEAD/BODY are 3/n, over B's `fn2-block-read`.
- **The interim table.** It loses GROUP, LISTGROUP, NEXT, LAST, STAT, OVER and XOVER. These answer
  `:query` where the profile serves reading. Without reading, `*fn2-answer-unread*` gives the 503,
  or 412 for NEXT and LAST.
- **Book time.** `cursor.lisp` took 1,339 s on forge with a kind-wide stobj tuple (920 shape lemmas)
  and 501 s with the form's per-arm tuple (24fce1ecd). The remainder is the cursor's own shape:
  `render-single`'s guard, `render-step`, and `:seek` writing 12 children through C's read ops. What
  removes it: split those sub-arms per branch, and have C's read ops return only what they change.

### 15.1 What is read, and from where

| reply | rows read | how |
|---|---|---|
| GROUP `211 COUNT LOW HIGH GROUP` | `fn2-groups` (name → group), `fn2-group-counts` (group → count low high) | two exact lookups in one run, so the numbers and the pinned view are one instant; count 0 renders `0 high+1 high` (the model's `(0, wm+1, wm)`) |
| LISTGROUP | as GROUP, then `fn2-overview` over `(group, lo..hi)` | a range read stopping at the pinned view (position limit) |
| NEXT / LAST | `fn2-overview` | NEXT: a range read from `(group, current+1)`, one entry; LAST: bisection over one-entry range reads below `current` (at most 61 starts for u60 numbers), never a numeric walk |
| STAT/HEAD/BODY/ARTICLE by number, current | `fn2-overview` exact `(group, n)` at the view, then `fn2-article` (state: `:withdrawn` → 423 `withdrawn-number`) | exact lookups; the Message-ID is the overview line's fourth field |
| … by Message-ID | `fn2-identity` (accepted fact for the Message-ID octets) → article, then `fn2-article` | C's identity read by Message-ID (C-S4 below); number 0 in the reply (the model admits 0) |
| OVER/XOVER, HDR/XHDR, XPAT by number or range | `fn2-overview` over `(group, lo..hi)` | resumable range read: at most 32 entries examined and 4 KiB rendered per run (§15.4); HDR's fields from the stored overview line (Subject, From, Date, Message-ID, References, `:bytes`, `:lines`); other fields need the stored header (with bodies, 15.6) |
| LIST ACTIVE/COUNTS/NEWSGROUPS, wildmat | `fn2-groups` range over every name, `fn2-group-counts` per group | the groups range is an octet-keyed range read (C-S4 asks for it); status `y` while posting is served, else `n` |
| NEWNEWS | `fn2-overview` by position | a positioned seek per group (`fn2-seek-start`, INBOX 4.1) after the position the date maps to; the date-to-position map is owed (15.6) |

**The pinned view (the model's logical snapshot; Astra's position, taken).** STORAGE-DESIGN §4
decision 2: a connection reads a logical version, never an old root. A connection's `view` is pinned
to the engine's published frontier (C-S4 `fn2-read-frontier`, the `:published` position C's engine
row carries) at its greeting, and re-pinned by every GROUP and every LISTGROUP (the bare form too:
the model's `_select_group` pins in both); every reader decision then answers as of `view`:

- overview reads (`(group, number)`, a stream whose position grows with the number) stop at the
  first entry whose position exceeds `view` (the range read's position limit), exact lookups by
  number included;
- GROUP's numbers are the group's **at the view**, reconstructed without a historical summary:
  `high_v` is one less than the positioned seek's answer (`fn2-seek-start` over `(group, ·)` after
  position `view`: the least number from which every entry is newer than the view), `count_v =
  count_now − |entries in (high_v, high_now]|` (a range read over the numbers published since the
  view, so its cost is the publications since the pin, never the group's size), `low_v` the first
  entry at the view; `count_v = 0` answers `0 high_v+1 high_v` (the model's `(0, wm+1, wm)`);
- by Message-ID, the accepted fact's `binding ≤ view` (with C-S4's identity read, D6 2/n);
- LIST's per-group numbers the same way (D6 2/n).

Exact while nothing is withdrawn; withdrawals have no fn2 writer until D5's control transactions,
which then owe a versioned summary (recorded as `fn2-cursor-withdrawal-view`, 15.7). GROUP's
lookups are resumable C steps across runs (no single-run atomicity is claimed): every number it
renders is a function of `view`, which the run that pins it fixes first. **Read contract outcomes as typed replies**: `:read` serves;
`:gap` and `:unavailable` answer the command's declared 503 (`:no-projection`); `:wait` and
`:stale` are not reachable for a view taken from the published frontier once C's coverage
invariant covers untouched schemas (Astra: publication stamps only the batch's own overlays), so
until C states it the cursor reads with `fn2-range-no-position` semantics plus its own position
limit and never calls the plan with a position above the frontier; `:refused` stops the core.

### 15.2 The kind: a taken kind, not a field set on `fn2-conn`

Two positions were weighed. Fields on `fn2-conn` would need C's read state (a range row, its
sources, a field stripe, run cursors) per connection, `C` = 256 of them resident whether reading or
not, and would make the connection's widest arm wider. A **taken kind** `fn2-cursor` (A-S7, as the
upload and the transaction are) has its own capacity `X` (ROUND2 B.1: 256; the tiny profile 4) and
D0 resource `:cursor-row` (rank 13, "a query cursor from its command to its last reply byte"), so a
reader beyond `X` waits on the kind's FIFO holding only its connection (scenario 2: a stalled reader
holds its reserved window and nothing else), the read state is per cursor row, and the connection
keeps only what outlives a command: **the selection** (`group`, `current`, `view` on `fn2-conn`).
Taken, for admission and ownership (the arm language's read sets already removed the width limit;
with `X = C` the profile saves no rows, a smaller `X` does).

Phases (the brief's, each with its reason; holds `(:cursor-row)` in every live phase, plus
`:cache-pin` from 15.6 while a body streams):

| phase | arm | does |
|---|---|---|
| `:free` | idle | free chain |
| `:select` | `fn2-cursor-select` | accept the connection's TX hand (15.3); re-parse the command line (≤ 512 octets of the connection's RX, read under its owner: a cross-row read); resolve the target: the group by name, the Message-ID's article, or the connection's selection |
| `:seek` | `fn2-cursor-seek` | position the read: exact lookups, a range start, LAST's bisection, NEWNEWS's seek; one bounded C step per call, at most 32 per run |
| `:need-page` | `fn2-cursor-page` | a run page the read named (`:miss`) is loaded by a storage job (`(:storage-job :read)`); unreached until C1c installs runs in the served core (refuse-phase, as `fn2-conn-unreached`) |
| `:inspect` | `fn2-cursor-inspect` | the delivered entry against the command's filter (XPAT's wildmat, LIST's wildmat, HDR's field) |
| `:render` | `fn2-cursor-render` | the status line, then rows into TX until the next row does not fit the run's 4 KiB or TX; the terminator when the read ended |
| `:send` | `fn2-cursor-wait` | TX handed back to the connection; no work until the connection hands it again (more) or lets the cursor go (finished) |
| `:finish` | `fn2-cursor-finish` | release the read rows (C-S4 `fn2-read-release`); move to `:draining` |
| `:failed` | `fn2-cursor-fail` | a failure after the success line was sent (scenario 3): the stream ends incomplete, the connection closes, no fresh refusal is inserted; unreached until bodies (15.6) |
| `:draining` | `fn2-cursor-drain` | reclaim the row (`fn2-machine-reclaim-fn2-cursor`), waking the kind's FIFO head |
| `:retired` | idle | generation exhausted |

Fields: `conn :link conn-gen :u60 request :u32` (copied by the take: who to answer; every
hand-over and every read-back checks both generations and the request), `line-s line-e :u32` (the
command line in the connection's RX), `group current view :u60` (the connection's selection,
copied: `group` 0 is none, group identifiers being positive; `current` 0 is none, numbers starting
at 1; the view is always pinned), `access-ref :u32` (the pinned access rule, W01), `article :u60`
(an article identifier, distinct from `current`), `tag :u8 reply :u16`, `lo hi next :u60` (the
range and the first number not yet rendered), `roff :u32` (the rendered prefix of a row longer
than what is left of TX), `seen :bool` (any entry delivered), `step :u8`, `update (:enum
fn2-cursor-update (:none :current :selection))` (what the connection copies back), `more :bool
done :bool`, `tx-slot :link tx-gen :u60`, `stopped :bool next-free :link`. Budget `(:bytes 8192 :steps 32
:descriptors 0)` (15.4's run; the cursor issues nothing, cap 0); capacity `(fn2-profile-x profile)`, 0 unless the profile serves reading
(`:reading t`: H's tour and sim-layer-d set it; the served node profile with D9).

### 15.3 The connection's half, and TX by hand-over

`fn2-answer` gains the answer `:query` for every cursor command (after its sub-form checks, which
stay where they are): nothing is rendered. `fn2-conn` gains the phase `:query` (holds unchanged:
`:connection-row :rx-range :tx-range`) and the fields `query :link query-gen :u60` and `group current
view :u60` (15.2's selection; `current` is the current article number). The line is **not consumed** until the cursor ends (start/pos stay at the line), so the
cursor reads its arguments where they are and a refused take re-runs nothing but the take.

The reply is written by the cursor into **the connection's TX slot, handed over** with the pool's
own `fn2-pool-hand` / `fn2-pool-accept-hand` (pool.lisp). This is an ownership transfer of the
workspace, not a loan: the D0 reservation stays the connection's (it holds `:tx-range` in every
phase), while write authority moves with the pool owner; the invariant is that TX's pool owner is
the connection except between a hand to the matching cursor and that cursor's hand back. The cycle
(Astra's, taken):

1. the connection owns TX empty (`pending = borrows = 0`) and hands it to the cursor `(*fn2-cursor-kind* id gen)`, waking it;
2. the cursor accepts, renders a page, hands TX back to `(*fn2-conn-kind* conn conn-gen)`, wakes the connection and waits in `:send`;
3. the connection accepts, sends (`:reply`, `after = :query`), waits for the borrow's release, resets TX, and returns to `:query`;
4. `:query` hands TX again while the cursor said `more`; after the **last** page is sent it copies the selection back (per `update`), consumes the line and wakes the cursor to finish: the cursor row lives to the last reply byte (D0's `:cursor-row`).

Cancellation: a failed Send moves the connection to `:closing` while its cursor waits in `:send`
holding nothing of the connection's; the connection's release wakes its cursor as it wakes its
upload, and a cursor that finds its connection's generation, `query` or request moved drains.
`:query`'s arm:

| condition | the run |
|---|---|
| no cursor yet | `fn2-machine-take-fn2-cursor` (copies `conn conn-gen request line-s line-e group current view access-ref principal-slot`); `:no-row`/`:pool` parks the connection on the kind's FIFO; `:ok`: hand TX, wake |
| TX handed back by the matching cursor | accept; `:reply` with `after = :query` |
| back from `:reply`, the cursor `more` | hand TX again, wake |
| back from `:reply`, the cursor `done` | copy the selection back, clear `query`, consume the line, wake the cursor, `:command` |
| otherwise | nothing (parked on the cursor) |

The hand-over operations are D's thin wrappers over pool.lisp in conn.lisp's op events
(`fn2-conn-hand-tx`, `fn2-cursor-hand-tx`; defcosts with no D0 effect: no hold moves).

### 15.4 Runs, budgets, continuations (scenario 6)

**Pages restart the read.** A page never holds a delivered entry across a yield (an entry's octets
are references into an overlay arena the sealer may free between runs, C's amendment (b)): each
`:render` run starts its range read at `next`, the first number not yet rendered, delivers and
renders rows while they fit, and ends the page at the first that does not; a row longer than what
TX holds when empty (an overview line may be 1,024 octets and a connection's TX 1,024) is rendered
in pieces from `roff`, re-delivered by the next page's restart. So one positioned start per page
(a lower-bound descent) is the price, and the entry lifetime question disappears.

**Budget.** C's range step passes its budget to every source (`fn2-range-advance-all`), so a step
over `S` sources costs at most `S × budget` reads. A `:render` run takes at most
`*fn2-cursor-steps*` = 4 range steps of budget 128 over at most 8 sources (4,096 reads) and renders
at most 2,048 octets; the kind's budget is `(:bytes 8192 :steps 32 :descriptors 4)`, above B.3's
4 KiB as the transaction's is (recorded departure; performance is published, not a gate).

An OVER over `1-2147483647` (the grammar's article-number cap) on a group of three entries costs
three deliveries and an `:end`, not two billion steps: C's range read seeks to `lo` and delivers only
stored keys. LISTGROUP renders numbers only (at most 22 octets a row). OVER renders `NUMBER TAB line`,
`line` the overview row's stored octets (which D5 2/n writes with its Xref suffix through C-S3a).

### 15.5 Replies (the catalogue's rows; each a fixture)

| command | success | refusals, in the model's order |
|---|---|---|
| GROUP g | 211 count low high g | 411 (`fn2-groups` absent), 503 `:no-projection` (`:gap`/`:unavailable`) |
| LISTGROUP [g [range]] | 211 … list follows, numbers, `.` | 412 (no g, none selected), 411 |
| NEXT / LAST | 223 n mid | 412, 420 (current not in the view), 421 / 422 |
| ARTICLE/HEAD/BODY/STAT [n \| mid] | 220/221/222/223 n mid (+ block) | 412, 420, 423 `no-number` / `withdrawn-number`, 430 `no-msgid` / `withdrawn-msgid`; HEAD/BODY/ARTICLE 503 `:no-framing` until 15.6 |
| OVER/XOVER [range \| mid] | 224 + rows | 412, 420, 423 (OVER) / 420 (XOVER) on an empty range, 430 |
| HDR/XHDR/XPAT | 225 / 221 + rows | 412, 420, 423/430; a field the overview does not carry: 503 until 15.6 |
| LIST ACTIVE/COUNTS/NEWSGROUPS [wildmat] | 215 + rows | none beyond §4.3's |
| NEWGROUPS / NEWNEWS | 231 / 230 + rows | 503 `:no-century` (§4.3); NEWNEWS's date map owed (15.6) |

### 15.6 Slices

| slice | contents | waits on |
|---|---|---|
| D6 1/n | C-S4's first half (core children, the stripe, range reads and the exact lookup for read rows); the kind, the connection's `:query`, the TX cycle with cancellation; GROUP, LISTGROUP, NEXT, LAST, STAT by number and current, OVER/XOVER by number and range; the view at the greeting; the units over state seeded through C-S3, WIRE over every transcript, the interim JSON regenerated | C's `:published` frontier column |
| D6 2/n | C-S4's second half (the identity read with membership visibility, the ordered scan for LIST); STAT/OVER by Message-ID, HDR/XHDR/XPAT over the overview fields, LIST ACTIVE/COUNTS/NEWSGROUPS at the view | D5 2/n's overview rows for a real read-back |
| D6 3/n | ARTICLE/HEAD/BODY: stored octets through storage jobs (`:need-page`, `(:storage-job :read)`), the lease before the success line, `:failed` (scenario 3), Xref prepended; HDR of any stored field | S-ARTICLE-LOCATION (B, C), D4 3/n |
| D6 4/n | NEWNEWS and NEWGROUPS by position (the date-to-position map); run pages through `:need-page` | C1c, D5 2/n's injection clock |

### 15.7 Keystones (statement first; `fn2/books/owed-cursor.lisp`, teeth in `tests/cursor-unit.lisp`)

The subject is the served core at its adapter boundary after a seeded published state:
`fn2-cursor-serve-run (profile seeds later transcripts)`, the wire of each client after `seeds` (one
article a batch: identity fact, article row, group-count accept, overview row) are recorded and
published through C-S3's own operations, as `tests/txn-unit.lisp` seeds identity facts, with
`later` published one per adapter round once the client has received two replies (so after its
first command's reply), and the core's visit count. The reference is `fn2-cursor-spec-wire`, the
model's replies over the list view, written from RFC 3977 and the model, not from the cursor.

| name | statement | teeth |
|---|---|---|
| `fn2-cursor-reply-exact` | seeded state well formed, a transcript of covered commands ending in QUIT: every chunking gives the reference's bytes | positive: every covered command positive and refused; negative: LOW off by one for an empty group, one entry past the view; the seeded store publishes through C-S3 and the served core still answers the interim 503 (owed) |
| `fn2-cursor-view-pinned` | a transcript opening with GROUP and naming no other GROUP/LISTGROUP: publications after its first reply change none of its replies | positive: OVER, NEXT, LAST, STAT after a later publication; negative: the reference over the union differs (a reader without the position limit) |
| `fn2-cursor-range-cost` | GROUP then OVER lo-hi is answered exactly **and** the transcript's machine visits are at most a constant plus a constant per entry in the range, whatever hi − lo (the conjunction keeps it non-vacuous) | positive: `1-2147483647` over three entries; negative: a numeric walk's visits exceed the bound |
| `fn2-cursor-ownership` *(with the cursor)* | every octet a connection is sent belongs to its own request; no stale cursor writes a reused connection's TX; a disconnect releases the cursor | a Send failure while the cursor waits; a stale-generation hand |
| `fn2-cursor-withdrawal-view` *(departure, with control transactions)* | a withdrawal after the pin | D5's cancel fixture |

Astra's further witnesses (hypothesis removal beside mutation: rows split across pages, partial
Sends, run replacement between pages, sparse LAST, the source-capacity boundary) are D6 1/n's unit
cases.

### 15.8 Seams (sent through main, exact forms)

- **C-S4, served reads for cursor rows** (to C; D offers to write it in `fn2/books/machines-c-read.lisp`
  as machines-c-groups.lisp is written, C reading the diff, since C1c holds C's seat). A C core child
  `fn2-reads`, one row per cursor slot (`(fn2-profile-x profile)` rows): an exact lookup's
  continuation (`lphase lbound lrow lver`, as `fn2-succ-txns`), range row `x` of a served
  `fn2-ranges`, sources `[x·8, x·8+8)` of a served `fn2-range-sources`, seek row `x` of a served
  `fn2-seeks`, eight run cursors after the transactions', and a field stripe of
  `*fn2-read-stride*` rows after B's and the sealer's (`fn2-b-field-rows` gains `+ x·stride`). Every
  operation `(… fn2-core)`, a defcost each:
  ```lisp
  (fn2-read-key x j value fn2-core) -> (mv code fn2-core)          ; integer key field j (j >= arity: hi's)
  (fn2-read-key-octets x j slot gen off len okind oslot ogen fn2-core) -> (mv code fn2-core)
  (fn2-read-lookup x sid budget fn2-core) -> (mv code fn2-core)    ; :ok :absent :more :miss (fn2-xl-step)
  (fn2-read-range x sid pfield plimit fn2-core) -> (mv code fn2-core)   ; fn2-range-start over [lo, hi]
  (fn2-read-next x budget fn2-core) -> (mv code fn2-core)          ; :entry :end :more :miss
  (fn2-read-identity x mslot mgen moff mlen okind oslot ogen budget fn2-core) -> (mv code article fn2-core)
                                                                    ; the accepted fact of a Message-ID
  (fn2-read-value x f fn2-core) -> value                            ; integer field f of the entry
  (fn2-read-octets x f dslot dgen okind oslot ogen fn2-core) -> (mv code len fn2-core)
                                                                    ; append octet field f to a workspace
  (fn2-read-frontier fn2-core) -> (mv code position)              ; the greatest published commit position (built)
  (fn2-read-release x fn2-core) -> (mv code fn2-core)
  ```
  **Ruled (main and C, 2026-10-30): D writes it, C and B read the diff, with C's five amendments,
  binding.** (a) The stripe: reads stripes sit below the sealer's 1,280-row stripe, which sits just
  below the transaction stripes anchored at the table's end: `base(x) = rows − 1024·t −
  *fn2-b-seal-field-rows* − stride·(x+1)`, B's `128·fc-rows` at or below `base(0)`;
  `fn2-b-field-rows` and `fn2-idc-profilep` gain `+ x·stride`; the stride a named constant of the
  book, at most 1,024. (b) Staleness: the sealer moves overlays into runs between any two steps and
  frees the overlay's arena in the same step as it installs the run, so every read continuation
  re-checks its source at each step (an overlay source its row's phase and arena generation, a run
  source the schema's run version) and on a change re-seeks from the resume key or answers `:stale`;
  it never reads a freed arena; `:miss` keeps its word though resident pages cannot raise it before
  M2's cold leg. (c) `fn2-read-frontier` reads a `:published` position C adds to its engine row
  (`fn2-id-engine`, set in `fn2-succ-publish`), not the overlays' coverage (a retired overlay's
  coverage disappears; runs carry no position). (d) LIST over `fn2-groups` is not a range read (the
  range engine refuses octet keys, `:key-kind`, and is not extended): it is a whole-schema ordered
  scan, `fn2-read-scan` / `fn2-read-scan-next` over the same read row (C2a's run scan beside the
  overlay index in key order, newest wins by SEQ then run identifier), bounded per step. (e)
  `fn2-read-identity` reads the accepted fact through the decision path's own lookup
  (`fn2-run-lookup-step`, the overlay locate), answering `(:found article)`, `:evidence` or
  `:absent`, never through the identity adapter.
  **Built, first half** (`fn2/books/machines-c-read.lisp`, unit `tests/read-unit.lisp`; the record
  is C's doc §8 item 13): (a) and (b) as ruled; `fn2-read-key` takes a region (`:lo`/`:hi`), and
  `fn2-read-value` / `fn2-read-octets` answer `(mv code ...)` (assert, never absorb: `:stale` once
  the schema's run version moved since delivery); (c) waits on C's `:published` column
  (`fn2-cursor-view-pinned` stays owed until it lands). **Second half built**: (d) `fn2-read-scan` /
  `-scan-next` (a whole-schema ordered scan whose resume key is the delivered key, copied into the
  cursor's workspace and skipped once), (e) `fn2-read-identity -> (mv code article candidates)`, the
  selection and evidence status of IDENTITY-ACROSS-PEERS ruling 8 over C's engine as it stands; the
  rest of the typed read result (availability, coverage, authorization) is the owed row
  `fn2-read-identity-typed-exact`. Per C's §4a the cursor (and the txn) decide replies from the
  separate facts a decision or read returns (selection, evidence status, coverage), never from a
  verdict alone.
- **C-S3a, a late octet argument** (C's; landing): `(fn2-successor-arg-octets-late t i j max)` at `:prepare` (`max` within the slot's octet capacity, else `:bounds`), `(fn2-successor-fill-octets t i j slot gen off len okind oslot ogen)` between stage and bind (`:state` unless staged and unbound, `:bounds` past `max`); bind refuses `:state` while a late argument is unfilled. As asked (for D5 2/n's overview line): the overview line carries the
  Xref suffix, whose numbers are assigned at stage, so `(fn2-successor-arg-octets-late t i j max
  fn2-core)` at `:prepare` reserves room for at most MAX octets, and `(fn2-successor-fill-octets t i
  j slot gen off len okind oslot ogen fn2-core)` between `fn2-successor-stage` and `fn2-successor-bind`
  supplies them (`len ≤ max`; bind copies them as today).
- **S-ARTICLE-LOCATION** (to B and C, for D6 2/n): the article row names where its stored octets are
  (B's payload block references from the batch member, or C5's locations schema), so a cursor can
  issue `(:storage-job :read)` jobs and take its lease before the success line.

### 15.9 The design review (Astra, `build/d-seat/d6/astra-1.md`)

Astra would build the taken kind, keep the selection on the connection and hand TX over; taken.
Changed on its reading: the view is the model's logical snapshot (pinned at the greeting, re-pinned
by every GROUP and LISTGROUP, numbers reconstructed at the view, 15.1), not latest-only reads; the
cursor lives through the last Send and is cancelled by the connection's release (15.3); pages
restart the read and long rows render in pieces (15.4); the budget counts sources (15.4); the
sparse-range witness uses the grammar's cap, 2147483647; `fn2-cursor-view-pinned` is stated for
transcripts that do not re-pin; an ownership keystone joins. Recorded as two positions: Astra
would generalize `fn2-xl-step` over an explicit continuation allocation; D extends `fn2-succ-txns`
and `fn2-run-cursors` by `X` read rows (and `8X` source cursors) so the one lookup serves both, which
is the same generalization by allocation, with no copy of the code. Deferred with reasons: the
identity read with membership visibility and LIST's per-group metadata (D6 2/n, C-S4's second
half), `:miss` with page identity (C1c's runs).
