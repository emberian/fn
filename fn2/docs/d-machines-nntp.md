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
| T10, resident state bounded by the profile | `fn2/books/owed-d.lisp`, `fn2/tests/owed-d-unit.lisp` | D1a | D |
| the command-grammar DSL `defgrammar` | `fn2/books/grammar.lisp` | D2a | D |
| the NNTP command and reply table | `fn2/books/nntp-grammar.lisp` | D2a | D |
| generator, mutator, fuzzer and its three mutation controls | `fn2/books/grammar-gen.lisp`, `fn2/tests/grammar-fuzz.lisp` | D2b | D |
| table check against H's model | `fn2/tests/grammar-oracle.py` (reads `fn2/tests/model/nntp_model.py` from `fn2/h-harness`) | D2a | D |
| listener/connection machine | `fn2/books/conn.lisp` | D3 | D |
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
| D2 parser over pool ranges | R6a1 (`fn2-pool-scan`, `fn2-pool-drop-prefix`, `fn2-pool-compare` with two owners) | D2a builds the DSL, table, parser and renderer over A's existing checked scalar exports (`fn2-core-read`, `fn2-core-write`), bounded by the 4 KiB run quantum; D2c ports line finding and prefix retention to R6a1's primitives once they land and deletes the scalar inner loop (the derived path only). |

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
| 7 | `:tls-slot` | :slot | `(:round2 :ltls 16)` | none | A handshake job, held for the handshake only. |
| 8 | `:upload-row` | :row | `(:profile :u)` | none | An article input in progress, held while its bytes arrive. |
| 9 | `:chunk-window` | :window | `(:round2 :large-upload-windows 16)` | none | Two 256 KiB chunk ranges of a large upload, held while it streams. |
| 10 | `:transaction-row` | :row | `(:profile :t)` | none | A posting transaction from admission to its outcome. |
| 11 | `:identity-reservation` | :reservation | `(:profile :t)` | none | The Message-ID and operation identity claim of one transaction. |
| 12 | `:cursor-row` | :row | `(:profile :x)` | none | A query cursor from its command to its last reply byte. |
| 13 | `:wait-row` | :row | `(:profile :w)` | none | A parked consumer wait from registration to its reply or cancellation. |
| 14 | `:subscription-edge` | :edge | `(:round2 :esub 4096)` | none | One wait row's edge to a stream, reserved at registration. |
| 15 | `:control-output` | :bytes | `(:profile :w)` | none | The reply window a wake or control reply needs, reserved at registration so delivery never waits. |
| 16 | `:cache-pin` | :pin | `(:round2 :cache-profile)` | :recovery | An object lease under a pinned view, held while a reply streams it. |
| 17 | `:batch-membership` | :records-and-bytes | `(:round2 :batch 1024 4194304)` | none | A transaction's records in a commit batch until publish. |
| 18 | `:storage-job` | :job | `(:profile :jread :jwrite)` | :recovery | A read or write slot: a storage job row, held across its issue, completion and verification. |
| 19 | `:storage-window` | :pool-slot | `(:profile :pool-classes)` | :recovery | The pool range a storage job reads into or writes from. |
| 20 | `:fence-slot` | :slot | `(:profile :fence-slots)` | :fence | One fence in flight per storage domain. |
| 21 | `:cancel-credit` | :credit | `(:profile :ncancel)` | :cancel | One outstanding cancellation request. |
| 22 | `:operation` | :op | `(:profile :o :qa)` | (:close :cancel :arm-wake :fence) | One op row with its outbox descriptor and two result cells, reserved together (fn2-op-reserve); held for one issue. |

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

**Interim, layer A only.** `*fn2-resource-a-holds*` (the kinds each phase of `fn2-listener`,
`fn2-echo`, `fn2-scribe` may hold; pending operations are the outstanding table's, and waiting for a
completion is not a resource wait) and `*fn2-resource-a-wait-reasons*` (A's `fn2-wait` enum by the
kind it awaits: `:issued` none, `:op-credit` → `:operation`, `:pool` → `:storage-window`,
`:admission` → `:connection-row`) are R7's to move into each `defmachine`'s `:holds`; then they are
deleted here, like `*fn2-resource-effects*` once R7 declares the effects on its allocator operations.
R7 splits the listener into `:accepting` (`:accept-credit`) and `:admitting` (`:accept-credit
:connection-row`), the case per-phase holds cannot state while one phase spans both (A/D DSL seat,
2026-10-29).

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

## 4. The machine DSL: what D needs from R7 *(seam request; A builds it)*

D's machines declare through A's `defmachine` with R7's arm contracts. The forms D needs, exactly:

1. **Arm contract per continuation and per observation handler**: `:cost (:bytes F :steps F
   :descriptors F)` where each `F` sums declared `defcost` entries of the calls the arm makes plus
   constants; `:writes (field ...)`; `:tables (child ...)` naming D's registered children; `:next
   (phase ...)`; `:uses (operation ...)`; `:holds` per phase as **resource-kind names from D0's
   `*fn2-resource-order*`** (so `holds(S') - holds(S)` is checked against the bundle each acquiring
   call declares).
2. **`defcost` for outside calls**, at least: A's pool and issue wrappers, R6a1's range primitives,
   D0's bundle acquire/release operations (each declaring its resource effect as an ordered list of
   kinds), D2's parser and renderer continuations (`:bytes` bounded by the run quantum), B's commit
   reference and C's lookups (declared by their layers).
3. **The continuation record**: what a run keeps when a budget is exhausted is the row's fields
   (no separate record); the arm contract's `:next` must include the arm's own phase whenever its cost
   form can reach the cap.
4. **Obligation stubs** into `fn2-squares` per arm (`:schema :bound` for cost ≤ cap and the cost
   function, `:invariant` for frame and continuation preservation, phase totality per kind, account
   conservation per declared entry), `:from (:machine K)`, with generated executable teeth.
5. **The common row fields of ROUND2 §B.1** (`phase, generation, principal-slot:u16,
   account-ref:u32, ready-prev/next:u32, wait-reason:u8, deadline`) generated for every kind (they
   exist today), with `wait-reason` an enum whose values include every D0 resource kind (a wait reason
   names the exhausted kind, never a bare integer).
6. **Refusal postures** (`:on-refusal`, R6b item 2) for D's kinds: connection close-and-release from
   the close reserve; upload discard to terminator; transaction refused by typed word.

R7's port of listener, echo/null and scribe is D1's "A4's three machines re-declared"; D does not
redo it. D3 is R7's first D consumer and reports every gap back through main.

## 5. Catalogue: the machine ownership matrix

Every kind of ROUND2 §B.2, with its owner, phases, retained fields, capacity (§B.1) and simultaneous
per-run budget (§B.3; work stops at any limit). All are declared through A's `defmachine`.

| kind | owner (quest) | phases | retained fields beyond the common row | capacity | per-run budget |
|---|---|---|---|---:|---|
| listener/connection | D3 | `accepting greeting command article-input reply upgrading closing draining` | capability token; RX/TX ranges; parser offset u32; command ordinal; selected view (version + leases); auth/config refs; active request refs; outstanding-use count u32 | `C` 256, accept credits 8 | 4 KiB parsed/rendered, 32 steps, 4 descriptors |
| TLS admission | D7 | `requested reserved running result-ready cancelling draining done` | connection MRef; config generation; job OpRef; evidence range; negotiated flags; channel-binding digest | `Ltls` 16 | 32 metadata operations |
| upload | D4 | `head identity receiving validating discard sealed aborting draining` | connection/request; source and stored lengths u64; BLAKE3 scan continuation; two chunk ranges; manifest cursor; Message-ID range; transaction ref; TAKETHIS ordinal | `U` 128; windows 16 | 4 KiB scanned/hashed/copied, 32 manifest entries |
| transaction | D5 | `admit lookup reserve prepare ready batched accepted refused uncertain draining` | operation identity (principal-id, operation-id); authority/config version; identity reservation; membership cursor; dependency-manifest root; proposed index root; batch ref; outcome | `T` 128 | 32 index entries/comparisons/units; 4 KiB comparison |
| query cursor | D6 | `select seek need-page inspect render send finish failed` | request kind; pinned view/root; article/group refs; index position; source offset u64; render offset u32; framing state; pending ranges | `X` 256 | 32 examined entries, 4 KiB inspected/rendered |
| consumer wait | D8 | `registering checking parked eligible polling replying cancelling` | consumer/history/incarnation ids; registration epoch; principal/query/view versions; acked and scanned positions; edge head/count; pending-wake bit | `W` 256; `Esub` 4,096 (separate row) | 32 edges or entries, 4 KiB output |
| cache/storage job | D4 (first consumer: upload extents), D6 (reads) | `reserve issue waiting verify ready failed cancelling draining` | expected block identity/address/digest; pool range; OpRef; verification offset; owner/waiter refs | `Jread` 64, `Jwrite` 16 | 4 KiB verify/copy, 32 metadata ops, 4 descriptors |
| timer/grant/wake services | D7 | `idle scanning dispatching pending` | heap/list cursors; resource-wait heads; dirty-subscription cursor; latest clock observation | one each | 32 timers, grants or edges |
| commit batch | **B** (B3b), migrated into the arm contracts by B after R7 | `collect seal dependencies log-write fence durable install publish notify uncertain draining` | batch identity; predecessor head; members; dependency cursor/count; outstanding counts; packed ranges; proposed root; fence OpRef; publication cursor | `B` 2 | 32 members/dependencies or 4 KiB, 4 descriptors |
| cleaner, checkpoint, recovery | **B** | per §B.2 | per §B.2 | one each | 32 entries or 4 KiB |

## 6. The grammar DSL *(design; D2a rewrites)*

`defgrammar NAME` declares a wire grammar once; it is D's DSL (the third of EXECUTION-MODEL §5), and
its entries are DSL-METATHEORY's `command` kind, registered through `fn2-declare`. A command entry:
keyword, typed arguments (number, range `n-m`/`n-`, Message-ID, wildmat, keyword, token), the protocol
states that admit it, whether it opens a multi-line input block, and its reply codes. The grammar
level declares the framing: CRLF lines, the 512-octet initial-line cap (RFC 3977 §3.1, with the
`specs/nntp.md` lines the table cites), pipelining, dot-stuffed blocks with the header-line limit,
discard-to-terminator after a refusal, and the two hand-off boundaries (STARTTLS: nothing framed
during the handshake; COMPRESS: E's, and per H's ruling of 2026-10-29 advertised and accepted only
after authentication, NNT-054).

Generated: the incremental parser as a continuation over `[parser-offset, fill)` of the connection's
RX range under a byte budget (at most 4 KiB per run), its state retained as row scalars (never a
list); the reply renderer into the TX range; the generator and mutator (D2b); and five obligation
stubs with teeth: totality under the connection row's guard over arbitrary octets, linear
consumption, fragmentation invariance, bounded retained input, reply typing. The table is checked
against H's model (`nntp_model.py`: `HELP`, `KEYWORDS`, `SPECS`) and the fn1 evidence
(`books/nntp-help.lisp:52-59`'s keywords, `books/protocol-table.lisp`).

## 7. Keystones, phased

| statement | admitted with | over |
|---|---|---|
| T10 `fn2-core-state-bounded` | D1a | the assembled core's children and their `fn2-columns` rows: a generated resident measure equal to a registry sum of the profile, unchanged by `fn2-turn` (no array grows after init) |
| T1 `fn2-turn-served-safety`, T8 `fn2-reply-trace-fragmentation-invariant` / `fn2-connection-privacy` | D3 | the connection machine and grammar |
| T6 `fn2-refusal-no-committed-mutation` / `fn2-outcomes-three`, T9 `fn2-exact-identity` | D5 | the transaction machine, C's identity schema, B's commit batch |
| closure audit `fn2/tests/turn-guards.lisp` | D9 | `fn2-turn`'s executable closure |

## 8. The ABI reconciled *(D3)*

Differences between ROUND2 §D and A's §4 known now: `Connect` (E4's peers), the control inbox `Qc`,
`EvidenceObserved`, `ServicePosture` payloads, `Trace` payloads, `Send` with one range (four
reserved). D3 records each with its resolution here.

## 9. The sprint's gaps, and how D plans around them

The sprint (`origin/fn2/sprint-cd` 8e3488fcb) is compost; its gaps are the seams.

| gap | state | plan |
|---|---|---|
| G1 closed machine registry | closed by R5c's open registry (`defcorechild`, assembly sections) | D's kinds register in D books included by `assembly-index` after B's |
| GD1 dispatcher fallback hardwired to A's core | closed by the same: the generated dispatch's refusal arm receives the assembled `fn2-core` | none |
| GD2 no commit/recovery machine | B3b on `fn2/b-durability` | D5 references B's batch; no stand-in persistence |
| GD3 no arm cost/frame contract | R7 | §4's seam request; D3 waits on R7 |
| GD4 no retained-prefix compaction | R6a1 `fn2-pool-drop-prefix` | D2a interim over scalar exports, D2c ports |
| GC1 no two-owner range compare | R6a1 `fn2-pool-compare` | C's and D5's consumer |

## 10. Departures, seam requests and open items

- Seam request to A (via main): R6b item 1 re-cut onto D0 (§2); R7 carries §4's forms.
- `declare.lisp` gains the `command` kind's table entry (D2a), purely additive.

## 11. Deferred assertions E must restore

Everything that needs authentication, access rules, the TLS adapter or the CLI: AUTHINFO/SASL,
XREDEEM, STARTTLS completion (D7 has the admission half), COMPRESS (after authentication only),
posting permissions, access-rule refusals, the natives needing them. Listed per command as D3-D9 meet
them.

## 12. Quests

| quest | contents | waits on | state |
|---|---|---|---|
| D0 | resources.lisp, the tables of §3 as data with certification checks, the owed deadlock-freedom keystone, per-bundle exhaustion and cancellation scenarios for A's existing bundles | A only | done |
| D1a | T10 in owed-d.lisp with teeth | A only | next after D2a |
| D2a | defgrammar, the NNTP table, parser, renderer, obligation stubs, every-split test, H-model table check | A only | parallel with D0 (second worktree) |
| D2b | generator, mutator, fuzzer, the three mutation controls | D2a | |
| D2c | parser onto R6a1's scan and drop-prefix | R6a1 | |
| D3 | connection machine, greeting/HELP/QUIT/MODE/DATE/CAPABILITIES, timers, 400 refusals, ABI reconciled, T1 and T8 | R7, C2/C3, D0, D2 | |
| D4-D9 | per the brief | per the brief | |
