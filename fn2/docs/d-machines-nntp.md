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
| resource order, admission bundles, protected reserves (data + checks) | `fn2/books/resources.lisp` | D0 | D (a library: includes only declaration machinery, so A's `defmachine` `:holds` can read it) |
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

## 3. Acquisition *(design; D0 makes `fn2/books/resources.lisp` authoritative and rewrites this section as its printed form)*

EXECUTION-MODEL §7a item 2. Seven tables (a)-(g), as the brief requires. The order principle: **a
resource is ranked by how long it is held**: what a machine holds across many runs and external waits
comes first, what it holds only for one issue comes last. Every bundle acquires in ascending rank, so a
holder of rank `r` only ever waits for ranks above `r`.

**(a) The total order** (draft ranks; D0 may reorder with a recorded reason):

| rank | resource kind | unit | capacity (ROUND2 §B.1, initial) | protected reserve |
|---:|---|---|---|---|
| 1 | listener accept credit | credit | 8 | none |
| 2 | connection row (admission credit) | row | `C` = 256 | none |
| 3 | principal reservation (per account dimension) | quantity | per principal limits | system reserve for recovery/control |
| 4 | connection RX range, TX range | pool slot by class | per profile classes | none |
| 5 | TLS handshake slot | slot | `Ltls` = 16 | none |
| 6 | upload row | row | `U` = 128 | none |
| 7 | large-upload chunk window | window (two 256 KiB ranges) | 16 | none |
| 8 | transaction row | row | `T` = 128 | none |
| 9 | identity reservation | reservation | per transaction | none |
| 10 | query cursor row | row | `X` = 256 | none |
| 11 | consumer wait row | row | `W` = 256 | none |
| 12 | subscription edges | edge | `Esub` = 4,096 | none |
| 13 | control-output reservation (reply window for wakes and control replies) | bytes in TX | per wait row | reserved at registration |
| 14 | cache pin / object lease | pin | per cache profile | recovery reserve |
| 15 | cache/storage job row | row | per profile | recovery reserve |
| 16 | batch membership (record count and packed bytes) | records, bytes | 1,024 and 4 MiB per batch | none |
| 17 | read slot, write slot | slot | `Jread` 64, `Jwrite` 16 | recovery reserve |
| 18 | fence slot | slot | 1 per storage domain | **fence reserve** |
| 19 | operation reservation: op row + outbox descriptor + two result cells (one atomic kind in A, `fn2-op-reserve`) | op | `O` = 1,024, `Qa` = 1,024, `Qr` = 2,048 | **close, cancel, ArmWake, fence reserves** (A30) |
| 20 | service work (one bounded run of a scheduled service) | visit | calendar | the four protected service classes |

**(b) Admission bundles.** Every transition that acquires names its bundle as an ordered list of
kinds; it acquires the whole bundle or nothing, and on refusal it keeps its continuation with a wait
reason naming the first exhausted kind. The first bundles: listener Accept `{1, 2, 4(RX), 19}`;
connection Receive `{19}` (RX already held); Send `{19}` (TX held); Close `{19 from the close
reserve}`; scribe Write `{17, 19}`, Fence `{18, 19 from the fence reserve}`, Read `{17, 19}`;
STARTTLS `{5, 19}`; POST/IHAVE/TAKETHIS admission `{3, 6, 7, 8}` then identity `{9}` then batch
`{16}`; ARTICLE/BODY `{3, 10, 14}` then reads `{15, 17, 19}`; consumer wait `{3, 11, 12, 13}`.

**(c) Held-while-waiting restriction.** A machine waiting for kind `k` holds only kinds of rank
below `k` (and its own row). Waiting for an adapter completion is not waiting for a resource: its
result cells were reserved at issue (§D.1), so it completes under the environment progress assumption.

**(d) Release and rollback.** On refusal nothing was acquired, so nothing is released. On
cancellation, close and a failed result, release runs in **descending** rank: op reservation
(after the terminal and any release result), job and slot, pins, membership not yet sealed, rows,
pool ranges, principal reservation (settled, never refunded past what was charged: disconnect erases
no charge, rule 5), admission credit, accept credit. A range still externally borrowed is released
only on `BorrowReleased`.

**(e) Protected reserves.** Close, Cancel, ArmWake and Fence draw from op reservations set aside at
init and never lent to ordinary issue, so a table full of idle receives can still time out and close
(A30; R6b item 3). Recovery and control draw on the system reserve of every account dimension.

**(f) Notification debt leaves a committed batch.** A batch owes nothing per recipient after
`publish`: each request outcome is a state bit on its own transaction row (the connection reads it
when it next runs, its reply window was reserved at command admission); each affected subscription is
reached by the wake service's dirty-subscription cursor over the published frontier, and a waiter
registering late compares its cursor with the frontier (ROUND2 §E.2). So two slow recipients hold
their own rows and windows, never a batch slot; the batch drains once its own writes' borrows are
released.

**(g) Why no cycle.** A wait-for edge `m → n` exists only when `m` waits for a kind `k` that `n`
holds. By (c) every kind `m` holds ranks below `k`; `n` holds `k`, and if `n` waits it waits for a
kind above `k`. Ranks strictly increase along every path, so no path returns to `m`. Protected
reserves are never held while waiting, so release paths add no edge. D0 checks (b) and (c) over the
tables at certification and states the owed keystone (no reachable state where every holder waits on
another holder) with teeth.

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
| D0 | resources.lisp, the tables of §3 as data with certification checks, the owed deadlock-freedom keystone, per-bundle exhaustion and cancellation scenarios for A's existing bundles | A only | next |
| D1a | T10 in owed-d.lisp with teeth | A only | after D0 |
| D2a | defgrammar, the NNTP table, parser, renderer, obligation stubs, every-split test, H-model table check | A only | parallel with D0 (second worktree) |
| D2b | generator, mutator, fuzzer, the three mutation controls | D2a | |
| D2c | parser onto R6a1's scan and drop-prefix | R6a1 | |
| D3 | connection machine, greeting/HELP/QUIT/MODE/DATE/CAPABILITIES, timers, 400 refusals, ABI reconciled, T1 and T8 | R7, C2/C3, D0, D2 | |
| D4-D9 | per the brief | per the brief | |
