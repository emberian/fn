# fn2 layer C: the ordered-run metadata engine

Present state, rewritten whole by the layer-C seat. The contract is
`build/coordinator/briefs/FN2-LAYER-C-ORDERED-RUNS.md` (with its inbox-delivery section). The
decisions it serves are `build/coordinator/fn2/STORAGE-DESIGN.md` §1 and §4 (the summary equation,
fold versions, identity, decision 6), `STORAGE-DESIGN-ASTRA.md` "The concrete storage format" §B,
§C and §E, `FILTERS-2026.md`, `INBOX-DELIVERY.md` §4-5, `UNIVERSAL-CONSTRUCTIONS.md` §2.1-2.4 and
§4.3 with §12 decisions 2 and 3 as ember accepted them, and `TRANSPORT.md` §9. Layer A's decisions
(`fn2/docs/a-pool-host-sim.md`) and layer B's (`fn2/docs/b-durability.md`) bind this layer too. A
departure from a decision that is not recorded here is a defect.

## 1. Where each piece lives

| piece | file(s) | quest |
|---|---|---|
| the `:schema` declaration kind (table `fn2-schemas`) | `fn2/books/declare.lisp` (one additive line pair; foundation edit) | C1 |
| generic run page: C's page header and restart layouts, writer and reader tables, page writer, sealing, page reader | `fn2/books/runs-page.lisp` | C1 |
| `defrunschema`: per-schema entry, index-entry and run-descriptor layouts, key comparison, writer/seek entry points, the schema's registration | `fn2/books/runs-schema.lisp` | C1 |
| multi-page runs: the build (one writer per level, promotion of sealed pages into index entries), the verified-page cache, resumable lookup cursors, the run-level adapter and keystone | `fn2/books/runs.lisp` | C1b' |
| the manifest schema (the engine's own directory is a run) | `fn2/books/runs-manifest.lisp` | C1c |
| identity schema, its specification, the decision machine over overlays and installed runs, the recording under the conflict bound, adapters and keystones (`fn2-identity-assemble`, expanded after the run assembly) | `fn2/books/identity.lisp`; unit `fn2/tests/identity-unit.lisp` | C2b |
| installed runs (the resident view of each schema's sealed runs; the manifest makes it durable in C1c) | `fn2/books/runs.lisp` (`fn2-run-installed`) | C2b |
| active overlay per schema: a bounded in-memory sorted run (tables and placement in `fn2/books/overlay.lisp`; entry, locate, insert generated at the assembly) | `fn2/books/overlay.lisp`, `fn2/books/runs-assemble.lisp` | C2a |
| range scan from a lower bound (cursor path, next leaf through it) | `fn2/books/runs.lisp` (path table), `fn2/books/runs-assemble.lisp` | C2a |
| Ribbon filter per sealed run: the build (band, insertion, back substitution, page), the probe, the adapter and keystones | `fn2/books/ribbon.lisp`; unit `fn2/tests/ribbon-unit.lisp` | C2c |
| article metadata, overview, addressing schemas; the group directory and operation outcomes | `fn2/books/ordered.lisp` | C3, D5 seams |
| range reads (merge over overlays and runs, resume key, version) and the read plan; assembled by `fn2-range-assemble` | `fn2/books/range.lisp`; unit `fn2/tests/range-unit.lisp` | C3 |
| the served assembly: the production schemas assembled once with the identity decision, then the range reads | `fn2/books/runs-served.lisp`, `fn2/books/range-served.lisp` | C-ONE-ASSEMBLY |
| C in the served core: the engine's tables as core children, the decision rows' field stripes, the identity operations layer D calls (C-S1), their defcosts and core wrappers (`fn2-identity-core-events`) | `fn2/books/machines-c.lisp`, materialized in `fn2/books/assembly-callbacks-c.lisp`; unit `fn2/tests/identity-core-unit.lisp` | C-S1 |
| the batch's private successor (C-S3, which replaced C-S2): the transaction and write-slot tables, the engine row, put / arg / arg-octets / arg-octets-late / resolve / stage / fill-octets / out / bind / release / publish / drop over every schema, their defcosts and core wrappers (`fn2-successor-prepare-events`, `fn2-successor-commit-events`) | `fn2/books/machines-c-successor.lisp` (tables, put, arg, arg-octets, arg-octets-late, resolve; includes machines-c), `machines-c-stage.lisp` (stage, out, fill-octets), `machines-c-bind.lisp` (bind, release, publish, drop, defcosts, wrappers), materialized in `assembly-callbacks-c-prepare.lisp` (with the identity decisions) and `assembly-callbacks-c-commit.lisp`; unit `fn2/tests/identity-core-unit.lisp` | C-S3 |
| the group directory's genesis and lookup, the generic exact lookup over overlays and runs (S-GROUP), their defcost and core wrappers (`fn2-groups-core-events`) | `fn2/books/machines-c-groups.lisp` (includes machines-c-bind; included by `assembly-index`); unit `fn2/tests/groups-unit.lisp` (with S-OUTCOME and S-ARTICLE-ID) | D5 seams |
| fold declarations (`defrunschema :fold` on the `:schema` row: interpretation, initialization, coverage, observation; the step compiled twice, as a list function and as the served step over decoded rows) | `fn2/books/runs-schema.lisp` | C4a |
| the folds the clients read: group counts and watermarks, the consumer cursor, principal charges (durable half) | `fn2/books/folds.lisp` (included by runs-served before the assembly) | C4a |
| the folds' summary contract through the real engine (`fn2-fold-image`) and the generated keystones | `fn2/books/folds-served.lisp`; unit `fn2/tests/folds-unit.lisp` | C4a |
| registration, read-state, edge-policy and inbox folds; the select-versus-materialize check | `fn2/books/folds.lisp`, `fn2/sim/check-consumer.lisp` | C4b |
| compaction with reservations and backpressure; relocation under a lease | `fn2/books/compact.lisp` | C5 |
| IDENTITY checker (an independent list interpreter with its own Binding); CONSUMER checker | `fn2/sim/check-identity.lisp` (C2d); `fn2/sim/check-consumer.lisp` (C4) | C2d, C4 |
| acceptance | `fn2/tests/sim-layer-c.lisp` (scenario M3 so far; `fn2/tests/sim-layer-c-sweep.lsp` the 10,000-seed driver) | C2d-C6 |
| C's test world: the served assembly (range-served) and the teeth makers | `fn2/tests/runs-assembly.lisp` | C2b |
| units | `fn2/tests/runs-unit.lisp` (over the overview and identity schemas), `fn2/tests/identity-unit.lisp`, `fn2/tests/range-unit.lisp`, `fn2/tests/sim-layer-c.lisp` (all include `runs-assembly`), `fn2/tests/ribbon-unit.lisp` (the filter alone), `fn2/tests/identity-core-unit.lisp` (the served core) | each |

Every C book starts `(fn2-book-layer :c)` after its includes, so its rows count under layer C.

## 2. The seams C stands on

| seam | owner | what C uses | state |
|---|---|---|---|
| byte pool, handles, owners | A | `fn2-pool-reserve/read/write/lease-out/release-out/hand`; one 64 KiB class for run pages | on dev |
| `defcolumns`, `defmachine`, `defcorechild`, assembly sections | A | C's resident tables; C's machines (sealer, compactor) declared through A's `defmachine`; children registered in a C registration book included by `assembly-index` after B's | on dev |
| range compare with two owners (GC1) | A (R6a1 `fn2-pool-compare`, `pool-ranges.lisp`) | exact octet comparison of a stored key against a query in another owner's slot | **landed** at 09ad4a57f; C's interim compare is deleted (C1b') |
| native u64 columns (GC4) | A | persistent identifiers | **closed**: `:u64` exists (A-WIDTH-PER-COLUMN); C keeps u60 resident columns per A-WIDTHS and canonical varints on disk |
| `deflayout` | B | every C page structure, entry, index entry, descriptor | on dev; the codec, never a second one |
| page header, page kinds, page sealing and checking | B | `fn2-format-page-header`, `:run-data :run-index :partitioned-filter :manifest`, `fn2-format-run :page` (seal and check), parent-held digest rows | on dev |
| digest row to pool bytes | B | a parent encodes its child's 32 hash bytes from a pool range | **landed** at 810a4c376: `fn2-digest-store` in format-check.lisp (§8 item 1) |
| dependency entries, run-replacement and relocation records | B | `fn2-format-dependency-entry`, `fn2-format-run-replacement`, `fn2-format-relocation` | on dev |
| commit batch accepts C's sealed pages and installs C's roots (GC2) | B | dependencies phase covers C-written pages; install swaps C's per-schema root handle | **agreed form** (§8 item 2), B builds it inside B5 |
| allocator typed edges | B | extents for run pages; `:installed-root`, `:prepared-successor`, `:promised-read`; retire/release through the FIFO | on dev |
| identifier namespaces for `(:id NS)` | B (layout) | `run`, `stream`, `position`, `consumer`, `version` | **landed** at 810a4c376; C uses `(:id run)` from C1 |

The sprint's C scout (origin/fn2/sprint-cd, `fn2/sprint/c/`) is compost: its pages were a single
volatile page with a per-entry directory and a linear identity scan. Its gaps GC1-GC4 are the rows
above.

## 3. Page encoding (C1)

A run page is a B structured page. The physical hash, identity binding and padding check are B's:
`BLAKE3("fn2/physical-page/v1" || exact encoded page)`, checked against the parent-held hash and the
expected (physical unit, allocation pair, kind, encoded length, history, incarnation).

```
offset 0                 B page header (fn2-format-page-header), page-kind per level:
                           :run-data (level 0), :run-index (level >= 1), :manifest (manifest run)
offset A = *fn2-run-header-area* = 32 * ceiling(page-header-max/32) = 96
                         payload (payload-length bytes):
  A                        C run-page header (fn2-run-page-header), in a reserved region of
                           *fn2-run-page-header-max-size* bytes; the gap after it is zero
  E = A + header-max       entries, ascending by the schema's key order, each encoded by the
                           schema's generated entry (level 0) or index-entry (level >= 1) codec
  D                        restart directory: restarts x fn2-run-restart (u32 LE entry offset)
  A + payload-length       zero padding to the page size (B checks it)
```

`fn2-run-page-header` fields, in wire order: `schema (:id schema)`, `schema-version :u8`,
`run (:id run)`, `level :u8`, `ordinal :varint` (page number within its
level), `entries :varint`, `restarts :varint`, `restart-interval :u8`. Restart `j` is the offset of
entry `j * restart-interval`. Entries are stored whole (no prefix compression in format version 1:
the scholar's "recoverable exact octets" admits compression, and it is a measured later version,
not a default). The page is 64 KiB (`*fn2-format-page-size*`), a format parameter.

Decisions inside the contract:
- **C-HEADER-RESERVED.** The C header has varint fields whose length is known only when the page
  closes, so its region is reserved at its generated maximum and the entries start at a fixed
  offset. Readers never search for the first entry.
- **C-RESTART-BUFFER.** Restart offsets are buffered in a resident table during page construction
  (`fn2-run-restarts`, `writers * *fn2-run-restart-capacity*` rows, capacity 4096 since every
  entry is at least one byte and the interval is at least 16) and written after the last entry, so
  the padding after the directory is real zero padding checked by B, never an unchecked gap.
- **C-FENCES.** A level-k+1 index entry is the first key of its child page plus the child's
  `fn2-format-ref` (prefixed `CHILD-`, carrying the parent-held expected hash) and the child's
  entry count. Fence pointers are therefore separator keys; a search descends from the run root by
  lower bound over index entries. Directories are themselves pages; nothing is resident per page.
- **C-MANIFEST-IS-A-RUN.** The engine's directory (per-schema run descriptors) is a run of the
  manifest schema keyed by `(schema, run)`. One page encoder, one reader, one sealing path.

A run descriptor (generated per schema, `NAME-run`): `run, height, pages, entries`, the key
fields prefixed `MIN-` and `MAX-` (the run's fences), `ROOT-` ref, `FILTER-` ref (zero until C2).

## 4. Schemas, keys and merge rules

`(defrunschema NAME :id N :key ((field kind)...) :value ((field kind)...) :merge RULE
:page-kind KIND)` registers `(:schema NAME)` through `fn2-declare` and compiles, through
`deflayout`: `NAME-entry` (key fields then value fields), `NAME-index` (key fields, `CHILD-` ref,
`child-entries`) and `NAME-run` (the descriptor). It generates `NAME-compare` (field-by-field over
two decoded field ranges: integers numerically, octets lexicographically by bytes, a digest by its
32 bytes) and nothing else. `fn2-run-assemble`, run once after a world's last schema, generates the
layout dispatcher (`fn2-run-layout-decode/-encode/-size/-compare/-fields/-keys`, a `case` over the
registered schema ids, level 0 the entry layout and a positive level the index layout) with its
shape lemmas proved by cases, and the generic `fn2-run-add` (append, refusing an out-of-order key
by name), `fn2-run-seek` (bounded lower-bound search inside one page), `fn2-run-build-add`,
`fn2-run-build-promote`, `fn2-run-index-nth` and `fn2-run-lookup-step`, all guard-verified once
there. A schema declared after the assembly is refused by name. No runtime code walks a
declaration.

| schema | key | value | merge rule | quest |
|---|---|---|---|---|
| identity | exact Message-ID octets (≤ 250), content identity (digest) | article, acceptance binding ref, state, event | `:union` (a Binding: equal entries collapse, distinct contents under one Message-ID are a recorded conflict, never an overwrite) | C2 |
| article metadata | article | source/projection/membership refs, birth event, withdrawal state, version | `:latest` | C3 |
| overview | (group, group-number) | article, commit position, overview fields | `:unique` (a duplicate key is corruption) | C3 |
| addressing (`addr`) | (principal, position) | event article, arriving stream, reason bits | `:unique` | C3 |
| group counts (`fn2-group-counts`, id 5) | group | count, low, high | `:latest`, fold | C4a |
| consumer cursor (`fn2-consumer-cursor`, id 6) | (consumer, epoch) | position, version | `:latest`, fold | C4a |
| principal charges (`fn2-principal-charges`, id 7) | (principal, dimension) | charged | `:latest`, fold | C4a |
| operation outcomes (`fn2-outcome`, id 9; S-OUTCOME) | (principal, operation) | request digest, outcome (reply code, u16), event | `:unique` (within the declared retry lifetime: C5's retention) | D5 seam |
| group directory (`fn2-groups`, id 8; S-GROUP) | exact name octets (≤ 250) | group | `:latest` | D5 seam |
| obligations | obligation | owner, article, state, terms ref, release evidence ref | `:latest` | C4 |
| locations | logical object | current placement ref | `:latest` | C5 |
| manifest | (schema, run) | the run descriptor fields | `:latest` | C1 |

**A fold is a schema (C4a; STORAGE §4 decision 1).** `defrunschema ... :merge :latest :fold (:events
((KIND (ARG ...) [:when TEST] :set ((FIELD EXPR) ...)) ...) :init :empty :coverage :history-start
:observe (FIELD ...))` declares the fold on the schema's own declaration row; there is no second
declaration kind. An event is `(KIND ARG-VALUE ...)`, its key the args named by the key fields; a
row's value is its value fields (integer kinds only, so it fits B's u60 field rows), and an absent
row reads as zeros. EXPR is a natural, a field or arg name, `+ - min max` or `if` over the tests `= <
<= and or not`; every set field is computed from the old row. A failed TEST is `:refused`, a result
outside its field's width `:range`, and neither changes the row (assert, never clamp). From the one
declaration the schema generates the step twice: `NAME-FOLD-STEP` over list values (with the list
fold `NAME-FOLD-SPEC` and `NAME-FOLD-OBSERVE`, logic only) and `NAME-FOLD-APPLY` over decoded field
rows (served, guard-verified, dispatched by the assembly's `fn2-fold-apply`). A bootstrap
initialization `(:from FN)` and a later coverage start `(:from POSITION)` are refused until a fold
needs one. The folds of C4a, as D and E read them: group counts (`:accept g n` when `high < n`: count
+1, low the least number, high n; `:withdraw g n` when the group holds an article at or under high:
count -1, the watermarks stay, RFC 3977's bounds), the consumer cursor (`:ack c e to`, forward only;
`:rebase c e query start`, a newer query version and its start), principal charges (`:charge`,
`:refund` of at most what was charged).

**Identity is a Binding (UC §4.3, decision 3).** `B : Message-ID → P_fin(content facts)`, merged by
union. The schema is `fn2-identity` (id 1): key `(message-id (:octets 250)) (content :digest)`,
value `state (:accepted :conflict)`, `article`, `binding` (the accepting event), `principal` (the
offerer). The key includes the content identity, so a Message-ID's facts are adjacent and
`conflicted(mid)` is "two adjacent entries share the octets".

The decision (`fn2-id-decide-start`, `fn2-id-decide-step`, one row of `fn2-id-decides` per
decision in flight) visits every identity overlay, then every installed identity run, each
positioned at the lower bound `(mid, empty content)`, and reads that Message-ID's block: whether
`(mid, c)` is recorded and in which state, and how many other contents are. The answer is
`:duplicate` when `(mid, c)` is recorded as the accepted content, `:evidence` when it is recorded
only as conflict evidence (a re-offer of evidence must never hear "already stored"; D's §14.4.3),
`:conflict` when another content is, else `:stored`. One step skips, in one bounded scan of the
table, every overlay row that is not a readable identity overlay and every installed row that is not
a live identity run, so a decision on a node with nothing recorded answers in three steps. Each step is bounded (a run's
block is read through the scan, one entry per step; a block longer than the bound plus two is cut
short) and resumable; `:miss` hands the caller the page to load. `:found`/`:absent` come from byte
comparisons only; no filter decides.

**Concurrency (C2d).** Decisions are resumable, so others record and seal between their steps.
Two checks make a record safe without locking: the *stamp* of the Message-ID's bucket (a table
`fn2-id-stamps` indexed by the octets' hash modulo its rows, bumped by every record) and the
*identity version* (`fn2-id-version`, the greatest live identity run identifier, which every
installation raises). A decision takes both at start; `fn2-id-record` refuses `:stale` before any
other verdict when either moved, and the caller decides again. The stamp catches a fact recorded
after the decision passed the overlay that took it; the version catches a fact that moved from an
overlay into a new run while the decision was in flight (it would otherwise be met twice, or not at
all). Layer D's identity reservation keeps same-Message-ID offers from racing at all; the refusal
is the engine's own guarantee.

The recording (`fn2-id-record`) writes a stored offer as the accepted content and a conflicting
one as evidence, while the Message-ID holds fewer than `*fn2-identity-contents-max*` = 4 contents
(the accepted one and three conflicting); past that the offer is refused
`:identity-conflict-bound` and nothing is recorded. The evidence entry names the offering
principal; charging it against that principal's account is layer D's accounting. The offer's
octets are copied into the overlay's arena, so the decision and every later lookup are exact after
the offer's body and journal placement are reclaimed. The served choice of content is a separate
statement; evidence only grows. Exact octets are kept permanently (STORAGE §4 decision 6).
This record is being replaced: §4a states its successor (rulings 3 and 7).

## 4a. Identity across peers: the record's new shape (statement first; rulings 3 and 7 of IDENTITY-ACROSS-PEERS-20261030.md)

This replaces the identity record of §4. It is written before the code; the old shape is deleted
when the new one lands (no twin). Astra read the first draft (2026-10-31). This text takes its
changes; the two places where we disagree are stated with both reasons.

**Why the record changes.** Today `fn2-identity` (id 1) stores an unqualified `:accepted` or
`:conflict` under (Message-ID, content), refuses a fifth content per Message-ID, and decides by
walking the Message-ID's whole block. Under the rulings that is wrong three times:
- An unqualified state cannot say who accepted.
- A set bounded per name is not closed under union.
- The decision's cost grows with the competitors.

### Identities (ruling 2: four keys, kept as four)
- **N, the name:** `(namespace (:id namespace)) (name (:octets 250))`. Netnews is namespace 1, one
  global namespace (RFC 5536). A name is never prefixed by the receiving domain.
- **C, the content identity:** `(profile u8) (algorithm u8) (digest :digest)`. The profile names
  the subject and its extraction rule (ruling 1). The digest is the subject's, never the upload's
  raw digest.
- **O, an origin:** `(lineage :digest) (domain :digest) (incarnation …) (position …)`.
  - Lineage and domain are portable 32-byte identities: the descriptor or genesis digest under a
    named encoding profile. Bare local integers cannot tell independently created domains apart.
  - Incarnation and position take B's declared types from the envelope's origin fields (B-S2).
- **E, an occurrence:** `(O, ordinal)`, the ordinal being the fact's index within its member.
  - An import or a retry preserves E. A new observation gets a new E.
  - So two observations count twice; a retransmission counts once.

### Records
Evidence and history entries are immutable union facts. Candidates and the summary are materializations
that commit atomically with the facts that justify them. They are generated, never independently
authoritative. Local bookkeeping lives in local records, never inside a fact: sponsorship,
charges, storage location, import position.

| record | key | fields | merge |
|---|---|---|---|
| `fn2-identity-evidence` (id 1; replaces `fn2-identity`) | (N, C, E) | `kind` (`:binding`, `:invalid-signature`, `:out-of-scope`, `:resolution`), `issuer`, `proof` (the retained portable evidence's identity: the signed envelope, a proof, or the observed bytes), `dependencies` (the identity of the retained dependency set; zero when none), `rule` (the validation rule and its version, where one applies) | `:union`; the same key with an unequal payload is an inconsistency, never newest-wins |
| `fn2-identity-history` (id 11; the peer's history entry, RFC 5537 §3.3, fn1 peering.md §2.5) | (N, C, O) | `evidence` (E of the supporting evidence), `article` (relative to O, as O issued it) | `:union`, same rule |
| `fn2-identity-candidates` (id 12, generated) | (N, C) | `evidence-present`, `binding-qualified`, `local-entry` (O of this domain's history entry, or none) | materialized at commit |
| `fn2-identity-summary` (id 13, a fold) | N | `selected-content` (C, or none), `selected-entry`, `first-local-entry`, `resolution` (E of the last resolution applied), `candidates`, `evidence`, `history entries`, `coverage` (none, or the scope of a recorded gap) | `:latest`, fold |
| `fn2-identity-local` (id 14, local) | (N, C, E) | `sponsor`, `charged` (per dimension), `object` (where the proof's bytes are), `imported-at` | `:latest`, local only |

- **Competition is derived, never stored.** A binding competes at A and can be selected at B. An
  invalid-signature observation never makes a later properly supported binding of the same C
  ineligible.
- **A resolution statement is evidence** (kind `:resolution`). It names its target, its authority
  dependencies and its ordering information. The summary's `resolution` field is an output; the
  statements themselves are retained.
- **The interpretation context is the node's own commit domain** (ruling 13: one domain per node).
  It is stated in every summary statement below, never left implicit.
- **The six permanence states (ruling 9) are read, not stored.** They come from evidence, history entries,
  the article's withdrawal, the body's availability, and C5's obligations. "Under a custody
  obligation" needs the obligations source; it is not derivable from the other four.

### The admission transition (one compound fold event per name per transaction)
Two summary slots for one key in one transaction would each stage against the same old row:
`fn2-succ-stage-fold` reads the tip, not an earlier slot's staged row. So one event per name per
transaction:
- `:admit (N, deltas, establish)`. The deltas come from the engine, never from the caller: new
  evidence (count), new candidate (0/1), new history entries (count). They are the outcome of the union
  inserts staged in the same transaction. `establish` is set when this admission is a local
  acceptance and the name is unselected at the serialized tip: it sets `selected-*` and
  `first-local-entry`.
- `:history-import (N, new)`. Counts an imported history entry once. It never selects (ruling 14).
- `:resolve (N, E)`. Selects a named eligible binding under an authority-qualified resolution
  statement and the declared ordering. It deletes nothing.
- `:coverage-gap (N, scope)`. Records the scope and reason of omitted evidence. Clearing a gap
  needs an explicit completion witness (`:coverage-established`), never one later admission.

**A lost acceptance race replans into evidence-only admission** (ruling 6). Two transactions both
see the name unselected; the first to stage `establish` wins. The second's stage refuses only the
`establish` part, and its transaction stages again as evidence. A generic `:refused` must never
discard evidence.

**The commit position arrives after stage** (`fn2-txn-commit-1`: stage, admit, then bind with the
returned event). The local history entry's O carries that position, so it is a late-bound field, filled
at bind. This is C-S3a's mechanism grown from octets to integers. A late value never feeds a
guard, a key lookup, arithmetic or an allocation: stage decides eligibility, the deltas and
establishment; bind copies the position into the declared reference fields. The generator states
that finalization cannot fail, and that the fully bound event equals the staged one finalized.

**Funded admission (ruling 7).**
- Everything an admission will publish is reserved before stage, against the offerer, sponsor or
  peer, through `fn2-principal-charges`: evidence storage, the retained proof and dependencies,
  history entry, candidate and summary rows, and liability. Each is a separate dimension; work done is
  accounted separately.
- Facts, charges, candidates and summary share one private successor and one publication.
- A replay of the same admission neither counts nor charges again; a new observation does both.
- An admission refused for want of funds records no fact. It records a coverage gap, and the gap
  itself must be funded: the interaction reserves a small coverage-maintenance budget at its
  start. Where even that cannot be funded, a pre-funded coarser gap (per namespace and history
  cut) conservatively marks every affected name's reads. An unfunded peer offering endless fresh
  names never buys one permanent row per name.
- Coverage always names its scope: locally processed offers through cut p, or an imported history
  through its advertised cut. An absent summary never means globally complete.

### A refinement found while planning the build: integer handles, no octet fold values
The summary never stores a content identity or an origin. Each candidate (N, C) carries a
**candidate ordinal** `h`, assigned by the summary fold at its first admission: `:admit`'s
`:assign ((h (+ candidates 1)))` when the content is new. `selected` and `first-local-entry`
are ordinals. The decision reads the candidate row's `h` and the summary's `selected`, and
compares two integers: `:none` when selected is 0, `:same` when they are equal, `:other`
otherwise.

This keeps every fold value an integer. It also makes the late-bound field unnecessary for the
fold: `h` is known at stage. The history entry row's position takes the commit position by C-S3's
existing `:event` source at bind. So vocabulary items 3's late-bound integers (4 below) and the
octet fold values of item 1 drop out. What remains:
- octet and digest fold **keys** (N, and (N, C) for candidates, which is a fold too);
- the union insert with freshness;
- stage-result fold args;
- full-key exclusive resume;
- the resized layouts.

### The engine vocabulary this needs (the compiler grows; nothing hand-written)
1. **Typed octet and digest fold keys and values.** Logic generation, ownership checks, resolve,
   stage, bind and resume all carry them, and typed content comparison and copying with them.
2. **A union insert in the successor** (`:union` slots beside `:unique` and `:latest`). Stage
   answers `:new` or `:already-present` against the tip. The same key with an unequal payload is
   `:inconsistent`.
3. **Stage-result argument sources.** A fold arg may be a slot's staged freshness (`:new-of k`),
   validated against the tip.
4. **Late-bound integer fields**: C-S3a's rule, extended to integers.
5. **Full-key exclusive resume** for range rows over octet keys, with typed prefix bounds.
6. **Generated layouts sized for these schemas**, recomputing the 12-field / 8-value slot limits
   and their costs rather than squeezing the records to fit.

### The reads (each at a named view; a pinned view never substitutes content, ruling 8)
| read | answers |
|---|---|
| `fn2-identity-exact (N, C, view)` | the candidate row: evidence present, binding qualified, the local history entry; admission also checks the specific E or O for replay |
| `fn2-identity-summary-read (N, view)` | selection, locally known counts, the interpretation context, coverage, all at the same view as the exact read |
| `fn2-identity-evidence-start / -step (N, view, resume, budget)` | immutable evidence in full-key order, resumed strictly after the last delivered key, and whether the view's cut is still available |

**The evidence cursor reads a view, not a position fence.** Content-key order is not commit order:
a row at key a, position 20, precedes key z, position 10, and a cut at 15 must still return z. So
the range engine's stop-at-the-first-position-above-the-limit is wrong here. The cursor scans the
view with full-key resume. An incremental consumer (E4's evidence stream) needs a position-ordered
admission index of its own, because a key-order cursor misses insertions behind its resume key.
The two are separate reads, never one.

**The decision** (`fn2-identity-decide`, replacing the block walk of `fn2-id-decides`) is one exact
read plus one summary read. It returns three orthogonal facts plus one compatibility verdict:
- **The facts:** the selection relation (`:none`, `:same`, `:other`), the evidence status
  (novelty and kind), and coverage.
- **The verdict, in this precedence:**
  - `:duplicate`: a local history entry holds (N, C), including accepted content whose body was
    reclaimed.
  - `:evidence`: a qualified binding is known and no local history entry holds it.
  - `:conflict`: neither of the above, and the selection names another content.
  - `:stored`: neither of the above, and the name is unselected. It means eligible for
    admission, not durably stored.

D's txn consumes the facts, not only the verdict:
- `:evidence` is not article refusal: a foreign binding can be known while the local name is
  unselected.
- `:duplicate` never suppresses new independent evidence carried with duplicate bytes (ruling 14).

**Cost** is a fixed number of logical probes per stable attempt, with no enumeration of a name's
candidates, evidence or history entries. The bound is stated in source count, run heights, key-byte
bounds and the retry conditions (a version move restarts the attempt; a page miss waits). It is
not "three descents": `fn2-xl-step` visits overlays and possibly several runs.

### Keystones (statements before code)
A positive witness asserts the complete antecedent, the successful run of the real entry points,
and the conclusion. An error result or an impossible premise never counts as a pass.

| name | statement | positive; negative (the tooth) |
|---|---|---|
| `fn2-identity-union-order-free` (re-scopes `fn2-identity-binding-converges`: one node only) | For a fixed set of facts (identities and payloads), every admissible schedule of insertion, replay and sealing yields exactly that evidence set and history entry set, read back by the real scans of every installed run and published overlay. | two observations of (m, a), a replay of the first, and attributed history entries, in permuted delivery and sealing orders: two evidence rows. Negative: a node deduplicating by (m, a) returns one row. Dropping the consistent-payload hypothesis exposes `:inconsistent`. |
| `fn2-identity-interpretation-determined` (ruling 3) | Equal evidence, history entries, resolution statements, gap facts, interpretation context and version, and cut give the summary of `fn2-id-interpret-spec`, an independent list interpreter, read through the real summary read. | history entries A:a@7 and B:b@9, interpreted for A, in two delivery orders with one resolution: equal, and equal to the spec. Changing only the context to B may change the selection: the context hypothesis has teeth. Negative: selection by delivery order. A resolution present in only one run is not a positive witness. |
| `fn2-identity-attributed` | History entries of distinct origins for the same (N, C) all survive with their exact origins. Importing a foreign history entry into an unselected local context leaves it unselected. | A's and B's history entries for the same (m, a), even at the same numeric position: both survive. Negative: a store keyed by (m, a) alone collapses them; a node that selects on an imported history entry. |
| `fn2-identity-no-ceiling` | For fresh admissible requests whose reservations hold and whose steps make progress (hypotheses independent of success), each commits, with no per-name cardinality test in the path. An unfunded request commits no fact and records the gap. | nine distinct bindings for one name plus a second observation of one: nine candidates, ten evidence. A tenth-content request without funds: no fact, coverage names the gap. Negative: refusing the fifth funded content (the old bound); committing the unfunded fact; a count that wraps. |
| `fn2-identity-decide-bounded` | Per stable attempt, the decision makes a fixed number of logical probes, each within the structural bound (sources x height x key bytes), independent of the name's candidate and evidence counts. Its verdict and facts equal the read spec (a separate conjunct). | controlled source counts and heights, with growing same-name competitors, under instrumented comparator and page work. Negative: a decision that advances through every competitor breaks the bound. Without the stable-attempt hypothesis, completion is false (endless restart). |
| `fn2-exact-identity` (re-stated) | Through reclamation, sealing and compaction, the decision preserves N's namespace and exact octets, C's profile and algorithm, and accepted-versus-evidence meaning. | accept C1, retain competing C2, release the bodies, seal, query: C1 `:duplicate`, C2 `:evidence`, a new C3 `:conflict`; the same bytes in another namespace or profile are no duplicate. Negative: dropping the namespace, the profile or the reclaimed history entry. |
| `fn2-identity-summary-adequate` (generated per fold event, as C4a's) | The summary observed through the real read equals the fold of its events, and a replay changes nothing. | Negative: a replay that counts twice. |
| `fn2-identity-admission-atomic` | At every crash cut of a publication, facts, charges, candidates, summary and coverage are all present or all absent. | Negative: a cut that exposes charges without their facts. |
| `fn2-identity-evidence-cursor-exact` | A cursor at a view delivers exactly the view's evidence rows for N, in key order, across seals and version moves. | Negative: pagination that omits an eligible row after a seal. |

**`fn2-identity-linearizable` changes in substance, not only by losing the bound.** The checker
verifies one publication transition carrying the facts, charges, candidates, summary and coverage:
- two decisions see the name unselected, one local acceptance wins, and the other commits conflict
  evidence without article membership;
- a replay never double-charges;
- dropping the first batch invalidates the conclusions staged on it.

Its teeth: publishing a count without its evidence; two first local acceptances; committing a
losing conflict whose winner was dropped.

### Two positions recorded
1. **Count widths.**
   - Astra: a fixed-width count (u32 or u60) refuses updates eventually, so it is itself a
     ceiling. Use logical naturals with an extensible, resumable representation, and expose any
     interim bound.
   - C: counts are u60. 2^60 admissions per name cannot be reached at any rate the node can
     charge for. `fn2-identity-no-ceiling` states the representation bound as an explicit
     hypothesis (count < 2^60), and an overflow is a named stop (assert, never absorb), never a
     wrap.
   - Agreed: the theorem never claims "for any n" without the hypothesis, and the decision never
     decodes the counts.
2. **Candidates.**
   - Astra: a materialized (N, C) candidate index is required, because a history entry lower bound under
     (N, C, O) may find another origin's history entry first.
   - C agrees, and builds candidates as a generated materialization, updated in the same
     publication. The alternative, an origin-prefix seek, answers only the narrower question and
     would have to search inherited incarnations.

### Order of work (C's; engine ops and schemas, not arms)
1. The vocabulary (above, items 1-6), each with its unit.
2. The five records, and the deletion of `fn2-identity`: its `:record` slot kind,
   `*fn2-identity-contents-max*`, `*fn2-id-block-max*`, and `:identity-conflict-bound` in every
   vocabulary that names it (stage, txn, upload words, conn-answer). D's txn migration takes the
   word changes with ruling 6's evidence-commit path.
3. The decision and the three reads.
4. The checker's rewrite, then the keystones' teeth as evaluating functions, then the
   `defthm-owed` rows.

## 5. The write path (C1, C2, C5)

- **Writer.** `fn2-run-writers` rows hold one run under construction: schema, run, level, page
  slot/generation, cursor, entries and restarts in the page, page ordinal, previous-key field base.
  `NAME-add` encodes at the cursor through the generated encoder after checking the size against
  the space left for the directory, and refuses `:order` when the key does not exceed the previous
  key (`:union` admits equal Message-IDs with distinct contents because the content is in the key).
  `:full` means: finish this page and start the next. Finishing writes the directory and the C
  header, encodes the B header, and seals the page through `fn2-format-run :page` with `sealp`
  (resumable, 4096 bytes per call) into a digest row; the parent's index entry takes the child's
  ref. Every step is bounded; exhaustion is a continuation.
- **Build (C1b').** A run build (`fn2-run-builds` row) owns one writer row per level. Its caller
  drives `fn2-run-build-work` (one bounded unit: close, head, seal of the highest pending level) and
  acts on what it returns: `(:sealed L)` once per page (the writer row names the page; the caller
  records it), `(:promote L)` (call `NAME-BUILD-PROMOTE`: the sealed page's first key and
  parent-held reference become an entry of level L+1), `(:need-page L)` (give level L a fresh
  C-owned 64 KiB workspace and its physical identity from the allocator), `(:root L)`, or `:idle`
  (append the next entry with `NAME-BUILD-ADD`, or `fn2-run-build-finish`). The protocol keeps the
  library free of allocator and device coupling; C1c's sealer machine is its caller.
- **Overlay (C2a).** One bounded active overlay per schema, fed by the commit batch's prepared
  successor (Astra §E: the read-visible successor overlay is built before sealing; installation is
  a handle swap). An overlay is an in-memory sorted run: entries are encoded by the schema's entry
  codec into one C-owned arena workspace in arrival order, and a resident index of their arena
  offsets is kept in key order (locate by binary search, insert by opening a gap; both bounded by
  the overlay's index capacity). `:active` takes inserts; `:frozen` is being sealed and stays
  readable; then `:free`. An equal key is refused `:duplicate` and changes nothing; no room is
  `:full` (seal and start another). Sealing reads the overlay in order into the run writer.
- **Filter (C2c).** A sealed run gets one Ribbon filter page (`:partitioned-filter`, FILTERS-2026
  item 2): homogeneous Ribbon, w = 64 coefficient bits, r = 8 result bits, so the solution Z is one
  byte per slot. Slots = keys + ceiling(keys/16) + 63. Every key gives one equation c . Z = 0 over
  GF(2)^8 on the 64 slots from its start s; a homogeneous system is always solvable, so the build
  never fails or retries. The build (`fn2-ribbon-start`, `-add`, `-finish`, `-work`; table
  `fn2-ribbon-builds`, band `fn2-ribbon-band`) clears its band rows, inserts each key (shift out
  low zero bits, store in a free row or eliminate against the row pivoted there; a dependent key
  reduces to zero; at most 4096 steps per call, the continuation kept in the build row), solves
  from the top slot down (a free slot's byte from a generator seeded by the run, so pages are
  reproducible), writes Z through a run writer row opened on the page, closes, writes B's header
  (`fn2-run-head-b`, shared with run pages) and the filter header (`fn2-ribbon-header`: schema,
  run, seed, keys, slots, width, bits), and seals through B's sealer into a digest row (the
  parent-held hash). Its caller (C1c's sealer; the identity adapter today) feeds it the run's
  Message-IDs as it seals the overlay.
- **Sealer (C1c, engine half; `sealer.lisp`).** One seal row (`fn2-seals`: phase `:idle :build
  :filter :install :failed`, sub-phase, the overlay O, the next entry POS, schema, run, the run and
  unit counters, the root page, the hash workspace, the filter page, its resources WBASE FBASE CROW
  FILL and its owner) and one bounded step, `fn2-seal-step` (budget at most 4,096 bytes of page
  work): `:idle` picks the sealable overlay (C-SEAL-ORDER) and starts the real build over it, an
  empty one retired at once; `:build` drives `fn2-run-build-work` and acts on each answer (cache
  the sealed page, promote, give the level a fresh 64 KiB page under the owner, the root, or the
  overlay's next entry through `fn2-ov-entry` and `fn2-run-build-add`, then finish); `:filter`
  (identity runs) opens the filter page on the build's seventh writer row and drives the Ribbon
  build over the overlay's Message-IDs; `:install` enters the run in a free row of the resident
  view with its filter, retires the overlay (frozen to free, arena released) and releases the hash
  workspace in the same step, answering `:done`. `:full` and `:cache` are backpressure;
  any other refusal is an invariant the caller stops on. Its field rows from FBASE: the build's,
  the decoded entry at `*fn2-seal-eb*`, the filter writer's at `*fn2-seal-fw*`; its digest rows
  are in checker row CROW's stripe, regions 129-134 the levels' parent-held hashes, 135 the
  filter's. The pages stay resident (C-SEAL-RESIDENT); B's run-replacement member makes them
  durable (the device half).
- **Sealing through the commit protocol.** C's sealer machine (declared through A's `defmachine`)
  reserves extents, writes sealed pages into them and harvests their completions; the commit batch
  then carries a run-replacement record naming old and new manifest refs, lists every new page in
  its dependency manifest, and its fence covers them; install swaps C's per-schema root. Until B's
  seam (§8 item 2) lands, C1 seals pages and builds runs in the pool and checks them with B's real
  checker; no durability is claimed for them.
- **Retirement.** A replaced run's extents are retired through the allocator FIFO after the run
  replacement commits and released only when no edge (installed root, selectable checkpoint,
  promised read) protects them.
- **Compaction (C5).** Reserved, incremental, resumable merge of runs by the schema's merge rule,
  with a declared maintenance reserve; admission backpressures before the debt exhausts that
  reserve (STORAGE-DESIGN-ASTRA §4's price: compaction bytes per committed byte, reported).
  Relocation under a stalled lease moves only placement; the lease keeps its content identity.

## 6. The read path and the read contract (C1-C4)

- **Lookup.** A lookup cursor names its schema; descend from the run root by lower bound over index pages, then seek inside the data
  page: binary search over restarts, linear decode within one interval. Each call is bounded
  (≤ 4096 pool reads) and resumable from `(page, restart lo, restart hi, entry)`. A per-run perfect
  hash is measured against this sorted search before it is adopted (C6).
- **Filter probe (C2c).** `fn2-ribbon-probe` reads the filter page's two headers (refusing a
  malformed one by name), hashes the query's octets with the page's seed, and XORs the bytes at
  the coefficient's set bits from s: nonzero is `:absent`, zero `:maybe`. The identity decision's
  run-start phase probes a run that has a filter (`fn2-run-installed` FILTER, FUNIT, FCOUNTER; the
  page through the verified-page cache, `:filter-miss` when it is not there) and skips the run on
  `:absent`; the decision row counts READS and SKIPS. `:maybe` reads the run, so `:found` and
  `:absent` still come only from byte comparisons.
- **Exactness.** A lookup's `:found` means a byte-equal key was compared; `:absent` means the
  search ended at a lower bound whose key is greater. Neither ever comes from a filter alone.
- **Scan (C2a).** A cursor notes, at every level of its descent, the page (slot, generation,
  physical identity), its entry count and the index entry it took. A scan positioned at the lower
  bound of a query delivers level-0 entries in order (`:entry`); at a leaf's end it climbs to the
  lowest level with an entry to the right, takes it, and descends leftmost (`:more`, `:miss` as for
  lookup), and answers `:end` after the last entry. A page of its path that left the cache answers
  `:lost`: the caller re-seeks strictly after the last delivered key.
- **Range reads (C3).** `fn2-range-start` names the schema, lo and hi key regions, the source rows,
  cursor rows and head regions it may use, and an optional position field and limit;
  `fn2-range-step` is one bounded step answering `:entry` (the entry's rows at the range's OUT, read
  under its owner, valid until the next step), `:end`, `:more`, `:miss` or a refusal. Sources are
  the schema's overlays (active or frozen) and live runs, each with one decoded head; the step
  advances the sources that need it, delivers the least head (equal keys: the newest source, an
  overlay over any run, a greater run identifier over a smaller), and makes the delivered key's
  successor the query. Its meaning is that resume key plus the schema's version
  (`fn2-run-version`): when the version moved every source is found again strictly after the
  resume key; when an overlay took an insert its source is located again. A stream read stops at
  the first entry whose position exceeds the limit (position is monotone in key order within one
  group or principal). It never holds an old manifest or a physical traversal state as its meaning.
- **The read contract (UC §12 decision 2)**, `fn2-read-plan (strength p fallback cov append)` →
  `(mv outcome position limit)`; coverage is the active overlay's COV (`fn2-ov-cover`, monotone).
  Every read names its strength: `exactly-at p` (needs
  retained version state or snapshot plus replay; unavailable history is a gap) or `at-least p` (a
  threshold read on coverage). Fallbacks are `wait`, `stale-ok` and `catch-up` (the projection's
  maintenance state at `cov` advanced over `(cov, p]`), which replaces `select` as the general
  fallback. Every outcome returns its position.
- **Inbox (INBOX §4).** Streams are per-stream indexes keyed so that position is monotone in key
  order (overview by (group, number); `addr` by (principal, position)); `Seek(stream, after = p)` is
  the cursor's positioned entry (C3). The `edge-policy`, registration and read-state folds and the
  optional `inbox` fold with its coverage declaration are C4; the select-versus-materialize
  equivalence is the CONSUMER checker's differential check.

## 7. Interim choices (each replaced, never kept beside its replacement)

- **C-KEY-OCTETS.** An octet key field is at most `*fn2-run-key-octets-max*` = 512 bytes, so one key
  comparison (A's `fn2-pool-compare` over the common prefix, then the shorter first) stays inside a
  run's 4096-byte quantum. Message-IDs are at most 250.
- **C-OWNER.** C's pages are pool workspaces owned by C's engine owner. The generated encoder takes
  one owner for destination and payload sources, so octet values are copied into C-owned storage at
  admission (the overlay) before they are encoded.

- **C-RUNTIME-PRECONDITIONS (proof cost).** Every per-schema function `defrunschema` generates
  is a thin straight line over the schema's codec; its preconditions (writer row, restart range,
  field ranges, phase, schema, level) are checked at run time by one generic function proved once
  (`fn2-run-add-check`), and its success or failure is committed by another (`fn2-run-add-commit`).
  A first version proved the whole append's arithmetic per schema: 8 minutes and a failed guard.
  The split makes each schema cost about one second of proof.

- **C-ASSEMBLY (replaces C-GLUE-UNVERIFIED).** The per-schema build and lookup glue that C1b'
  admitted with `:verify-guards nil` is deleted: there is no per-schema glue. The run assembly
  generates one layout dispatcher at the assembly point (as A's machine dispatch is generated) and
  the append, seek, build and lookup are written once over it and guard-verified there. The proof
  cost moved from per schema to per assembly and fell. Measured on the laptop under load: the
  append (split into a pure readiness check and a straight-line write) 2 s, the page seek 0.5 s,
  the build 0.2 s, the lookup 1.4 s (the lookup step, split into its three phases, each
  guard-verified on its own, went from 355 s unsplit to 0.13 s); the whole assembly is about 4 s
  with the unit's 2 schemas and 5.6 s with 9. A schema's expansion is now its
  three deflayouts and its key order. The owed row `fn2-run-glue-verified` records the
  certify-time check: every assembled schema's build and lookup path (the generic entry points,
  the dispatcher, its codecs and key order, every function its declaration generated, and any
  per-schema glue by the old names) must be `:common-lisp-compliant`, or `fn2-run-assemble` fails
  naming the schema and the function.
- **C-ONE-ASSEMBLY (done with C-S1).** A world holds one assembly: the dispatcher and the generic
  functions are defined once. The production schemas are assembled in `runs-served.lisp` (with the
  identity decision) and `range-served.lisp` (the range reads); the node's assembly includes them
  through `machines-c.lisp`, and every C unit includes them through `tests/runs-assembly.lisp`. The
  run units' fixture schemas (`fn2-rt-num`, `fn2-rt-mid`) are deleted: their tests run over the
  overview schema (numeric key) and the identity schema (octet key), whose keystone teeth they
  supply.
- **C-ASSEMBLY-THEORY.** Each assembly (`fn2-run-assemble`, `fn2-identity-assemble`) expands inside
  an `encapsulate` with one local theory (the rows accessors of the pool, fields, digests and
  checker tables folded, as in runs.lisp), so its proofs do not depend on the including world's
  theory: the identity unit's world first broke proofs the runs unit's world had passed. A phase
  that reads a cursor row and calls a helper proves its shape lemma with the row accessors folded
  (unfolded, two such lemmas took 115 s and 135 s). Inside the generated guard proofs, a stobj's `-rows` accessor is disabled
  exactly where a callee has changed that stobj (the shape lemmas are stated over `-rows`) and left
  enabled where an element's type is read from the recognizer; disabling it everywhere loses the
  element typing and sends the prover into inductions.
- **C-OVERLAY-SORTED (FILTERS-2026 item 3 not adopted, measured alternative).** The active overlay
  is a bounded resident sorted index over an arena, so membership in it is an exact binary search
  over at most its index capacity. A filter in front of it would save decodes no measurement has
  shown to matter; InfiniFilter's two properties (growth without rebuild, deletion) answer needs
  this overlay does not have: it is bounded and sealed when full, and a removal from a sorted index
  is exact, so deleting a non-member cannot arise. Revisit only with a measurement of overlay probe
  cost against a filter.
- **C-PAGE-FILL.** A writer's fill limit (bytes of header, entries and directory) is a page-fill
  parameter, like a block size; the encoded page stays 64 KiB. Tests use small fills to reach many
  pages and levels with few entries.
- **C-CACHE.** The verified-page cache is direct mapped by physical unit and keyed by the exact
  (unit, allocation counter) pair, so a reused unit never answers for an old allocation. A page
  enters only after B's checker accepted it under its parent-held hash (or after its own seal). A
  lookup that needs an absent page stops with `:miss` and names the reference; its caller (the
  sealer or reader machine, C1c/C3) loads, verifies and installs it, then steps again.
- **C-FILTER-ONE-PAGE.** A run's filter is one page: at most `*fn2-ribbon-keys-max*` = 61,472
  keys (`:filter-capacity` past it). Overlay seals are far below it; runs larger than one page
  come from compaction (C5), which partitions the filter by hash (one page per partition, a
  partition directory in the descriptor's FILTER- ref) when it first produces one.
- **C-FILTER-HASH.** The filter key is a 64-bit hash of the Message-ID octets: two 32-bit FNV-1a
  streams with bases derived from the run's seed, each finalized by MurmurHash3's fmix32 (32-bit
  products split so none exceeds 2^49); the start comes from the first word, the coefficient from
  both. Not cryptographic: a Message-ID aimed at a run's filter costs one extra run read, never a
  wrong answer (the decision still compares bytes), so an adversary buys read amplification only,
  which admission already charges.
- **C-FILTER-INSTALLED (interim until C1c).** Until the run descriptor and the manifest exist, a
  run's filter page is named in its `fn2-run-installed` row (FUNIT, FCOUNTER) and cached after its
  own seal, as run pages are; C1c moves it to the descriptor's FILTER- ref with its parent-held hash.
- **C-IDENTITY-STALE.** Records are linearized by refusal, not by locks: `:stale` when the bucket
  stamp or the identity version moved since the decision started (§4). Measured on scenario M3
  (three decisions in flight, a seal one tick in twelve, six Message-IDs): about 45 stale records
  per 30 offers, so a retry is common under that contention; production seals are far rarer and D's
  reservation removes same-Message-ID races. Revisit with D's measurement under the concrete
  profile.
- **C-RANGE-KEYS.** Range reads take schemas whose key fields are all integers (`fn2-range-keys-ok`,
  generated at assembly; `:key-kind` otherwise): the resume point is the delivered key's successor
  (its last field plus one), which needs no stored octets. Every ordered schema of C3 is such.
- **C-RANGE-NEWEST.** Equal keys in two sources deliver once, newest winning. For a `:unique`
  schema that happens only while an overlay is being sealed into its run (the same entry twice);
  a `:latest` schema's newer row replaces an older one. In the overlay an equal key replaces the
  entry for a `:latest` schema (`fn2-ov-reput`: the new entry is encoded at the arena's fill and its
  index row repointed; the old bytes stay until the overlay is sealed, so the arena bounds
  replacements too) and is refused `:duplicate` otherwise (C4a).
- **C-POSITION-SEEK.** `Seek(stream, after = p)` over overview is a bisection over the number:
  each probe is a range read of one entry from `(group, mid)`, narrowing on its position; the
  answer is the number from which a read delivers exactly the entries after `p` (one past the last
  entry at or before `p`). Cost: about log2(range) probes of one descent each, no format change.
  The alternative, a position fence in index entries (a second order searched over the same
  pages), is a format change taken only if consumer seeks measure as hot; `addr` seeks by its key.
- **C-RANGE-ASSEMBLY.** The range reads are generated by their own macro in their own book
  (`range-served.lisp`, including `runs-served.lisp`), so neither assembly book nears the minute
  (20.6 s and 25.5 s on the laptop under load).
- **C-SUCCESSOR (C-S3).** Every engine write of a transaction goes through its batch's private
  overlays (phase `:private`, the overlay's BATCH column) until B publishes the batch: publication
  freezes every private overlay of the batch, of every schema, in one step (`:frozen`, readable,
  covering the batch's last commit position), and moves the bucket stamp of every identity fact
  bound to it, so a decision in flight around the publication refuses `:stale`. A transaction's
  writes are its write slots (§8 item 8): declared at `:prepare`, resolved against the installed
  runs, staged against the tip and bound in its `:ready` arm. The tip of a key is the overlay of its
  schema (private, published or active) taken last that holds it: overlays carry SEQ, the order
  they were taken in (an engine counter set when a spare becomes a batch's), which is batch order,
  and the range reads resolve equal keys between overlays by it too. A fact's octets are copied
  into the arena at bind through the engine's one bind scratch (4 KiB, one slot's octets at a time;
  byte by byte until A-S8's `fn2-pool-copy-across` lands). Room: a transaction's rows of one
  schema must fit one empty overlay together (else `:capacity`), so stage holds one spare per
  schema the transaction writes and bind takes the batch's newest private overlay with room or a
  spare; `:full` is backpressure. Until C1c's sealer seals frozen overlays into runs, the overlays
  accumulate: capacity is overlay rows times arena entries, its exhaustion backpressure at stage.
  Built against the proposal, with these differences (each a decision, sent to main with the
  READY): (1) **C-STRIPE**: W = `*fn2-succ-slots*` = 16 is a format constant, not a profile key,
  because a transaction's field-row stripe (1024 rows: 16 slot blocks of 48 rows, then the
  identity decision's 256) sizes B's `fn2-fields` table (`fn2-b-field-rows`), and a
  profile-dependent stride would put C's key into B's book; 16 slots hold a POST cross-posted to
  five groups with two addressees. (2) `fn2-successor-out` returns `(mv code value)`, never a bare
  value (assert, never absorb): `:state` unless staged, bound or published, `:kind` for a record
  slot or an octet field. (3) `:event` is an insert's integer field or a record slot's article (arg 0;
  S-ARTICLE-ID: the article identifier is the member's commit position), never a fold's arg (a fold step must know
  its args at stage); `:out` never feeds a fold's key arg (resolve must read the key) and never
  reads a record slot. (4) A `:unique` insert is checked for a duplicate at stage only when its
  key args are all `:value`; a key with an `:out` or `:event` arg (overview's number, `addr`'s
  position) is fresh by construction and bind's insert refuses a duplicate as an invariant
  failure. (5) A decision whose fact is bound is `:held` (the decision phases `:staged :bound
  :published` are gone): offers are refused until the transaction's release. (6) The record
  slot's bind copies the decision's octets into the scratch and encodes from the slot's own rows,
  leaving the decision's offer rows as they are: C-S2 repointed them at the scratch, so a
  transaction whose batch was dropped and that bound again would have encoded whatever the
  scratch then held. (7) A fold's assigned arg is declared on the event (`:assign ((number (+
  high 1)))`, C4a's DSL) and gets its own keystone, NAME-ASSIGN-ADEQUATE-KIND. Cost bases: resolve
  4,096 pool reads per step; stage 4,096 bytes (one located entry per overlay of each slot's
  schema; fold rows are tens of bytes); bind 8,192 bytes (octet copies of at most 4 KiB per slot
  and the encoded rows).
- **C-FOLD-UNCHANGED (E.P1, 2026-10-31).** A fold event's failed `:when` refuses the stage with
  `:refused` by default: the transaction must plan again, which §4a's admit race needs. An event
  may instead declare `:unless-when :unchanged`. Then the served and list steps both answer
  `:unchanged` and leave the row. Stage marks the slot (column `unchanged`), sizes it 0 and goes on,
  and bind skips it as it skips an empty slot. `(fn2-successor-applied tx i fn2-core) -> (mv code
  verdict)` reads `:applied` or `:unchanged` once staged (`:state` before, `:kind` for an insert or
  record slot). The cursor's `:ack` declares it, so an ack that lost its race to a later one answers
  `behind` instead of `accepted` (e-continuation.md E.P1) and the transaction still commits.
- **C-UNION-STAGE (§4a vocabulary, 2026-10-31).** An insert into a `:union` schema reads its key at
  the tip, as a `:unique` one does. Found with the same payload, it is already present: stage answers
  `:ok`, the slot binds nothing, and `fn2-successor-applied` is unavailable for inserts (`:kind`).
  Found with another payload, it is `:inconsistent`. A `:union` schema's value fields are integers
  (defrunschema refuses octets and digests there), so stage compares the payload whole, row by row.
  Each staged slot's block row 44 (`*fn2-succ-fresh*`) holds 1 when fresh and 0 when it binds nothing.
  The arg source `(:new K)` reads it from an earlier slot K, so a fold counts only fresh facts.
- **C-SUCCESSOR-BOOK.** The successor (C-S2, now C-S3) is books of its own, apart from
  `machines-c.lisp` (the decision, C-S1): together they made one book of 58.8 s on forge. C-S3 is
  three books in a chain along its phases, `machines-c-successor.lisp` (tables, the `:prepare`
  calls, resolve), `machines-c-stage.lisp` (stage, out) and `machines-c-bind.lisp` (bind, release,
  publish, drop, the defcosts and the core wrappers), the last included by `assembly-index`: as
  one book it certified in 197 s on forge, 115 s of it one lemma no guard needed (deleted).
  The core wrappers are materialized the same way, in two books: `assembly-callbacks-c-prepare`
  (the identity decisions, put, arg, arg-octets, arg-octets-late, resolve) and
  `assembly-callbacks-c-commit` (stage, out, fill-octets, bind, release, publish, drop). Then
  `assembly-callbacks-c` holds the group directory and the sealer. With C-S3a's two wrappers, the
  one book read 69.4 s on forge: each wrapper is about 6.5-7 s, two preservation lemmas over
  fn2-core-wfp.
- **C-SHAPE-READS.** A helper's shape lemma (type, wfp and rows of every stobj it returns) folds
  the row reads whose values only feed run-time checks and callee arguments (`fn2-fields-ref-*`,
  the decision's owner triple, the engine's scratch row, the stage's stamp and version reads):
  the preservation lemmas of the writes need only the written index. Unfolded, every read became
  a case split: `fn2-idc-rehome`'s lemma took 375,056 prover steps and 14.4 s on the laptop (17.8 s
  on forge), folded 0.3 s; stage 3.9 s to 0.4 s; bind 4.4 s to 1.5 s. A read whose value is a later
  write's index (the decision's QBASE) stays unfolded: its type comes from the recognizer. The
  1.25 s once measured for the same lemma came from a world built by `ld` of the books' sources, whose
  top-level `local` theory events stay in force; a certified world drops them, so time a lemma in a
  world that includes the certified books.
- **C-MANIFEST-ENTRY.** The manifest schema (`runs-manifest.lisp`, `fn2-manifest` id 10, key
  (schema, run), `:latest`, pages `:manifest`) holds per live run its height, entry count, the
  root page's identity and parent-held hash and the filter page's (zero when it has none): twelve
  fields, the successor's bound for every assembled schema (`fn2-succ-schemas-fit`). The run
  descriptor's per-schema `MIN-`/`MAX-` fences and its page count are not in it: they differ in
  shape per schema and the root page holds the fences.
- **C-SEAL-ORDER.** An overlay is sealable when it is `:frozen` and no overlay of its schema that
  is `:frozen`, `:private` or `:active` has a smaller SEQ; of the sealable ones the least SEQ goes
  first. A newer frozen overlay sealed before an older private one would put newer rows into a
  run that the older overlay outranks. Run identifiers grow, so run order is SEQ order, and every
  overlay a reader still meets is newer than every run, which is what the readers' newest-wins
  rules assume.
- **C-SEAL-RESIDENT (interim until M2's cold leg).** The engine half names each page itself (a
  unit counter in the seal row; physical identity (unit, unit)) and installs every sealed page in
  the verified-page cache. The cache is direct mapped by unit, so a seal whose next unit's cache
  row is occupied refuses `:cache` (backpressure) and evicts nothing: served capacity is the
  cache's rows of pages until the cold leg reloads pages through the storage path.
- **C-ENGINE-OWNER (as built, C1c).** The engine's workspaces (overlay arenas, the bind scratch,
  the sealer's pages and hash workspace) are owned by the sealer machine's row:
  `*fn2-idc-owner-kind*` is `fn2-sealer`'s position in the machine registry (declared in
  `machines-c-sealer-kind.lisp`, after A's kinds and `fn2-commit`, before C's successor books),
  local slot 0, generation 1. The local slot, not the global id, because the owner constants are
  used before the index exists; the core events assert `*fn2-sealer-kind*` equals it.
- **C-SEALER-MACHINE (C1c).** `fn2-sealer` (capacity 1; phases `:sealing :stopped`) drives
  `fn2-seal-step` through the core wrapper `fn2-sealer-step` (defcost 4,096 bytes over the 16
  tables): `:more :retired :done` keep it runnable; `:idle` parks it on the D0 wait kind
  `:sealable`; `:full` and `:cache` stop the core by name (`:sealer-full`, `:sealer-cache`; C-SEAL-
  BACKPRESSURE); any other answer stops it as an invariant (`:sealer`). It is woken by the grant
  service's fifth source (main's ruling: a D0 wait and a grant, never a direct wake id): C attaches
  `fn2-sealer-ready` (the row parked on `:sealable` in `:sealing`, the seal row idle, an overlay
  sealable) and `fn2-sealer-grant` (clear the wait, wake the row) to the constrained pair together,
  proving its liveness constraint. Its tables (seal row, run build, seven writers and their
  restarts, Ribbon build and band) are C's core children; its field rows the sealer stripe of B's
  fields table (`*fn2-b-seal-field-rows*` = 1,280, just below the transactions' stripes, which are
  anchored at the table's end); its checker row 3 + `:large-upload-windows`. Genesis
  (`fn2-engine-genesis`: the group directory, then the seal row) runs in `fn2-init-engine`.
  Measured (tests/sealer-machine-unit): the tiny profile's genesis groups overlay is sealed into a
  three-entry run by the real executor, the overlay retired, the row parked again, the executor
  idle, and every group answers through the lookup's run leg.
- **C-SEAL-BACKPRESSURE (interim until M2's eviction gives a resource wake).** The sealer's
  wake (`fn2-seal-pending-p`: the seal row idle and an overlay sealable) covers only the empty
  case. A row parked on `:full` or `:cache` in the build or at install has pending-p false, so it
  was never woken: a silent stall. A row parked on `:full` at the pick has pending-p true, so it was
  re-granted every turn: a spin. Both were found writing the arm table for the machine-form
  redesign. Until a page workspace, a cache row or an installed-run row freed is a wake, they stop
  the core by name: `:sealer-full` (a pool class or the installed-run rows exhausted) or
  `:sealer-cache` (a direct-mapped cache row held by another page; no eviction before M2's cold
  leg). Assert, never absorb. Controls are in tests/sealer-machine-unit, one per case: no hash
  workspace slot at the pick, no page workspace in the build, both cache rows held, the one run
  row held. Each stops by its name, with the row :stopped and the overlay still frozen; the same
  small profile without the pressure seals as before.
- **C-SEAL-NO-ROW (interim until B5-4a).** A profile without the checker row 3 + windows (today
  every profile that does not set `:format-slots` to at least 4 + windows) stops the sealer's row
  at genesis: overlays then accumulate as before C1c (backpressure at stage). B5-4a sizes the
  format tables for the row in every profile and refuses a lower setting; this interim goes then.
- **C-DECISION-STRIPES (C-S1, C-S3).** The decision rows are the profile's `:t` (one per
  transaction) and share B's `fn2-fields` table: B's 128-row stripe per format slot from row 0,
  then one 1024-row stripe per transaction ending at the table's end (`fn2-b-field-rows` sizes the
  table for both). In a stripe: the successor's 16 write-slot blocks of 48 rows from +0 (each: the
  staged row at +0, the args as given at +12, evaluated at +24, the key's run row at +36), then
  the decision from +768: the offer at +0, its lower bound at +2, the decoded entry at +4, the run
  reader at +84.
  A decision's run cursor is the cursor row with its number. An offer refuses `:bounds` when the
  stripes would reach into B's.
- **C-LEVELS.** A build has at most `*fn2-run-max-levels*` = 6 levels, a format parameter: with
  64 KiB pages and index entries of at most about 350 bytes, six levels address over 10^13 pages.
  Exhaustion is the named refusal `:levels`.

## 8. Seam requests (sent to main with the exact form)

1. **B: hoist the digest-to-pool copy.** In `fn2/books/format-check.lisp`, after `fn2-fc-word-byte`:
   ```lisp
   (defun fn2-digest-store (left row slot gen off okind oslot ogen fn2-digests fn2-pool)
    (declare (xargs :stobjs (fn2-digests fn2-pool) :measure (nfix left)
     :guard (and (fn2-digest-rowp row fn2-digests) (fn2-pool-wfp fn2-pool)
                 (natp left) (<= left 32) (natp off))))
    (if (zp left) (mv :ok fn2-pool)
     (mv-let (code fn2-pool)
      (fn2-pool-write slot gen (+ off (- 32 left))
       (fn2-fc-word-byte (fn2-digest-word row (floor (- 32 left) 4) fn2-digests) (mod (- 32 left) 4))
       okind oslot ogen fn2-pool)
      (if (eq code :ok) (fn2-digest-store (- left 1) row slot gen off okind oslot ogen fn2-digests fn2-pool)
       (mv code fn2-pool)))))
   ```
   with its `fn2-pool-preserves` lemma; `fn2-commit-digest-copy` becomes a call with
   `*fn2-commit-kind*`. C calls `fn2-digest-store`; C writes no copy of its own.
2. **B: the commit batch carries C's pages and installs C's roots (GC2). Agreed form.** C prepares
   one C-owned 4 KiB workspace: offset 0 the encoded `fn2-format-run-replacement` body (at most
   167 B), from offset 256 N contiguous `fn2-format-dependency-entry` records (1 ≤ N ≤ 31), each a
   page write C already harvested `:ok` with its exact length. Admission
   `(fn2-commit-admit-runs schema slot gen body-len entry-bytes entry-count okind oslot ogen
   fn2-core) → (mv code batch fn2-core)` hands the workspace to the commit kind; `:exhausted`
   retries, `:admission` names a malformed member; refusal changes nothing. The batch's fence (or
   preflush) covers the listed writes. After its root swap only, B calls the constrained
   `(fn2-runs-install schema batch slot gen okind oslot ogen fn2-core) → (mv code fn2-core)` (C's
   amendment: the commit kind's owner triple for a read-only decode), which C attaches with
   `defattach` in its assembly book; the default refuses `:unregistered`; a non-`:ok` code leaves
   the batch uncertain (durable, uninstalled). An uncertain batch never calls the hook; recovery
   replays it. Runs over 31 pages list the rest through C-sealed `:dependency-manifest` pages named
   by one ordinary entry each; B5 recovery follows such an entry one level (C's second amendment).
3. **B: identifier namespaces.** Add `run stream position consumer version` to the `(:id NS)` list
   in `fn2-layout-kindp`.
4. **A: R6a1's `fn2-pool-compare`** (GC1). Landed at 09ad4a57f; C uses it.
5. **A: one word book.** `fn2/sim/prng.lisp` holds `fn2-u32`, `fn2-u32-mul` and `fn2-prng-mix32`
   (fmix32); C's `ribbon.lisp` needed the same in `books/` and has `fn2-ribbon-mul32` and
   `fn2-ribbon-mix`. Asked: hoist the three into a `fn2/books/` word book that `sim/prng.lisp`
   includes; C then calls them and deletes its copies.

6. **C-S1 (to D, served).** `(fn2-identity-offer d mslot mgen moff mlen dslot dgen doff okind
   oslot ogen fn2-core) → (mv code fn2-core)` (decision row `d` idle or done; the octets readable
   under the owner for the decision's life), `(fn2-identity-step d budget fn2-core) → (mv answer
   fn2-core)` (`:more`, `:stored`, `:duplicate`, `:evidence`, `:conflict`; `:miss` cannot arise
   before C1c installs runs in the served core; budget ≤ 4,096), `(fn2-identity-release d
   fn2-core) → (mv code fn2-core)`; defcosts in `machines-c.lisp`.

7. **C-S2 (to D and B; replaced by C-S3, item 8; kept as the record of what D and B were sent).** A fact becomes visible only through its batch.
   D's transaction learns its batch at `:ready` (B-S2 admission), and nothing may fail after
   admission, so the stage is split in two calls made in the same `:ready` arm:
   `(fn2-identity-stage d fn2-core) → (mv code fn2-core)` immediately before
   `fn2-commit-admit-txn` (`:ok`: validated against the published state, room held; `:stale`:
   decide again under the claim; `:duplicate` / `:evidence`: nothing to record;
   `:identity-conflict-bound`; `:full`: backpressure; `:capacity`: the entry exceeds an arena), and
   `(fn2-identity-bind d batch article binding principal fn2-core) → (mv code fn2-core)` right after
   admission `:ok` (the fact enters batch's private overlay; a non-`:ok` is an invariant failure).
   B calls `(fn2-identity-publish batch fn2-core)` after the root swap and before any member result
   (the batch's private overlays freeze, readable at once; the stamps of their facts' buckets move,
   so decisions in flight around them refuse `:stale`), and `(fn2-identity-drop batch fn2-core)`
   for a batch that ends refused (its private overlays' arenas are released, its decisions are done
   again with nothing recorded). An uncertain batch calls neither; recovery resolves it. Release of
   a staged or bound decision is refused `:state`.

8. **C-S3 (to D and B; proposed 2026-10-30; built, with the differences listed under §7
   C-SUCCESSOR). Every engine
   write of a transaction goes through its batch's private successor, so a POST's group-count
   accept, its overview row, its article row, its `addr` entries and its operation outcome become
   readable in the one step that publishes its identity fact.** C-S2 becomes the identity case of
   this seam; its stage and bind are replaced (no twin), its offer, step and release stay.

   *Why it has this shape.* A fold write reads the key's newest row and writes the step's result
   (C4a's real step). Two POSTs to one group in one batch, or in a batch and its follower, must
   chain: the second reads the first's unpublished row. Group numbers must be assigned in commit
   order (INBOX §4.1: position is monotone in key order within a group, which is what makes the
   positioned seek exact), so the number is assigned at admission time from the tip, never at
   `:prepare`. The tip a staged write reads is: the private overlays of every unpublished batch,
   newest first, then the published overlays, newest first, then the installed runs. The arm that
   stages, admits and binds is one transition, so nothing else stages or binds between a
   transaction's stage and its bind.

   *Slots.* Transaction row `t` (= its decision row, as C-S2) owns `W` write slots
   (`fn2-succ-slots`, a C core child, `T x W` rows; `W` is the profile's `:successor-slots`,
   default 8; a transaction needing more is refused at `:prepare` by D's word for it). Calls made
   before `:ready` (at `:prepare`):
   - `(fn2-successor-put t i sid kind fn2-core) -> (mv code fn2-core)`: slot `i < W` of `t` writes
     schema `sid` by `kind`: a fold event kind of `sid` (`:accept`, `:withdraw`, `:ack`,
     `:charge`, ...), `:insert` (a whole entry of a `:unique` or `:latest` schema: key fields then
     value fields), or `:record` (the identity fact of decision `t`; `sid` = identity; at most one
     per transaction). `:ok`, `:bounds`, `:schema` (not registered), `:kind` (not an event of
     that fold, or `:insert` on a fold), `:state` (slot staged or bound).
   - `(fn2-successor-arg t i j src value fn2-core) -> (mv code fn2-core)`: argument `j` of slot
     `i` (the event's args in declaration order; for `:insert` the entry's fields; for `:record`
     the fact's `article` then `principal`) comes from `src`:
     `:value` (the integer `value`), `:event` (the member's commit position, bound at bind;
     `value` ignored), or `:out` (`value` = `k * 2^8 + f`, a packed handle: field `f` of slot
     `k < i`'s row after its step; `f` is the generated `*NAME-FIELD-F*` index). An octet field
     (the overview line) is `(fn2-successor-arg-octets t i j slot gen off len okind oslot ogen
     fn2-core) -> (mv code fn2-core)`: readable under that owner until bind, which copies it into
     the arena (as C-S2's bind copies the Message-ID). An argument the fold declares `:assign`
     (group counts' `:accept number`, assigned `(+ high 1)` from the tip row) takes no call; the
     logged event carries the assigned value, so the list fold is unchanged.
   - `(fn2-successor-resolve t budget fn2-core) -> (mv answer fn2-core)`: reads, for every slot
     whose key is fully `:value`, the key's newest row in the installed runs (bounded, resumable:
     `:more`, `:miss` with the page as C-S1, `:ok`), and notes the schema's run version. Until C1c
     installs runs in the served core it answers `:ok` in one call.

   In the `:ready` arm, in this order, in one transition:
   - `(fn2-identity-stage t fn2-core)` is replaced by `(fn2-successor-stage t fn2-core) -> (mv
     code i fn2-core)`: every slot in order against the tip (a key found in an overlay is newer
     than any run; otherwise the resolved row, if the schema's run version has not moved, else
     `:stale`, and D resolves again), then the step (assigned args computed, `:out` args read),
     then room held for every slot (an overlay of the slot's schema already private to the open
     batch, or a held spare). `code`: `:ok`; `:stale` (resolve again; for `:record` also decide
     again, as C-S2); `:refused` (slot `i`'s fold test failed: an ack behind the cursor, a refund
     over the charge; D's word for that operation); `:range` (a field would leave its width);
     `:duplicate` (a `:unique` key held at the tip, or the identity fact's C-S2 answer),
     `:evidence`, `:identity-conflict-bound` (the `:record` slot, as C-S2); `:full` (no room now:
     backpressure, stay `:ready`); `:capacity` (an entry exceeds an arena). `i` names the slot.
   - `(fn2-successor-out t i f fn2-core) -> value`: field `f` of slot `i`'s row after its staged
     step (D reads the assigned group number here and writes the membership record into its
     member workspace before admission).
   - `(fn2-commit-admit-txn ...)` (B-S2), unchanged, except that it returns the member's commit
     position (below).
   - `(fn2-identity-bind t batch article binding principal fn2-core)` is replaced by
     `(fn2-successor-bind t batch event fn2-core) -> (mv code fn2-core)` right after admission
     `:ok`: every slot's row (the staged step, `:event` args = `event`) enters `batch`'s private
     overlay of its schema; a `:latest` key `batch` already holds is replaced in place. A non-`:ok`
     is an invariant failure. The identity fact's `binding` is `event`.
   - `(fn2-successor-release t fn2-core) -> (mv code fn2-core)` at the outcome (frees the slots
     and the decision; `:state` while bound to an unresolved batch), replacing
     `fn2-identity-release`.

   *Publication.* `fn2-identity-publish` and `fn2-identity-drop` are renamed
   `(fn2-successor-publish batch fn2-core)` and `(fn2-successor-drop batch fn2-core)`, same
   arguments, same call sites in B's commit kind (after the root swap, before any member result;
   for a refused batch). Publish freezes every private overlay of `batch`, of every schema, in
   one step, sets their coverage to the batch's last event, and moves the identity stamps; drop
   releases them and returns `batch`'s slots and decisions to staged-before-admission state with
   nothing recorded. Readers (range reads, the identity decision) see published overlays only.
   Equal keys in two published overlays resolve to the later one (overlays carry the order they
   were taken in, which is batch order; the sealer seals them in that order, so run identifiers
   keep it).

   *Asked of B with this seam.* (a) `fn2-commit-admit-txn` returns `(mv code batch event
   fn2-core)`, `event` the member's commit position `(domain 0, sequence)`, assigned in admission
   order and increasing across batches (INBOX §4.1; the overview row's `position` and the `addr`
   key need it before the batch seals). (b) A batch whose predecessor is dropped is dropped, and
   drops come in batch order (the follower's successor already names the leader's proposed root;
   C's tip chains the same way). (c) An uncertain batch's private overlays stay in the tip; a
   batch chained on it resolves after it (recovery publishes or drops in order).

   *What D's arms become.* `:prepare`: the article's slots (`:record`; `:insert` article row;
   per group `:accept` and an `:insert` overview row whose `number` is `(:out k high)` of that
   group's accept and whose `position` is `:event`; `:insert` `addr` per addressee with `:event`;
   `:insert` operation outcome), then `fn2-successor-resolve` to `:ok`. `:ready`: stage, out,
   pack, admit, bind. Accept order equals commit order by construction; a cross-posted article
   holds one accept per group.

   Not in this seam: read-state, registration, edge-policy and inbox folds (C4b) are written by
   E's ack and registration transactions through the same calls.


9. **S-GROUP (to D, ruled 2026-10-30; built).** The group directory is the schema `fn2-groups`
   (id 8, `ordered.lisp`): exact name octets (at most 250) to `(:id group)`, `:latest`. Genesis:
   `(fn2-groups-genesis profile fn2-core) -> (mv code fn2-core)`, called by `fn2-init-executor`
   right after the core init (a refusal stops the core, reason `:engine-genesis`), puts the profile's
   `:groups` list, `((NAME . GROUP) ...)` with NAME a string of 1-250 characters and GROUP a positive
   u60, into one published overlay of the directory (an engine arena; SEQ the engine's next;
   coverage 0); a malformed list is `:groups`, a repeated name `:duplicate`, more names than an
   overlay holds `:capacity`. E owns the configuration later; the profile key is the interim.
   Lookup, with one difference from the request (the transaction row `tx` first: a lookup is
   resumable and its continuation, query rows and cursor are the transaction's):
   `(fn2-group-lookup tx slot gen off len okind oslot ogen budget fn2-core) -> (mv code group
   fn2-core)`, the name the LEN octets at [OFF, OFF+LEN) of SLOT/GEN under the owner, the same
   arguments on every call; `:ok` with the group, `:absent` (441), `:more` (call again: one source
   per call, an overlay search or one run step of at most BUDGET ≤ 4,096 reads), `:miss` (a run page
   to load, as C-S1), `:bounds`, `:state` (the transaction's identity decision is in flight or
   resolve is inside a run descent: look groups up before offering the Message-ID, or after its
   decision is done, and before resolve). Sources newest first: published overlays by SEQ, then live
   runs by identifier; a run version that moves during the run leg restarts the lookup. The generic
   exact lookup under it (`fn2-xl-step`, `machines-c-groups.lisp`) serves any schema's exact key.
10. **S-OUTCOME (to D, ruled 2026-10-30; built).** `fn2-outcome` (id 9): key (principal,
   operation), value (request digest, outcome u16, event), `:unique`: an `:insert` slot whose key
   args are `:value` is checked at stage against the tip and the runs (`:duplicate`); the digest by
   `fn2-successor-arg-octets`, the event by `:event`. Its unit found a C-S3 defect, fixed with it: an
   octet arg's row carried value 0, which the codec refuses for a digest field (`:unknown-tag` at
   bind; a digest's row carries the presence value 1), so every `:insert` with a digest (the article
   row's source, this request digest) failed at bind; `fn2-succ-arg-octets` now writes 1 for a digest
   field (a field whose value check refuses length 0).
11. **S-ARTICLE-ID (to D, ruled 2026-10-30).** No allocator: the article identifier is the member's
   commit position. The article row's key takes it by `:event` (an insert's integer field; built
   in C-S3), and so does the identity record's article (arg 0 of the `:record` slot: added with
   this seam; its principal stays `:value`); bind writes the same `event` into both.
12. **C-S3a, a late octet argument (to D, for D5 2/n's overview line; built).** The overview
   line carries the Xref suffix, whose numbers are assigned at stage, so its octets exist only
   after stage. `(fn2-successor-arg-octets-late tx i j max fn2-core) -> (mv code fn2-core)` at
   `:prepare` declares octet arg J of insert slot I with at most MAX octets: `:kind` for a key
   field (stage and resolve read keys), a digest or an integer field, or a slot that is not an
   `:insert`; `:bounds` for MAX past the field's octet bound. Stage counts the entry at MAX, so the
   room it holds covers any fill. `(fn2-successor-fill-octets tx i j slot gen off len okind oslot
   ogen fn2-core) -> (mv code fn2-core)` between `fn2-successor-stage` and `fn2-successor-bind`
   gives the octets by reference: `:state` unless the transaction is staged and not bound,
   `:kind` unless J is a late arg of the slot, `:bounds` for LEN past MAX, `:owner` for an owner
   other than the slot's other octet args'. The transaction stays staged. Bind refuses `:state`,
   binding nothing, while a late arg is unfilled since the last stage: every stage (a re-stage,
   or the stage after a dropped batch) recopies the entry from the raw rows, which hold only the
   bound, so the fill follows the last stage. Columns LATE and FILLED of `fn2-succ-slots`; unit
   `fn2/tests/identity-core-unit.lisp` (`fn2-icu-late`: every refusal above, a re-stage that needs
   the fill again, and the published overview overlay's arena holding the 20 filled octets and
   none of the source's octets past them).
13. **C-S4, served reads for query cursor rows (D writes it on C's ruling, 2026-10-30; first half
   built in `fn2/books/machines-c-read.lisp`, C and B reading the diff).** Read rows are
   `(fn2-b-read-rows profile)` = `:x` when the profile sets `:reading`, else 0 (machines-b, beside
   `*fn2-b-read-stride*` = 1,024). Children: `fn2-reads` (R rows: the op, the query owner, the
   delivered entry), `fn2-ranges` (R), `fn2-range-sources` (8R), `fn2-seeks` (R); `fn2-succ-txns`
   grows to t + R (read row x's exact lookup is row t + x, served by `fn2-xl-step` unchanged) and
   `fn2-run-cursors` to t + 9R (lookup cursor t + x, source cursors t + R + 8x + i), paths with it.
   (a) The stripe of row x is `rows − 1024·t − *fn2-b-seal-field-rows* − 1024·(x+1)`
   (`*fn2-read-stride*` = 952 used of it: lo key +0, hi key +80, eight source heads from +160, the
   lookup decoding into source 0's); `fn2-b-field-rows` and `fn2-idc-profilep` gain `1024·R`.
   (b) Every range or seek step re-finds its sources from the resume key when the schema's run
   version moved or an overlay source's row no longer holds the taking it located (phase active or
   frozen, schema, SEQ: a SEQ is issued once per taking); a delivered entry is read only under the
   run version it was delivered under, else `:stale`. (c) `fn2-read-frontier (fn2-core) -> (mv
   code position)`, a pure read of `fn2-successor-published` (C's `:published`, 93ede3b02); the view a
   connection pins (`fn2-cursor-view-pinned` turns live with the cursor). (d) LIST's ordered scan,
   `fn2-read-scan x sid wslot wgen wk ws wg` / `fn2-read-scan-next x budget`: the range read's
   sources and merge over any schema, octet keys included, from the schema's least key; its resume
   key is the delivered key itself, copied into the caller's workspace (WSLOT/WGEN under WK WS WG, the
   query owner) and skipped once by the next step, so a re-find after a seal neither repeats nor loses
   a key; never an octet-keyed range. (e) The identity read, `fn2-read-identity x mslot mgen moff mlen
   okind oslot ogen budget -> (mv code article candidates)`: the decision path's lower query (the
   Message-ID, an empty content) and its classification (`fn2-id-classify`) over the same merge, the
   whole block of the Message-ID: `:found` with the accepted fact's article, else `:evidence`, else
   `:absent`, and the candidates (conflict facts met at this cut). That is the selection and evidence
   status of IDENTITY-ACROSS-PEERS ruling 8 over this engine; availability, coverage and authorization
   wait on §4a's records and S-ARTICLE-LOCATION (owed row `fn2-read-identity-typed-exact`,
   owed-cursor.lisp). Operations, each a defcost and a core wrapper
   (`fn2-read-core-events`): `fn2-read-key x region j value` (region `:lo`/`:hi`),
   `fn2-read-key-octets x j slot gen off len okind oslot ogen` (one owner per row until release, else
   `:owner`), `fn2-read-lookup x sid budget` (`:ok :absent :more :miss`), `fn2-read-range x sid pfield
   plimit`, `fn2-read-next x budget` (`:entry :end :more :miss`), `fn2-read-seek x sid lo hi p pfield`
   / `fn2-read-seek-step x budget -> (mv code answer)`, `fn2-read-value x f -> (mv code value)`,
   `fn2-read-octets x f from n dslot dgen doff dk ds dg -> (mv code copied left)`, `fn2-read-release x`,
   and the scan and identity read above. Unit: `tests/read-unit.lisp` (LIST across a seal of the
   group directory, an overview scan across a seal of the seeds' overlays, identity reads with and
   without conflict evidence).

14. **S-ARTICLE-LOCATION (to D and B, ruled 2026-10-31; lands with §4a's records).** `fn2-article`
   (id 2) gains the stored octets' location as one reference in the format's reference shape,
   `(fn2-format-prefix "LOCATION-" *fn2-format-ref*)`: `location-storage-domain`,
   `location-physical-unit`, `location-writer-epoch`, `location-allocation`, `location-page-kind`,
   `location-encoded-length`, `location-expected-hash`. That is one level, as for a run's manifest:
   - an article that fits one 64 KiB payload block names that `:raw-source` page;
   - a larger one names its `:source-manifest`, whose entries are the content-named blocks
     (B-HASH-ATTACHED).
   **Count bound: exactly one reference per article.** A multi-block article is named through its
   manifest, never by a list in the entry, so the entry's size does not grow with the article.
   The txn writes the field at bind from the accepted member's source reference (b-durability.md
   §11b S9): the `SOURCE-` reference of its `:article-acceptance` record, field for field, so the run
   entry and the durable record never disagree. Until D4 3/n the reference names the upload window's
   durable extent (B-S1); after it, the content-named block or the source manifest. B's
   `:promised-read` edge holds what the reference names while the entry names it.
   ARTICLE/HEAD/BODY (D6) read the field through `fn2-read-value` and hand it to B's
   `fn2-block-read` (§11b S10). A manifest takes one more read through the same op. C never reads the
   octets.
   Under `:latest` a withdrawal rewrites the whole entry, so its writer copies the location from the
   entry it read.

## 9. Keystones (defthm-owed, each with teeth)

| name | statement (real entry points) | teeth | quest |
|---|---|---|---|
| `NAME-page-roundtrip` (generated per schema) | for sorted, well-formed entries that fit one page (`fn2-run-page-inputp`), the real append, close, head and seal produce, and B's checker accepts under the parent-held hash, exactly the octets of `fn2-run-page-spec` (B's list codec for the headers and each entry, the restart directory, zero padding) | positive: 40 entries per test schema, inputs checked; negative: unsorted entries (refused `:order` part way) give a different image | C1 |
| `NAME-seek-lower-bound` (generated per schema) | the real page seek returns `(:found i)` or `(:absent i)` equal to `fn2-run-lower-bound-spec` over the spec key order | positive: queries before, inside, between, after and at restart boundaries, including empty octets and a query held by another owner; negative: the unsorted page disagrees with the spec | C1 |
| `NAME-run-lookup-exact` (generated per schema) | for at most 64 sorted well-formed entries and a fill at which every page holds two entries (`fn2-run-run-inputp`), a run built through the real build entry points and searched from its root through the real cursor steps answers `(:found entry)` exactly when an entry's key equals the query's, with that entry, and `(:absent nil)` otherwise (`fn2-run-key-lookup-spec`) | positive: present, between, before, after and empty-octet queries over multi-level runs of both test schemas; negative: unsorted entries make the conclusion false | C1b' |
| `fn2-exact-identity` (RELEASE-PLAN T9) | offers decided and recorded through the real decision and recording, sealed into runs every `split` offers, the offers' staging workspace released, then queries decided: each answer equals `fn2-id-answers-spec` (`:duplicate` iff recorded as the accepted content, `:evidence` iff recorded only as evidence, `:conflict` iff another content is, else `:stored`) | positive: the M3-shaped scenario (a conflict, a duplicate, five contents for one Message-ID against the bound of four; two queries answer `:evidence`) at splits 0, 4 and 1; negative: a node whose summary dropped the Message-ID octets answers `:stored` to the re-offer of m1 with another content, where the statement requires `:conflict` | C2b |
| `fn2-identity-binding-converges` (`:route`; its scope is one node's order-independence, and it is re-stated as `fn2-identity-union-order-free` with the §4a record) | two nodes whose offers record the same facts with the same states (each Message-ID's first-arriving content accepted, the rest evidence; any order otherwise, duplication or sealing schedule, within the bound) hold equal Bindings with states, read back by the real scan of every installed run, and each is `fn2-id-state-binding-spec`'s; the IDENTITY checker's `:binding` event compares states too (departure 2) | positive: one fact set in two orders keeping first arrivals (one with a duplicate) under splits 2 and 3, equal to each other and to the spec; negative: the review's (m,a),(m,b) against (m,b),(m,a), equal key sets but different Bindings; a node that refuses a conflict and records nothing differs from the spec | C2b, strengthened after C-S3 ||
| `fn2-ribbon-no-false-negative` | a filter built through the real start, add, finish and work from at most 256 keys seals, passes B's checker under its parent-held hash, and its probe answers `:absent` only for a query that is no key (`fn2-ribbon-answers-sound`) | positive: 200 keys and 56 others probed, every key `:maybe`, at least 50 others `:absent`; negative: a filter built without key 17 answers `:absent` to it | C2c |
| `fn2-ribbon-mutation-refused` | any one-byte change (offset in the page, nonzero XOR) of a sealed filter page is refused by B's checker by name | positive: changes in B's header, the filter header, Z and the padding refused while the unchanged page is accepted; negative: a zero change is accepted | C2c |
| `fn2-identity-linearizable` | for every seed and at most 64 offers, the M3 scenario's trace (interleaved decisions, records, seals with filters, bodies released, then every pair queried and the Binding scanned) is accepted by the independent IDENTITY checker | positive: 40 seeds pass with races exercised (1,808 stale records) and 722 seals; negative: the same schedules with the stamp and version checks defeated are refused by name (37 of 40) | C2d |
| `fn2-range-read-exact` | a range read through the real steps over runs and an overlay (at most six sources of 48 sorted entries, any budget, the overlay sealed into a run after any delivery) delivers exactly `fn2-range-spec`: the union, newest entry per key, from lo to hi, cut at the position limit | positive: seven windows (whole group, inner window, position limit, empty, the other group, budget 1 with a seal after the third and after the first delivery), non-vacuous (15 rows, the overlay's row for 4); negative: an unsorted run reads back otherwise | C3 |
| `fn2-range-seek-position` | within one stream whose positions grow with the number, the seek over runs and an overlay answers `fn2-range-seek-spec`: one past the last entry at or before `p` | positive: group 1 at p = 0, 35, 40, 41, 150 (0 4 5 5 16) and group 2, equal to the spec; negative: positions that do not grow with the number mislead it | C3b |
| `NAME-summary-adequate-KIND` (generated per fold and event kind; 6 rows) | for a state of at most 8 rows (`NAME-fold-statep`), an event of that kind and at most 8 query keys, sealed or not: the rows written through the real insert observe through the real range read as the fold's state (`obs(σ s) = obs s`), and after the event applied by the real step (range read of its key, `fn2-fold-apply`, overlay replace) as the fold's step of it (`σ(δ(s,e)) = δ_Σ(σ s, e)`, observed at every query) | positive: an event on a held key and one on a fresh key or refused, sealed and in the overlay; negative (TRANSPORT §9 tooth 2): an engine whose step adds one to the first value field disagrees | C4a |
| `NAME-summary-cut` (generated per fold; 3 rows) | for at most 8 events, every cut k, sealed or not: `Fold(Summary_k, E_{k+1..n})` through the real engine observes as the whole list fold | positive: every cut of a six-event scenario, both placements (exhaustive in the tiny profile); negative: a summary that drops a row, and a summary step applied twice (or off by one, for the idempotent cursor); weak (tooth 1): a projection of the observation that is not step-closed, evaluated | C4a |
| `fn2-sealer-run-equals-overlay` | at most four published batches of at most 48 distinct well-formed rows of the groups schema, SEQs in batch order, a fill at which every page holds two entries: after the real `fn2-seal-step` is driven until idle, every lookup through the installed runs (newest first, the real cursor) answers as the overlays did, the newest batch holding the key (`fn2-sealer-spec`) | positive: three overlapping batches at fills 400 and 65,536, answers from each batch and two absent; negative: a sealer stopped before the last overlay; SEQs against batch order read the older rows | C1c |
| `fn2-manifest-replacement-atomic` (engine half) | for one nonempty batch of the groups or identity schema, the views (live runs, overlay phase) at every cut of the real sealer's steps are exactly the old runs with the overlay frozen, then the new run with the overlay free, never a third (`fn2-sealer-cuts-ok`); the device half (B5 recovery over the run-replacement member) owes the same of the recovered manifest | positive: 30 groups rows and 20 identity facts with their filter, at fill 400; negative: a run beside its still-published overlay, and neither | C1c |
| `fn2-select-materialize-equivalent` | for every policy assignment and materializer schedule, a consumer's observations equal the select-only reference | a materializer that skips an entry; a reader that trusts the fold above `cov` | C4 |
| `fn2-compaction-preserves-observations` | a compaction step preserves every supported read at every unexpired pin | a merge that drops a pinned version | C5 |
| `fn2-relocation-preserves-lease` | a relocation under a lease publishes the replacement before retiring the old placement and keeps the content identity | relocation that retires first | C5 |

Teeth are zero-argument evaluating functions in the unit books, run by `fn2-assert-owed-teeth`;
OWED.md is regenerated when the export is green.

## 10. Quest plan

| quest | contents | acceptance | waits on |
|---|---|---|---|
| C1a | `:schema` kind in declare.lisp (foundation commit, worktree, export green) | export PASS, unchanged counts plus zero | dev |
| C1b | runs-page, runs-schema; runs-unit with a numeric-key and an octet-key test schema | **done**: books under 60 s; sealed pages pass B's checker, a flipped byte is refused; seek agrees with the spec; the two page keystones' teeth | C1a |
| C1b' | runs.lisp: multi-page build, promotion, verified-page cache, resumable lookup cursor; `NAME-run-lookup-exact`; R6a1's compare in place of the interim | **done**: 3,000 entries at a 400-byte fill build 80 pages, height 4, and every query answers right; the teeth | C1b, R6a1 |
| C1c | sealer machine; run descriptor and manifest schema; run sealing through the commit batch (B's GC2 member); retirement through the allocator; the assembly dispatcher (C-GLUE-UNVERIFIED's remedy) | **engine half done** (`sealer.lisp`, `runs-manifest.lisp`, `sealer-unit`): both keystones' teeth, the first-overlay rule, an identity seal with its filter. Then the machine (`machines-c-sealer.lisp`), then the device half: tiny exhaustive death cuts over one run replacement: recovered manifest is old or new, never mixed | B's GC2 member (device half) |
| C2a | range scan through the cursor path; the generic overlay | **done**: scans and overlays agree with the list specification; both keystones' teeth | C1c first item |
| C2b | identity schema, the decision machine, the recording under the bound, the two keystones | **done**: the M3-shaped scenario pinned; both keystones' teeth | C2a |
| C2c | Ribbon per sealed run, the probe in the identity decision | **done**: no key ever `:absent`; 8.5 bits/key at 60,000 keys (8.75 at 2,000); false positives 0.375% (75 in 20,000) and 0.395% (790 in 200,000 at 60,000 keys) against 2^-8 = 0.39%; the M3-shaped scenario reads only the runs holding the Message-ID (an absent one reads none); both keystones' teeth | C2b |
| C2d | IDENTITY checker; scenario M3 (interleaved decisions, seals, bodies released); the stamp and version refusal | **done (engine leg)**: 200 seeds of 30 offers all accepted, 9,077 stale records, 3,607 seals; defeated checks refused on 188 of 200; 10,000 seeds in `sim-layer-c-sweep.lsp`. The device leg (run pages through the commit batch, recovery) waits on C1c and B's GC2 | C2c |
| C3a | metadata, overview and `addr` schemas; range reads with resume key and version; the read plan | **done**: the keystone's teeth; `addr` read after a position by key; an octet-keyed schema refused `:key-kind` | C2d |
| C3b | positioned seek (`fn2-seek-start`, `fn2-seek-step`, table `fn2-seeks`) | **done**: keystone fn2-range-seek-position's teeth; 10 probes over [0, 1000) | C3a |
| M2 | XOVER-shaped reads over cold sparse groups charging directory and overlap reads | needs the cold leg: pages loaded through the storage path (C1c) | C1c |
| C4a | fold declarations on the schema row, overlay replace, group counts, consumer cursor, principal charges, the adequacy and summary-cut keystones | the keystones' teeth (every cut of the tiny scenarios, sealed and not) | C2, C3 |
| C4b | registration, read-state, edge-policy, inbox folds; CONSUMER checker; `fn2-select-materialize-equivalent`; C-S3 (fold writes in D's transaction through the private successor) | the equivalence's teeth; D6/E reads | C4a |
| C5 | compaction with reservations and backpressure, relocation under a stalled lease | compaction under a stalled lease; compaction bytes per committed byte | C4, C1c |
| C6 | permanent exact-identity retention and reclamation tests; perfect hash measured against sorted search inside a sealed run | 10,000 seeds concrete (nightly row); the measurement table | C5 |

## 11. Certify times

Every C book under 60 s on the laptop (the one-minute rule); the table lives in
`build/coordinator/fn2/lanes/c-continuation.md`, refreshed after every quest.

## 12. Departures (numbered; each with its remedy and its state)

1. **The fold compiler ran in `:program` mode** (C4a, `runs-schema.lisp`'s `fn2-rf-*` and
   `fn2-defrunschema`, 43 functions), against the brief's and both layer docs' "no `:program`"
   (REVIEW-20261030 §1). Remedy: logic mode with `:verify-guards nil`, as every other generator
   in fn2/books (the generators run at macro time and are never served); the one function whose
   termination needed a change is `fn2-rf-test`, which now answers nil on an atom (its callers pass
   only tests `fn2-rf-testp` accepted). State: applied; no `:program` function is left in fn2.
2. **`fn2-identity-binding-converges` was weaker than its name** (REVIEW-20261030 §1): it compared
   key sets, so two nodes offered (m,a),(m,b) in opposite orders "converged" while answering one
   query `:duplicate` on one and `:evidence` on the other; the IDENTITY checker's `:binding` event
   dropped the state the same way. Remedy: the Binding image carries each fact's state, the
   premise is equality of the recorded states (`fn2-id-state-binding-spec`, sensitive to first
   arrival), the conclusion adds that the image is that spec, and the checker's `:binding` facts
   are (mid c state) with a control refusing exchanged states. Which content wins when nodes saw
   different first arrivals is the served choice: first arrival, stated per offer sequence by
   `fn2-exact-identity`; converging it across peers is E4's (peering), not this row's. State:
   applied.
3. **The sealer kind declares the other kinds' descriptor cap (4)** although it issues nothing
   (C1c). A's callers' guard proofs (`fn2-scribe-write`) range over every kind's caps and cannot
   show a row's kind is kept across an issue, so a registered kind whose
   descriptor cap is below another's charge broke them. Remedy: A proves the issue paths keep
   `fn2-machine-kind` (or states the charge check per the row's own kind), and the sealer's cap
   drops to 0. State: open, named to the A5r seat.
