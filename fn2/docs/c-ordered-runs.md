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
| article metadata, overview, addressing schemas; range cursors | `fn2/books/ordered.lisp`, `fn2/books/cursor.lisp` | C3 |
| `deffold` (interpretation, initialization, coverage), the folds (cursors, accounts, pins, signer heads, registration, read-state, edge-policy, inbox), the summary cut | `fn2/books/folds.lisp`, `fn2/sim/check-fold.lisp` | C4 |
| compaction with reservations and backpressure; relocation under a lease | `fn2/books/compact.lisp` | C5 |
| IDENTITY checker (an independent list interpreter with its own Binding); CONSUMER checker | `fn2/sim/check-identity.lisp` (C2d); `fn2/sim/check-consumer.lisp` (C4) | C2d, C4 |
| acceptance | `fn2/tests/sim-layer-c.lisp` (scenario M3 so far; `fn2/tests/sim-layer-c-sweep.lsp` the 10,000-seed driver) | C2d-C6 |
| C's test assembly: the identity schema and the run units' fixture schemas, assembled once; the teeth makers | `fn2/tests/runs-assembly.lisp` | C2b |
| units | `fn2/tests/runs-unit.lisp`, `fn2/tests/identity-unit.lisp` (both include the test assembly), `fn2/tests/ribbon-unit.lisp` (the filter alone) | each |

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
| fold rows | (table, object) | version, value or value ref | `:latest` (latest-only; pins retain versions, C5) | C4 |
| operation outcomes | (principal, operation) | request binding digest, outcome, event | `:unique` within the declared retry lifetime | C4 |
| obligations | obligation | owner, article, state, terms ref, release evidence ref | `:latest` | C4 |
| locations | logical object | current placement ref | `:latest` | C5 |
| manifest | (schema, run) | the run descriptor fields | `:latest` | C1 |

**Identity is a Binding (UC §4.3, decision 3).** `B : Message-ID → P_fin(content facts)`, merged by
union. The schema is `fn2-identity` (id 1): key `(message-id (:octets 250)) (content :digest)`,
value `state (:accepted :conflict)`, `article`, `binding` (the accepting event), `principal` (the
offerer). The key includes the content identity, so a Message-ID's facts are adjacent and
`conflicted(mid)` is "two adjacent entries share the octets".

The decision (`fn2-id-decide-start`, `fn2-id-decide-step`, one row of `fn2-id-decides` per
decision in flight) visits every identity overlay, then every installed identity run, each
positioned at the lower bound `(mid, empty content)`, and reads that Message-ID's block: whether
`(mid, c)` is recorded, and how many other contents are. The answer is `:duplicate` when `(mid, c)`
is recorded, `:conflict` when another content is, else `:stored`. Each step is bounded (a run's
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
- **Cursors (C3).** A range cursor holds a stable resume key and the logical version (the root
  generation it read); after a yield it re-seeks from the resume key in the current version. It
  never holds an old manifest or a physical traversal state as its meaning.
- **The read contract (UC §12 decision 2).** Every read names its strength: `exactly-at p` (needs
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
- **C-ONE-ASSEMBLY.** A world holds one assembly: the dispatcher and the generic functions are
  defined once, so two books that each assemble cannot be included together (the OWED export
  includes every unit). C's units therefore share one test assembly book. When the node's
  production assembly lands (with the sealer, C1c), the C units move onto it: their fixture schemas
  join it under the test profile or the units use the production schemas.
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

## 9. Keystones (defthm-owed, each with teeth)

| name | statement (real entry points) | teeth | quest |
|---|---|---|---|
| `NAME-page-roundtrip` (generated per schema) | for sorted, well-formed entries that fit one page (`fn2-run-page-inputp`), the real append, close, head and seal produce, and B's checker accepts under the parent-held hash, exactly the octets of `fn2-run-page-spec` (B's list codec for the headers and each entry, the restart directory, zero padding) | positive: 40 entries per test schema, inputs checked; negative: unsorted entries (refused `:order` part way) give a different image | C1 |
| `NAME-seek-lower-bound` (generated per schema) | the real page seek returns `(:found i)` or `(:absent i)` equal to `fn2-run-lower-bound-spec` over the spec key order | positive: queries before, inside, between, after and at restart boundaries, including empty octets and a query held by another owner; negative: the unsorted page disagrees with the spec | C1 |
| `NAME-run-lookup-exact` (generated per schema) | for at most 64 sorted well-formed entries and a fill at which every page holds two entries (`fn2-run-run-inputp`), a run built through the real build entry points and searched from its root through the real cursor steps answers `(:found entry)` exactly when an entry's key equals the query's, with that entry, and `(:absent nil)` otherwise (`fn2-run-key-lookup-spec`) | positive: present, between, before, after and empty-octet queries over multi-level runs of both test schemas; negative: unsorted entries make the conclusion false | C1b' |
| `fn2-exact-identity` (RELEASE-PLAN T9) | offers decided and recorded through the real decision and recording, sealed into runs every `split` offers, the offers' staging workspace released, then queries decided: each answer equals `fn2-id-answers-spec` (`:duplicate` iff recorded, `:conflict` iff another content is, else `:stored`) | positive: the M3-shaped scenario (a conflict, a duplicate, five contents for one Message-ID against the bound of four) at splits 0, 4 and 1; negative: a node whose summary dropped the Message-ID octets answers `:stored` to the re-offer of m1 with another content, where the statement requires `:conflict` | C2b |
| `fn2-identity-binding-converges` | two nodes whose offered fact sets are equal (any order, duplication or sealing schedule, within the bound) hold equal Bindings, read back by the real scan of every installed run | positive: one fact set in two orders (one with a duplicate) under splits 2 and 3, equal to each other and to `fn2-id-binding-spec`; negative: nodes that refuse a conflict and record nothing hold different Bindings for the two orders | C2b |
| `fn2-ribbon-no-false-negative` | a filter built through the real start, add, finish and work from at most 256 keys seals, passes B's checker under its parent-held hash, and its probe answers `:absent` only for a query that is no key (`fn2-ribbon-answers-sound`) | positive: 200 keys and 56 others probed, every key `:maybe`, at least 50 others `:absent`; negative: a filter built without key 17 answers `:absent` to it | C2c |
| `fn2-ribbon-mutation-refused` | any one-byte change (offset in the page, nonzero XOR) of a sealed filter page is refused by B's checker by name | positive: changes in B's header, the filter header, Z and the padding refused while the unchanged page is accepted; negative: a zero change is accepted | C2c |
| `fn2-identity-linearizable` | for every seed and at most 64 offers, the M3 scenario's trace (interleaved decisions, records, seals with filters, bodies released, then every pair queried and the Binding scanned) is accepted by the independent IDENTITY checker | positive: 40 seeds pass with races exercised (1,808 stale records) and 722 seals; negative: the same schedules with the stamp and version checks defeated are refused by name (37 of 40) | C2d |
| `fn2-fold-summary-adequate` (per fold) | the summary rule's homomorphism certificate per event kind: `obs(σ s) = obs s` and `σ(δ(s,e)) = δ_Σ(σ s, e)`, hence `Fold(Summary_k, E_{k+1..n})` observes as the full fold | TRANSPORT §9's two teeth: a relation weaker than the observation, an off-by-one summary step | C4 |
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
| C1c | sealer machine; run descriptor and manifest schema; run sealing through the commit batch (B's GC2 member); retirement through the allocator; the assembly dispatcher (C-GLUE-UNVERIFIED's remedy) | tiny exhaustive death cuts over one run replacement: recovered manifest is old or new, never mixed | B's GC2 member |
| C2a | range scan through the cursor path; the generic overlay | **done**: scans and overlays agree with the list specification; both keystones' teeth | C1c first item |
| C2b | identity schema, the decision machine, the recording under the bound, the two keystones | **done**: the M3-shaped scenario pinned; both keystones' teeth | C2a |
| C2c | Ribbon per sealed run, the probe in the identity decision | **done**: no key ever `:absent`; 8.5 bits/key at 60,000 keys (8.75 at 2,000); false positives 0.375% (75 in 20,000) and 0.395% (790 in 200,000 at 60,000 keys) against 2^-8 = 0.39%; the M3-shaped scenario reads only the runs holding the Message-ID (an absent one reads none); both keystones' teeth | C2b |
| C2d | IDENTITY checker; scenario M3 (interleaved decisions, seals, bodies released); the stamp and version refusal | **done (engine leg)**: 200 seeds of 30 offers all accepted, 9,077 stale records, 3,607 seals; defeated checks refused on 188 of 200; 10,000 seeds in `sim-layer-c-sweep.lsp`. The device leg (run pages through the commit batch, recovery) waits on C1c and B's GC2 | C2c |
| C3 | metadata, overview, `addr`, range cursors with resume key and version, positioned seek, M2 | XOVER-shaped reads over cold sparse groups charging directory and overlap reads | C1 |
| C4 | `deffold`, the folds with their three declarations, summary cut exhaustively in tiny, CONSUMER checker, inbox equivalence | the scholar's chapter-1 scenario exhaustively in tiny | C2, C3 |
| C5 | compaction with reservations and backpressure, relocation under a stalled lease | compaction under a stalled lease; compaction bytes per committed byte | C4, C1c |
| C6 | permanent exact-identity retention and reclamation tests; perfect hash measured against sorted search inside a sealed run | 10,000 seeds concrete (nightly row); the measurement table | C5 |

## 11. Certify times

Every C book under 60 s on the laptop (the one-minute rule); the table lives in
`build/coordinator/fn2/lanes/c-continuation.md`, refreshed after every quest.
