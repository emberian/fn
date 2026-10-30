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
| identity schema, Binding merge, conflict bound | `fn2/books/identity.lisp` | C2 |
| active overlay per schema (bounded resident sorted table), InfiniFilter for the identity overlay | `fn2/books/overlay.lisp`, `fn2/books/infinifilter.lisp` | C2 |
| Ribbon filter per sealed run | `fn2/books/ribbon.lisp` | C2 |
| article metadata, overview, addressing schemas; range cursors | `fn2/books/ordered.lisp`, `fn2/books/cursor.lisp` | C3 |
| `deffold` (interpretation, initialization, coverage), the folds (cursors, accounts, pins, signer heads, registration, read-state, edge-policy, inbox), the summary cut | `fn2/books/folds.lisp`, `fn2/sim/check-fold.lisp` | C4 |
| compaction with reservations and backpressure; relocation under a lease | `fn2/books/compact.lisp` | C5 |
| IDENTITY and CONSUMER checkers | `fn2/sim/check-identity.lisp`, `fn2/sim/check-consumer.lisp` | C2, C4 |
| acceptance | `fn2/tests/sim-layer-c.lisp` (+ driver `.lsp`) | C2-C6 |
| units | `fn2/tests/runs-unit.lisp`, one per later book | each |

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
32 bytes), `NAME-add` (append one entry to a writer, refusing an out-of-order key by name) and
`NAME-seek` (bounded lower-bound search inside one page). No runtime code walks a declaration.

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
union. The key includes the content identity, so a Message-ID's facts are adjacent entries and
`conflicted(mid)` is "two adjacent entries share the octets". An offer `(mid, c)` decides `stored`,
`duplicate` (an entry `(mid, c)` exists) or `conflict` (an entry `(mid, c')`, `c' ≠ c`, exists). A
conflict refusal records its evidence as an entry under a per-Message-ID bound on retained
conflicting contents, charged to the offering principal, with the named refusal
`:identity-conflict-bound`. The served choice of content is a separate statement; evidence only
grows. Exact octets are kept permanently (STORAGE §4 decision 6); a filter or hash may reject,
never decide.

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
- **Overlay (C2).** One bounded active overlay per schema, fed by the commit batch's prepared
  successor (Astra §E: the read-visible successor overlay is built before sealing; installation is
  a handle swap). Sealing an overlay produces a level-0 run through the writer. The identity
  overlay carries an InfiniFilter (FILTERS-2026 item 3) that never deletes a non-member (the 2024
  lower bound).
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

- **Lookup.** Descend from the run root by lower bound over index pages, then seek inside the data
  page: binary search over restarts, linear decode within one interval. Each call is bounded
  (≤ 4096 pool reads) and resumable from `(page, restart lo, restart hi, entry)`. Per-run Ribbon
  filters skip runs on a miss (C2); a per-run perfect hash is measured against this sorted search
  before it is adopted (C6).
- **Exactness.** A lookup's `:found` means a byte-equal key was compared; `:absent` means the
  search ended at a lower bound whose key is greater. Neither ever comes from a filter alone.
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

- **C-GLUE-UNVERIFIED (proof cost; owed remedy).** The per-schema build and lookup glue
  (`NAME-BUILD-ADD`, `NAME-BUILD-PROMOTE`, `NAME-INDEX-SKIP`, `NAME-INDEX-NTH`,
  `NAME-LOOKUP-STEP`) is admitted with `:verify-guards nil`; everything it calls is guard-verified
  (the generic build work, promotion check, child reference, commit, cache, cursor save, and the
  per-schema page-level append and seek). Measured: verifying the lookup step's guard per schema
  took over 5 minutes and failed on missing frame lemmas; a schema's whole expansion now costs
  about 15 s (numeric) and 6 s (identity-shaped). The glue therefore runs through its executable
  counterpart with guard checks at each call, which is slower but checks every precondition. The
  remedy, owed before C3 serves: one layout dispatcher generated at the assembly point (as A's
  machine dispatch is) over all registered schemas, so the build and lookup algorithms are written
  and guard-verified once against the dispatcher's shape lemmas instead of once per schema.
- **C-PAGE-FILL.** A writer's fill limit (bytes of header, entries and directory) is a page-fill
  parameter, like a block size; the encoded page stays 64 KiB. Tests use small fills to reach many
  pages and levels with few entries.
- **C-CACHE.** The verified-page cache is direct mapped by physical unit and keyed by the exact
  (unit, allocation counter) pair, so a reused unit never answers for an old allocation. A page
  enters only after B's checker accepted it under its parent-held hash (or after its own seal). A
  lookup that needs an absent page stops with `:miss` and names the reference; its caller (the
  sealer or reader machine, C1c/C3) loads, verifies and installs it, then steps again.
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

## 9. Keystones (defthm-owed, each with teeth)

| name | statement (real entry points) | teeth | quest |
|---|---|---|---|
| `NAME-page-roundtrip` (generated per schema) | for sorted, well-formed entries that fit one page (`fn2-run-page-inputp`), the real append, close, head and seal produce, and B's checker accepts under the parent-held hash, exactly the octets of `fn2-run-page-spec` (B's list codec for the headers and each entry, the restart directory, zero padding) | positive: 40 entries per test schema, inputs checked; negative: unsorted entries (refused `:order` part way) give a different image | C1 |
| `NAME-seek-lower-bound` (generated per schema) | the real page seek returns `(:found i)` or `(:absent i)` equal to `fn2-run-lower-bound-spec` over the spec key order | positive: queries before, inside, between, after and at restart boundaries, including empty octets and a query held by another owner; negative: the unsorted page disagrees with the spec | C1 |
| `NAME-run-lookup-exact` (generated per schema) | for at most 64 sorted well-formed entries and a fill at which every page holds two entries (`fn2-run-run-inputp`), a run built through the real build entry points and searched from its root through the real cursor steps answers `(:found entry)` exactly when an entry's key equals the query's, with that entry, and `(:absent nil)` otherwise (`fn2-run-key-lookup-spec`) | positive: present, between, before, after and empty-octet queries over multi-level runs of both test schemas; negative: unsorted entries make the conclusion false | C1b' |
| `fn2-exact-identity` (RELEASE-PLAN T9) | the identity decision for `(mid, c)` is `duplicate` iff a stored fact `(mid, c)` exists, `conflict` iff a fact `(mid, c')`, `c' ≠ c`, exists, and the answer is unchanged after the body's and the journal placement's reclamation | positive: M3 scenario; negative: a summary that drops the octets fails "re-offer the same Message-ID with different content" | C2 |
| `fn2-identity-binding-converges` | two nodes with equal validated fact sets have equal Bindings and equal `conflicted` | positive: two delivery orders; negative: a node that refuses a conflict and records nothing diverges | C2 |
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
| C2 | identity schema, overlay, InfiniFilter, Ribbon, IDENTITY checker, M3 | identity correct after bodies and placements reclaimed; filter bits/key and probe time | C1 |
| C3 | metadata, overview, `addr`, range cursors with resume key and version, positioned seek, M2 | XOVER-shaped reads over cold sparse groups charging directory and overlap reads | C1 |
| C4 | `deffold`, the folds with their three declarations, summary cut exhaustively in tiny, CONSUMER checker, inbox equivalence | the scholar's chapter-1 scenario exhaustively in tiny | C2, C3 |
| C5 | compaction with reservations and backpressure, relocation under a stalled lease | compaction under a stalled lease; compaction bytes per committed byte | C4, C1c |
| C6 | permanent exact-identity retention and reclamation tests; perfect hash measured against sorted search inside a sealed run | 10,000 seeds concrete (nightly row); the measurement table | C5 |

## 11. Certify times

Every C book under 60 s on the laptop (the one-minute rule); the table lives in
`build/coordinator/fn2/lanes/c-continuation.md`, refreshed after every quest.
