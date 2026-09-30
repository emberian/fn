# Paged history: the resident set as a function of connections and the suffix, never of the store (2026-09-29)

Lane `lane/paged-history` (Fable), row P1 of the master list, from dev
`e78a6645d` with `lane/byte-model` `17501844c` merged for
`docs/resource-contract.md`. A design document: no book, host or registry
file changed. Dependent counts are transitive includers over the
`include-book` graph of `books/` and `tests/acl2/` at this revision (the
runner's closure reads a few higher; recount with `tools/shape_books.py`
before editing).

Ember (2026-09-29): "is there any way we can avoid materializing the entire
heap store?" and "more on-disk data structures is actually extremely wise
and smart." The mandate, in one sentence: **the process's resident set is a
function of the open connections and of the record suffix since the last
checkpoint, never of the store.** The store's limits T (transactions) and H
(history octets) bound the disk (**D1**) and nothing else.

What holds today (the resource contract's **M2**, PRF-198 / PRF-314): the
figure charges the heap for every record the profile admits, twice (the
collector's copy), so the small profile (T 16,384, H 8 MiB, R 196,608,
G 16, K 128) reserves 1,179 MiB at `init` and the launcher's empty-store
figure is 770 to 825 MB; the scale gate (T 2^20) 26,929 MB; SYNTH_1M
54 GB. Only the payload arena is paged (`fn-arena-extent`, on demand from
the log files); every index is heap-resident, and there are three
Message-ID indexes.

## A. The survey

Access-pattern classes are GPT-6's (planning/review-2026-09-28-gpt6.md,
"Representation and page-store calls"): **count**, **indexed access**
(point lookup by key), **bounded cursor** (a range, resumable), **fold**
(over every row), **append-prefix** (the suffix grows; the prefix is
immutable), **snapshot** (the checkpoint's image of a prefix). The figure
terms are `books/heap-store-figure.lisp`'s and the MiB figures are the F8
record's small-profile column (planning/evidence/f8-reservation-2026-09-28.md,
"after this lane").

### A.1 Structures whose size scales with the store

| # | structure (book, field) | scales with | readers on the served / durable / BP paths, and the host caller | class | figure term today | paged today? |
|---|---|---|---|---|---|---|
| 1 | history rows: `fn-hist$c-rows` (books/history-columns, one decoded event tree per record) | T, header octets | `fn-hist-at` (every `-hx` twin: consumer poll `consumer-poll-index`, BP fast lookups `bp-native-app-fast`, owner completion refresh `owner-refresh-indexed`); `fn-hist-load` at the open (host/owner-host.lisp:427, O(store)); `fn-hist-sync` per commit (owner-host.lisp:877, 896, 2855); `fn-hist-refresh` for offline verbs (host/store-node-host.lisp:92); the carried folds `fn-hist-bytes/debt/usage-carried` (incremental) | indexed by seq; append-prefix; fold (carried); snapshot | **records**: 2 × T × 16,096 (`*fn-heap-record-octets*` = 4,096 fixed + 48 × 250 Message-ID) plus 2 × 32 per header octet; F8's table prints 384 MiB at 12 KiB a record; at the current constant 503 MiB | the IMAGE exists: FNADTSN2 history pages (books/history-pages `fn-hp-`, written at every checkpoint by `fn-hp-x-append-all`, host/native/proto-history-pages.lisp) and the image-plus-suffix abstract stobj `fn-hrecs` (books/history-records; A2 PRF-920, A5 PRF-923 on lane/composed-owner-books). The SERVED readers still read the heap: the host calls `fn-hrecs` once (`fn-hrs-disk-history`, host/native/extent.lisp) |
| 2 | Message-ID index (i): `fn-hist$c-mids` (hash eql: salted FNV-32 → seqs, confirmed against the row: `fn-hist$c-collect`) | T | `fn-hist-msgid-records` → the `-hx` twins above; `fn-pidx-existing-action` (POST's existing-article decision, owner-host.lisp:1465, 13 host calls) | indexed | inside **records**: the "Message-ID octet's trie and names", 48 × 250 = 12,000 of the 16,096 octets a record (75 % of the term) | no |
| 3 | Message-ID index (ii): `fn-cat$c-msgids` (hash equal: Message-ID string → seqs) | T | `fn-cat-msgid-seqs`, `fn-cat-view-find` (ARTICLE/HEAD/BODY/STAT by Message-ID, owner-host.lisp) | indexed | inside **records** | no |
| 4 | Message-ID index (iii): the owner's view trie `fn-mxc` (books/msgid-index-concrete, premise `fn-scar-view-indexedp` established at `fn-own-start`, books/owner-offer-indexed) and (iv) the persistent trie `fn-midx` (1 host call, `fn-midx-lookup`; J1 item 3, lane join-f2-midx, is retiring it) | T | `fn-pix-history-hasp` (IHAVE/CHECK offer decision, books/peer-offer-indexed) | indexed | inside **records** | no |
| 5 | catalog rows: `fn-cat$c-rows` (books/catalog, one held record per event: the 11-position wire tuple with the payload handle) and `fn-cat$c-wbv` (version → withdrawn rows), `fn-cat$c-octets` | T | `fn-sca-load-held-rows` at the open (owner-host.lisp:415, O(store)); `fn-cat-at`, `fn-cat-view-articles` (the acceptance projection), `fn-cat-view-below/-last-visible` (GROUP, LISTGROUP, OVER, NEWNEWS), `fn-cat-prepare-sealed` (POST), `fn-cat-withdraw/-redecide` (cancel, expiry) | indexed by seq; bounded cursor; fold (the projection); append-prefix; mutable visibility | inside **records** (the fixed 4,096) | no |
| 6 | memberships and group tables: `fn-cat$c-groups` (group → rows), `fn-cat$c-numbers` ((group . number) → seq, `fn-cnx-`), `fn-cat$c-lives` (group → count low high), `fn-gidx` buckets (LIST COUNTS through the pinned trie), the owner's `facts` (group-configuration facts) | memberships (≤ H / 320), groups | `fn-cat-group-number/-next/-high/-count/-rows`, `fn-cnx-view-range/-seq/-walk-range`, `fn-olc-` (LIST COUNTS), LIST/GROUP/LISTGROUP/NEWNEWS in books/nntp | indexed (group → summary; (group, number) → seq); bounded cursor (a number range) | **memberships**: 2 × 320 × H/320 = 2 H (16.3 MiB at small; 2 TiB at the default profile's 1 TiB) | no |
| 7 | the arena's handle table: `fn-arena$x` EXT (books/payload-arena-extent, 6 words a handle) and the staged pages of the batches not yet durable | T; the log batch | `fn-arena-count/-release/-seal-*`, `fn-durable-realize-octets` (A-DURABLE-EXTENT, the host's bounded cache) | indexed by handle | **handles**: 48 T (0.8 MiB at small; 48 MiB at T 2^20); the staged payloads within the log's operator bounds | the PAYLOADS are (arena-offheap-2/3); the handle table is not |
| 8 | the node's per-record lists: `fn-node` bindings (Message-ID, subject, obligation id per article; `fn-node-find-binding` indexed by an exec hash), the retention pins and charges (`fn-retain-`; obligations), the identity index `fn-rii` and the statement index `fn-stx-index` (rebuilt over the whole store at every open, `fn-rii-sco-finalize-configured`; incremental-finalize's note) | T, obligations | `fn-rtf-pin-count/-reserved`, `fn-snrt-` (unaffordable-obligation refusal), `fn-stx-index-bindings` (store-node-host.lisp:1475), `fn-rii-classified-open` (5 host calls), carry-abandon's waiver | indexed; count; fold (rebuilt at open) | inside **records** (the fixed part) | the obligations REPORT is paged (`fn-nlp-`, lane obligations-paged); the pins are not |
| 9 | the checkpoint's capture buffers: `fn-ock-capture-budget` = 3 H + a segment, twice | H | `fn-scka-next-checkpoint` (books/store-checkpoint-arena-writer), the pipeline `fn-ockp-` | snapshot | **in flight: two octet buffers** 48.4 MiB at small (3 TiB at the default profile) | no: a checkpoint captures the state; a paged store writes dirty pages |
| 10 | the open's transient: chunk lists, suffix vectors, the per-record build | the observed store (OU, ON) | `fnn-recover` / every offline open (host/native/io.lisp), `fn-rii-sco-extend-open` | fold (a replay) | **open**: 76.0 + 16.0 + 32.0 MiB at small; F1's 2.4 GB transient at 100k | A5's paged fold is READY (PRF-923); the served open still decodes |
| 11 | per-peer feed queues (`fn-own` `feeds`: one queue per configured peer of the articles not yet offered) and the refused-offer memory (`refused`, books/refused-offers, PRF-235, in memory only) | peers × pending articles; offers | `fn-scar-feed-span`, `fn-own-transit-outcome`, `fn-own-conn-live-session` | append-prefix (a cursor per peer) | not a figure term (unbounded, "Not bounded" 4) | no |
| 12 | expiry: `fn-xpy-ctx-classes` partitions every article at reclaim (host/checkpoint-host.lisp:189) | T | `store reclaim`, online reclaim (lane online-reclaim-4) | fold | not a figure term (a maintenance quantum) | no |

### A.2 What must stay resident, and why

- **Per-connection state** (`fn-own` `conns`: id, version, frontier, wire
  framing, the POST session, the posting configuration, the observation,
  the verdicts): the M7 connection budget already bounds it by
  `max-conns`. The archive a connection is "pinned to" is a **generation
  pointer** into the committed view (structure shared with `view`), never a
  copy: on pages it is a root name plus the log length at the pin
  (A6's root lifetime), so a pinned reader keeps its pages alive by the
  root, not by the heap.
- **The suffix and its index**: the records committed since the last
  adopted image, decoded (they are being served now), with the suffix's
  own Message-ID index (a hash over ≤ the suffix's records) and the
  suffix's group summaries. Bound: the checkpoint cadence.
- **Credits** (M5, M6): the article-slot pool
  (`*fn-heap-article-slot-budget*` 64 MiB, at most 32 slots) and the
  per-request buffers, funded from the operator's budget; the page cache is
  a credited pool of the same kind (B below).
- **The page cache's pinned pages**: the pages an active read has faulted
  in and named in its continuation; bounded by connections × the reader
  class's page need (B.3).
- **The staged payloads** of the log batches not yet durable (arena-offheap-3:
  bounded by `+fnn-checkpoint-batch-octets+`-class operator bounds, never
  by H).
- **The core's dynamic content, the threads' stacks and runtimes, the
  collector's room**: the base.

### A.3 The suffix admission boundary

A checkpoint becomes due at half K, where K is the persisted profile's
`max-open-suffix`. The due rule alone cannot bound commits made while a
publication runs or is deferred. The ratified recovery policy therefore
requires admission limiting as well as publication progress.

`fn-csa-post-admission` now refuses the next POST by name when its new
committed count would exceed the last durable checkpoint count plus 2 K.
`fn-owner-post-boundary` reads the carried count and durable frontier under
the owner mutex before allocating a transaction identity or preparing its
record. Refusal is `checkpoint-deferred` (POST 441); a newly durable
checkpoint can reopen admission. The source theorem and exact-boundary
scenario are PRF-1098 / SCN-1011. Matching native execution remains pending.

This rule bounds each admitted POST relative to the durable checkpoint; it
does not prove a global suffix bound across every mutation kind or fund the
physical decoded suffix. Packed frames and canonical retained context can
exceed a per-record wire-size estimate. Actual representation funding and
checkpoint rescue remain separate P12 obligations.

## B. The design

### P12 implementation contract amendment (GPT-6.1, 2026-09-29)

The ratified [review](review-2026-09-30-gpt6-log2.md) section2 supersedes
A.3's older policy-question wording. PRF-1098 now supplies the POST suffix
admission boundary; PRF-963 remains only the deferred-checkpoint health code.
Neither establishes complete rescue capacity. The current maintenance
reserve funds one release record; it is not a resource-vector rescue proof.

The first implementation increment is `books/page-read-resources.lisp`,
an admission-algebra library, with no served allocation or complete P12
claim. It uses five explicit units: resident octets (collector copy
included), disk octets, registered descriptor credits, executing worker
slots, and spent process-local read identities. The last coordinate is one
named identity namespace; Store txids and file identities need their own
coordinates/refinement, never an aggregate that treats them as fungible.

`fn-prs-issue(B,U,R,C,next,limit,demand)` issues only when the supported
vector covers `U + R + C + demand` and the next local read identity is
representable. Failure changes neither credits nor identity; repeated
refusal spends neither. Settlement releases reusable coordinates but never
refunds an identity. Supplied static rescue R survives an admitted charge;
the library does not establish `R >= W(P,Omega(s))` or that the host's
supplied U/C/demand represent its actual allocations.

For the current uncompressed cold prefetch, `fn-prs-worker-demand` charges
twice the protected buffer's `elen + 32` plus conservatively supplied
bookkeeping, and the native worker's stack/runtime once. It charges one
execution slot, no descriptor opening, and one local read identity. A
registered file incarnation instead holds `fn-prs-incarnation-demand`:
its own bookkeeping and one descriptor credit. Shared descriptors are not
charged once per worker. A compressed reader needs its actual expansion
demand, not this constructor. Bookkeeping/runtime inputs have no measured
bound established by the library.

The ownership API from `books/page-read-ownership.lisp` constructs the
token at the old `next` only after admission, with a named equality to the
admission's returned `next + 1`; there must not be two independent counters.
An immutable token-to-charge binding is separate from that book's seven
row fields. Cancel, deadline, client loss and stale completion do not
refund. Only the first actual matching completion settles ownership, then
refunds after dropping the extent mutex; the wrapper must prove exactly-once
settlement and the lock order. A refused issue allocates no buffer/thread.

The next pool increment (`page-read-ledger`, `page-read-host`, PRF-1065,
SCN-1002) binds the complete immutable token to its charge in a dedicated
ACL2 stobj. Actual worker death plus join, rather than a callback still
running on that worker, is the native release observation. A cached vector
retains its buffer charge until eviction; the file incarnation retains its
FD charge until actual close. Persistent hash arrays may retain peak capacity
after removing entries and must be baseline-funded at installation. The
current adapter accepts supplied accounting inputs; it establishes no
measured allocator bound or productive supported profile by itself.

The operational grammar now names five explicit, positive u64 quantities:
`cold_heap_octets`, `cold_workers`, `cold_descriptors`, `cold_read_ids` and
`cold_file_ids`. Read and file identities have independent finite namespaces;
neither wraps or refunds names. The file wrapper calls
`fn-pio-file-issue-with-limit` before opening. Registration passes the actual
path string to ACL2's `fn-prs-incarnation-path-demand`; the selected 64-bit
SBCL string-layout model charges `32 + 4 * length(path)`, in addition to the
supplied incarnation bookkeeping and collector copy allowance. The saved
SBCL 2.6.8 hbox layout probe supports this target choice, not an arbitrary
Common Lisp allocator guarantee. The native supported-profile consumer and
physical baseline remain open, so explicit policy is still refused by run.

The agreed follow-on uses persistent startup executors: their stack/runtime
storage is baseline-funded until service shutdown, and each running or
returned job holds a worker lease until exact owner settlement. It does not
infer RSS release from joined thread death. Hash bucket capacity, cache
buffers and decoder highwater have separate lifetimes and funding duties.

Remaining complete increments, in order:

1. Supported operator resource policy, representability and initial funding;
   no guessed max-connections surrogate. Operational policy belongs in
   configuration; the planned durable `page-cache-octets` profile field is
   an intentional format/layout change. Coordinate both with the limits lane.
2. Ownership + immutable charge relation through issue, completion, failed
   read, cancellation and late/stale callbacks; actual pread stall witness,
   repeated timeouts, refusal before allocation, incarnation retirement.
3. Performed checkpoint/recovery demand W: existing whole-store terms until
   P3/P8 remove them, codec expansion, retained old/new generations and
   cleanup. Reserve static worst case first if justified; charge positive
   demand growth before every accepting primitive, not just POST.
4. Refused-response, diagnostics and audit primitives must use already
   funded bounded workspace without borrowing rescue or silently growing
   durable identities/artifacts. A crash leaves a bounded recognizable set.
   Admission algebra alone does not prove these primitives preserve slack.
5. Host-called suffix/rescue gate, its requirement/spec/scenario together,
   full literal witnesses, matching candidate native evidence, then the
   T/H-independent figure only after its physical representation premises
   are established. No abstract gate is a substitute for measured peak.

### B.1 The page layouts

Every paged structure is an FNADTSN2 sequence ADT (books/proto/adt-bytes)
in the page store (books/pagestore, 16 KiB pages of u64 words,
copy-on-write commits, a per-page BLAKE3 digest in the table entry that IS
the ADT's page-digest leaf, `fn-hp-page-digest-is-leaf`). Fixed-width
cells, one word each; a column read is one word; pool entries start on a
word. Regions are contiguous; a region that must grow is the writer's
`:grow R` verdict and moves alone (L-HP-DOUBLING, history-pages).

1. **History rows** (exists, `fn-hp-`): columns MKEY (u64), tree length
   (u64), the pool of tree octets; the catalog's held tuple is the same
   row (the wire tuple is a projection of the event, `fn-hist-key-article`),
   so **the catalog rows are not a second image**: A.1 row 5 gets two more
   columns on the same rows: VIS (u64: 0 visible, else the version withdrawn
   at, `fn-cat-withdrawn-at`) and HANDLE (6 words: the payload extent,
   A.1 row 7, `fn-arena$x`'s EXT entry). A row's node-side columns (A.1
   row 8: the obligation id, the subject digest's first word) go on the
   same rows.
2. **The Message-ID table** (new, prefix `fn-mpx-`, the first
   implementation, C row P2): an open-addressed table of BLAKE3 digests.
   Entry = (TAG u64, SEQ u64), 16 octets, 1,024 entries a page. TAG = the
   first word of `fn-digest` (BLAKE3, the attached digest) of the
   Message-ID octets, with 0 reserved for empty (a digest whose first word
   is 0 stores 1: the tag is `max 1 (word 0)`); SEQ = 1 + the record's
   sequence (0 empty). Home page = TAG mod pages; linear probing wraps
   **within the page**; a full home page overflows to the next page (the
   writer's verdict `:grow` when any page passes 3/4 occupancy keeps the
   table's load under 1/2, so an overflow is the named limit L-MPX-OVERFLOW:
   a lookup reads the home page and at most its successor). A hit is a
   candidate; the reader confirms the exact Message-ID against the history
   row (as `fn-hist$c-collect` confirms an FNV bucket today), so a tag
   collision costs one row read and never a wrong answer. **Worst case:
   one table page a lookup, two at an overflow, plus the row.**
   Duplicates (the same Message-ID at several sequences, `fn-cei-article-
   records-for` returns all) are separate entries with the same TAG, in
   probe order oldest first: the lookup collects every matching entry of
   the probe run, so the paged answer is a list in sequence order.
   **The suffix merge at checkpoint**: the resident suffix index (a hash
   over the ≤ 2 K suffix records) is folded into the table pages when the
   image is committed: dirty pages ≤ the suffix's distinct home pages
   (≤ 2 K) plus a `:grow`. Between checkpoints a lookup is the suffix index
   first (memory, O(1)), then the table (one fault).
3. **Memberships and group tables** (row P5): the group directory (a
   table like 2 keyed by the group name's digest: GID u64, COUNT, LOW,
   HIGH, NAME offset into a name pool: 5 words) and the **membership run**:
   rows (GID u64, NUMBER u64, SEQ u64) sorted by (GID, NUMBER), 24 octets,
   682 a page, with a per-page first-key column in the directory so a
   range starts at one page (binary search over the first-key column:
   log₂(pages) words, one page). A group's number range is a bounded
   cursor over consecutive pages; a (group, number) → seq lookup is one
   page; the group's summary is one directory row. A withdrawal does not
   move a row: VIS on the history row decides visibility, and the summary's
   COUNT is carried (the catalog's `fn-cat$c-lives` fold, on the row).
   The suffix's memberships are merged at checkpoint like 2 (an insert into
   a sorted run is a page split: the writer's verdict, copy-on-write).
4. **The pins and obligations** (row P6): a table keyed by obligation id
   (u64) with the pin's charge and evidence state; the count and reserved
   charge are carried on the root record (folds become carried numbers,
   as `fn-hist-bytes-carried` already is).
5. **The statement and identity indexes** (row P7): tables like 2 keyed by
   the identity's digest.

### B.2 The cache

A **page cache budget C** is a profile field (`page-cache-octets`,
validated with the rest: `fn-bs-profile-validate` refuses a C under the
connection capacity's pinned need, B.3). The cache is a credited pool of
M6's kind: a fault acquires a page credit before the read
(`fn-mcr-acquire`), a page holds it while pinned, eviction releases it
(GPT-6: "cache credit is reclaimable only after actual eviction").
Pages are pinned by the reads that named them; an unpinned page is
evictable, clock-order. **The active read's required pages are preserved**:
a reader class declares its page need P (B.3), the read pins as it faults,
and a read that would exceed its class's P is a modelling error refused by
name, never a silent scan. So no progress-measure argument is needed for
eviction: a pinned page is never evicted, and every reader is finite in
pages by its class.

**Faults are asynchronous requests outside the owner mutex** (A4's
discipline, core READY 92f292e54): a served step that needs a page not
resident returns `(:fault ROOT-GENERATION PAGE-ID EXPECTED-DIGEST
CONTINUATION)`; the host's I/O thread preads the page, verifies the
digest ACL2 named, and re-enters the owner with the page filled and the
continuation; the continuation carries the read's generation and the pages
it holds pinned. A page that arrives after the root changed, or with the
wrong digest, or not within the step's deadline, makes the read
**`unavailable`** (the cold-read 403 shape time-bars wired: "try again"),
**never absent**: absence is decided only from a verified page under the
read's own root. A timeout never becomes a 430.

### B.3 The page need per reader class, and the served read's cost on a miss

| class | reader (host function) | pages a read needs at most (P) | cost on a cold miss (16 KiB preads) |
|---|---|---|---|
| point lookup by Message-ID | ARTICLE/HEAD/BODY/STAT `<msgid>`, IHAVE/CHECK, POST dedupe | 1 table page (+1 at overflow) + 1 column page + ⌈tree octets / 16 KiB⌉ pool pages | 3 preads for a 2 KiB record; 4 with the overflow; the payload extent read is A-DURABLE-EXTENT's and already on demand |
| point lookup by number | ARTICLE `n`, STAT, LAST/NEXT | 1 directory page + 1 run page + the row's 2 | 4 |
| bounded cursor | GROUP, LISTGROUP, OVER/XOVER, NEWNEWS, HDR over n rows | 1 directory + ⌈n / 682⌉ run pages, then ≤ 2 row pages a row, Q rows a scheduling step (D27's quantum; the step yields with its cursor) | 2 + 2 Q a step; a group's articles are scattered over the seq-ordered rows, so OVER is 2 preads a row cold and cached warm |
| count / summary | GROUP's count-low-high, LIST, LIST COUNTS | 1 directory page per 409 groups | 1 |
| append-prefix | the commit (`fn-hist-sync`, `fn-cat-commit`) | 0 (the suffix is resident) | 0 |
| fold | the acceptance projection, expiry classes, the open's replay | never over the image on a served path: the projection is carried on the root (VIS, COUNT), expiry is a bounded cursor over the run by (GID, DATE), the open adopts | — |
| snapshot | the checkpoint | the dirty pages: ≤ 2 K row-home pages + the merged index pages + the directory, written in `+fnn-checkpoint-batch-octets+` (4 MiB) batches | — |

### B.4 The manifest: image ↔ exact log prefix ↔ schema

The page store's root record (pagestore's commit record, two slots,
self-checked) carries A2's binding (PRF-920, `store-checkpoint.fnsc`'s F
row): the store identity, the log prefix length N and the log's chain
trailer at N (the record log is the authority: `fn-lg-`'s chain), the
schema digest of every region (the FNADTSN2 schemas of 1 to 5, so a page
is interpreted only under the schema that wrote it), and the image
generation. `fn-hrecs-faithful` (established at adoption, replay, import
and recovery; preserved at mutation, fill and eviction, A2) is the
relation every equality theorem assumes; a root whose N is not a prefix
of the log's length, or whose trailer differs, is refused by name at the
open (foreign store, different history at equal count: A3's swaps).

### B.5 The crash model at every write

Two already-modelled cuts compose: the log's (`fn-lgu-`, durable acceptance
at every crash point) and the page store's (`pgs-open-after-crash`: a crash
anywhere in a commit opens on the new or the previous root state and never
anything else; a record not landed whole is the previous). The image is
a cache of a log prefix, so **the open after any cut = adopt(the newest
whole root) + replay(the log from that root's N)** = the full replay
(PRF-923's paged fold, composed with `fn-hrecs-faithful`); a torn image
commit costs a longer replay (from the previous root's N), never a
different history. Every process-death cut in the host's image write is a
model crash point (`native_program_check`); the dirty-page write's own
order (pages, then the table, then the root slot) is pagestore's.

### B.6 The theorem per moved reader (the 5u method)

One reader at a time, each with the equality theorem to the heap reader
it replaces, stated over the host-called function:

    (implies (fn-mpx-faithful pg hist)            ; the table + suffix index
             (equal (fn-mpx-records msgid pg)     ; the paged reader
                    (fn-hist$a-msgid-records msgid hist)))   ; = fn-cei-article-records-for

and the same shape for `fn-cat-view-find` (by number), `fn-cat-view-below`
(a cursor: the paged cursor's n rows are the heap cursor's), the group
summary, the pin count. The reusable refinements are per class, not per
caller (GPT-6): **indexed access** (a table faithful to a key function
answers the key's records), **bounded cursor** (a page-range walk over a
sorted run answers the range), **count** (a carried number is the fold's
value), proved once over the abstract page model and instantiated per
key function. The host line switches when the theorem is certified and
the native passes; the heap twin is deleted in the LAST step of each row
(the wide edit: history-columns 751 dependents, catalog 80, node 1,015),
batched into one recertification per wide book.

A reader whose theorem needs `fn-mpx-faithful` gets it from the open
(adoption establishes it) and every commit (the suffix index's append
preserves it): the premise is established on the host path, never assumed
(GPT-6: "do not make the host assume the relation it is supposed to
establish"; K6's premise audit).

### B.7 The recovery path

The open reads the root (two slots, self-check), binds it to the log
(B.4), adopts the image without decoding a row (A5: `open touches no row
pages`), replays the ≤ 2 K suffix from the log (one chunk at a time,
`fn-heap-open-chunk-bound`), builds the suffix index and summaries (O(K)),
and is `:ready`. Damage discoverable at first touch, named: a page whose
BLAKE3 differs from its table entry (`damaged-page`), a short read of the
image file (`damaged-image`), a table page that fails its digest
(`damaged-table`). Each is `damaged` by name, never absence, never a
silent skip; the explicit full scan stays (`store verify`: every page
against its digest, every row decodable, the run sorted). Ready time,
cold-first-query cost and the full scan are reported separately.

### B.8 The new figure

    FIGURE = BASE + SUFFIX(K) + CACHE(C) + CREDITS + CONNECTIONS + ROOM

- BASE: the core's dynamic content (140.8 MiB observed), the core file
  outside the dynamic space (204.1), the threads (30 × (1 + 4) MiB = 150).
- SUFFIX(K) = 2 K × (`*fn-heap-record-octets*` + 32 × HDR) × 2 (the
  collector's copy) + the suffix index (2 K × 16) + the staged payloads of
  the batches not yet durable (2 × (4 MiB + R)). Small: 8.0 + 0.004 + 8.4
  = 16.4 MiB.
- CACHE(C) = C, the operator's page-cache budget (default 64 MiB; the
  friend's 2 GB node 16 MiB), validated ≥ max-conns × P_max × 16 KiB.
- CREDITS = the article-slot pool (64 MiB at most, M5) + the in-flight
  lists (7.5) + the checkpoint's write batch (2 × 4 MiB = 8; replaces the
  3 H capture buffers).
- CONNECTIONS = M7's per-connection budget × max-conns (already in the
  reservation's thread terms for 30).
- ROOM = the collector's nursery term (at most an eighth of the rest,
  `fn-heap-with-nursery-is-at-most-an-eighth-more`).

**The small profile's figure becomes about 740 MiB reserved** (494.9 base
+ 16.4 suffix + 64 cache + 79.5 credits + 1.2 open chunk = 656 MiB, plus
room ≤ 82) against 1,179 MiB today, and **its dynamic heap about 380 MB**
(656 − 204.1 core file − 150 threads + room) against 770 to 825 MB;
with C = 16 MiB and 16 MiB of slots (the 2 GB friend node) about 640 MiB
reserved. Assumptions: the observed core (214,012,928 : 147,604,131), 30
threads at SBCL's 1 MiB stack + 4 MiB runtime, the small preset's K = 128
and R = 196,608, records at the 250-octet Message-ID ceiling. The number
that matters more: **it does not move with T or H** — the scale gate
(T 2^20, 26,929 MB today) and SYNTH_1M (54 GB today) reserve the same
740 MiB plus whatever cache the operator gives them.

The theorem shape (PRF-198's and PRF-314's successor, books/heap-paged-figure
when the terms exist): `fn-heap-paged-figure-holds-every-store` with the
same hypotheses as `fn-heap-store-figure-holds-every-store` but the need
stated over the suffix length s ≤ 2 K and the pinned pages p ≤ C, and
**`fn-heap-paged-figure-is-independent-of-the-store`**: for profiles that
differ only in T and H, the figures are equal. The memberships keystone
(PRF-314) becomes a disk statement: the run's octets are 24 a membership,
within H's charge of 320.

### B.9 What becomes moot, and how

- **Header weight (w = 8 vs 4).** The heap cost of a header octet
  (`*fn-heap-record-header-octet-cost*` 32) multiplies nothing once the
  tree octets live in the pool pages: the choice is the disk image's cell
  width, and FNADTSN2 cells are 8 octets (word-aligned reads) — a disk
  term the operator's H already bounds (D1). Moot for memory; for disk
  keep 8.
- **D13 (never forget), (a) versus (b).** (a) "keep all history, raise T
  as the machine grows" was painful because T was a heap term; now T is a
  disk term and raising it is a table `:grow` (copy-on-write, no resident
  change). (b) the `remember` window was motivated by bounded state on a
  fixed machine; that state is now bounded by K and C regardless of the
  history's age, so (b) survives only as a disk-space policy, which D2 and
  reclaim already cover. Recommend (a); no sequence-base change.
- **F1 peak versus settled.** F1 (the 100k store's reopen not fitting its
  figure: a 2.4 GB decode transient) and F3 (the posted state 1,083 MB
  against the reopened 780) were both "the whole store decoded on the
  heap"; the open now adopts (no decode) and replays ≤ 2 K records one
  chunk at a time, so peak = settled + one chunk, and posted = reopened =
  the same figure (a posted record is a suffix row until the checkpoint,
  then a page). F5 (the launcher's figure growing with the disk) goes
  with them: the observation sizes nothing.

## C. The rows

Ranked by figure term removed ÷ dependents recertified (dependents from
the include graph at this revision; the wide deletions are the last step
of each row and are batched). "Live lane" names who holds the books today
(`tools/boxes.sh` tokens and the LANEDUMPs at 05:00Z: limits-live-3 holds
wide-native-admin, correctness-remainder-2 wide-served; composed-owner-5 on
lane/composed-owner-books holds history-records, store-files,
store-checkpoint-arena-writer, payload-arena-extent; join-f2-2/-5 and
join-f2-midx hold served-catalog-join, catalog's served chain and
msgid-index; incremental-finalize holds replay-identity-index's finalize;
online-reclaim-4 the reclaim path; carry-abandon retention's waiver).

| row | what | books | readers moved (host caller) | theorem | natives | figure term removed | dependents recertified | live lane's books touched |
|---|---|---|---|---|---|---|---|---|
| **P2** | the Message-ID table (B.1.2) with the suffix index and the checkpoint merge; then delete `fn-hist$c-mids`, `fn-cat$c-msgids`, the view trie's role | NEW books/msgid-pages (`fn-mpx-`), tests/acl2/msgid-pages-tests; host/owner-host.lisp lines for `fn-pidx-existing-action`, `fn-cat-view-find`; the `-hx` twins' callers | `fn-hist-msgid-records` (consumer poll, BP fast lookups, completion refresh), `fn-cat-msgid-seqs`/`fn-cat-view-find` (ARTICLE by Message-ID), `fn-pix-history-hasp` (IHAVE/CHECK), `fn-pidx-existing-action` (POST) | `fn-mpx-records-is-hist-msgid-records` under `fn-mpx-faithful`; the indexed-access refinement lemma | recovery, served_differential, nntp_post_probe, replay_determinism | 12,000 of 16,096 octets a record × 2 T: **375 MiB at small**, 24 GB at T 2^20 | 0 for the new book and the host lines; the deletions: history-columns 751, catalog 80, msgid-index-concrete 759 (one batched edit each, last) | join-f2-midx (fn-midx's retirement: P2 replaces the view trie only after J1 (3)); composed-owner-5 (the faithful relation composes with `fn-hrecs-faithful`) |
| **P3** | the served history rows over the image: `fn-hist` executes as image + suffix by `attach-stobj` (as `fn-arena` → `fn-arena-paged`), `fn-hist-load` at the open replaced by adoption | books/history-records (fn-hrecs, A5), a new books/history-attach (the attach), host/owner-host.lisp:427, host/store-node-host.lisp:92 | `fn-hist-at`, `fn-hist-load`, `fn-hist-refresh`, `fn-hist-sync` | `fn-hist-paged-at-is-at` under `fn-hrecs-faithful` (PRF-920/923's successors); the attach keeps every certificate above fn-hist | recovery, served_differential, checkpoint_auto | the fixed 4,096 × 2 T (**128 MiB at small**) + the open's per-record build 32 + suffix vectors 16 | 0 above the attach; history-records 717 if its exports change | composed-owner-5 (history-records, store-files: after it reports) |
| **P4** | the catalog on the same rows (VIS, HANDLE columns), `fn-sca-load-held-rows` replaced by adoption; `fn-cat-view-*` as paged readers | books/catalog, catalog-view, catalog-number-index, served-carried; host/owner-host.lisp:415 | `fn-cat-at`, `fn-cat-view-articles/-below/-last-visible/-number-find`, `fn-cat-prepare-sealed`, `fn-cat-withdraw` | per reader, the bounded-cursor refinement | served_differential, nntp_post_probe, cancel | the catalog rows (inside the records term) and the open's O(store) load | catalog 80, catalog-number-index 52, served-carried 96 | join-f2-2/-5 (served-catalog-join 25, the 200+ uses of fn-sca-load-held-rows), correctness-remainder-2 (wide-served) |
| **P8** | the checkpoint as dirty pages: the capture buffers (3 H, twice) become the 4 MiB write batch; the merge of P2's and P5's suffixes | books/owner-checkpoint-writer (23), owner-checkpoint-pipeline (18), store-checkpoint-arena-writer (6) | `fn-scka-next-checkpoint`, `fn-ockp-` | `fn-ockp-dirty-pages-bound` (≤ 2 K + columns); PRF-365's snapshot keystone restated over pages | checkpoint_auto, state_checkpoint, recovery | **48.4 MiB at small; 3 H in general** (3 TiB at the default profile) | 47 | composed-owner-5 (fn-scka) |
| **P5** | memberships and group tables as the directory + the sorted run (B.1.3) | books/catalog's group tables, group-bucket-index (559), nntp-list-counts, owner-list-counts-read | `fn-cat-group-*`, `fn-cnx-*`, `fn-olc-*`, LIST/GROUP/LISTGROUP/NEWNEWS | the bounded-cursor and count refinements | served_differential, group_access | **2 H: 16 MiB at small, 2 TiB at default** | group-bucket-index 559 (the wide one; batch with P4's catalog edit) | join-f2-5 (the catalog's served chain) |
| **P6** | the node's per-record lists and the pins as paged rows and a table; counts carried | books/node (1,015), retention (1,018), store-node (682), retention-figures | `fn-node-find-binding`, `fn-rtf-pin-count/-reserved`, `fn-snrt-` | the count refinement; `fn-retain-paged-pins-are-the-pins` | recovery, peering obligations, carry-abandon's native | the fixed part's node share; the O(obligations) pins | node 1,015 + retention 1,018 (ONE batched wide edit, last of all rows) | carry-abandon (N9), incremental-finalize (the node's finalize), online-reclaim-4 |
| **P7** | the statement and identity indexes as tables; no rebuild at open | books/replay-identity-index (26), statement-field, store-node-host.lisp:1475 | `fn-stx-index-bindings`, `fn-rii-classified-open` | the indexed-access refinement, instantiated | recovery, replay_determinism | the O(store) rebuild at every open (A9's note) | 26 | incremental-finalize (A9) |
| **P9** | the arena's handle table as the HANDLE column of P3's rows; the stage stays | books/payload-arena-extent (5) | `fn-arena-count`, `fn-durable-realize-octets` | `fn-arx-entry-is-the-row-handle` | recovery, served_differential | 48 T (0.8 MiB at small; 48 MiB at T 2^20) | 5 | composed-owner-5 (A6's count column), online-reclaim-4 (fn-xrt-scan) |
| **P10** | expiry as a bounded cursor over the run by (GID, DATE) | books/expiry (4), host/checkpoint-host.lisp:189 | `fn-xpy-ctx-classes` | the cursor's classes are the fold's classes | expiry's native | a maintenance fold over T (a quantum, not a term) | 4 | online-reclaim-4, expiry |
| **P11** | feed cursors and a bounded refused-offer ring | books/owner-feed (470), refused-offers (505) | `fn-scar-feed-span`, `fn-own-transit-outcome` | the feed's queue is the rows after the cursor | peering feed natives | "Not bounded" 4's peers × pending | 470 + 505 (wide; batch) | join-f2 (peer arm) |
| **P12** | the figure's successor: books/heap-paged-figure (BASE + SUFFIX + C + CREDITS), `page-cache-octets` in the profile, the contract's M2 row rewritten, the operator docs | books/heap-store-figure (16), heap-breakdown, byte-store-frame (the profile field: wide), docs/resource-contract.md | `fn-heap-decide` (the launcher's figure) | `fn-heap-paged-figure-holds-every-store`, `fn-heap-paged-figure-is-independent-of-the-store` | init/launcher natives | the whole state term | 16 + the profile book's closure | limits-live-3 (the profile's policy set verb; the new field goes in with its edit) |

P2's first READY (this lane, `books/msgid-pages.lisp`, PRF-957): the
logical side, for every tag function: the indexed-access refinement
`fn-mpx-confirm-is-the-records-for` (a nat-listp of candidates, ascending,
below the length and complete, confirmed against the rows, is
`fn-cei-article-records-for`) and the keystone
`fn-mpx-records-is-the-records-for` (the home page merged with the
overflow page, confirmed, under `fn-mpx-faithful`), restated against
`fn-hist$a-msgid-records`; teeth `tests/acl2/msgid-pages-tests.lisp`
(a colliding tag attached; found twice in order, once, never; overflow;
a labelled stale entry; `table-okp` and `faithful-from` dropped in turn).
Next: the executable pages over `pgs-mem` words with the BLAKE3 tag by
functional instantiation and the suffix index; then the host switch of
`fn-cat-view-find` first.

Order of landing: P2 now (no live lane holds a new book; the host lines
are one-line switches under the existing twins' theorems); P3 and P8 after
composed-owner-5 reports; P4 and P5 after join-f2-5 and
correctness-remainder-2 release the served chain; P7 after
incremental-finalize; P6 last (the node's wide edit, once); P9 with P3;
P10 with online-reclaim-4; P11 any time after P4; P12 when P2, P3, P8
have removed their terms (the figure book asserts what exists, never a
plan).

Measure at convergence (not now): the small profile's launcher figure and
VmHWM on the 100k and SYNTH_1M stores after P3 and P8; the cold ARTICLE
cost by Message-ID (B.3's 3 preads) on the served differential fixture.

## Amendment 2026-09-29 (lane paged-history-3): the Message-ID table under PKT-774 and GPT-6's calls

Row P2's table (books/msgid-pages-exec) now carries ember's W2b ruling and
GPT-6's 2026-09-29 calls (planning/review-2026-09-29-gpt6-decisions.md):

- **The key is the generation's.** The tag is BLAKE3 keyed_hash under a
  purpose key of the node secret ("fn/msgid-index/v1"); one key per index
  generation, stable across every ordinary checkpoint, never per
  checkpoint; a generation changes only through a controlled rebuild (the
  next generation built beside the old, `fn-mpxt-grow-into`, adopted only
  when every entry landed) or on compromise. A key derived from a
  compromised node secret restores nothing: a rotation is a fresh
  node-secret epoch and a rebuild under its key. Row P8's page image binds
  the key identifier (the entry's epoch and the label) into its manifest.
- **The structural bound is the guarantee; L-MPX-OVERFLOW is restated.** A
  lookup reads the tag's home page and, only when it is full, its overflow
  page, never further (`fn-mpxt-reach`), and confirms at most 2,048
  candidates against the rows' exact Message-IDs: PRF-991
  `fn-mpxt-candidates-page-need`, for every tag, key known or not. The
  occupancy argument (a full page needs 1,024 entries where the mean is at
  most 512) now bounds only how often the fourth outcome occurs.
- **The fourth outcome.** Besides present, absent and unavailable, the index
  answers INDEX-SATURATED (`:mpx-saturated`): the home page and its
  overflow are both full (`fn-mpxt-saturatedp`), so the placement has
  nowhere to go. The placement is not made and the table keeps every
  mapping (`fn-mpxt-put-places-iff-not-saturated`,
  `fn-mpxt-add-saturated-keeps-the-table`); the served POST refuses by name
  before durable acceptance (the catalog's key-argument export at THE
  SWITCH), the health state names the rebuild. It is admission capacity,
  separate from the reader's bound, and an implementation limit stated as
  such (2,049 Message-IDs whose tags share a home page cannot be admitted
  however empty the rest is), never slipped in under D27. Under the table
  condition "no page and its successor are both full" nothing is refused.
- **Fixtures are structural**: direct tags, a home page and its overflow
  filled by 2,048 entries under one tag, an equal-tag/different-Message-ID
  exact-compare witness and a saturated-grow/refused-add witness
  (SCN-1034, concrete stobj source REPL) -- not
  claims about BLAKE3.
- **B.6, corrected**: a verdict of a concrete structure behind an abstract
  stobj needs its inputs in the logic: the saturated export takes the key
  as an argument and its logic is over the fold `fn-mpxt-build key rows`;
  the catalog's correspondence clause is that equality.

## P12 startup and physical funding join — 2026-09-30

This is the concrete next implementation contract for paged funding and
physical lifetime. It does not activate the currently unsupported resource
policy or claim full Store rescue. The coordinator selected funded supported
defaults before served recovery; an unfunded startup compatibility mode is
not part of the design. Until the join is implemented, a missing/unsupported
policy refusal is an integration frontier, not the intended default service.

The existing prelaunch path `fnn-heap-store-profile` loads the persisted
profile through `fnn-load-config`. The run path is
`fnn-operator-execute-run` → `fnn-control-owner-run-normalized` →
`fnn-owner-run` → `fnn-owner-install` → `fnn-open-live-store` → recovery.
Install the ACL2-supported policy and its permanent baseline before calling
`fnn-owner-install`; only then create native storage and start persistent
executors. The same normalized profile/policy must feed the launcher and
that installation. `cold_heap_octets` is dynamic allowance: the pool budget
and baseline also include each actual executor's stack/runtime, and the
launcher reserves those workers separately from connection threads.

The concrete APIs are `fn-owner-page-read-install-baseline`, then
`fnn-extent-pool-storage-start(F,W,9)` and `fnn-extent-executor-start(W)`.
The six physical maps are four incarnation maps at capacity F, one issued
map at W and one cache-token map at 9: the current ACL2 cache retains eight
entries and insertion may briefly retain a ninth. Capacity is normalized to
at least eight by ACL2 before native construction. The pinned runtime silently
clamps constructor capacity at 2^24; the supported configuration must reject
an unrepresentable request before allocation. Permanent backing stays charged
after removal; job completion releases a lease, not the idle thread's storage.
An executor slot is a 64-byte native object, a 32-byte waitqueue, one 16-byte
all-workers list cell and a four-cons ACL2 row. The native probe confirmed
these target object sizes. Source and hash-array measurements are recorded in
`evidence/paged-resource-pool/`; allocator assumptions remain runtime-specific.

| Default component | Concrete source / remaining boundary |
| --- | --- |
| Cache allowance | The earlier design selected 64 MiB; the durable `page-cache-octets` field remains unimplemented. It must fund actual retained representations, independently of the eight-entry work policy. |
| Worker count | A supported operational concurrency choice, funded with the exact launcher stack/runtime. The narrow native fixture uses two, not an inferred production default. |
| Descriptor capacity F | Must be bounded open descriptor slots with pinned refusal/eviction, or a proved bound from the enforced suffix and retained active generations. Do not allocate four all-history maps from total T merely to obtain a numeric bound. |
| Per-incarnation metadata | Charge the path, live map/ledger rows and observed device/inode integer representation, including bignums. F bounds concurrent open incarnations, not lifetime file IDs. Old pinned generations can prevent close, so their overlap must be bounded by the maintenance contract. |
| Incarnation after descriptor eviction | Live extent handles still need the same immutable file identity; reopening a replaced pathname or an unlinked old checkpoint is invalid. Retained physical names and their retirement need a real contract before such eviction. |
| Fresh protected read | Typed `(:discovery id file eoff elen)` lease, file held until the borrowed vector is relinquished; no fabricated integrity trailer, and no verified-cache settlement. |
| Decoder and page scratch | Charge compressed input list, input/output arrays, subsequence, decoded list and retained decoder highwater. A page adapter may simultaneously hold 2048 u64 words, 16384 bytes, and a 2048-cons word list with boxed integers. A returned list can outlive the primitive. |
| Ordinary cold extent | ELEN may pack many records, so a record size is not its bound. Current whole-extent allocation needs exact funding; a useful default otherwise requires streaming verification and requested slices/windows. No arbitrary stored-data cap substitutes for that change. |
| Ledger mutation scratch | Register/settle/remove copy list spines; baseline or per-step scratch must cover their actual bounded active cardinality and collector coexistence. |

A default is supported only after these allocations agree with profile
representation and launcher funding. Explicit offline tooling enters its own
bounded lifecycle; absence of pool state grants no offline permission to a
served read. Named prelisten refusal and a 403 response to an admitted running
service are distinct outcomes and must be tested separately.

Snapshot preparation adds another, separate contract. The private builder's
fixed page scratch and digest state can be leased before capture, and staging
growth admitted before writes, but that only establishes a safe attempt and
cleanup. Full P12 rescue requires enough resources to finish for the accepted
state: the canonical target page count cannot be inferred from wire history
bytes or record count alone because retained context and key snapshots are
encoded too. The old/new/staging/spool coexistence and dW+ before POST remain
open. Refusing midway and deleting staging is not that stronger rescue claim.


### Selected runtime startup and operational maintenance lease

PRF-1117 / SCN-1023 add the concrete bootstrap plan and explicit
A-COLD-RUNTIME boundary. The plan consumes the observed selected runtime,
actual thread-registry node cardinality and zero pending creators/corpses.
It funds the six maps, permanent executor layout plus sourced conservative
runtime margin/AVL old/new paths, and two removal-list spines for at most
F+W+9 ledger bindings. Startup must remain serialized before writer/listener
threads. `thread-source-2026-09-30.md` records the exact source hashes,
constructor inventory and observation scope. Unsupported observations refuse
before constructor arguments are returned. Native activation remains pending.

PRF-1121 / SCN-1026 add the operational attempt API:
`fn-owner-maintenance-admit(epoch,suffix-count,demand,pool)` returns a typed
`(:maintenance id epoch suffix-count)` token; `fn-owner-maintenance-grow`
reserves additional resident/disk/descriptor demand before allocation, and
`fn-owner-maintenance-release` requires definite joined cleanup with no
surviving charged aliases. The caller's demand constructor must cover actual
representations, including the13-cell source cursor and retained reversed
suffix spine; arbitrary opaque caller numbers do not establish physical
funding. The controller observes cheap source context, admits maintenance,
acquires the exact root pin, then captures exclusivity/source pointer under
the same owner mutex. Refusal unwinds leases without changing capture ticket,
Store count or publication state. A maintenance row holds worker1 throughout,
so a simultaneous page/window reader needs another funded worker slot.

The current cold-only budget has disk0. This API deliberately cannot create
staging disk credit; explicit startup maintenance disk funding must be joined.
Incremental safe-attempt growth is independent of full R>=W, whose canonical
accepted-obligation size carry and old/new/cleanup envelope remain open.

### Raw window source demand

`cold-read-window.lisp` now records the fixed raw window representation,
retained digest frame highwater, source transient cons inventory and actual
natural widths. The descriptor gate checks the full protected end plus the
32-byte trailer against the selected signed off_t ABI before a native call.
The source-model demand is unchanged between a4096-byte and a1-TiB protected
extent with the same identity widths; ELEN is never a vector capacity.
`evidence/paged-resource-pool/window-source-2026-09-30.md` states the exact
inventory and remaining caller/arithmetic joins. This source component is
unactivated; compressed backing storage is recorded separately and is not
a complete compressed-job demand. No productive default claim changes.

The raw source natural-width ceiling includes the ledger's spent ticket
successor. A successor can need a larger object at a digit/alignment boundary;
the old identity's width alone is insufficient. This correction does not
close primitive arithmetic scratch, first-use native guard-cache baseline,
actual admission integration or the full producer reserve.
