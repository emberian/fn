# The store representation: pages are the state (2026-10-01)

Coordinator synthesis after the Codex era. Inputs, all under
`build/coordinator/`: the critic's review (`codex-era-architecture-review`),
the route architects (`design-route-A-codex-skeleton`,
`design-route-B-evolve-existing`), four scouts (`scout-book-graph`,
`scout-served-runtime`, `scout-state-representation`, `scout-claim-structure`)
and three scholars (`scholar-representation`, `scholar-proof-engineering`,
`scholar-literature`), each dated 2026-10-01, plus the coordinator's own
reading of `books/store-node`, `catalog`, `msgid-pages`, `payload-arena-paged`,
`history-columns`, `page-read-pool-state`, `defrecord` and `assumptions`.

ember's charge (2026-10-01): the store is the foundation of the orthogonal
persistence of the larger system (docs/architecture.md: a persistent
event-log substrate between Robigalia systems); it must be high performance,
high quality and high assurance "via metaprogramming, proof engineering,
mechanical sympathy, and careful algorithmics and datastructures"; and a full
up-front accounting of every resource spent on a user's behalf is a founding
goal (the warranty).

## 1. What is there

- **The live state is cons structure.** `fn-sn` is a 14-position list with
  hand-written `fn-ag-car` accessor chains. One article is a positional
  held record (~4.5 KB, ~190 heap objects, ~97% traced by the collector),
  held three to four times: the store record, the catalog row
  (`fn-cat$c-rows`, `(array t)`), the history row (`fn-hist$c-rows`,
  `(array t)`) and the node lists, agreeing only by theorem. The four
  `equal` hash tables of the catalog cons a key per lookup.
- **The disk already has the right skeleton:** a copy-on-write page store
  with per-page BLAKE3 and two-slot roots, a chained log, and the keyed
  open-addressed Message-ID pages (`msgid-pages`: typed u64 words, 16 KiB
  pages, tag-then-confirm, two pages worst case, a generic indexed-access
  refinement specialised once) — all proved. `msgid-pages` is the template.
- **The boundary leaks.** `fn-pgs-fill-realize` (books/assumptions.lisp) is
  specified to return a 2,048-element list per 16 KiB page, so every page
  fill conses ~50 KiB. `raw_dispatched` is empty at dev: every served
  `fn-sn-statep`-guarded entry walks every event per call.
- **Codex's runtime skeleton** aims at the right thing (one resource ledger,
  prepaid turns, page-completion ownership) but its pool is an untyped
  stobj field holding a 5-element list, it is unrelated by theorem to the
  credit ledger and the heap figure, it gated the served path before any
  producer existed, and it rested proof on observing SBCL's collector.
  Its index-backing tree duplicates the page store's copy-on-write and
  contradicts the two-page Message-ID bound.

## 2. The target

**Pages are the state.** Typed u64 column pages plus a byte pool,
sequence-indexed; dense per-group number runs; per-group overview pools; a
fixed frame arena the collector never copies or scans; frames filled by
`pread` into the frame, so the on-disk and in-memory images are the same
bytes. About 600 octets an article on pages and no heap objects for stored
content. Open = page 0 + the log tail. Checkpoint = the dirty pages.
Snapshot = a root. A reader pins a generation; the laggard past the
retention bound is refused (LMDB free-by-generation, libmdbx ousting).
`fn-sn` becomes a root record. Persistence is not reachability over the Lisp
heap; mmap is not the cache (residency would be unaccounted and faults would
land inside ACL2 code).

**The accounting is a resource vector, prepaid, by construction.** One
ledger in one stobj, typed: resident octets, disk, descriptors, worker
slots, identity spaces, work. The precedent is seL4 untyped memory and
KeyKOS space banks: the system never allocates on its own; each request
draws on its user's bank; the owner's own needs (next image, active segment,
rescue) are reserved before any user's request; teardown is destroying the
sub-bank. Every served read's cost is the pages it touches, so the tariff
falls out of the representation. The collector's copy is the honest 2x
bound, measured as F1 evidence, never the proof.

**Index structures.** Message-ID: keep tag + confirm + two pages; replace
the next-generation rebuild with linear hashing (one page split per step
under a root-carried split pointer; INN's dbz is the precedent).
(group, number) -> seq: dense per-group runs, 8 octets a membership.
No cell holds a page number (region-relative references); the cache is one
stationary u64 array.

**Crash story.** One recovery-refinement theorem composing the log's and the
page store's cut models; KeyKOS's format-time reserve of two image
generations sized by the suffix bound K.

## 3. How it is built: generators, generic theories, instances

From the proof-engineering scholar's inventory (counts at dev b34835bd4):

| generator | replaces |
|---|---|
| `def-loop` | 494 hand loop twins, 850 equivalence inductions (~13k lines) |
| `def-representation` (+ `def-buffer`), promoted from `books/proto/adt` | 285 hand abstract-stobj obligations (~5.8k lines); checks the attachment trap at expansion |
| `def-carried` | 27 carried-invariant books (10k lines); derives D40's raw-dispatch rows |
| `definterface :operation` + a resource-monoid theory | Codex's 46 accounting books; per entry: tariff, charge-before-effect, settle-once, bound, dispatch row, teeth |
| `defkeystone` v2 | 3,272 hand must-fails (20-28% of tests/acl2) |

One library theorem per shape, instances by functional instantiation; the
community std/fty patterns imitated, not included (2026-09-20 ruling);
`def-ruleset` adopted.

## 4. Order

0. **Restore a serving node on dev** (both routes' M0): undo the eight
   served-path breaks the runtime scout confirmed (bootstrap gate, page pool
   never installed, mux returns before writing, response unpin fenced, POST
   precheck needing `:absent`, the auth start hook, the consumer-position
   reconfigure preflight, cold-read admission); fix the 341 old-arity record
   calls or revert the acceptance-binding field (ember's call); one image,
   the native matrix green on init/POST/read/restart.
1. **`def-loop` and `def-representation`** first — every later stage is
   instances of them.
2. **The page-word boundary:** `fn-pgs-fill-realize` fills a frame in place
   (a stobj array), not a list; the Message-ID scan returns fixnum words.
3. **The paged catalog behind `attach-stobj fn-cat`** (zero-copy fill;
   no dependent recertifies).
4. **Dense per-group number runs and overview pools** replacing the `equal`
   hash tables.
5. **History and node lists on the same rows;** `fn-sn` a root record;
   D40 raw dispatch over the carried invariants (`def-carried`).
6. **The resource vector** as one typed ledger (Codex's pool/PIO reused as
   the frame-ownership layer), `definterface :operation` charging every
   entry, the credit ledger and heap figure related by theorem and retired.
7. **Linear hashing** for the Message-ID table; the two-generation checkpoint
   reserve; the recovery-refinement theorem.

A serving node after every stage.

## 5. Decisions (RATIFIED by ember 2026-10-01 ~late evening: "inclined to take your recommendations")

- History: P3 rows (this design) over Codex's dense history epoch. RATIFIED.
- The acceptance-binding record field: REVERTED in stage 0 (back to the
  11-argument record); re-done once later as the relay-v1 subject binding,
  as typed words, not a 48-octet list. RATIFIED.
- CRC-0 BP primaries: the refusal is REVERTED (dtn7-rs interop). RATIFIED.
- The FN-RCL2 tombstone: KEPT as deliberate; a decision row records it. RATIFIED.
