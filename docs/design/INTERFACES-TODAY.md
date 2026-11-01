# fn interfaces today (origin/dev = 3bbfc4dca)

What each component of fn exposes **as it exists at origin/dev 3bbfc4dca**, so fn2 can be
rebuilt bottom-up against written-down boundaries. Every claim cites `path:line` at
that commit (paths relative to the fn repo root; read with
`git -C ~/dev/fn show origin/dev:<path>`).

## Method and what the numbers mean

- The tree was extracted with `git archive origin/dev books host` and parsed by a
  small s-expression reader (top-level forms, recursing into `encapsulate`/`progn`/
  `defsection`/`local`/`mutual-recursion`). Scripts and their outputs are kept in the
  explorer scratchpad `/private/tmp/claude-501/-Users-ember-dev-minidregg/d0d33f7b-1304-4ad3-96f2-1735fa3775b2/scratchpad/tools/`
  (`forms.py`, `comp.py`, `ifc.py`, `report.py`, `cmap.py`, `group18.py`);
  they are cheap to rerun (~10 s).
- **code** = non-blank, non-`;` lines. **exec** = code lines inside an executable
  definition form (`defun`, `defund`, `define`, `defmacro`, `defconst`, `defstobj`,
  `defabsstobj`, `defexec`, ...; `defun-nx` excluded). **thm** = code lines inside
  `defthm`/`defthmd`/`defrule`. The remainder (code - exec - thm) is `in-theory`,
  `include-book`, `verify-guards`, macro-generated events (`defrecord`,
  `deftransition`, `definterface`, ...), tables.
- A component is a set of books chosen by file-name glob (`tools/cmap.py`); 229 of the
  1,434 books fall outside the 17 named components (DSL/def-* macros, image-world,
  entries-*, native-control, store-node/export/import, anchor, control, CBOR, ...)
  and are reported under "other" where they matter.
- **Host-declared entries** are the `definterface` forms: 1,934 forms, 1,916 distinct
  names (the parser's count; a plain `grep` of `(definterface NAME` sees 1,919 tokens, counting words in
  comments such as `name`, `:delegates`, `refuses`) (1,018 in `host/interfaces.lisp`, 14 in the generated `host/interfaces-raw.lisp`,
  the rest in the ACL2-mode host files `host/*-host.lisp`). A **raw call site** is an
  occurrence of the entry's name in non-`;` text of `host/native/*.lisp` (docstrings included, so a
  count can be high by the odd mention) (the raw
  Common Lisp host), which calls entries through `fnn-call` (`host/native/io.lisp:1578`)
  and its wrappers with a quoted symbol.
- "Stobjs threaded" are read from each definition's `(declare (xargs :stobjs ...))`.
- Whole tree: 1,434 books, 497,144 code lines, of which 160,196 exec and 297,179 thm;
  21,489 executable definitions, 36,552 theorems.

## Findings in one screen

- The host boundary is **1,916 entries wide and almost never deep**: 1,271 entries have one raw call
  site, the maximum is 22 (`fn-octets$c-reserve`), and the most-called entries are accessors and
  exit-code projections (section 18).
- The narrow, proved kernels exist (TCPCL session 7, `fn-hist` 5, `fn-hrecs` 8, `fn-mlh` 12, host
  lease 7, served step 6, acceptance 3, injection 4, consumer position 8, BP outbound 1x7), but the host
  reaches most of them through wide `:program` wrapper layers over ACL2 state globals: the owner
  (371 entries, a 15-field record in global `fn-owner` plus 106 more `fn-owner-*` globals), the store
  node (64), the BP step tower (364) (sections 10, 1, 15, 20).
- Bytes cross the boundary as cons lists by default: 486 `fnn-octet-list` sites in 39 raw files; the
  array paths are the octet buffer `fn-octets` (13 exports, 16 congruent clones), the arena, the page
  store's `pgs-mem` and `fn-rtc-st` (sections 7, 3, 9).
- Planned or proved machinery not wired to the host: the runtime-contract POST transaction `fn-ptx-*`
  (0 host references), the paged checkpoint (model only), the owner scheduler `fn-osch-*` (comments
  only), the owner carrier stobj `fn-owner-st` (referenced by the raw host, defined nowhere). The
  runtime contract has exactly two executable instances (echo, host lease).
- The include graph is one strongly connected tangle at component level; at book level the store spine
  is inverted (file kernel includes the history stobj) and the owner is the hub (section 19).
- No `fn-cs-*` consumer prefix exists; 9 raw-dispatched entries have no `definterface` (section 18a).

## 1. Byte store crash model and the file kernel

**Size.** 32 books (`byte-store*.lisp`, `store-files*.lisp`), 17,539 code lines, **2,893 exec**,
13,597 thm; 443 definitions, 1,149 theorems. Largest: `byte-store-record-provenance-bytes`
(2,604 code, 0 exec), `byte-store-scan` (2,336 / 270), `byte-store-record-provenance-node`
(2,011 / 0), `store-files` (952 / 512), `byte-store-frame` (872 / 409), `byte-store-programs`
(559 / 402). It is a proof component: 84% of its lines are theorems.

### 1a. The byte model (`fn-bs-*`, books/byte-store.lisp)
- Purpose: inodes + directories + an ordered PENDING list; fsync drains one inode's or
  one directory's pending ops; a crash lands an arbitrary torn subsequence; every
  syscall takes an environment OUTCOME (EIO/ENOSPC explicit, fsyncgate)
  (`books/byte-store.lisp:1-14`). Logic only: "the recognizer, the view, the fences, the
  crash and every syscall are withdrawn at the end" (`books/byte-store.lisp:28-31`).
- State: a list `(:byte-store unit inodes dirs pending next-ino)`
  (`books/byte-store.lisp:39-45`, constructor `fn-bs-make` `:77`): `unit` posp write unit;
  `inodes` alist ino -> **octet list** (durable content); `dirs` alist dir-id -> (alist
  name -> ino|dir-id); `pending` op list in issue order; `next-ino` natp.
- Operations (all pure, state in / state out, no stobjs):
  `fn-bs-create s dir name outcome` (`:527`), `fn-bs-write s ino offset octets outcome`
  (`:544`), `fn-bs-fsync-file s ino outcome` (`:564`), `fn-bs-fsync-dir s dir outcome`
  (`:578`), `fn-bs-link s sdir sname ddir dname outcome` (`:595`), `fn-bs-rename` same
  formals (`:616`), `fn-bs-unlink s dir name outcome` (`:630`), `fn-bs-mkdir s parent name
  id outcome` (`:644`), `fn-bs-read s ino` (`:659`), `fn-bs-crash s choices` (`:503`),
  views `fn-bs-view`/`fn-bs-content`/`fn-bs-names` (`:326-338`), fences
  `fn-bs-fence-file`/`fn-bs-fence-dir` (`:388`, `:399`). Ten syscalls + crash + view.
- Programs over the model (books/byte-store-programs.lisp): a program is a list of steps
  (syscall, an fn-sf event, or `:cut`) (`:4-10`); `fn-bs-step bs ks step outcome groups
  capacity` (`:89`), `fn-bs-run bs ks steps outcomes groups capacity` (`:133`), and the
  transcribed host sequences `fn-bs-frontier-program`, `-record-program`,
  `-finish-program`, `-recover-program`, `-init-program`, `-workflow-program`,
  `-receipt-program`, `-inbox-program` (`:163-546`). These are the specification of the
  host's syscall order, checked by D1-D5 disciplines (`:25-28`), not called at run time.
- Bytes: `octets` in `fn-bs-write` and inode content are ACL2 octet lists.
- The only two host-declared entries in this component are metadata codecs in
  `books/byte-store-frame.lisp` (frontier = CBOR uint in an FNSM frame; profile = a
  frame-field record, `:1-9`): `fn-bs-config-encode (values)` (`:991`, decl
  `host/interfaces.lisp:622`, 1 raw site in io.lisp) and `fn-bs-profile-resolve (request
  current)` (`:1115`, decl `host/interfaces.lisp:2872`, 1 site in heap.lisp).

### 1b. The file kernel (`fn-sf-*`, books/store-files.lisp)
- Purpose: allocator replacement, one-file transaction publication, crash choices, the
  completion gate, recovery barriers; it does not model POSIX (`books/store-files.lisp:1-7`).
  The host drives it only through the `fn-sn` composition (`:9-11`).
- State: `(:store-files phase frontier frontier-candidate RECORDS record-candidate
  completion-pair SUCCESSES recovery-barriers)` (`:57-58`; accessors `:82-121`,
  constructors `fn-sf-make` `:136`, `fn-sf-make-fields` `:129`). RECORDS and SUCCESSES are
  snoc-lists; RECORDS may be BASED `(:hrs-based HANDLE . SNOC)` naming a committed
  history image (`:59-76`).
- Operations: one dispatcher `fn-sf-dispatch s event groups capacity`
  (`books/store-files-traces.lisp:120`) over 17 events: `:start-frontier :frontier-file
  :frontier-replace :frontier-dir :refuse-reservation :prepare-record :record-file
  :prepublish-abort :abort-completion :record-link :record-dir :core-completion
  :emit-success :lose-success :crash :recover :recovery-barrier`
  (`books/store-files-traces.lisp:121-160`), each a `fn-sf-<event>` transition in
  `books/store-files.lisp:686-1135`. Plus `fn-sf-initial-state` (`:678`), `fn-sf-statep`
  (`:667`), crash-image predicates `fn-sf-crash-imagep s frontier records` (`:1025`).
- Composition: `fn-sn` record (books/store-node.lisp:32-35) =
  `(groups capacity files node keyring index keyring-generation verdicts
  historical-keyring-snapshots identity-next-sequence config-history consumer-projection
  topic-projection derived-event-index)`; `fn-sn-io s operation result` (`:1469`) steps the
  files kernel and the node together.
- Who calls: no host entry names `fn-sf-*`/`fn-bs-*` directly (beyond the two codecs).
  The host reaches the kernel through 24 `fn-store-sn-*` wrappers in
  `host/store-node-host.lisp` (64 declarations in that file), all `:program` mode,
  holding the composed record in the state global `fn-store-sn`
  (`host/store-node-host.lisp:1450-1462`). Each has 1-3 raw call sites, all in
  `host/native/io.lisp`. The POST entry: `fn-store-sn-prepare (msgid-octets payload
  group-codes id-octets subject-octets evidence-octets charge observation fn-arena state)`
  -> `(mv nil KEYWORD-or-(:seal OCTETS) fn-arena state)` (`:1480-1538`), stobjs
  `fn-arena state`, every byte argument guarded `fn-cbor-octet-listp`. Others:
  `fn-store-sn-io (operation result state)` (`:1450`) returns the files phase,
  `fn-store-sn-finish (state)` (`:1629`), `-known-abort` (`:1588`),
  `-refuse-reservation` (`:1547`), `-lookup (msgid-octets fn-arena fn-hist state)`
  (`:1721`), `-recover-rows`/`-recover-from-checkpoint (rows frontier config-octet-records
  state)` (`:597`, `:896`).
- Includers: 59 include-book edges from other components (22 from "other", 8 checkpoint,
  8 config, 7 BP, 4 owner, 3 log); host files `host/store-host.lisp` (byte-store-frame,
  byte-store-txn-name) and `host/store-node-host.lisp` (byte-store-state-checkpoint-program).

## 2. The log kernel

**Size.** 40 books (`store-log*.lisp` 32, `frame*.lisp` 8; the glob also catches
`books/log-sink.lisp`, the diagnostic log sink, counted here): 17,086 code lines,
**3,860 exec**, 11,616 thm; 589 definitions, 1,627 theorems. Largest:
`store-log-recover-copy` (2,470 / 452 exec), `store-log-durable` (1,317 / 176),
`store-log` (1,284 / 263), `store-log-buffer` (1,243 / 278), `store-log-kernel-concrete`
(700 / 314).

- Purpose: one append-only inode per segment holding FNLG frames, each padded to the write
  unit, whose payload is the previous entry's 32-octet trailer (the chain) then a chunk
  (kind 1: one FNST record frame; kind 2: >=2 records each after a 4-octet length); the
  scan from the front is the only name of the durable history (the frontier)
  (`books/store-log.lisp:1-22`). Keystones `fn-lg-scan-of-log-append`,
  `fn-lg-scan-of-torn-entry` (`books/store-log.lisp:24-40`).
- **State (what the host holds).** The concrete kernel, a list
  `(:lgc COUNT LAST FRONTIER NEXT-TXID BATCH INFLIGHT ACKED PHASE)`
  (`books/store-log-kernel-concrete.lisp:15-16`, `fn-lgc-make` `:485`, accessors `:489-496`);
  it refines the logical `(:lgk COMMITTED LAST FRONTIER ...)` by `fn-lgc-of` (`:4-5`, `:499`;
  keystone `fn-lgc-run-refines-the-kernel` `:26`). The host keeps it in the `kernel` slot of
  the raw struct `fnn-log` (`host/native/io.lisp:7512-7545`: `path fd kernel unit max extent
  count octets bmax omax pending reserved index genesis lock sealed sync-state sync-cv ...`),
  mutated only under the struct's mutex because the syncer thread fences concurrently
  (`:7533-7538`).
- **Exported operations (host-declared, 76 in this component).** The kernel transitions, all
  pure on `c`, no stobjs:
  `fn-lgc-take (c record txid count octets bmax omax unit)` -> `(:full|:taken|:refused c' entry-octets)`
  (`books/store-log-kernel-concrete.lisp:589`; 4 raw sites), `fn-lgc-t-prepare (c record)`
  (`:518`), `fn-lgc-append-admitsp/-append-octets/-append (c unit [extent])` (`:540`, `:526`,
  `:546`), `fn-lgc-fence (c unit)` (`:558`), `fn-lgc-fence-failed (c)` (`:567`; 12 raw sites,
  the most-called log entry), `fn-lgc-finish-one (c)` (`:573`), `fn-lgc-consume-to (c txid)`
  (`:581`), rotation `fn-lgc-rotate-admitsp/-rotate-needed-p (c)` (`:605`, `:612`),
  `fn-lgc-rotation-octets/-rotate (c k unit)` (`:650`, `:657`), extension
  `fn-lgc-extension-needed-p/-target (c extent unit)` (`:668`, `:672`), observers
  `fn-lgc-count/-last/-frontier/-next-txid/-acked/-phase (c)`.
  Open/stream (`fn-lgw-*`, books/store-log-stream.lisp, store-log-walk-once.lisp,
  store-log-buffer.lisp): `fn-lgw-start (genesis floor)` (`store-log-stream.lisp:89`), the
  in-place step `fn-lgw-step-buf-count (st unit max extent fn-octets)` stobj `fn-octets`
  (`store-log-buffer.lisp:1517`; the host preads an entry into the octet buffer
  `fn-octets-lg` and ACL2 decides it by index, `store-log-buffer.lisp:14-21`),
  `fn-lgb-next-record (i pos extentp fn-octets)` (`:1427`), `fn-lgw-kernel (st)` (hands the
  kernel to the host, `store-log-stream.lisp:288`). Segments `fn-lgs-*` (names, open plan,
  next segment, `store-log-segments.lisp:64-361`); lineage `fn-lgl-*`
  (`store-log-lineage.lisp:68-120`); damage/repair verdicts and texts `fn-lgdm-*` (15 entries,
  `store-log-damage.lisp:118-701`); read-only probe scan `fn-lgo-*`
  (`store-log-open-scan.lisp:118-1181`, called from `host/native/heap.lisp`); recovery copy
  `fn-lgrc-copy-verdict (free need)` (`store-log-recover-copy.lisp:1553`).
- **The acknowledge keystone.** `fn-lgu-acknowledge (c n)` (`books/store-log-durable.lisp:1104`)
  = `fn-lgc-host-run c (fn-lgu-finishes n)` in logic, an `n`-fold `fn-lgc-finish-one` in exec
  (`:1095-1108`); the host calls it once per COMPLETE (`host/native/io.lisp:8340-8346`, 2 raw
  sites). KEYSTONE `fn-lgu-acknowledge-acknowledges-only-recoverable-records`
  (`books/store-log-durable.lisp:1171`): every acknowledged record is recovered from every
  admissible crash image of every cut of the host's run of the active segment; scope one
  segment, no rotation (`:1-19`, `:43-47`). `fn-lgu-log-max (r)` (`:406`) and
  `fn-lgu-take-verdict (record max)` (`:410`) are its other host entries.
- **Byte representations.** Records in `fn-lgc-take` are octet lists (the host converts with
  `fnn-octet-list`, `host/native/io.lisp:9487`); a segment read at open goes through the
  stobj `fn-octets-lg` (array buffer) in the streaming walk; the logical `fn-lgc-open (s
  genesis unit max floor)` takes the segment as a **string** (`:guard (stringp s)`,
  `books/store-log-kernel-concrete.lisp:686-687`) and is not the path the host runs (the host
  opens through `fn-lgw-start`, `host/native/io.lisp:7898`). Rotation and append octets come
  back as octet lists the host writes with `fnn-log-pwrite fd offset octets`
  (`host/native/io.lisp:7599`).
- **Who calls.** Raw host: `host/native/io.lisp` almost exclusively (`fnn-log-*` around
  `:7583-8346`), `host/native/heap.lisp` (open-scan probe), `host/native/owner.lisp` (2 sites:
  `fn-lgc-rotate-needed-p`, `fn-lgs-next-segment`). ACL2 host files that include log books:
  `host/store-host.lisp` (10 log books), `host/checkpoint-host.lisp` (store-log-reclaim),
  `host/interfaces.lisp` (6). Books: 109 include-book edges from other components (57 from
  "other", 14 BP, 6 checkpoint, 5 owner).

## 3. The page store (pages, roots, digests, reclaim/gc) and the page-read machinery

**Size.** 85 books in the bucket, 25,439 code lines, **7,325 exec**, 16,679 thm; 1,137
definitions, 2,119 theorems. It is five things under one glob; by sub-family:

| family | books | code | exec | what |
|---|---|---|---|---|
| `pagestore*` | 18 | 10,015 | 2,201 | the CoW page store `pgs-` (model, exec, gc, digest cursor) |
| `page-read-*`, `page-window-*`, `page-file-*`, `page-discovery`, `page-executor` | 20 | 3,650 | 1,312 | the read pool: direct/cold/window page reads by worker threads |
| `cold-*`, `decoded-*`, `extent-*` | 23 | 3,088 | 1,400 | cold-read windows, decoded windows/workers, extent window stream, extent retire |
| `heap-*`, `idle-collection` | 8 | 3,487 | 1,194 | memory figures, heap reservation, the `store ROOT VERB` heap command, idle GC |
| `reclaim*`, `store-reclaim*`, `store-sweep` | 16 | 5,199 | 1,218 | content reclamation (retention rule + holders), chunked reclaim walk |

### 3a. The page store `pgs-` (books/pagestore*.lisp)
- Purpose: the owner's snapshot as a page store with copy-on-write commits (LMDB shape): dirty
  pages to fresh space, then the page table, then one commit record into the root's other
  slot; FORK = new root sharing pages (`books/pagestore.lisp:1-13`). Two layers sharing the
  decisions: a MODEL over `pages`/`roots` with the constrained digest seam `pgs-digest`, and an
  EXECUTABLE over a stobj of u64 words that the host fills/drains with two primitives
  (`:15-38`). Named boundary A-PGS-OBSERVE (prototype, not theorems) and A-CRYPTO
  (`:40-55`).
- Model operations (pure): `pgs-open disk r mode` (`books/pagestore.lisp:330`),
  `pgs-roots disk` / `pgs-root-slots r disk` (`:325-326`), `pgs-alloc n m alloc` (`:492`),
  `pgs-plan-commit disk r mode dirty alloc` (`:610`), `pgs-commit disk r mode dirty alloc`
  (`:679`), `pgs-fork disk r r2 mode` (`:700`), `pgs-crash disk r writes keep k slot-value`
  (`:671`). Keystones `pgs-open-after-commit`, `pgs-open-after-crash`, `pgs-fork-isolation`
  (`:22-26`).
- Executable state: stobj `pgs-mem` with six resizable `(unsigned-byte 64)` arrays `pgs-w
  pgs-m pgs-t pgs-d pgs-v pgs-tv`, 16 KiB pages (`*pgs-page-words*` = 2048)
  (`books/pagestore-words.lisp:35-44`); octet scratch `fn-octets-pg`; gc stobj `pgs-gc`
  (mark flags `pgs-gm`, free flags `pgs-gf`, scratch `pgs-gs`;
  `books/pagestore-gc.lisp:9-16`, `:48`); digest stobj `pgs-digest-state`
  (`books/pagestore-digest-cursor.lisp:6`).
- Executable operations (stobjs `pgs-mem fn-octets-pg`): `pgs-x-commit (lpages n txid alloc
  slot ...)` -> `(mv RESULT pgs-mem fn-octets-pg)` (`books/pagestore-exec.lisp:2244`), split
  as `pgs-x-commit-prepare` (`:2135`) / `pgs-x-commit-apply` (`:2212`);
  `pgs-x-open-dir rec ...` (`:1719`), `pgs-x-open-page i txid mode ...` (`:1843`),
  `pgs-x-read i off ...` (`:1874`), `pgs-x-read-rec`/`pgs-x-write-rec` (`:1621`, `:1660`),
  `pgs-x-commit-durable lpages pgs-mem` (`:2643`), `pgs-x-fill sel a ws pgs-mem` (`:1538`),
  `pgs-x-grow`/`-grow-image` (`:751`, `:2623`). GC: `pgs-g-mark-run`, `pgs-g-mark-words`,
  sweep step, `pgs-g-install` (`books/pagestore-gc.lisp:17-37`).
- **Who calls.** The host declares exactly one `pgs` entry, `fn-pgs-frame-len`
  (`host/interfaces.lisp:3785`), read by the raw fill primitive `fn-pgs-fill-frame (file addr
  sel base pgs-mem)`, which the raw host DEFINES (`host/native/extent.lisp:2018-2051`: one
  pread, 2048 LE words into the selected array) under assumption book
  `books/assumptions-pgs-host-io.lisp`. Everything else in `pgs-x-*` is called from books:
  `pgs-x-commit` from `history-pages`, `history-image-snapshot`, `paged-checkpoint-image`,
  `pagestore-refine`; `pgs-mem` threads through 46 history-image/history-pages/paged-checkpoint
  books. So the page store is the substrate under sections 6 and 8, not a host boundary.
- Bytes: page content is u64 words in `pgs-mem`; octets appear only in `fn-octets-pg` and the
  digest (BLAKE3 over the words' LE octets, keystone `pgs-x-words-digest-is-blake3`,
  `books/pagestore.lisp:42-45`).

### 3b. Reclaim
- `books/store-reclaim.lisp:1-25`: the decision `fn-rcl-reclaimable` (retention rule +
  every holder: reader pin, consumer cursor, outbound feed, BP obligation), the tombstone
  `fn-rcl-tombstone-of`, and `fn-rcl-reclaim-state`.
- Live pass: three chunked passes over the generation-pinned history root
  (`books/reclaim-chunked-walk.lisp:1-20`), carried accumulator stobj `fn-rcwacc` with one
  field `fn-rcwacc-acc` (`:681-682`). Host entries: `fn-rcwacc-init (configs fn-rcwacc)`
  (`:688`), `fn-rcwacc-finish (fn-rcwacc)` (`:692`), `fn-rcwacc-canon-step (configs chunk h
  fn-arena fn-rcwacc)` (`:711`, declared raw in `host/interfaces-raw.lisp:37`),
  `fn-rcwacc-predict-step (configs chunk h fn-rcwacc)` (`books/reclaim-chunked-seal.lisp:343`),
  all called from `host/native/owner.lisp` (1-2 sites each).

### 3c. Page-read machinery and heap
- The read pool's state is the stobj `fn-page-read-pool` (`books/page-read-pool-state.lisp:6`:
  `fn-prp-data fn-prp-mode fn-prp-incoming-slot fn-prp-alloc-installation fn-prp-alloc-mode
  fn-prp-alloc-epoch ...`); window workers `fn-page-window-workers`, `fn-pww-*`
  (`books/page-window-worker-storage.lisp:13-41`); decoded job `fn-decoded-job`
  (`books/decoded-worker-job.lisp:6`); extent window buffers `fn-ew-buffer`/`fn-ew-span`
  (`books/extent-window-buffer.lisp:13`, `books/page-window-span.lisp:16`).
- Host entries (88 in the bucket): most-called `fn-owner-page-read-ledger (fn-page-read-pool)`
  (`books/page-read-pool-state.lisp:22`, 8 raw sites in extent.lisp) and `fn-pwx-boundp
  (ledger w token phase)` (`books/page-window-executor.lisp:30`, 8); `fn-pio-*` direct
  admission/cancel/complete (`books/page-read-direct.lisp:80-208`,
  `books/page-read-ownership.lisp:27-58`); `fn-prstartup-*` (9); `fn-heap-*` (23, mostly
  1-site decisions for `host/native/heap.lisp`, `mux.lisp`, `operator.lisp`), headed by
  `fn-heap-command-decide` with 17 formals (`books/heap-command.lisp:392`). Raw callers:
  `host/native/extent.lisp`, `extent-decoded.lisp`, `heap.lisp`, `owner.lisp`, `mux.lisp`.
  ACL2 host files: `host/page-read-host.lisp`, `page-window-executor-host.lisp`,
  `page-decoded-window-host.lisp`, `page-executor-host.lisp`, `page-file-lease-host.lisp`,
  `page-window-lease-host.lisp` (one per executor surface).
- Includers: 165 include-book edges from other components (111 "other", 14 owner, 7 peering).

## 4. The catalog

**Size.** `catalog*` 25 books, 13,747 code, **3,102 exec**, 9,366 thm (434 defs, 1,334 theorems);
with the record shapes it stands on (`records*`, `held-*`, 15 books, 4,232 code / 1,073 exec)
the bucket is 40 books, 17,979 code, 4,175 exec. Largest: `catalog-logic` (4,854 / 1,054),
`catalog-paged` (3,042 / 723), `records-canonicality` (1,311 / 22), `catalog-live-links`
(1,126 / 137).

- **The generic.** `books/catalog.lisp` (246 lines) includes `catalog-paged`, does
  `(attach-stobj fn-cat fn-cat-paged)` (`:14-15`) and introduces the attachable abstract stobj
  `fn-cat` (`:17-48`), foundation `fn-cat$c`, recognizer `fn-cat-p` (logic `fn-cat$ap`),
  creator `create-fn-cat`, correspondence `fn-cat$corr-w`. The logical value is the committed
  history: a true list of held records, oldest first, sequence = position
  (`books/catalog-logic.lisp:4-6`).
- **The 23 exports, exactly** (`books/catalog.lisp:22-46`; logic `fn-cat$a-*` signatures from
  `books/catalog-logic.lisp:415-520, 4161`; every one threads stobj `fn-cat`, the `:protect t`
  ones are the five mutators):

| export | args | logic meaning (`catalog-logic.lisp:20-45`) |
|---|---|---|
| `fn-cat-count` | — | `(len C)` |
| `fn-cat-at` | seq | `(nth seq C)` |
| `fn-cat-msgid-seqs` | msgid | sequences of rows carrying that Message-ID, ascending |
| `fn-cat-group-number` | group n | first row binding (group . n), or nil |
| `fn-cat-group-next` | group | 1 + group high |
| `fn-cat-group-count` | group | rows in group |
| `fn-cat-total-octets` | — | retained octets |
| `fn-cat-visible-at` | seq v | row below version v and not withdrawn by v |
| `fn-cat-group-live-count` / `-live-low` / `-live-high` / `-raw-low` | group | live summary |
| `fn-cat-live-next` / `fn-cat-live-prev` | group k | least live number above / greatest below k |
| `fn-cat-horizon` | — | withdrawal horizon |
| `fn-cat-commit` (protect) | h | append `(fn-cat-assign h C)`: numbers assigned from groups' nexts |
| `fn-cat-withdraw` (protect) | target by | mark withdrawn; first cancel wins |
| `fn-cat-redecide` (protect) | seq context | replace the row's context |
| `fn-cat-clear` (protect) | — | nil |
| `fn-cat-withdrawn-at` | w | rows withdrawn at version w |
| `fn-cat-clear-keyed` (protect) | key | clear under a key |
| `fn-cat-msgid-saturatedp` | key msgid | Message-ID table refusal (no unplaced rows on the served path) |
| `fn-cat-index-health` | key | index health |

  18 readers, 5 writers (the `:protect t` exports commit, withdraw, redecide, clear,
  clear-keyed, `books/catalog.lisp:37-42`).
- **catalog-logic.** The reference foundation `fn-cat$c` (`books/catalog-logic.lisp:527-548`):
  `rows (array t)`, `count`, `mpx` (nested `fn-mlh`, the linear-hashing Message-ID table),
  `numbers` (hash (group . number) -> seq), `groups` (hash group -> (count . next)), `octets`,
  `lives` (group -> (count low . high)), `hz` (horizon), `wbv` (version -> rows withdrawn),
  `unplaced`, `raws` (group -> least raw-kept number). Its role now: "the correspondence
  reference, never the generic's executable foundation" (`books/catalog.lisp:1-5`).
- **catalog-paged.** The executable foundation `fn-cat$p` (`books/catalog-paged.lisp:116-143`):
  `rows : fn-crow` (typed columns + byte pool from one `def-representation`, `:101`),
  `tab : fn-cat$c` nested whole (its rows array repurposed as overflow), `dm : fn-dmap`
  (dense per-group runs: numbers + live next/prev links, `books/catalog-dense-map.lisp:627`),
  `wbv` (binary trie), `ovf` (overflow rows), `olen`. Abstract stobj `fn-cat-paged`
  (`:3739`) with the same 23 exports renamed `fn-cat-paged-*`. Proof by simulation of the
  old foundation on the view (`:38-46`).
- **The held row (15 fields).** `fn-held-make sequence txid generation msgid payload groups
  obligation-id content-subject release-evidence charge stamp facts context numbers
  withdrawn` (`books/held-record.lisp:139-160`): the 11 wire positions of `fn-record-p` with
  `payload` replaced by an arena HANDLE (`fn-payload-handle-p`), plus `facts` = `fn-hf (octets
  body-start body-lines control)` (`:40-50`; the NOV column `fn-hnov (tomb ok subject from date
  msgid references)` rides as the 4th element of `control`, `:52-79`), `context` = `fn-hc
  (verdict delta generation)` (`:105-114`), `numbers` ((group . n) ...), `withdrawn` nil |
  (at . by) (`:7-15`). In the paged columns: `seq txid gen charge stamp payload` as u64,
  `msgid` octets in the pool, `wpres wat wby`, `aux` (the remainder as one tree,
  `store-tree-codec`), `nums` (`books/catalog-paged.lisp:12-29`).
- **Bytes.** Message-IDs: strings in the logic (`fn-record-msgidp`), octets in the paged pool;
  the payload never lives in the catalog (a handle into the arena, section 7). The three
  metadata identities are `fn-record-metadata-bytes-p`.
- **Who calls.** No raw host site names a `fn-cat-*` export (0 of 23); the raw host holds the
  stobj from the live state's user-stobj alist (`host/native/io.lisp:455`, `:528`) and passes
  it to 15 host-declared entries that thread `fn-cat`, all in `host/owner-host.lisp`
  (e.g. `fn-owner-post-boundary (msgid-octets payload-length group-count charge fn-cat state)`
  `:2853`, `fn-owner-finish-identity (fn-arena fn-cat fn-hist state)` `:3045`,
  `fn-owner-chunk-span (id start end sched fn-octets fn-arena fn-cat state)` `:5428`),
  `host/history-root-host.lisp` (`fn-owner-orcp-load-catalog-begin/-chunk`, `:297`, `:304`),
  `host/native-live-status-host.lisp:77`, and `books/served-query-plan.lisp:144`. Books using
  exports: `fn-cat-count` 35 books, `fn-cat-commit` 23, `fn-cat-at` 20, `fn-cat-withdraw` 14,
  `fn-cat-visible-at` 12. 12 ACL2 host files include `books/catalog.lisp` (D61 attach order).
  The bucket's own host-declared entries are 3 record-string codecs
  (`books/records-shape.lisp:135`, `:175`; `books/records-stamp.lisp:6`).

## 5. The message-id index (`fn-mlh`)

**Size.** The `msgid*` family is 12 books, 6,662 code, **1,819 exec**, 4,556 thm (254 defs, 770
theorems); largest `msgid-linear-exec` (2,333 / 568) and `msgid-pages-exec` (2,227 / 540, the
flat predecessor `fn-mpxt`, still the specification walk). The glob `index-*` also matched 26
books (3,936 code, **3,506 exec, 251 thm**) that are a different thing: the owner's
index-reader request/backing/connection-repin machinery (`fn-irr-`, `fn-irq-`, `fn-ira-`,
`fn-ibp-`, `fn-ich-`, `fn-icr-`; e.g. `books/index-reader-request.lisp:1-3` "Registered
producer request vocabulary and its actual range controller"). It is 89% unproved executable
code; none of its 215 functions is named by the raw host; 25 are named by ACL2 host files
(`host/index-reader-request-host.lisp`, `host/index-connection-repin-prepare-host.lisp`,
`host/receiver-repin-source-host.lisp`), which carry 0 `definterface` forms.

- **State.** Three nested stobjs (`books/msgid-linear-exec.lisp:118-142`): a page `fn-mlg`
  (`fn-mlg-w`: array of 2,048 `(unsigned-byte 61)` words, 1,024 slots in two columns: TAG in
  word J, SEQ+1 in word 1024+J); a table page `fn-mlt` (`fn-mlt-pg`: resizable array of
  `fn-mlg`, up to 64); the table `fn-mlh` with fields `dir` (array of `fn-mlt`), `pages`, `n`
  (round modulus), `s` (split pointer), `count`, `key` (32 octets, the keyed-BLAKE3 key), `stuck`.
  Geometry and growth: one page per split, directory 256 wide and doubling
  (`:7-21`); tag = keyed BLAKE3 word reduced to 60 bits, floored at 1 (`:25-28`).
- **Operations** (all thread `fn-mlh`): `fn-mlh-tag (msgid key)` (pure, `:91`),
  `fn-mlh-tag-of (msgid fn-mlh)` (`:599`), `fn-mlh-candidates (tag fn-mlh)` -> list of seqs
  (`:936`), `fn-mlh-seqs (msgid rows fn-mlh)` = confirm candidates against rows (`:965`),
  `fn-mlh-put (tag seq fn-mlh)` (`:1405`), `fn-mlh-split (fn-mlh)` (`:1896`),
  `fn-mlh-add (tag seq fn-mlh)` = put + at most one split (`:2354`), `fn-mlh-saturatedp (tag
  fn-mlh)` (`:1392`), `fn-mlh-reserve (pages fn-mlh)` (`:320`), `fn-mlh-clear (fn-mlh)`
  (`:2423`), the fold `fn-mlh-build-from (i u rows fn-mlh)` (`:2508`) / `fn-mlh-build-tail`
  (`:2873`). Abstraction `fn-mlh-abs` (`:996`); keystones `fn-mlh-candidates-is-cands` and
  `fn-mlh-seqs-is-spec-from` (`:47-53`). About 12 operations: a genuinely narrow boundary.
- **Bytes.** Message-IDs enter as strings (`msgid`); the table stores no Message-ID bytes, only
  60-bit tags and seq words ("the heap holds 16 octets an entry", `books/catalog-logic.lisp:9-10`).
- **Who calls.** Only the catalog: `fn-cat$c-mpx` is a nested `fn-mlh`
  (`books/catalog-logic.lisp:533-539`), reached through `fn-cat-msgid-seqs` and
  `fn-cat-msgid-saturatedp`. Other books naming `fn-mlh-*`: `catalog-logic`, `catalog-paged`,
  `catalog`, `post-admission-keyed`, `blake3-string`. No host declaration, no raw call site.
  A second, older Message-ID structure survives: the persistent trie `fn-midx-*` for immutable
  reader views (`books/msgid-index.lisp:1-9`).

## 6. History and columns (and the paged history)

**Size.** 85 books, 17,960 code, **4,155 exec**, 12,499 thm (618 defs, 1,676 theorems):
`history-*` 72 books (14,779 / 2,981), `topic-history-*` 12 (2,611 / 985), `served-columns`
1 (570 / 189). Largest: `history-records` (1,409 / 279), `history-image-binding` (904 / 150),
`history-pages-relocate` (740 / 86).

There are **three stobj layers**, each an abstract stobj over the same logical value (the
history: true list of retained events, sequence = position, `books/history-columns-foundation.lisp:5-8`):

1. **`fn-hist`** (books/history-columns.lisp:17-31), attachable, attached to `fn-hist-paged`
   (`:15`). Exports, exactly five: `fn-hist-count` (), `fn-hist-at` (seq), `fn-hist-msgid-records`
   (msgid), `fn-hist-append` (ev, protect), `fn-hist-clear` (salt, protect); logic meanings
   `len`, `nth`, `fn-cei-article-records-for`, `append`, `nil` (`:56-72`). Reference foundation
   `fn-hist$c` is GENERATED by `(def-representation-index fn-hist (event :object) ...)`
   (`books/history-columns-foundation.lisp:115-123`): rows array, count, Message-ID buckets
   keyed by salted 32-bit FNV-1a (the one host call passes salt 0, so the hash is public and
   an adversary can force one bucket; answers stay exact, `:42-48`).
2. **`fn-hist-paged`** over `fn-hist$p` (`books/history-paged.lisp:11-17`): fields `root :
   fn-hrecs$c` (the immutable resident image), `mids` (hash eql: Message-ID buckets naming
   ordinals), `salt` u32, `generation`, `bound`; same five exports renamed `fn-hist-paged-*`
   (`:394-402`). "The resident image is immutable between root adoption; append writes only
   the arbitrary-event tail" (`:1-3`).
3. **`fn-hrecs`** over `fn-hrecs$c` (`books/history-records.lisp:64-77`, `:1358-1370`): fields
   `pgs : pgs-mem` (a nested page store, section 3), `oct : fn-octets-pg`, `img` (0/1),
   `salt`, `nimg`, `lens`/`starts` (five-element header lists), `npages`, `txid`, `sfx`
   (suffix array of events since the image), `lo`/`hi`. Eight exports: `fn-hrecs-count`,
   `-at`, `-vlen`, `-phys`, `-append` (protect), `-fill` (protect), `-load` (protect),
   `-flush` (protect). Reads return need-verdicts `(:need-page P PHYS)`; one retry loop
   `fn-hrecs-get`/`fn-hrecs-read` serves each need with one host fill (`fn-pgs-page-words`) and
   the page digest check; A-PGS-HOST-IO enters there only (`books/history-records.lisp:19-27`).
   Image format FNADTSN2 (`:7-9`). Shadow stobj `fn-hrecs$s` for adoption
   (`books/history-paged-adopt.lisp:9`).

- **Columns.** The overview column is the `fn-hnov` record decided once at intern
  (section 4); `books/served-columns.lisp:1-30` (`fn-scol-`) serves OVER/XOVER, HDR/XHDR, XPAT
  from it under relation `fn-scol-okp fn-arena fn-cat` (rows with a decided column carry exactly
  the facts of their handle's octets).
- **Host-declared entries: 41 defined in history books + 19 in `host/history-root-host.lisp`.**
  The image builder/snapshot `fn-his-*` (22: `fn-his-build-begin (salt fn-hrecs$c)`
  `books/history-image-build-rows.lisp:17`, `fn-his-build-open/place-run/close`
  `books/history-image-concrete.lisp:6-31`, `fn-his-build-finish (expected-count fn-hrecs$c)`
  `books/history-image-builder.lisp:12`, `fn-his-release (fn-hrecs$c)`, `fn-his-readback-page
  (write octets fn-hrecs$c)`, `fn-his-image-header-np`, `fn-his-skip-octets` (5 raw sites each),
  `books/history-image-snapshot.lisp:88-315`), called from `host/native/io.lisp`. The paged root
  `fn-hist$p-*` and credit accounting `fn-hroot-*` (17 together; `fn-hist$p-*`: adopt-stage, append, read, root-index-next, candidate-word, root-generation,
  dispose; `books/history-paged-adopt.lisp:24-147`, `books/history-paged.lisp:86`; six declared
  `:raw-guarded`/`:raw-with` in `host/interfaces-raw.lisp:16-27`) and the credit/demand
  accounting `fn-hroot-*` (`books/history-root-credit.lisp:40-108`), all called from
  `host/native/history-root.lisp`. The owner's root lifecycle wrappers `fn-owner-hroot-begin /
  -activate / -row / -pin-funded / -detach / -retire / -read-plan / -read-fund ...`
  (`host/history-root-host.lisp:31-288`), stobjs `state` and sometimes `fn-hist`.
- **Bytes.** Events are ACL2 objects (held records with arena handles); the on-disk image is
  u64 words in `pgs-mem`; `fn-his-readback-page` takes `octets` as an octet list; Message-IDs are
  strings (`:key-p stringp`, `books/history-columns-foundation.lisp:116`).
- **Who calls.** Raw host: `io.lisp` (snapshot build and readback), `history-root.lisp` (paged
  root), `owner.lisp`. 33 ACL2 host files include `books/history-columns.lisp` (the D61 attach
  order: `host/interfaces.lisp:22-26`, `host/store-node-host.lisp:9-12`). Books: 71
  include-book edges from other components (48 "other", 5 owner, 4 served, 4 checkpoint).

## 7. The payload arena and the octet buffer

**Size.** 31 books, 9,416 code, **4,068 exec**, 4,738 thm (388 defs, 845 theorems). Largest:
`payload-lz-dict-1` (1,371 code, 1,370 exec: a constant LZ dictionary), `payload-arena-extent`
(1,359 / 363), `octet-text` (1,043 / 405), `octets-stobj` (1,006 / 372), `store-intern`
(783 / 166). `payload-arena.lisp` itself is 370 code / 33 exec: the generic is generated.

### 7a. The arena `fn-arena`
- Purpose: the one long-lived home of every retained payload; a held record names its payload
  by HANDLE = position in the arena's logical list of sealed payloads
  (`books/payload-arena.lisp:6-13`). Guarantees as theorems over the logical view: a sealed
  handle is immutable, a handle is never reused, the reseat is the only re-point, the forget the
  only take-away (`:35-60`).
- Generic produced by `(def-generic fn-arena ...)` (`books/payload-arena.lisp:115-135`) after
  `(attach-stobj fn-arena fn-arena-extent)` (`:113`). **15 exports**, with the logic formals
  (`books/payload-arena-bytes.lisp:76-122`, `books/payload-arena-extent-logic.lisp:44-119`;
  every one threads stobj `fn-arena`):
  - reads: `fn-arena-count ()`, `fn-arena-payload-len (h)`, `fn-arena-get (h i)`,
    `fn-arena-get-span (h at n)`, `fn-arena-payload (h)`;
  - updates: `fn-arena-seal-list (xs)` (an octet list), `fn-arena-seal-buffer (fn-octets)` (the
    POST's seal, "the host boundary", `books/payload-arena.lisp:62-64`), `fn-arena-seal-range (a b
    fn-octets)`, `fn-arena-clear ()`, `fn-arena-seal-extent (file eoff elen poff plen trailer)`,
    `fn-arena-reseat-extent (h file eoff elen poff plen trailer)`, `fn-arena-release (h)`,
    `fn-arena-seal-lz-extent (file eoff elen poff plen trailer n dict)`,
    `fn-arena-reseat-lz-extent (h file eoff elen poff plen trailer n dict)`, `fn-arena-forget (h)`.
- Executable foundation `fn-arena$x` (`books/payload-arena-extent.lisp:61-66`): `inner :
  fn-arena-paged` (generated paged byte store), `ext` (per-handle extent descriptors, i.e. a
  payload can live in a log segment extent instead of the heap), `stage` (array of
  `fn-arena-page`, each one resizable byte array, `:57-59`), `files`. Abstract stobj
  `fn-arena-extent` with the same 15 exports (`:1570-1598`).
- **Who calls.** 94 host-declared entries thread `fn-arena` (owner, store-node, BP, live
  status ...). The raw host names arena exports directly at only 19 sites (`fn-arena-count` 8,
  `-get` 3, `-get-span` 3, `-seal-buffer` 2, `-seal-list` 1, `-release` 1, `fn-arena$x-*`
  readers in extent.lisp), e.g. `host/native/io.lisp:1984-1985` stages the handle then seals the
  live octet buffer. 32 host-declared entries are defined in this bucket: the extent reader
  `fn-arx-*` (`books/payload-extent.lisp:109-667`, `books/payload-extent-read.lisp:28-70`), the LZ
  append/replay `fn-lzr-*` (`books/payload-lz-append.lisp:93-377`), reader pins `fn-arpn-*`
  (`books/arena-reader-pins.lisp:193-211`).

### 7b. The octet buffer `fn-octets` and its congruent clones
- `books/octets-stobj.lisp:1-64`: abstract stobj whose logical value IS an octet list
  (`fn-cbor-octet-listp`) and whose exec is `fn-octets$c` = `buf` resizable `(unsigned-byte 8)`
  array + `fill` count (`:72-79`); defabsstobj at `:1160`. **13 exports**: `fn-octets-len`,
  `-get i`, `-put i o`, `-truncate m`, `-append-octet o`, `-clear`, `-reserve n`, `-list`,
  `-from-list xs`, `-append-list xs`, `-append-back off n`, `-get-word i k`, `-append-word w k`
  (`:29-46`); five are `defun-inline` for span loops (`:21-24`).
- Clones `:congruent-to fn-octets`, made by `(def-buffer NAME ...)` (`books/def-buffer.lisp:100`):
  `fn-octets-lg` (log walk), `fn-octets-pg` (page store), `fn-octets-pub` (checkpoint
  publication), `fn-octets-rd` (reader), `fn-octets-rx` (receive), `fn-octets-bp` (BP rotation),
  `fn-octets-ctl` (control), `fn-zin-win`/`fn-zin-tab`/`fn-zin-out` (inflate), `fn-web-in`/
  `fn-web-out`, `fn-pgb`, `fn-ast-ws`, `fn-dss-b`/`fn-dss-out` (16 clones in 13 books).
- **The host's octet buffer** (`host/native/io.lisp:298-370`): the live object is the state's
  user-stobj-alist entry, a two-slot vector (array, count) (`:303-305`); `fnn-live-octets` (`:313`),
  `fnn-octets-fill (vector)` = reserve + one `replace` + set count (`:319-325`), the A-HOST
  boundary; `fnn-octets-clear` (`:327`), `fnn-octets-release` (`:346`), and the publication
  buffer's `fnn-live-octets-pub`/`fnn-octets-pub-fill`/`-release` (`:340-366`). One buffer,
  one owner thread (served attempt under the service mutex; the checkpoint thread uses `-pub`).
  The raw host's most-called entry of this bucket is `fn-octets$c-reserve (n fn-octets$c)`
  (`books/octets-stobj.lisp:275`, 22 raw sites in 9 files). 38 host-declared entries thread a
  `fn-octets*` stobj.
- **`fnn-octet-list` (`host/native/io.lisp:264`: `(coerce octets 'list)`) sites by file**: 486
  non-comment occurrences in 39 raw files: io 120, owner 77, control 27, operator 26,
  signature-command 19, bp-app 18, hybrid-control 14, bp-service 13, admin 13, workflow 12,
  peer-invite 11, bp 11, bp-node 11, pull-service 10, tls-reload 9, anchor 9, tls 7, pattern 7,
  checkpoint 7, web-host 6, store-identity 6, control-transport 6, tcpcl 5,
  operator-control-client 5, operator-live 4, heap 4, feed-service 4, feed-filename 4,
  bp-obligation 4, mux 3, consumer-local 3, keys 2, bp-control 2, auth-admin 2, consumer-remote 1,
  config 1, bp-session 1, bp-listener-control 1, auth-read 1. Each is a byte vector turned into a cons
  list (16 bytes of heap per octet, `books/payload-arena.lisp:6-9`) before a core call: the list representation is still the
  default at the host boundary; the buffer path is the exception.

## 8. The checkpoint (`store-checkpoint.fnsc`, writer and reader)

**Size.** 45 books (`store-checkpoint*` 15, `checkpoint*` 9, `paged-checkpoint*` 6,
`recovery-*` 8, `charged-totals*` 2, `store-open*` 3, `store-recover-stream`, 
`store-replay-bound`), 17,233 code, **4,356 exec**, 11,489 thm (649 defs, 1,506 theorems).
Largest: `checkpoint-codec` (1,564 / 370), `charged-totals-header` (904 / 174),
`checkpoint-publish` (827 / 396), `store-checkpoint-open` (767 / 255). The owner's writer
`books/owner-checkpoint-writer.lisp` is counted under section 10.

- **File and format.** One file at the store root, `store-checkpoint.fnsc`
  (`books/byte-store-state-checkpoint-program.lisp:25`). FNSC segments: an FN-style frame
  (header 37 octets: magic, schema, index, count, length, sequence; chunk; 32-octet trailer
  chained over the previous trailer, `fn-frame-trailer`) of at most SEG octets
  (`books/store-checkpoint-codec.lisp:1-27`, `books/store-checkpoint-tables.lisp:33-37`). The
  payload is a postfix stack-machine program over ACL2 trees (atoms: NIL, naturals below
  2^2040, negatives, characters, strings, KEYWORD/ACL2/CL symbols, non-empty octet lists;
  `books/store-checkpoint-codec.lisp:11-21`). Schema 3 = four TABLES in order F, P, E, R
  (`books/store-checkpoint-tables.lisp:1-26`): F one row `(3 S FRONTIER REVISION log-position)`;
  P one payload row per committed event; E one row per event with octet leaves as references
  `8 NAT(s)` into P; R four fold roots (configuration fold at S, identity context, consumer
  cursor, topic prefix). Under the records flip the file is the arena run A followed by the
  four tables (`books/store-checkpoint-arena-writer.lisp:6-11`). Schema 2 is refused by name
  (D34, `books/store-checkpoint-codec.lisp:4-5`).
- **The value.** `fn-sco-capture (configs records)` (`books/store-checkpoint-open.lisp:197`) =
  the record list and each fold's accumulator; `fn-sco-open (c configs frontier suffix)` (`:273`)
  resumes every fold over a suffix; keystone `fn-sn-recover-from-checkpoint-equals-full-recover`
  (`:15-18`). Tables and capture are inverses (`fn-sct-capture-of-tables-of-capture`,
  `books/store-checkpoint-tables.lisp:41-44`).
- **Writer.** Two step machines driven by the host one segment per step through the publication
  buffer `fn-octets-pub`:
  arena run `fn-scka-write-step (pst n count s segment-bound file-bound fn-arena fn-octets)`
  (`books/store-checkpoint-arena-writer.lisp:579`) with `fn-scka-write-donep (pst count)` (`:575`)
  and `fn-scka-srcs-n (rows n lacc sacc fn-arena)` (`:391`); tables
  `fn-ockp-step (setup pst b bytes seg s segment-bound file-bound fn-octets)`
  (`books/owner-checkpoint-writer.lisp:917`), `fn-ockp-donep (pst)` (`:912`),
  `fn-ockp-segment-octets (record-octets bytes)` (`:476`). Store-node wrappers
  `fn-store-sco-publish-setup-of (prepared segment-octets profile config free revision log
  state)` (`host/store-node-host.lisp:1087`), `fn-store-sco-publish-next (fn-arena state)`
  (`:1058`), `fn-store-sco-encode-chunk (records n fn-arena)` (`:976`). The publication protocol
  (stage, link, barrier; explicit marker as authority, `:corrupt` distinct) is
  `books/checkpoint-publish.lisp:1-20`.
- **Reader.** The host reads one segment at a time into the octet buffer
  (`fnn-state-checkpoint-plan`, host/native/io.lisp) and hands a PLAN of frames `(HEADER A B
  TRAILER)` to `fn-store-sco-decode (plan fn-octets state)` (`host/store-node-host.lisp:685`),
  which calls `fn-sccr-decode-plan` (`books/store-checkpoint-reader.lisp:13-40`); then
  `fn-store-sco-decode-finish (i end fn-octets state)` (`:699`), `fn-scka-seal-n (i end n
  fn-octets fn-arena)` loads payloads into the arena (`books/store-checkpoint-arena-load.lisp:41`).
  Segment admission `fn-store-sco-segment-admit (header total profile file-bound)` (`:850`), read
  bound, header/trailer octets, `fn-store-sco-select (status sequence count profile)` (`:875`).
  Staged-file verification before the rename `fn-sccv-initial/-step/-final`
  (`books/store-checkpoint-verify.lisp:54-111`). The history image rides beside it:
  `fn-store-sco-image-open (file fn-hrecs$c state)` (`host/store-node-host.lisp:1119`). Charged
  totals header `fn-cth-header-open (seg profile config)` (`books/charged-totals-header.lisp:1135`,
  8 raw sites, the most-called checkpoint entry).
- **Paged checkpoint** (`books/paged-checkpoint*.lisp`): "checkpoint = dirty pages, open = root
  + log tail", model level over the CoW page store, **no host wiring**
  (`books/paged-checkpoint.lisp:1-4`), with keystones `fn-pck-dirty-is-the-delta`,
  `fn-pck-dirty-bound`, `fn-pck-open-after-commit-is-full-recover`,
  `fn-pck-crash-recovers-from-old-or-new` (`:13-19`).
- **Bytes.** Header/trailer as short octet lists, chunks as octet-buffer ranges, payload leaves
  sliced back to octet lists "the retained representation until PKT-293"
  (`books/store-checkpoint-reader.lisp:36-38`).
- **Who calls.** Host-declared: 13 entries defined in this bucket, 21 `fn-store-sco-*` in
  `host/store-node-host.lisp`, 9 reclaim/rollover wrappers in `host/checkpoint-host.lisp`
  (`:28-173`), 3 `fn-ockp-*`. Raw callers: `host/native/io.lisp` (most), `checkpoint.lisp`,
  `owner.lisp` (`fn-sco-records`, 3 sites). Includers: 83 include-book edges from other
  components (59 "other", 11 owner).

## 9. The runtime contract (actions, completions, pool, handles)

**Size.** `runtime-contract*` 23 books, 15,597 code, **3,148 exec**, 11,849 thm (474 defs,
1,639 theorems); with `runtime-bootstrap*`/`runtime-operation*` (10 books, 428 code) and the
resource ledger `resource-*` (5 books, 4,075 / 993) the bucket is 38 books, 20,100 code,
4,514 exec.

- **The contract** (`books/runtime-contract.lisp:1-111`). One executor, many machine instances.
  An ACTION is `(kind id incarnation op args)`; a COMPLETION is `(kind id incarnation op
  outcome)` with outcome `(:done n) | (:short n) | (:failed reason) | (:cancelled)`, the only
  event the layer consumes (`:3-10`). 14 action kinds `*fn-rtc-kinds*` = `:recv :send :pread
  :pwrite :fsync :close :accept :timer :bp-send :hand :pool :grant :extend :opened` (`:119-120`);
  `:in` kinds `:recv :pread`, `:out` kinds `:send :pwrite :bp-send` (`:123-124`). The layer owns
  SLOTS `(incarnation status resource)`, status `:free :live :closing :draining`, slot 0 the
  listener, slot 1 the owner (`:17-23`); POOL buffers `(generation owner bytes)` with owner
  `:free | (:workspace id inc) | (:leased id inc dir) | (:handed id inc to tinc)`, and at an
  action boundary a buffer is named by a HANDLE `(h g off len)` (`:24-30`); USES, the
  outstanding-action table `(kind id inc handle op)` (`:31-36`). Machines see only
  `fn-rtc-view` (BORROWED, `:38-50`); octets pass between instances only by `:hand`
  (`:52-61`); a completion matching no use changes nothing (T6, `:63-66`); cancellation keeps the
  use until the action's own completion; A-HOST-COMPLETES: one completion per submitted action
  (`:68-77`). v1 limit: one outstanding action per (kind id inc) (`:83-89`). Work budget
  q + `fn-rtc-step-c` per step (`:98-106`); commit only on the instance's own `:fsync (:done n)`
  (`:108-111`).
- **Layer operations** (list state, pure): state `fn-rtc-make config slots pool uses mstates
  next-op` (`:487`), `fn-rtc-init cfg` (`:1659`), `fn-rtc-step s e q` (`:1581`; `fn-rtc-step*`
  `:1494`), `fn-rtc-deliver s id inc ev q` (`:1439`), `fn-rtc-view id inc s` (`:1412`),
  `fn-rtc-grant n s` (`:1306`), `fn-rtc-submit-okp kind hd id inc s` (`:1093`),
  `fn-rtc-step-cost`/`-step-c` (`:1587`, `:1614`). The instance machine `fn-rtc-m-step` is
  constrained in an `encapsulate` (`:518-567`); instances obtain the theorems by
  `:functional-instance`.
- **Executable state.** Abstract stobj `fn-rtc-st` (`books/runtime-contract-pool.lisp:780`): logical
  value the list state; exec arrays (slot table, machine states, per-buffer (generation owner
  fill), every buffer's octets in ONE `(unsigned-byte 8)` array at `[base(h), base(h)+cap(h))`,
  `:3-10`). 27 exports: readers `config slot mstate uses next-op owner gen fill byte free-slot
  v-owner v-gen v-fill v-byte v-pool`, writers `set-slot set-mstate set-uses issue set-meta reset
  splice put release-all init` (`:784-810`). `books/runtime-contract-exec.lisp:1-16` re-proves the
  layer over it, each function EQUAL to its list twin; `:in` completions carry no data (the
  worker already spliced the bytes).
- **Executable instances, today: two.**
  1. The echo machine `fn-rce-*` (`books/runtime-contract-echo.lisp:1-10`), exercised by
     `fn-rce-exercise (variant fn-rtc-st)` (`:340`) from `host/native/rtc-exercise.lisp:37`; it never
     commits, so its commit keystone is vacuous (`:5-7`).
  2. The host lease `fn-hld-*` (`books/runtime-contract-host-lease.lisp:1-18`): one ARTICLE
     response = one instance over the process's one `fn-rtc-st`; machine `fn-hlm-step` (`:30-36`)
     asks for a pool buffer on `:accept` and nothing else. Host entries: `fn-hld-init (profile cfg q
     fn-rtc-st)` (`:93`), `fn-hld-begin (r fn-rtc-st)` (`:104`), `fn-hld-workspace (h id inc
     fn-rtc-st)` (`:123`), `fn-hld-quantum (h id inc fn-dss-out fn-rtc-st)` (`:147`), `fn-hld-sent (id
     inc op outcome fn-rtc-st)` (`:172`), `fn-hld-end (id inc fn-rtc-st)` (`:183`), `fn-hld-window-base
     (h fn-rtc-st)` (`:192`), all called from `host/native/owner.lisp:900-964` under the owner mutex.
  Nothing else in the served product runs through the contract: the owner, mux, NNTP, peering
  and BP paths are not instances of it.
- **Resource ledger** (`books/resource-vector-exec.lisp:1-20`): typed stobj `fn-resource-ledger`
  (u64 budget/drawn arrays of `*fn-rv-k*` words, slot phase/generation/demand columns);
  host entries `fn-rl-draw (slot demand ...)` (`:239`), `fn-rl-settle (slot gen ...)` (`:265`), the
  syncer `fn-ros-install-syncer/-issue/-physical/-outcome/-drainedp`
  (`books/resource-syncer.lisp:41-115`), output `fn-rlo-install/-issue/-output/-physical/-drainedp/
  -capacity` (`books/resource-output.lisp:31-167`), BP session `fn-bpsg-install/-return/-acquire-turn`
  (`books/resource-bp-session.lisp:15-65`). Created raw-guarded (`host/interfaces.lisp:206-207`).
- **Bytes.** Actions carry handles and at most two bounded naturals, never bytes
  (`books/runtime-contract.lisp:100-102`); bytes live only in `fn-rtc-st`'s octet array and the
  host writes an `:out` range straight from it (`books/runtime-contract-host-send.lisp:1-8`).
- **Who calls.** 28 host-declared entries in the bucket; raw callers `owner.lisp`,
  `rtc-exercise.lisp`, `catchup-spool.lisp`, `bp-session.lisp`, `io.lisp`.

## 10. The owner machine (owner, scheduler, time, admission/memory)

**Size.** The largest component: 176 books, 54,152 code, **15,378 exec**, 35,555 thm (2,203 defs,
3,810 theorems), plus the 9,915-line raw `host/native/owner.lisp` and the 6,528-line ACL2
`host/owner-host.lisp` (194 `definterface` forms). By family (books / code / exec):
`owner-time*` 8 / 4,098 / 1,255; `owner-retain*` 7 / 3,435 / 142; `native-operator*`,
`native-retire` 3 / 3,302 / 1,908; `owner-invariants*` 5 / 2,710 / 101; `owner-snapshot*` 2 /
2,708 / 152; `owner-feed*` 7 / 2,697 / 698; `owner-prepare*` 6 / 2,442 / 347; `owner.lisp` 1 /
1,919 / 1,311; `owner-commit*` 6 / 1,724 / 702; `owner-host-relation` 1 / 1,660 / 9;
`scheduler*` 3 / 1,607 / 672; `owner-checkpoint*` 3 / 1,580 / 353; `owner-reclaim*` 7 / 1,439 /
319; `memory-*` 2 / 1,302 / 464; `owner-log*` 4 / 1,134 / 432; `output-*` 10 / 1,036 / 363;
`allocation-*` 6 / 932 / 490; `admission-*` 2 / 721 / 268; `clock*` 5 / 449 / 173;
`owner-scheduler` 1 / 339 / 159; and 60 smaller `owner-*` families.

### 10a. The owner record and where it lives
- `books/owner.lisp:1-60`: one owner process serializes the mutations of one store; readers observe
  a committed version; performs no I/O. The record is 15 positions
  `(store view conns next-id max-conns pending ledger clock facts config queue inflight feeds
  node-secret refused)` (`:7-9`, constructor `fn-own-make` `:652`): `store` the `fn-sn` composition
  (section 1); `view` (version frontier archive); `conns` each `(id version frontier wire session
  archive config observation verdicts)`; `pending` the one admitted transaction's connection;
  `ledger` proof-only; `queue` submissions `(id version mark decision [login account])`;
  `inflight` the one submission on the durable path; `feeds` the outbound feed table;
  `node-secret` the key ring; `refused` the refused-offer memory.
- Storage: the ACL2 state global `fn-owner` holds an owner CONFIGURATION record (`fn-ocfg`) whose
  owner is that record: `fn-owner-ocfg state = (f-get-global 'fn-owner state)`, `fn-owner-core state
  = (fn-ocfg-owner ...)` (`books/owner-state-accessors.lisp:8-15`). Around it, 106 further
  `fn-owner-*` state globals are read or written by host wrappers and books (156 distinct
  `f-get/put-global` names in all; most-used `fn-store-sn` 67 sites, `fn-workflow-state` 48,
  `fn-store-cfg` 24). The planned owner carrier stobj `fn-owner-st` is **not defined** at origin/dev:
  the raw host resolves it and faults when absent (`host/native/io.lisp:501-506`), and the design
  says the move did not land (`planning/design/owner-carrier-2026-10-04.md:77`). The carried
  invariant over the owner globals is trusted at dispatch as A-OWNER-INVARIANT-CARRIED
  (`host/owner-served-carried.lisp:1-40`).

### 10b. The model's entry: `fn-own-step`
`fn-own-step o event fn-arena` (`books/owner.lisp:2837`) dispatches 29 event kinds
(`:2842-2882`): `:open :open-peer :octets :read :advance :close :begin :store :complete :reopen
:observe :declare-group :configure :take :control-submit :legacy-control-submit :bp-transit-submit
:operator-submit :outcome :control-outcome :bp-transit-outcome :transit-outcome :feeds :feed-conn
:feed-lost :feed-replay :tick :tick-peer :feed-octets`, plus `fn-own-run` (`:2885`). Named
transitions: `fn-own-open o acfg` (`:1140`), `fn-own-read o id octets fn-arena` (`:1681`),
`fn-own-read-step o id event fn-arena` (`:1727`), `fn-own-close o id` (`:1796`),
`fn-own-take-submission o` (`:2458`), `fn-own-outcome o id word` (`:2593`).

### 10c. The entry points the host calls
The raw host does not call `fn-own-step`; it calls `:program` wrappers over the global, each "one
proved owner transition" (`host/owner-host.lisp:1-25`). The ones on the served path:
- served read: `fn-owner-chunk-span (id start end sched fn-octets fn-arena fn-cat state)`
  (`host/owner-host.lisp:5428`; input = cells [start, end) of the octet buffer filled by
  `fnn-octets-fill`, `host/native/owner.lisp:482-489`), returning a served PLAN that the host steps
  with `fn-splan-step-plan (step completion redeem)` (`books/served-plan.lisp:471`, 11 raw sites);
  driven by `fnn-owner-handle-chunk-step` (`host/native/owner.lisp:7056`) from `fnn-mux-step`
  (`host/native/mux.lisp`);
- connection lifecycle: `fn-owner-open (state)` (`books/entries-owner-host.lisp:46`),
  `fn-owner-close (id fn-arena state)` (`:51`, 6 raw sites in 5 files), `fn-owner-fault (id state)`
  (`:56`), `fn-owner-tls-established (id fn-arena state)` (`host/owner-host.lisp:4689`);
- POST writer: `fn-owner-take (fn-arena state)` (`host/owner-host.lisp:3094`), `fn-owner-io
  (operation result state)` (`:2043`), `fn-owner-known-abort (fn-arena state)`
  (`books/owner-post-carried.lisp:81`), `fn-owner-outcome (id word state)` (`:3948`),
  `fn-owner-post-boundary (msgid-octets payload-length group-count charge fn-cat state)` (`:2853`),
  `fn-owner-finish-identity (fn-arena fn-cat fn-hist state)` (`:3045`); the first four are the
  `:raw-with (:carried fn-owner-served-carried)` rows (`host/interfaces-raw.lisp:28-36`);
- control/peer: `fn-owner-control-submit (msgid-octets group-octets payload fn-arena state)`
  (`:3174`), `fn-owner-transit-decide (id-octets subject-octets fn-arena fn-cat state)` (`:3532`),
  `fn-owner-bp-transit-outcome (word fn-arena state)` (`:4054`);
- most-called owner readers: `fn-owner-next-store-coordinates (state)` 11 raw sites,
  `fn-owner-hybrid-snapshots` 9, `fn-owner-next-txid` 7 (`:4094-4114`).
Host-declared entries in this bucket: 189 in `host/owner-host.lisp` plus 171 defined in owner books
(largest prefix families `fn-otm-` 34, `fn-ores-` 14, `fn-ort-` 13, `fn-omr-` 13, `fn-nret-` 13).

### 10d. Scheduler, time, admission/memory
- **Owner scheduler** (`books/owner-scheduler.lisp:14-35`): classes `*fn-osch-order*` = `(:control
  :reader :poster :transit)` (`:49`); `fn-osch-next (s waiting) -> (mv class s')` (`:175`),
  `fn-osch-observe`, `fn-osch-health-lines`; keystone `fn-osch-control-waits-at-most-the-bound`
  (3 quanta). The raw host names `fn-osch-*` only in comments and docstrings (`host/native/owner.lisp:16-18`,
  `:2550`, `:2646`), never in a call; the class slots it uses come from `fn-ocs-class-index`/`fn-ocs-classp`
  (`books/owner-commit-steps.lisp:76-80`). The durable contact/retry scheduler `fn-sched-*`
  (`books/scheduler.lisp:1-15`) is called by pull-service only (`fn-sched-pull-due/-start/-finish`,
  `books/scheduler-peers.lisp:389-401`).
- **Time** (`fn-otm-*`, 34 host entries): the disk as an adversarial environment, barrier deadline,
  disk mode (`books/owner-time-model.lisp:1-15`): `fn-otm-admit-post (s)` (`:634`), held commit
  `fn-otm-held-plan (s event)` (`books/owner-time-held.lisp:183`), `fn-otm-disk-step (s kind reading
  arg)` (`books/owner-time-journal.lisp:280`), reconfiguration hold `fn-otm-hold-begin/-end/-next`
  (`books/owner-time-reconfig.lisp:35-52`), `fn-otm-wall-reading (seconds microseconds)`
  (`books/clock-wall-reading.lisp:18`); clock `fn-clock-observation (monotonic wall wall-error
  has-wall)` (`books/clock.lisp:48`); time bars `fn-otb-*` (`books/owner-time-bars.lisp:97-333`).
- **Admission/memory**: the memory equation M_base + M_owner + C x M_connection + M_inflight +
  M_maintenance <= M_configured (`books/memory-model.lisp:1-8`); article admission by three
  resources, transactions/history/memory, refusal word naming the first (`books/admission-memory.lisp:4-12`;
  `fn-adm-memory-admitp profile img cfg limit tot row` `:44`, `fn-adm-article-word ...` `:56`), called
  inside `fn-owner-prepare-buffer`; host gate install `fn-owner-memory-gate-install` (17 formals) and
  `fn-owner-memory-configure` (20 formals: `img resident-obs trigger pub-trigger profile tlsp live cold
  output peer workers cache-limit root window config address-obs core nursery fn-hist state`)
  (`host/owner-host.lisp:1792`, `:1806`).
- **Who calls.** Raw: `host/native/owner.lisp` (172 distinct `fn-owner-*` names), `mux.lisp`,
  `admin.lisp`, `web-host.lisp`, `pull-service.lisp`, `feed-service.lisp`, `hybrid-control.lisp`,
  `peer-invite.lisp`. Books: 416 include-book edges into this bucket from other components (326 from
  "other").

## 11. The served NNTP machine

**Size.** 157 books, 69,455 code, **20,459 exec**, 42,957 thm (2,531 defs, 5,186 theorems): the
largest proof mass in the tree. By family (books / code / exec): `served*` 42 / 20,543 / 5,108;
`nntp*` 37 / 18,893 / 5,356; `wire*` 13 / 8,408 / 2,019; `article-*` 17 / 7,501 / 2,096; `web-*` 13
/ 5,763 / 3,499 (the web face, glob-included here); `wildmat*` 3 / 2,133 / 775; `protocol-*` 3 /
2,158 / 626; `group-*` 10 / 1,646 / 566; `list-*` 4; `newnews*` 5; `nov*` 5; `string-line*` 3;
`response-*` 2; `reader-*` 2. Largest: `nntp-auth` (3,356 / 929), `served-catalog` (3,026 /
1,151), `served-catalog-chain` (2,187 / 813), `served` (2,047 / 548), `wire-grammar` (1,921 / 518),
`nntp-responses` (1,828 / 1,396).

- **`fn-served-step (conn octets fn-arena)`** (`books/served.lisp:1599-1616`), guard `t`,
  stobj `fn-arena`, result `fn-served-make-result conn' effects` (`:572`): one socket read, a fold
  over the read's octets one byte at a time (`fn-wire-feed-byte`), the dispatcher
  `fn-served-dispatch (conn event fn-arena)` (`:1119`) run on each framed event before the next byte
  (`books/served.lisp:11-30`). POST lives inside: the 340 offer carries `:begin-article`, the body
  comes back as one `(:article lines)` event, and an injected article leaves as a `(:submit
  decision)` effect (`:20-31`). Keystones: preserves `connp`, effects typed, partition independence,
  reply stream partition-independent, bounded NNTP steps (`:33-50`); OPEN: the cost of one
  `fn-auth-step` has no closed-form bound (`:52-54`). Counted variants
  `fn-served-step-counted(-fast) (conn octets fn-arena)` (`books/served-tls-prefix.lisp:145-178`).
- **The connection** (`fn-served-make-conn-live`, `books/served.lisp:239-244`): 11 positions
  `(wire session archive config observation injection verdicts buckets control pinned live)`;
  `pinned` = `(version frontier repinned)`, `live` = the owner's committed view at read start; only
  GROUP and LISTGROUP move the pin (`:61-73`).
- **The command set.** One `defprotocol` table `*fn-proto-table*` (`books/protocol-table.lisp:422`),
  one row per command with `:rfc :dispatch :parser :model :cat :xref :live :framing :fuzz`
  (`:17-40`). 31 commands + 3 pseudo-rows, by dispatch layer: `:session` CAPABILITIES HELP MODE QUIT
  DATE POST; `:archive` GROUP LISTGROUP LAST NEXT ARTICLE HEAD BODY STAT OVER XOVER HDR XHDR XPAT
  LIST NEWGROUPS NEWNEWS; `:peer` IHAVE CHECK TAKETHIS; `:auth` AUTHINFO STARTTLS COMPRESS XREDEEM;
  `:pinned` XFNCATCHUP XFN-ZARTICLE; pseudo-rows `(syntax) (unrecognized) (connection)`
  (`:424-1205`); LIST carries the forms ACTIVE NEWSGROUPS OVERVIEW.FMT HEADERS ACTIVE.TIMES
  DISTRIB.PATS MOTD COUNTS SUBSCRIPTIONS DISTRIBUTIONS (`:884-900`). The
  reference dispatcher is `fn-nntp-step (session archive env wire-event fn-arena)`
  (`books/nntp.lisp:156`) / `fn-nntp-step-pinned (session archive index verdicts env wire-event
  fn-arena)` (`:436`); the served one is the catalog arm `fn-nntp-archive-command-cat`
  (`books/served-catalog.lisp`, via `fn-scr-command`).
- **Reply shapes.** A step answers an EFFECT LIST. Effect constructors:
  `(:reply octets)` and `(:close)` (`books/nntp-session.lisp:145-147`); `(:submit decision)`; the
  STARTTLS effect `fn-auth-starttls-effect`; plus window/article/payload effects whose octets are
  pointers into the pinned archive. The host takes four projections, each a question about the
  effects: reply octets (`fn-served-reply-octets`), `fn-served-closingp` (`books/served.lisp:1896`),
  `fn-served-starttlsp` (`:1910`), `fn-served-submission` (`:1925`), with `-submission-login`/`-account`
  (`:1939-1950`). The host never writes a reply octet (`host/owner-host.lisp:23-25`). Since the render
  plan, the effect list IS an immutable plan rendered off the owner mutex in windows:
  `fn-splan-of-effects (effects)`, `fn-splan-window (plan w fn-octets) -> (mv status plan' fn-octets)`,
  `fn-splan-donep (plan)` (`books/served-plan.lisp:1-30`); the host's per-step record is read by
  `fn-splan-step-p/-closep/-consumed/-refusal-lines/-exposure-close/-handshake-owed (x)`
  (`:407-450`) and advanced by `fn-splan-step-plan (step completion redeem)` (`:471`). ARTICLE bodies
  render through `fn-asto-plan-render-window (plan window fn-arena fn-ast-ws fn-dss-out)`
  (`books/article-stream-owner.lisp:775`). POST outcome rendering: `fn-served-post-outcome (conn
  completion)` (`books/served.lisp:2025`).
- **Who calls.** `fn-served-step` itself is called by owner books (`books/owner.lisp:1674` inside
  `fn-own-read`; `owner-agent`, `owner-control-read`, `config-owner-live-read`, ...), never by the raw
  host. The raw host reaches this machine through the owner (`fn-owner-chunk-span`, section 10) and the
  30 host-declared plan/stream entries defined here (`fn-splan-` 13, `fn-asto-` 6, `fn-qplan-` 5,
  `fn-zc-` 3, `fn-rid-` 2, `fn-rpin-` 1), called from `owner.lisp`, `mux.lisp`, `web-host.lisp`,
  `pull-service.lisp`. Includers: 152 include-book edges from other components (75 "other", 24 owner,
  16 peering).

## 12. POST, acceptance, identity (the injection path)

**Size.** 68 books, 24,079 code, **6,830 exec**, 15,396 thm (1,134 defs, 2,202 theorems). By family
(books / code / exec): `post*` 17 / 10,415 / 1,825 (of which the five `post-transaction*` books are
7,620 code, 967 exec, 6,381 thm); `stx-*` (statements) 14 / 3,255 / 1,294; `injection*` 7 / 3,384 / 1,018; `statement*` 12 /
1,906 / 625; `acceptance*` 5 / 1,905 / 533; `poster*` 5 / 1,460 / 340; `body-chunks*` 2 / 906 / 248;
`moderation*` 3 / 837 / 401; `article.lisp` 691 / 391; `incoming*` 5 / 546 / 392; `cancel-lock*` 2.

The path today, outermost first:
1. **Wire to POST session.** `fn-served-step` (section 11) frames POST's body as one `(:article lines)`
   event. `fn-nntp-post-step (ps archive config observation injection wire-event fn-arena)`
   (`books/nntp-post.lisp:464`), guard `t`: POST allowed -> 340 + `:begin-article`; disallowed -> 440;
   awaiting + `(:article body)` -> injection, a refusal is 441 with reason, an acceptance emits a
   submission and no reply yet (`:1-17`). Two clock readings: `observation` pinned per connection,
   `injection` per event (`:19-31`). Pinned variant `fn-nntp-post-step-pinned` (`:1157`).
2. **Injection.** `fn-inj-decide (source config observation)` (`books/injection.lisp:966`): RFC 5537
   section 3.5 over exactly the source octets, one clock observation and a config record
   `fn-inj-make-config allow agent groups max-octets` (`:464`; `-full` adds `listing closed`, `:451`);
   it builds Path, Injection-Date, Message-ID, Date, Injection-Info and the injected octets
   (`:1-12`, `:34-39`); `fn-inj-source-of` recovers the source exactly (D25). Bytes: source and
   result are octet lists.
3. **Owner submission.** The `(:submit decision)` effect enters the owner queue; the writer is
   `fn-owner-take` / `fn-owner-post-boundary` / store events / `fn-owner-outcome` (section 10c). The
   store-side prepare is `fn-store-sn-prepare` (section 1) or the owner's `fn-owner-prepare-buffer`
   with memory admission (`books/admission-memory.lisp:12-16`).
4. **Acceptance machine.** `books/acceptance.lisp:1-13`: logical acceptance, no bytes, no disk.
   Article = `(message-id payload requested-groups memberships archive-pin)` with payload a HANDLE
   (`:20-30`). Two host transitions: `fn-accept-prepare (s generation msgid payload groups stamp)`
   (`:451`) and `fn-accept-complete (s txid generation completion-status)` (`:486`), guard
   `fn-statep s` carried; used by ACL2 host files (`fn-initial-state`, `fn-accept-prepare`,
   `fn-accept-complete`) and by `fn-sn-*`.
5. **Identity.** Message-ID tests on POST moved off linear walks to the catalog's table
   (`books/post-identity-index.lisp:1-12`); the statement index `fn-stx-*` carries three alists
   extended by one cons per article, licensed by `fn-stx-index-agrees-with-lace`
   (`books/stx-index.lisp:1-11`); statement recovery on open is `fn-ssr-intern-step (acc ws rs ps mode
   dicts fn-arena)` (`books/statement-recover-stream.lisp:43`, 9 raw sites in io.lisp) with
   `fn-ssr-rows`/`fn-ssr-seed`. Duplicate-versus-conflict keys on the poster's bytes
   (`books/poster-bytes.lisp`, `host/store-node-host.lisp:16-17`).
- **Not wired.** The runtime-contract POST transaction machine `fn-ptx-*`
  (`books/post-transaction.lisp:1-25`: PAYLOAD_WRITING -> LOG_WRITING -> COMMITTING -> PUBLISHED, three
  spans, keystones P0-P6 "stated in the packet and not yet proved"; 235 definitions in the five books) has **zero**
  references from any host file, raw or ACL2. (Its header says it is not in ACL2_BOOKS; at
  origin/dev it is reachable from the Makefile's certify roots, so that line is stale.)
- **Who calls.** Raw host names only `fn-nntp-post-step`'s refusal texts (`fn-post-store-refusal-text/
  -line`), `fn-find-article`, and the 4 host-declared `fn-ssr-*`/`fn-stxk-*` entries; everything else
  reaches this component through the owner and `fn-served-step`. ACL2 host files name 13 `fn-inj-*`
  config accessors (owner configuration). Includers: 146 include-book edges from other components (70
  "other", 22 owner, 18 served, 12 TLS/auth).

## 13. The consumer surface

**Size.** 55 books (`consumer*` 52, `app-*` 3), 10,229 code, **4,717 exec**, 4,893 thm (588 defs,
541 theorems): one of the least-proved components (46% exec). Largest: `consumer-store-invariants`
(1,348 / 37), `consumer-position` (840 / 414), `consumer-local-control` (499 / 379), `app-pattern`
(484 / 330).

- **There is no `fn-cs-*` prefix.** `git grep fn-cs- origin/dev` finds nothing in the repository. The
  surface is spread over seven prefixes: `fn-cp-` (the position kernel), `fn-col-` (the local owner
  profile), `fn-cbind-` (secret-bound variants), `fn-cwait-`/`fn-cwd-` (wait, withdrawal), `fn-cec-`
  (entry completion), `fn-ncl-` (the local control codec), `fn-cre-`/`fn-crb-` (remote ingress).
- **The decision kernel** (`books/consumer-position.lisp:1-4`: "E2 v1 finite consumer-position
  decision kernel ... A :write is a proposal, never durable acceptance"). Cursor `(:cursor history
  incarnation consumer principal query query-version view-version registration-epoch position)`
  (`:36-39`), magic "fncu" (`:21`), ids at most 64 octets (`:10`). Operations, all pure on the
  consumer state `s`: `fn-cp-register (s caller consumer query qver view)` (`:384`),
  `fn-cp-register-within (s max caller consumer query qver view)` (`:411`), `fn-cp-ack (s caller qver
  view cursor)` (`:418`), `fn-cp-rebase (s caller consumer query qver view)` (`:430`),
  `fn-cp-remote-register`/`-remote-rebase` (+ `groups account`) (`:449`, `:462`), codec
  `fn-cp-cursor-encode (cursor)` (`:53`) / `fn-cp-cursor-decode (octets)` (`:115`).
- **Owner-level operations** over the owner record `o` (`books/consumer-owner-local.lisp`):
  `fn-col-register (o max consumer group)` (`:46`), `fn-col-ack (o cursor-octets)` (`:67`),
  `fn-col-poll (o consumer fn-hist)` (`:151`), `fn-col-poll-report` (`:201`); poll windows
  `fn-col-poll-index-window (fn-hist position frontier budget)` (`books/consumer-poll-index.lisp:91`);
  bound (secret) variants `fn-cbind-poll/-ack/-poll-over` (`books/consumer-bound.lisp:139-469`); wait
  `fn-cwait-poll (oc acfg consumer secret fn-hist)` (`books/consumer-wait.lisp:63`),
  `fn-cwait-step-over (... elapsed seconds fn-arena fn-hist)` (`:215`), `fn-cwait-decide (answer elapsed
  seconds)` (`:84`).
- **What the host calls**: 11 owner wrappers in `host/owner-host.lisp`, each one raw call site in
  `host/native/owner.lisp`: `fn-owner-consumer-local-bootstrap (history incarnation state)` (`:2725`),
  `-register (consumer group state)` (`:2735`), `-ack (cursor-octets state)` (`:2749`), `-position
  (consumer state)` (`:2757`), `-status (consumer state)` (`:2764`), `-poll (consumer fn-arena fn-hist
  state)` (`:2771`), `-unregister (consumer state)` (`:2798`), `-bound-poll (consumer secret fn-arena
  fn-hist state)` (`:3393`), `-wait-step (consumer secret elapsed seconds fn-arena fn-hist state)`
  (`:3415`), `-wait-admit (waiters state)` (`:3428`), `-bound-ack (cursor-octets secret state)`
  (`:3435`); plus `fn-owner-prepare-consumer (event fn-arena state)` (`books/owner-cursor-domain.lisp:203`,
  a `:raw-with :carried` row) and the remote ingress `fn-owner-remote-ingress (request protectedp g
  state)` (`host/consumer-remote-host.lisp:14`). 25 host-declared entries are defined in consumer/app
  books (cursor/event codecs `fn-cpe-*`, `fn-cpj-*` projection, `fn-pat-*` app pattern, `fn-cre-*`
  remote ingress), called from `signature-command.lisp`, `pattern.lisp`, `consumer-local.lisp`,
  `consumer-remote.lisp`, `checkpoint.lisp`; 12 `fn-native-control-host-consumer-*` codecs serve the
  control client (`host/native-control-host.lisp`).
- **Bytes.** Cursors, ids and tokens are octet lists (`fn-cbor-octet-listp`, `books/consumer-position.lisp:24-26`);
  the remote path reads through the octet buffer (`fn-crb-open (g fn-octets)`,
  `books/consumer-remote-buffer.lisp:51`).
- Rebase is in the kernel (`fn-cp-rebase`) but has no owner wrapper: no host entry named `*rebase*`
  exists (`fn-cec-rebase-selected` is book-internal, `books/consumer-entry-completion.lisp:171`).

## 14. Peering: feed, pull, catch-up, journals

**Size.** 49 books (`peer-*` 36, `feed*` 12, `journal*` 1), 19,967 code, **8,021 exec**, 10,854 thm
(1,197 defs, 1,441 theorems). Largest: `peer-inbound` (1,574 / 717: IHAVE/CHECK/TAKETHIS served side),
`peer-pull` (1,569 / 806), `peer-invite` (1,293 / 603), `peer-catchup-spool` (1,214 / 482),
`peer-feed` (1,106 / 725). Sub-families: `peer-feed*` 3 books / 2,455 code; `peer-pull*` 3 / 2,357;
`peer-catchup*` 8 / 3,726. Raw services: `host/native/feed-service.lisp` (906 lines),
`pull-service.lisp` (1,313), `catchup-spool.lisp`.

- **Outbound feed** (`books/peer-feed.lisp:1-14`): one feed state per configured outbound peer; the
  queue holds Message-IDs and an offer state, no article bytes, UNDELIVERED obligations only (a final
  answer or give-up retires the entry). State `fn-feed-make (peer limits queue contact backoff-until
  conn next-attempt)` (`:596`, counted form `:587`); operations `fn-feed-enqueue (f msgid tick)`
  (`:823`), `fn-feed-offer (f msgid)` (`:906`), `fn-feed-offer-line (msgid streamingp)` (`:883`),
  `fn-feed-reply-class (f response)` (`:1092`). The feed table lives INSIDE the owner record (`feeds`,
  section 10a) and is stepped by owner events `:feeds :feed-conn :feed-lost :feed-replay :tick
  :feed-octets`; the host reaches it through 19 declared `fn-owner-feed-*` wrappers
  (`host/owner-host.lisp:3819-6218`: `-dial-open`, `-reply-chunk`, `-reply-article`,
  `-tls-established`, `-journal-replay`, `-backoff-ms`, `-connect-timeout`, ...) and six it calls with
  no `definterface` at all: `fn-owner-feed-tick (peer-octets monotonic state)` (`:5907`),
  `fn-owner-feed-lost (peer-octets monotonic state)` (`:6167`), `-configure`, `-peers`, `-restart`,
  `-reconcile-next` (named only in the owed-writer list, `host/owner-served-carried.lisp:176-180`),
  all from `feed-service.lisp`.
- **Pull** (`books/peer-pull.lisp:1-15`): NEWNEWS pull as owner work; dial, DATE, NEWNEWS since a
  cursor, offer each Message-ID to ITSELF on a logical transit connection so it meets the node's own
  IHAVE decision. Round state `fn-pull-round (phase peer wildmat since advances pending bound started
  listed todo answers unavailable buf current)` (`:307`, 15 fields); `fn-pull-begin (cursor wildmat
  now bound)` (`:383`), `fn-pull-step (r event)` (`:616`), `fn-pull-plan-for (peer plans)` (`:1991`).
  The host drives the session wrapper: `fn-pull-session-begin-pair (plan cursor now credential)`
  (`books/peer-pull-session.lisp:648`) and `fn-pull-session-step-triple (s event)` (`:915`), plus
  `fn-pull-plan-peer/-host/-port/-profile-path`, `fn-pull-schedule`, `fn-pull-records-replay`,
  `fn-pull-fresh-cursor`: 65 distinct entries named in `pull-service.lisp`.
- **Catch-up** (`books/peer-catchup.lisp:1-14`): fetch a peer's articles as XFNCATCHUP batches,
  streamed through 512-octet windows into a private spool, digest chain recomputed and compared, then
  replayed oldest first by IHAVE to this node. `fn-cu-begin (cursor wildmat)` (`:292`); the bounded
  spool controller `fn-csp-begin (plan cursor credential limit window)`
  (`books/peer-catchup-spool.lisp:589`) and `fn-csp-step (s event)` (`:539`), an offer WINDOW of W
  logical transit connections (`:4-12`); the serving half is `books/peer-catchup-serve.lisp`.
- **Round driver** `fn-prd-*` (18 host entries, `books/peer-round-driver.lisp:62-216`): deadlines,
  resume, idle, write quanta, the feed's next action `fn-prd-feed-action (phase outputp drainp offerp
  now deadline)` (`:216`); shared by feed and pull services.
- **Journals** (three framed envelopes, each with a total scan the host calls):
  FNFD feed journal (`books/feed-journal.lisp:1-3`; `fn-feed-journal-prefix (prefix)` `:17`,
  `fn-feed-journal-scan (peer prefix frame offset)` `:50`); pull journal `fn-pull-journal-scan (peer
  prefix frame offset committed)` (`books/peer-pull.lisp:1836`); FNCU catch-up journal
  `fn-cu-journal-scan (peer prefix frame offset)` (`books/peer-catchup.lisp:668`); the two scans are
  declared `:exempt` total decoders (`host/interfaces.lisp:356-362`).
- **Bytes.** Journal prefixes/frames arrive as octet lists (`fnn-octet-list prefix`,
  `host/native/pull-service.lisp:125`); articles cross as IHAVE bodies through the transit connection's
  served path; the spool is a file read in 512-octet windows.
- **Who calls.** 93 host-declared entries defined in peering books (`fn-pull-` 18, `fn-prd-` 18,
  `fn-csp-` 17, `fn-pfp-` 8, `fn-pfr-` 7, `fn-cu-` 5, `fn-redeem-` 4, `fn-feed-` 4, ...) plus 27 declared
  `fn-owner-feed/pull/catchup/peer-*` wrappers and the 24 in `host/peer-invite-host.lisp`.

## 15. BP and TCPCL (the node machine)

**Size.** 184 books, 59,980 code, **19,872 exec**, 33,110 thm (2,468 defs, 3,253 theorems): the second
largest component, almost entirely private (only 7 include-book edges from the named components; 196
from "other"). Families (books / code / exec): `bp-node*` 52 / 21,051 / 6,399; `bp-fnbs*` 25 / 3,377 /
1,459; `bp-receiver*` 10 / 4,611 / 174; `bp-session*` 4 / 997 / 515; `tcpcl*` 17 / 5,632 / 2,019; the
other `bp-*` 75 books. Largest: `bp-node-machine-invariants` (2,121 / 15), `tcpcl-session` (1,753 / 789),
`bp-node-progress` (1,669 / 1,615: 97% exec, `set-verify-guards-eagerness 0`,
`books/bp-node-progress.lisp:13`), `tcpcl-octets` (1,332 / 355). Raw host: 11 files
(`bp.lisp bp-app bp-contact bp-control bp-control-client bp-listener-control bp-node bp-obligation
bp-service bp-session tcpcl`), 6,793 lines; ACL2 host files `bp-native-app-host` (26 decls),
`tcpcl-host` (21), `bp-receipt-journal-host` (19), `bp-node-host` (17), `bp-node-machine-host` (17),
`bp-receive-evidence-host` (15), `bp-release-owner-host` (12). The DTN image is a separate build
(`host/native/build-dtn.lisp`).

- **The node machine's step is a tower of four.** The raw BP service's one decision call is
  `fnn-bps-foundation-step` -> `(fnn-core 'fn-bpnj-step state event)`
  (`host/native/bp-service.lisp:263-275`; header "Every decision is fn-bpnf-step", `:1-6`):
  1. `fn-bpnj-step (st event)` (`books/bp-node-job-offer.lisp:202`): job offer; equal to
     `fn-bpnp-step` on every event but `(:contact-job PEER KEY)`, `(:job-result KEY TOKEN OUTCOME)`
     and an unnamed base result (`host/native/bp-service.lisp:267-271`);
  2. `fn-bpnp-step (st event)` (`books/bp-node-progress.lisp:1824`): the "one host-called progress
     extension over the FNBS state" (`:1-3`), with `fn-bpnp-progress-step (st node observation routes
     generation budget)` (`:649`);
  3. `fn-bpnf-step (st event)` (`books/bp-node-foundation.lisp:717`): "Finite A1 foundation ... delegates
     existing outbound events to fn-bpn-step" (`:1-3`);
  4. `fn-bpn-step (st event)` (`books/bp-node-machine.lisp:1072`): the outbound lifecycle, events
     `:enqueue :contact :resume :persist-result :forward-result :clock :restart` (`:1060-1066`);
     limits 64 jobs, 16 MiB, 4,096 records (`:19-22`); KEYSTONE M1: no effect spelling can discharge
     an archive or forward undertaking (`:1092-1095`).
  Answers are `(state . effects)` read by `fn-bpnf-answer-state/-effects (ans)`
  (`books/bp-node-foundation.lisp:467-468`).
- **Host-declared BP entries: 246** defined in BP/TCPCL books plus ~127 in the seven BP host files.
  Largest prefix families: `fn-bpnf-` 47 (FNBS store: names, frames, held list, recovery plans,
  `books/bp-fnbs-*.lisp`, `bp-node-foundation.lisp`), `fn-bpn-` 21, `fn-bpnp-` 17 (publication
  authorize/frame/name per kind), `fn-tcl-` 17, `fn-bpnr-` 16 (recovery), `fn-tcrt-` 11 (retained TCPCL
  turn), `fn-bpsched-` 11 (session scheduler), `fn-bprc-` 9 (run class/exit codes: `fn-bprc-run-exit-code
  (c)` 8 raw sites, `fn-bprc-publication-evidence (outcome)` 8, `books/bp-run-class.lisp:78,127`), `fn-bpah-`
  9, `fn-bpsp-` 9, `fn-bpnpf-` 8 (node profile file). Job cursor: `fn-bpnjc-contact-next (st peer routing
  offered cursor)` (`books/bp-node-job-cursor.lisp:330`), `-contact-cursor (table peer)` (`:1058`),
  `-contact-close (table st peer cursor)` (`:1108`).
- **TCPCLv4 session** (`books/tcpcl-session.lisp:1-25`, RFC 9174): the served path is `fn-tcl-drive (s
  buf now)` (`:1042`); one-event entries `fn-tcl-open (s now)` (`:438`), `fn-tcl-send (s ref octets now)`
  (`:885`), `fn-tcl-pump (s now)` (`:854`), `fn-tcl-tick (s obs)` (`:918`), `fn-tcl-terminate (s reason
  now)` (`:795`), `fn-tcl-tcp-closed (s)` (`:810`); each returns `(fn-tcl-make-result session events
  unconsumed)`; `fn-tcl-sessionp` is a carried invariant (`:12-17`). Seven entries: a narrow boundary.
  The host calls them through `fn-tcl-host-drive (s buf now)` (`books/tcpcl-host-drive.lisp:11`),
  `fn-tcl-host-source-drive` (`books/tcpcl-received-source.lisp:86`), `fn-tcl-host-tick (s monotonic)`,
  `fn-tcl-host-pump (s now)` (`host/tcpcl-host.lisp:77-94`) and reads `fn-tcl-host-phase (s)` (8 raw
  sites). Local policy: one outbound transfer at a time, TLS never negotiated up (`:20-25`).
- **Bytes.** TCPCL input is a buffer `buf` the host prepends its carry to (octet list); outbound
  `octets` in `fn-tcl-send`; FNBS frames and ADUs are octet lists; held images up to 16 MiB
  (`books/bp-node-foundation.lisp:18`).

## 16. Configuration, live limits, store profile

**Size.** 41 books, 15,932 code, **5,275 exec**, 9,624 thm (737 defs, 1,007 theorems). Families (books /
code / exec): `config*` 23 / 10,000 / 2,788; `native-config*` 4 / 2,479 / 1,212; `store-capacity*` 2 /
961 / 239; `store-budget*` 3 / 683 / 263; `node-config` 1 / 657 / 173; `store-profile*` 4 / 463 / 168;
`limits-live` 1 / 343 / 229; `store-config` 1 / 160 / 86; `live-profile-control` 1 / 111 / 43. Largest:
`config.lisp` (2,358 / 1,754: 74% exec), `native-config-show` (1,315 / 357), `config-store-steps`
(1,206 / 48).

- **The configuration value** (`books/config.lisp:1-27`): a typed record, never written, only replayed
  from journal records. Value `fn-cfg-value-make-full (groups capacity quotas policies listeners peers
  limits authorities invitations accounts descriptions)` (`:542`; 11 fields, recognizer `fn-cfg-valuep`
  `:714`); the group table is a HISTORY (retirement records a generation, never deletes, `:19-23`).
  Versioned pair `fn-cfg-make (generation value)` (`:758`). A reconfiguration is a record
  `fn-cfg-record-make (sequence txid generation change stamp)` (`:2370`) carrying typed deltas
  `fn-cfg-delta-make (kind a b n rows)` (`:817`) of **29 kinds** `*fn-cfg-delta-kinds*` (`:839-847`:
  `:create-group :remove-group :set-capacity :set-quota :set-policy :set-listeners :set-peers :set-limit
  :set-peer :remove-peer :grant-control :revoke-control :issue-invitation :consume-invitation
  :account-invite :account-redeem :login-binding :add-peer-rows :remove-peer-rows :set-group-description
  :set-group-status :account-access :set-group-moderation :consumer-bind :set-default-subscriptions
  :withdraw-article :account-delete :set-group-authority :accept-peer`), stable codes by `defevent`
  (`:858`). Fold: `fn-cfg-apply-delta (v gen stamp d)` (`:1917`), `fn-config-replay (reserved ceiling
  records)` (`:2731`). Encoding: a count-prefixed CBOR stream (`:24-27`).
- **The store profile** (sealed at init; `books/byte-store-frame.lisp:1-19`): a frame-field record of 15
  natural fields `*fn-bs-pf-max-transactions*` (T) `max-history-octets` (H) `max-record-octets` (R)
  `max-article-octets` (A) `max-groups-per-article` (G) `max-group-name-octets` `max-open-suffix` (K)
  `max-consumers` `max-bp-rows` `max-config-generations` `max-credentials` `max-policy-members`
  `max-header-fields` `max-header-lines` `max-header-octets` (`:131-147`), read by `fn-bs-profile-field`;
  namespace accessors `fn-bs-profile-max-consumers` etc. (`books/store-profile-namespace.lisp:1-20`);
  `fn-bs-profile-resolve (request current)` resolves init (`books/byte-store-frame.lisp:1115`).
- **Live limits** (`books/limits-live.lisp:1-27`): an operator limit change is a `:set-limit`
  configuration row, never a profile rewrite; the served profile is the sealed one overridden field by
  field: `fn-lim-effective (sealed records)` (`:89`); the decision `fn-lim-decide (field n values use
  run-mb core nursery observations observed)` (`:172`) applies now / records for next start / refuses by
  name; live fields are T, H, A only. Host entries: `fn-lim-apply-row (values field n)` (`:65`),
  `fn-lim-protected-growth`, `fn-lim-decision-status/-appliedp`, `fn-lim-reply-line (field n d open-ms
  values funded)` (`:446`), `fn-lim-values-lines`; wrappers `fn-store-lim-effective (sealed
  octet-records)` and `fn-store-lim-use (state)` (`host/store-node-host.lisp:324-340`).
- **Owner live reconfiguration**: `fn-olau-authorize-observed (oc record-octets lock-owned observation
  profile)` (`books/config-owner-live-authorize-carried.lisp:171`), `fn-oclc-live-authorizep (oc)`
  (`books/config-owner-carried.lisp:562`), `fn-cfgc-readback-verdict (readback authorized generation
  frontier)` (`books/config-carried-open.lisp:310`), and the owner's `fn-owner-reconfigure-complete
  (generation state)` (`host/owner-host.lisp:1951`). POST budget naming `fn-sbud-post-boundary (profile
  msgid payload-length group-count charge)` (`books/store-budget-naming.lisp:137`).
- **Who calls.** 26 host-declared entries defined here, mostly from `host/native/admin.lisp` (the
  `policy`/`operator CONFIG` verbs), `io.lisp`, `heap.lisp`, `operator.lisp`; 6 `fn-store-cfg-*`
  wrappers in `host/store-node-host.lisp` (the store's configuration in global `fn-store-cfg`, 24
  sites); 27 declarations in `host/native-admin-host.lisp`, 4 in `native-config-host.lisp`, 1 in
  `config-host.lisp`. Includers: 172 include-book edges from other components (91 "other", 31 owner).

## 17. TLS, authentication, identity, keyring

**Size.** 41 books, 14,643 code, **5,813 exec**, 7,704 thm (918 defs, 1,055 theorems). Families (books /
code / exec): `blake3*` 4 / 2,984 / 802; `tls-*` 7 / 2,230 / 1,238; `hybrid-*` 8 / 2,128 / 1,022 (hybrid
ML-DSA signatures); `identity*` 4 / 910 / 371; `login-binding*` 2 / 776; `store-identity*` 3 / 725;
`scram` 593; `sasl` 474; `principal*` 2 / 442; `auth-*` 2 / 341; `node-secret` 232; plus `sha256`,
`hmac-sha256`, `crypto-seam`, `crypto-attach`, `key-statements`, `store-mount-identity`. Not in this
bucket but part of the surface: `books/nntp-auth.lisp` (3,356 code / 929 exec, counted in section 11)
and the statement keyrings `stx-keyring-records`, `statement-snapshot-keyring`,
`statement-keyring-publication` (section 12). Raw host: `tls.lisp` (1,251 lines), `tls-reload.lisp`,
`auth.lisp`, `auth-admin.lisp` (540), `auth-read.lisp`, `crypto.lisp`, `signatures.lisp`, `keys.lisp`,
`digest.lisp` (551), `store-identity.lisp`, `hybrid-control.lisp`, `signature-command.lisp`, and three
vendored C files (`fn-blake3.c`, `fn-mldsa65.c`, `fn-deflate.c`).

- **TLS is not ACL2's.** "TLS protocol, record protection, certificate parsing and cryptography are
  delegated to the system's libssl C ABI: OpenSSL 3.0 or later, or LibreSSL 3" (`host/native/tls.lisp:3-9`);
  trust premises listed at `:14-20`. ACL2 owns only decisions around it: the handshake ADMISSION
  `fn-hsb-admit (s hl trustedp address now queuedp)` (`books/tls-handshake-decision.lisp:315`; "decides,
  BEFORE the host runs SSL_accept, whether that work is started", `:10-13`) reached through
  `fn-owner-handshake-admit (family address queuedp state)` (`host/owner-host.lisp:4853`) and
  `fn-owner-tls-established (id fn-arena state)` (`:4689`); STARTTLS as an effect the served step emits
  (section 11); `tls reload` decisions `fn-tlsr-*`/`fn-tlsk-*` (31 declarations in
  `host/tls-reload-host.lisp`, "every decision is the book's", `:1-3`); peer verification
  `fn-peer-tls-verification (server-name trust)` (`books/peer-host.lisp:180`).
- **Authentication.** AUTHINFO USER/PASS, SASL, SCRAM inside the served machine:
  `fn-auth-step (as archive config observation injection wire-event fn-arena)`
  (`books/nntp-auth.lisp:1775`), `fn-auth-command (as config keyword args)` (`:1639`), `fn-auth-authinfo
  (as args)` (`:1344`); credentials `books/auth-credentials.lisp`; 7 declarations in
  `host/native-auth-host.lisp`.
- **Keyring / node secret** (`books/node-secret.lisp:1-15`): one random root per key epoch at
  `STORE/keys/node-secret.key` (0600 in 0700), never regenerated, older epochs kept as
  `node-secret-E.key`; purpose keys derived by `fn-ns-mac (key msg)` (`:89`); ring recognizer
  `fn-ns-ringp (r)` (`:137`, current epoch first); file codec `fn-ns-file-render (entry)` (`:280`) /
  `fn-ns-file-parse (octets)` (`:302`, declared `:exempt` total decoder, `host/interfaces.lisp:354`);
  `fn-ns-create-entry (identity root)` (`:162`), `fn-ns-rotate-entry (current identity root)` (`:167`),
  `fn-ns-entry-epoch`, `fn-ns-secret-width`. The ring is installed into the owner record's `node-secret`
  field after every open (section 10a).
- **Store identity / mount.** `fn-smid-*` (`books/store-mount-identity.lisp:392-1115`): statfs observation,
  start verdict, init policy, refusal text; 9 declarations in `host/store-identity-host.lisp`.
- **Digests.** BLAKE3 is ACL2's (`fn-blake3-stobj (m)` `books/blake3-stobj.lisp:610`,
  `fn-blake3-of-prefixed-buffer (prefix fn-octets)` `:586`, `-range (prefix a wn fn-octets)` `:573`); the
  saved images swap the vendored C BLAKE3 in after a start-up check (A-CRYPTO-NATIVE,
  `host/native/io.lisp:288-295`). Hybrid signatures: `fn-hsig-host-preimage (principal keys source)`
  (`host/hybrid-signature-host.lisp:29`, 7 raw sites), 14 declarations there and 15 in
  `host/native-hybrid-control-host.lisp`.
- **Bytes.** Secrets, certificates paths, credentials and MAC inputs are octet lists; the TLS channel's
  plaintext is consumed by peek-then-exact-consume (`host/native/tls.lisp:18-20`).
- **Who calls.** 30 host-declared entries defined in this bucket (BLAKE3 3, `fn-ns-*` 8, `fn-smid-*` 4,
  `fn-id-hex-octets`, ...), raw callers `io.lisp`, `digest.lisp`, `owner.lisp`, `operator.lisp`,
  `bp-app.lisp`, `bp-node.lisp`.

## 18. The host surface

### 18a. The declarations
- 1,934 `definterface` forms, 1,916 distinct entry names. Where declared: `host/interfaces.lisp` 1,018
  forms (`:1-20` explains it is loaded after every ACL2-mode host file and checked against the image's
  world; `tools/interface_emit.py` turns it into `planning/interfaces.json` and the extractor roots),
  `host/owner-host.lisp` 194, `native-operator-host` 82, `store-node-host` 64, `native-control-host`
  45, `web-host` 43, `store-host` 32, `tls-reload-host` 30, `native-admin-host` 27, `bp-native-app-host`
  25, `peer-invite-host` 24, `workflow-host` 24, `native-live-status-host` 23, `journal-publish-host`
  20, `tcpcl-host` 20, `history-root-host` 19, `bp-receipt-journal-host` 18, `checkpoint-host` 18,
  `page-read-host` 18, `bp-node-host` 16, `bp-node-machine-host` 16, `page-window-executor-host` 16,
  the generated `host/interfaces-raw.lisp` 14, and 20 smaller files.
- Class: 1,212 `:common-lisp-compliant` (guard-verified), 573 `:program`, 145 `:ideal` (not
  guard-verified; the host runs the logic definition).
- Dispatch: the raw host calls entries through `fnn-call` (`host/native/io.lisp:1578`) and its wrappers;
  by quoted-name forms, `fnn-core` 1,299 sites, `fnn-owner-core` 160, `fnn-call` 122, `fnn-core-state`
  85, `fnn-owner-action` 42, `fnn-core-page-read-pool` 24, `fnn-core-arena-state` 20; 1,792 distinct
  names are dispatched that way. **9 dispatched names have no declaration**: `fn-ats-enter-internal`,
  `fn-ats-uncertain-internal` (`host/native/owner-control-turn.lisp:19,38`), `fn-owner-feed-tick`,
  `fn-owner-feed-lost` (`host/native/feed-service.lisp:359,480`), `fn-owner-feed-reconcile-next`,
  `fn-owner-feed-restart`, `fn-owner-submission-intent`, `fn-owner-submission-resolution`
  (`host/native/owner.lisp:1699-5928`), `fn-owner-rx-turn-parser-span`
  (`host/native/receiver-parser-turn.lisp:22`), plus `fn-owner-feed-configure`/`-peers` through
  `fnn-owner-names` (`host/native/owner.lisp:1656`, `feed-service.lisp:141`).
- **Fan-in is flat.** Of 1,916 entries, 1,271 have exactly one raw call site and 401 have two; 13 have
  none; only 38 have six or more. 1,719 entries are called from exactly one raw file. The maximum is 22.
  The surface is wide, not deep: almost every entry is one host line's private helper.

**Declarations by subsystem** (distinct names; assigned by the defining book's component, a
host-defined wrapper by its file; "raw sites" summed):

| subsystem | entries | raw sites | of which zero-site |
|---|---|---|---|
| 10 owner machine (owner-host wrappers + owner books) | 371 | 622 | 0 |
| 15 BP/TCPCL | 364 | 523 | 0 |
| operator / admin / control CLI (`native-*`, `control-*`, `entries-native-*`) | 215 | 366 | 0 |
| 14 peering | 145 | 198 | 0 |
| 03 page store, page-read, heap, reclaim | 140 | 209 | 0 |
| 02 log kernel (incl. `host/store-host.lisp`) | 108 | 239 | 0 |
| 17 TLS/auth/identity/keys/digests | 101 | 147 | 1 |
| 01 byte store / file kernel (incl. 64 `store-node-host` wrappers) | 66 | 122 | 0 |
| 06 history/columns | 63 | 93 | 0 |
| 11 served NNTP (web face: `web-host`, `web-*`, reader) | 50 | 58 | 1 |
| 07 payload arena / octets | 44 | 81 | 4 |
| 08 checkpoint | 31 | 56 | 1 |
| 11 served NNTP (plans, streams) | 30 | 69 | 0 |
| 16 config/limits/profile | 30 | 43 | 0 |
| 09 runtime contract + resource ledger | 28 | 29 | 4 |
| 13 consumer surface | 26 | 42 | 0 |
| workflow / app (`workflow-host`) | 24 | 27 | 0 |
| store node, export/import, genesis (other `store-*` books) | 18 | 40 | 0 |
| failure scope / outcome classes | 16 | 53 | 1 |
| anchor | 12 | 12 | 0 |
| undefined in the parsed world (abstract-stobj exports and creators) | 10 | 17 | 1 |
| deflate / compress | 6 | 10 | 0 |
| other books | 6 | 12 | 0 |
| 12 POST/acceptance/identity | 4 | 14 | 0 |
| raw dispatch verdicts | 4 | 4 | 0 |
| 04 catalog (record-string codecs) | 3 | 6 | 0 |
| reader-model-host | 1 | 4 | 0 |
| **total** | **1,916** | | **13** |

### 18b. The 30 most-called entries (raw call sites in `host/native/*.lisp`)

| # | entry | formals | sites | raw files | defined |
|---|---|---|---|---|---|
| 1 | `fn-octets$c-reserve` | n fn-octets$c | 22 | io 5, deflate 4, extent 3, catchup-spool 2, web-host 2, owner 2, bp-session, tcpcl, bp-service, consumer-remote | `books/octets-stobj.lisp:275` |
| 2 | `fn-native-control-host-status-exit-code` | status | 20 | hybrid-control 5, operator-control-client 3, pattern 2, consumer-local 2, tls-reload 2, operator-live 2, +4 | `books/entries-native-control-host.lisp:118` |
| 3 | `fn-native-operator-host-result-store-root` | result | 17 | operator 13, +4 | `host/native-operator-host.lisp:69` |
| 4 | `fn-lgc-fence-failed` | c | 12 | io 12 | `books/store-log-kernel-concrete.lisp:567` |
| 5 | `fn-fs-classify` | class step | 11 | owner 7, io, tcpcl, admin, bp-control | `books/failure-scope.lisp:100` |
| 6 | `fn-splan-step-plan` | step completion redeem | 11 | owner 7, mux 2, pull-service, web-host | `books/served-plan.lisp:471` |
| 7 | `fn-native-operator-host-result-status` | result | 11 | operator 7, heap 3, io | `books/entries-native-operator-host.lisp:59` |
| 8 | `fn-owner-next-store-coordinates` | state | 11 | hybrid-control 5, owner 3, peer-invite 2, keys | `host/owner-host.lisp:4101` |
| 9 | `fn-lgc-last` | c | 10 | io 10 | `books/store-log-kernel-concrete.lisp:490` |
| 10 | `fn-store-sco-clear` | state | 10 | io 8, checkpoint, owner | `host/store-node-host.lisp:639` |
| 11 | `fn-cp-nth` | n x | 9 | signature-command 9 | `books/consumer-position-fields.lisp:8` |
| 12 | `fn-ssr-intern-step` | acc ws rs ps mode dicts fn-arena | 9 | io 9 | `books/statement-recover-stream.lisp:43` |
| 13 | `fn-owner-hybrid-snapshots` | state | 9 | peer-invite 5, hybrid-control 4 | `host/owner-host.lisp:4110` |
| 14 | `fn-cth-header-open` | seg profile config | 8 | io 7, heap | `books/charged-totals-header.lisp:1135` |
| 15 | `fn-bprc-publication-evidence` | outcome | 8 | bp-service 8 | `books/bp-run-class.lisp:127` |
| 16 | `fn-bprc-run-exit-code` | c | 8 | bp 4, bp-service 2, tcpcl, bp-node | `books/bp-run-class.lisp:78` |
| 17 | `fn-owner-page-read-ledger` | fn-page-read-pool | 8 | extent 7, extent-decoded | `books/page-read-pool-state.lisp:22` |
| 18 | `fn-pwx-boundp` | ledger w token phase | 8 | extent 7, extent-decoded | `books/page-window-executor.lisp:30` |
| 19 | `fn-tcl-host-phase` | s | 8 | tcpcl 8 | `books/entries-tcpcl-host.lisp:23` |
| 20 | `fn-hsig-host-preimage` | principal keys source | 7 | signatures 2, owner 2, +3 | `host/hybrid-signature-host.lisp:29` |
| 21 | `fn-outcome-code` | class | 7 | io 7 | `books/outcome-class.lisp:42` |
| 22 | `fn-arena-count` | (fn-arena) | 7 | owner 6, io | generic export, `books/payload-arena.lisp:121` |
| 23 | `fn-bs-imp-classify` | stage-present root-present | 7 | io 7 | `books/store-import-publication.lisp:196` |
| 24 | `fn-bpnf-stored-record-name` | epoch operation-id | 7 | bp-service 7 | `books/bp-fnbs-codec.lisp:310` |
| 25 | `fn-omr-control-path-octets` | result | 7 | operator 6, heap | `books/owner-maintenance-request.lisp:78` |
| 26 | `fn-native-operator-host-result-exit-code` | result | 7 | operator 6, io | `books/entries-native-operator-host.lisp:71` |
| 27 | `fn-native-operator-host-result-native-action` | result | 7 | heap 6, operator | `books/entries-native-operator-host.lisp:75` |
| 28 | `fn-owner-next-txid` | state | 7 | owner 7 | `host/owner-host.lisp:4094` |
| 29 | `fn-owner-bp-route-table` | state | 6 | bp-node 5, bp-service | `host/bp-native-app-host.lisp:39` |
| 30 | `fn-lgs-open-plan` | names first | 6 | io 6 | `books/store-log-segments.lisp:155` |

The most-called entries are accessors and exit-code/status projections, not transitions: the
transitions (`fn-owner-chunk-span`, `fn-bpnj-step`, `fn-lgc-take`, `fn-lgu-acknowledge`,
`fn-tcl-host-drive`) are each called from one to four sites.

### 18c. The raw host files by role (`host/native/`, 68 files, 53,008 lines incl. 3 C files)

| role | files (lines) | total |
|---|---|---|
| **io / store adapter** | `io.lisp` (10,418: the trust boundary, `fnn-call`, octet buffer, log, store open/recover/checkpoint), `checkpoint.lisp` (520), `immutable-publish.lisp` (185), `feed-filename.lisp` (71), `store-identity.lisp` (113) | 11,307 |
| **owner** | `owner.lisp` (9,915: the writable owner service, service mutex, attempt/commit/syncer), `history-root.lisp` (302), `owner-control-turn.lisp` (113), `receiver-parser-turn.lisp` (36), `rtc-exercise.lisp` (49) | 10,415 |
| **mux / connections** | `mux.lisp` (2,362: served connections on fixed I/O loops), `tls.lisp` (1,251), `tls-reload.lisp` (272), `deflate.lisp` (665), `web-host.lisp` (1,120) | 5,670 |
| **extent / memory** | `extent.lisp` (2,168: arena EXTENT realizer, page fills), `extent-decoded.lisp` (357), `heap.lisp` (753), `digest.lisp` (551), `crypto.lisp` (243), `signatures.lisp` (383) | 4,455 |
| **services: peering** | `pull-service.lisp` (1,313), `feed-service.lisp` (906), `catchup-spool.lisp` (273), `peer-invite.lisp` (581) | 3,073 |
| **services: BP/DTN** | `bp-service.lisp` (1,700), `bp-node.lisp` (1,429), `tcpcl.lisp` (1,054), `bp.lisp` (902), `bp-session.lisp` (431), `bp-app.lisp` (423), `bp-obligation.lisp` (402), `bp-control.lisp` (248), `bp-listener-control.lisp` (101), `bp-contact.lisp` (84), `bp-control-client.lisp` (19) | 6,793 |
| **services: control / operator / admin** | `operator.lisp` (1,261), `admin.lisp` (1,225), `control.lisp` (1,031), `auth-admin.lisp` (540), `hybrid-control.lisp` (358), `control-transport.lisp` (354), `operator-live.lisp` (322), `signature-command.lisp` (279), `pattern.lisp` (236), `consumer-local.lisp` (198), `keys.lisp` (104), `auth.lisp` (96), `operator-control-client.lisp` (77), `consumer-remote.lisp` (75), `login-bindings.lisp` (69), `config.lisp` (30), `auth-read.lisp` (14), `anchor.lisp` (457), `workflow.lisp` (846), `topic-local.lisp` (32) | 7,604 |
| **build / images / dev** | `build.lisp` (714), `build-dtn.lisp` (534), `build-store-test.lisp` (157), `raw-trap.lisp` (435: D40 raw dispatch table), `strip-world.lisp` (352), `dev-repl.lisp` (268), `trace.lisp` (204), `acl2-session.lisp` (93), `reader-model-host.lisp` (45) | 2,802 |
| **vendored C** | `fn-mldsa65.c` (590), `fn-blake3.c` (191), `fn-deflate.c` (108) | 889 |

Plus 58 ACL2-mode host files `host/*.lisp` (the `*-host.lisp` wrappers carry the 902 `definterface` forms
outside `interfaces.lisp` and `interfaces-raw.lisp`), the largest `owner-host.lisp` (6,528 lines).

## 19. Dependency order (who includes whom)

At component (glob) level every component includes every other: the 17 named components form ONE
strongly connected include graph (187 cross-component edges), because owner-, served- and store-named
books sit on both sides of most layers (e.g. `owner` books include `served`, and `served-catalog-owner`
includes `owner`). The heaviest directions: owner -> config 31, owner -> served 24, owner -> POST 22,
served -> POST 18, served -> owner 15, BP -> log 14, BP -> consumer 12, page store -> owner 13. So the
honest diagram is of the representative BOOKS (books are acyclic). Below, each line is a book, its
transitive include closure size in books, and the representative books it directly stands on
(transitive reduction among these 41 books; computed from `include-book` forms at origin/dev):

```
L0  cbor (0)    octets-stobj (1)    runtime-contract (1)
     |               |
L1  byte-store (5) consumer-position (5) node-secret (5) owner-time-model (6) tcpcl-session (7)
    acceptance (8) injection (12) config (14)         blake3-stobj (6) <- octets-stobj
                                                       pagestore-exec (10) <- blake3-stobj
                                                       frame (13) <- blake3-stobj
L2  payload-arena (21) <- octets-stobj
    bp-node-machine (20) <- blake3-stobj
    peer-feed (30) <- acceptance, frame
L3  history-records (124) <- acceptance, byte-store, consumer-position, frame, pagestore-exec
    nntp (120)            <- acceptance, payload-arena, config, frame
    peer-pull (86)        <- payload-arena, byte-store, config, peer-feed
L4  history-columns (133) <- history-records          nntp-post (137) <- injection, nntp
    peer-catchup-spool (124) <- peer-pull
L5  store-files (138)       <- history-columns     (the file kernel stands ON the history stobj:
    msgid-linear-exec (140) <- history-columns, node-secret        its RECORDS field may be BASED)
L6  store-node (150)  <- store-files
    catalog (174)     <- payload-arena, config, msgid-linear-exec
L7  store-log-kernel-concrete (170) <- store-node      store-log-durable (171) <- it
    store-checkpoint-open (176)     <- config, store-node
    nntp-auth (181)                 <- byte-store, consumer-position, nntp-post
L8  served (183) <- nntp-auth          served-plan (186) <- served
L9  owner (263) <- peer-feed, served, store-node       consumer-owner-local (271) <- owner
L10 limits-live (307), tls-handshake-decision (309)   <- store-checkpoint-open, owner
    store-checkpoint-arena-writer (324)              <- store-checkpoint-open, owner
    bp-node-job-offer (333)  <- bp-node-machine, peer-feed, served, store-node
    runtime-contract-host-lease (410) <- catalog, store-checkpoint-open, owner-time-model,
                                         owner, runtime-contract, served-plan
L11 host/*.lisp (ACL2-mode wrappers) -> host/interfaces.lisp -> host/native/*.lisp (raw)
```

Three things the order shows. (1) The genuinely low kernels (closure at most 30 books) are byte-store,
octets, BLAKE3, frame, page store, acceptance, injection, consumer position, node secret, config value,
TCPCL session, BP outbound machine, outbound feed, runtime contract, arena: fn2 can build each first.
(2) The store spine is inverted relative to the obvious order: the file kernel (`store-files`) and the
Message-ID table include the history stobj, the log kernel includes the store node, and everything
above the store node carries its 138-150 book closure. (3) The owner (263) is the hub: the BP job
offer, the checkpoint writer, live limits, the TLS decision and the host lease all include it.

## 20. Closing: which boundaries are narrow today

**Ten genuinely narrow boundaries (a dozen operations or fewer, and actually the boundary in use):**

| # | boundary | operations | count | where |
|---|---|---|---|---|
| 1 | TCPCLv4 session | `fn-tcl-drive open send pump tick terminate tcp-closed` | 7 | `books/tcpcl-session.lisp:438-1042` |
| 2 | history stobj `fn-hist` | `count at msgid-records append clear` | 5 | `books/history-columns.lisp:17-31` |
| 3 | history image `fn-hrecs` | `count at vlen phys append fill load flush` | 8 | `books/history-records.lisp:1358-1370` |
| 4 | Message-ID table `fn-mlh` (catalog-private) | `tag tag-of candidates seqs put split add saturatedp reserve clear build-from build-tail` | 12 | `books/msgid-linear-exec.lisp:91-2873` |
| 5 | runtime-contract host lease `fn-hld` | `init begin workspace quantum sent end window-base` | 7 | `books/runtime-contract-host-lease.lisp:93-192` |
| 6 | served step | `fn-served-step` + `reply-octets closingp starttlsp submission` + `post-outcome` | 6 | `books/served.lisp:1599-2025` |
| 7 | acceptance machine | `fn-initial-state fn-accept-prepare fn-accept-complete` | 3 | `books/acceptance.lisp:451-486` |
| 8 | injection | `fn-inj-decide fn-inj-make-config(-full/-listed/-closed) fn-inj-source-of` | 4 | `books/injection.lisp:451-966` |
| 9 | consumer-position kernel `fn-cp` | `register register-within ack rebase remote-register remote-rebase cursor-encode cursor-decode` | 8 | `books/consumer-position.lisp:53-462` |
| 10 | BP outbound machine | `fn-bpn-step` over 7 events (`:enqueue :contact :resume :persist-result :forward-result :clock :restart`) | 1 (7) | `books/bp-node-machine.lisp:1060-1072` |

Also narrow but not where the host stands today: the byte model `fn-bs` (10 syscalls + crash + read,
logic only), the page-store model `pgs-` (open/commit/fork/crash/alloc/plan-commit/roots, 7), the log
acknowledgement (`fn-lgu-acknowledge`, `-take-verdict`, `-log-max`: 3), the checkpoint value
(`fn-sco-capture`/`fn-sco-open`: 2), the node secret (8), live limits (`fn-lim-*`, about 8), the owner
scheduler `fn-osch-next/-observe/-health-lines` (3; no quoted host call site), the runtime contract's
list layer (`fn-rtc-init/-step/-deliver/-view/-grant`: 5, over 14 action kinds).

Narrow kernels 2-3, 6-7 and 9-10 are reached by the host only through a wide layer above them (the
owner wrappers, the store-node wrappers, the BP step tower), so their narrowness is not visible at the
host boundary.

**The boundaries that are not narrow (operations at the boundary as it exists):**

| boundary | count | what makes it wide |
|---|---|---|
| owner machine | **371** host entries | 189 wrappers in `host/owner-host.lisp` + 171 in owner books + 11 in other owner host files; `fn-own-step` has 29 event kinds; state is the 15-field record in global `fn-owner` plus 106 further `fn-owner-*` globals; the carrier stobj is not landed |
| BP / TCPCL host surface | **364** | four-deep step tower (`fn-bpnj` -> `fn-bpnp` -> `fn-bpnf` -> `fn-bpn`); 246 defined in BP/TCPCL books, the rest in seven BP host files (127 forms); `fn-bpnf-` alone 47 |
| operator / admin / control CLI | **215** | one host entry per verb arm, status/exit-code projections (the most-called entries in the tree) |
| peering | **145** | feed (19 declared + 6 undeclared owner wrappers), pull (65 names in `pull-service.lisp`), catch-up spool (17 `fn-csp-`), round driver (18 `fn-prd-`), three journals |
| page store / page-read / heap / reclaim | **140** | `fn-heap-*` 23 one-site decisions, `fn-pio-*` 13, read-pool and window executors; `fn-heap-command-decide` has 17 formals |
| log kernel | **108** | 76 in the log books (`fn-lgc` 20, `fn-lgdm` 15 damage texts/verdicts, `fn-lgs`, `fn-lgl`, `fn-lgo`, `fn-lgw`, `fn-lgb`) + 32 in `host/store-host.lisp` |
| TLS / auth / identity / keys | **101** | 31 `tls reload` wrappers, hybrid signatures 29, mount identity, BLAKE3, node secret; TLS itself is libssl |
| store node / file kernel | **66** | 64 `fn-store-sn-*`/`fn-store-sco-*`/`fn-store-cfg-*` `:program` wrappers over a global; `fn-sf-dispatch` 17 events; `fn-sn` record 14 fields |
| history/columns host | **63** | 22 image builder/snapshot `fn-his-*`, 17 paged-root/credit, 19 owner root-lifecycle wrappers (beside the 5-export stobj) |
| served plan / stream / web | **80** | 30 plan/stream entries + 50 web-face entries; 31 NNTP commands + LIST forms in one table |
| payload arena / octets | **44** host entries | 15 arena exports, 13 octet-buffer exports times 16 congruent clones, 94 entries threading `fn-arena`, and **486 `fnn-octet-list` conversion sites in 39 raw files** |
| checkpoint | **61** | 31 in checkpoint books + 21 `fn-store-sco-*` + 9 `checkpoint-host` wrappers; two writer step machines and a plan reader |
| runtime contract state `fn-rtc-st` | **27** exports | plus 14 action kinds; the resource ledger adds 21 host entries |
| configuration | **30** host entries | 29 delta kinds, 11-field value, 15 profile fields, owner live-reconfiguration carriers |
| catalog `fn-cat` | **23** exports | 18 readers, 5 writers; no raw call site, 15 owner entries thread it |
| consumer surface | **38** | 11 owner wrappers + 25 consumer/app book entries + remote ingress, over seven prefixes; no `fn-cs-*` exists |
| arena alone `fn-arena` | **15** exports | just over the line: 5 readers, 10 writers (seal x5, reseat x2, release, forget, clear) |
| octet buffer `fn-octets` | **13** exports | just over the line |

Count: **10** narrow boundaries in use (plus 8 narrow ones not at the host's level); **18** wide ones,
summing to roughly 1,900 host-visible operations, against a tree of 1,434 books, 497,144 code lines
and 160,196 executable lines at origin/dev 3bbfc4dca.
