# QUARRY: what lifts whole into fn2, and what does not (2026-10-28)

Read-only survey of the old tree as a quarry for fn2. Tree: `origin/dev` = 3bbfc4dca (the brief's sha; STATE.md says dev moved to 6521f18c4 at 02:20 EDT with tools-only gate commits, so the books and host measured here are unchanged by that move). Survivor list: `briefs/CUT-LEAD-20261016.md` section 3; foundation hold: `CUT-INVENTORY-20261016.md` tier C. Companion docs in this directory: `INTERFACES-TODAY.md` (what each component exposes), `EMBER-ARCHITECTURE-WORDS.md` (ember's intents), and `../REPRESENTATION-HISTORY-20261028.md` (the octet-list story; not repeated here).

## 0. The answer in five lines

1. **The leaves lift whole: 250 books, 144.9K lines (22% of the 652K book lines at dev), 39.4K executable-definition lines, 9.0K theorems, about 5,110 s of summed per-book certify wall** (224 of the 250 books are timed in the hbox run cited in section 1). The set is closed under include-book. It is the generator/DSL layer, the wire grammar and article parser, the crypto specs (BLAKE3, SHA-256, HMAC, SCRAM/SASL), the identity and acceptance kernel, the crash model and log kernel, the BP bundle and node machine, TCPCL, the page store, and the runtime contract. None of these books reaches the owner tuple, the store node, the catalog's held row, `served`, the history columns or any store-side structure (section 1 gives the test). The full list is Appendix A.
2. **The middles do not lift whole.** The NNTP command surface (`nntp-*`), the concrete log kernel and the recovery refinement, the BP application/FNBS publication layer, TLS policy and the auth wrapper all reach the old store through one to three include edges each. Those edges are named per family in section 2. Usually the include is there for one accessor or one constant, so the verdict is LIFT DEFINITIONS and re-prove against fn2's store, not a rewrite.
3. **The host lifts almost nothing whole.** 74K lines, of which `io.lisp` (10.4K) and `owner.lisp` (9.9K) hold 131 of the 271 lines that call `fnn-octet-list` (REPRESENTATION-HISTORY counts 263 with a stricter pattern). The narrow, reusable host pieces are the FFI seams: `tls.lisp` (OpenSSL), `crypto.lisp` (libsodium), `signatures.lisp` with `fn-mldsa65.c` (vendored PQClean), `digest.lisp` with `fn-blake3.c`, `fn-deflate.c`, and the socket and mux primitives.
4. **"TLS with our own crypto" is not what the tree has.** TLS is OpenSSL 3.5.8 through SBCL alien calls (`host/native/tls.lisp:1-20`). Ed25519 is libsodium (`crypto.lisp:9-12`). ML-DSA-65 is vendored PQClean C. BLAKE3 has an ACL2 definition with proved buffer and stobj twins, but the served image runs the vendored C (`digest.lisp:1-25`). SHA-256 and HMAC are pure ACL2 (they feed SCRAM). What lifts is the proved specifications plus the FFI seams; nothing in the tree is "our own TLS".
5. **The black-box natives are fn2's classical gate; the rest are not.** Of the 247 `tests/test_native_*.py` modules (57K lines), about 87 drive a node only through `Node`/`Client`, that is a socket and the CLI (27.5K lines). They carry over if fn2 keeps the CLI, `fn.toml` and control-socket surface, or if `tests/native_harness.py`'s `Node` class (one class, `native_harness.py:1413`) gets an adapter. About 75 run raw Lisp or mocks against host internals and about 17 assert on source text; those die with the old host. The load harness (`tools/load`, 11K lines) drives loopback sockets and carries; its `hooks/*.lisp` (in-image probes) do not.

## 1. Method and what the numbers mean

- **Tree.** `git archive origin/dev books host tests tools specs` was extracted into a scratch directory. There are 1,440 book files (including `books/proto/`), 652,201 lines, and the host is 74,374 lines.
- **lines** = `wc -l`. **exec** = lines spanned by executable definition forms: `defun`, `defund`, `define` (only up to its `///`), `defun-inline`, `defexec`, `defstobj`, `defabsstobj`, `def-loop`, `def-representation`, `def-buffer`, `defrecord`, `deftransition`, `defevent`. A real s-expression reader is used (comments, strings and `#| |#` are blanked), and it recurses into `encapsulate`, `progn`, `local`, `defsection` and `mutual-recursion`. **thm** = `defthm`, `defthmd`, `defrule*`, `defkeystone` forms, plus the theorems inside `define`'s `///`. Over the whole tree this gives 162,006 exec lines and 37,005 theorems.
- **Certify time** comes from the only hbox manifest with per-book walls: `/tank/fn/scratch/spans-view-walks/native-c19-vw/tree/build/acl2/certify-20261012T093213Z-3279561/manifest.json` (`book_wall_seconds`, 1,282 books, 22 slots, 900 s per-book budget, status failed with 19 book failures) plus its sibling `certify-20261012T091354Z-3204821` (72 books). It is a lane tree from 2026-10-12, so books newer than that have no time, and a figure near 900 s is a timeout, not a certify. The run the brief names, `native-cut-wave3-a45ccba6d` (`certify-20261028T013510Z-559277`), installed all 1,321 books from the cert cache (`fasl_installed 1321`, `certify_wall_seconds 0.002`, empty `certify.log`). It holds no per-book times.
- **Narrow / wide.** A book is **wide** if its include-book closure contains an *anchor*: the owner (`owner-*`), the store node (`store-node`), the catalog or its held row (`catalog`, `catalog-logic`, `catalog-paged`, `catalog-record`, `held-*`), `served`, `history-columns`, or `image-world*`. These are exactly the old tree's one-owner state and the representations fn2 replaces. A narrow book is **pure** if, in addition, its closure reaches no store-side structure outside its own family: `group-*`, `msgid-*`, `payload-arena*`, `payload-extent*`, `reclaim-*`, `body-chunks*`, `decoded-*`, `article-arena*`, `store-*` (other than the log family's own), `control-*`, `peer-*`, `hybrid-*`, `stx-*`, `index*`, `consumer-*`, `config*`, `native-*`, `node-*`, `statement*`, `lace*`, `page-read*`, `runtime-*` other than `runtime-contract*`, `allocation-*`. The **lift set** is the union of the pure books' closures (Appendix A). That union adds only twelve small leaves: `clock`, `journal-publish`, `node-secret`, `octet-window`, `outcome-class`, `path`, `path-update`, `payload-deflate`, `payload-kinds`, `payload-lz-value`, `profile-limits` and `snapshot-source-token`. `mailbox` (the RFC 5322 mailbox-list parser), `journal-publish` (immutable no-replace publication, 135 lines) and `node-secret` (the root-key derivation, closure of 6 books) were checked by hand and are leaves despite their names.
- **Boundary edge** = the first include on the shortest include path from a wide book to an anchor (breadth-first). Every edge quoted below was spot-checked with `git grep -n include-book origin/dev -- books/<f>.lisp`.
- **Families** are filename globs; each family's glob is stated in its section. 229 books are in no candidate family. They are the cut-eligible remainder: owner, store node, catalog, history, served, consumer, peer/feed, config, payload, image-world and so on.
- **Octet-list exposure.** The host count is `fnn-octet-list[^-a-z]` per file. In books, a definition counts as octet-list-typed if its first 1,500 characters name an octet-list recognizer (`fn-*octet*listp`, `unsigned-byte-listp 8`, `nat-listp`, `byte-listp`). This is an indicator and it undercounts: many list functions are untyped (REPRESENTATION-HISTORY section 2.1).
- **What fn2 changes**, as the verdicts use it (from `../REPRESENTATION-HISTORY-20261028.md` section 4 and CUT-LEAD section 1): (i) an article's bytes are one handle into one byte-pool extent from socket read to log write, and the octet list is `:logic` only; (ii) one owner with a typed root record instead of the 15-, 14- and 9-element cons tuples (`fn-own-make`, `fn-sn`, the view); (iii) the store's live state is fixed-width u64 column pages plus a byte pool, the log holds wire-ready payloads, and checkpoints are by dirty page (D41, DESIGN-RESOURCE-MODEL); (iv) semantics first, so certify is not a gate and proofs are re-proved later. Under (i), a book whose executable functions take octet lists still lifts as a **specification**. Its definitions are the `:logic` side and fn2 adds the buffer `:exec`. That is LIFT WHOLE for the proof and LIFT DEFINITIONS for the executable path. The tables say which side each family needs.

## 2. The families

Each row reads books / lines / exec lines / theorems / summed certify seconds (number of books timed). **PURE** books are in the lift set. **MID** books are narrow of the anchors but reach store-side structure. **WIDE** books reach an anchor.

### 2.1 Wire grammar and command surface (NNTP executable books)

Glob: `mailbox`, `nntp`, `nntp-*` except `nntp-auth*`, `wire*`, `wildmat*`, `utf8`, `decimal-text`, `octet-text`, `cbor*`, `protocol-*`, `raw-dispatch-verdict`, `response-*`, `nov-fields`, `string-line*`, `cancel-lock*`, `deflate*`, `article`, `article-{fields,header-*,kind*,line-bound,properties,subject,invariants,buffer}`.

| set | books | lines | exec | thm | certify |
|---|---|---|---|---|---|
| all | 86 | 48,060 | 11,922 | 2,771 | 1,406 s (80) |
| PURE | 31 | 17,503 | 4,603 | 1,004 | 283 s (30) |
| MID | 47 | 25,569 | 6,204 | 1,519 | 807 s (43) |
| WIDE | 8 | 4,988 | 1,115 | 248 | 316 s (7) |

**PURE (lift whole):** `wire-grammar` (2,232 lines, 185 thm: "one grammar language, one interpreter, and its two round trips proved once for every well-formed grammar", the grammar is data and is exported as `build/box/wire-grammar.json` for Mini's Lean interpreter), `wire-lines`, `wire-family-identity`, `wildmat`, `wildmat-work`, `utf8`, `octet-text`, `decimal-text`, `mailbox` (RFC 5322/5536 From), the article parser (`article`, `article-fields`, `article-header-census`, `article-header-limits`, `article-invariants`, `article-kind`, `-kind-acceptance`, `-kind-codec`, `article-line-bound`, `article-properties`, `article-subject`), `cancel-lock-lines`, CBOR (`cbor`, `cbor-invariants`, `cbor-record-scalar`, `cbor-record-stream`), `deflate-inflate` (3,039 lines, 171 thm), `deflate-frame`, `nov-fields`, `protocol-table` (1,264 lines; "one row per command", read by `tools/protocol_emit.py` without evaluation; the source of the dispatcher's arms, the RFC citations, the fuzzer grammar and the FAQ), `protocol-served-table`, `response-identity`.

**MID (lift definitions, re-prove later): the line codec and the whole command surface, because of one representation.** `wire.lisp:21` is `(include-book "body-chunks") ; the body held in article mode (B6)`. Every book above `wire` therefore inherits the B6 packed-bignum body, which REPRESENTATION-HISTORY section 2.3 lists for deletion (POST steps 3-4). That covers `wire`, `wire-scan` (+`body-chunks-span`), `wire-span`, `wire-invariants`, `wire-outbound-invariants`, and through `nntp-syntax.lisp:9-12` (`acceptance`, `wire`, `wildmat`) every `nntp-*` book. The command books then reach the old store directly:
- `nntp-responses.lisp:12,26,2710` include `reclaim-tombstone`, `article-arena-reads` and `msgid-index`;
- `nntp-session.lisp:9` includes `payload-arena`;
- `nntp-range-indexed` includes `group-bucket-article`, and `nntp-invariants` includes `group-bucket-cursor-invariants`;
- `nntp-post` includes `group-status` and `moderation`;
- `nntp.lisp` includes `control-served` and `peer-catchup-serve`;
- `nntp-enrollment` includes `stx-reader`, `hybrid-lifecycle` and `group-bucket-index`;
- `nntp-index(-runtime)` include `index`;
- `string-line-*` and `wildmat-cursor` go through `nntp-responses`.

The dispatcher's *decisions* (reply codes, range parsing, the reader state machine `nntp-session`, `nntp-syntax` at 562 lines and 304 exec) are the product. What they read (group buckets, the Message-ID index, the arena, tombstones) is the old store. **Verdict: LIFT DEFINITIONS.** Lift `nntp-syntax`, `nntp-session`, `nntp-responses`' reply rendering and `nntp-projection` as the command semantics, rebound to fn2's read interface (columns and spans). Re-prove the effects/invariants books (`nntp-effects` 155 thm, `nntp-invariants` 107, `nntp-spans` 205 at 451 s) once fn2's store exists. `wire` and `wire-scan` lift with the body held as a buffer span instead of `body-chunks`.

**WIDE (rewrite or drop):** `article-buffer` (→ `login-binding-live` → `owner-config`), `protocol-served` (`protocol-served.lisp`: includes `served-catalog-dispatch` and `served`), `nntp-help` (→ `nntp-auth`), `raw-dispatch-verdict` (→ `state-digest` → `store-intern` → `catalog-record`), `deflate-pool` and `-pool-check` (→ `payload-lz-record`), `wire-export` and `wire-family-consumer` (→ `consumer-reason` → … → `store-events` → `held-record`). `protocol-served`'s claim ("every reply code the dispatcher emits is in that command's row") is worth keeping as a statement; re-prove it against fn2's dispatcher. `wire-export` is the JSON exporter for Mini; rewrite it over `wire-grammar` alone (the consumer family it drags is cut-eligible).

**Host:** `host/native/mux.lisp` (2,362 lines; socket accept, plain and TLS read, write ranges: `fnn-mux-read-plain` is POST step 1) holds the reusable primitives. The command loop itself lives in `owner.lisp` (9,915 lines, 50 `fnn-octet-list` calls) and does not lift (section 3).

**Corpus and fixtures that carry:** `tests/fixtures/source-corpus/` (8 articles: client-path, generated-date, legacy, mime, signed, supplied-date, unknown-headers, xref); `tests/fixtures/fuzz-nntp/` (9 JSON cases: endless-body IHAVE/TAKETHIS, QUIT-then-AUTHINFO/STARTTLS/CAPABILITIES in the same read, torn/flipped store imports); `tests/fuzz_nntp.py` (1,695 lines, grammar from `protocol-table`); `tests/interop_nntplib.py`; `tests/interop_cbor.py` (450 lines); `tests/inn/pin.json` (INN 2.7.4 pinned by tarball sha256, the interop lab on hbox `/tank/fn/inn/2.7.4`); the RFC texts in the repo root (3977, 2980, 4642-4644, 4707, 5536, ...). ACL2 test books (`tests/acl2`) whose every book include is in the lift set and mostly wire: 8 (1,177 lines: wire-grammar, article, article-kind-codec, article-fields, wildmat, cbor, cbor-teeth, response-identity). Over all families, 77 test books (12,539 lines) lift with the set.

### 2.2 Authentication, acceptance, identity binding

Glob: `auth-*`, `sasl`, `scram`, `login-binding*`, `acceptance*`, `identity*`, `injection*`, `accounts`, `account-list`, `principal*`, `policy*`, `posting-account`, `nntp-auth*`, `served-auth-wire-bridge`.

| set | books | lines | exec | thm | certify |
|---|---|---|---|---|---|
| all | 34 | 22,984 | 4,720 | 1,156 | 126 s (28) |
| PURE | 15 | 7,521 | 2,169 | 382 | 51 s (15) |
| MID | 7 | 3,159 | 776 | 156 | 38 s (7) |
| WIDE | 12 | 12,304 | 1,775 | 618 | 36 s (6) |

**PURE (lift whole):** `sasl` and `scram` (SCRAM-SHA-256 over `hmac-sha256`, `sasl.lisp:48-49`), `auth-secret`, `identity` (the v1 content identity, `subject-v1 = BLAKE3("fn/subject/v1" || 0x00 || u32be(len) || payload)`, rendered by `fn-id-render`), `identity-hex`, `identity-invariants`, `acceptance` (+`-alloc`, `-invariants`), `injection` (1,270 lines), `injection-invariants`, `-path`, `-shape`, `-info-policy`, `posting-account`. Certify cost is trivial (51 s summed).

**MID:** `principal`, `policy` (and their invariants) include `statement` (`principal.lisp`: one include; `policy` also `lace` and `statement-invariants`). The statement/keyring layer is 16 books / 5.7K lines in closure and carries the signed-statement grammar (cut-eligible on its own merits). `accounts` includes `config`, `native-admin-shape` and `consumer-position`. `auth-credentials` reaches `body-chunks` through `nntp-syntax`. **Verdict: LIFT DEFINITIONS.** The principal/policy decision functions are small (principal 169 exec, policy 263); bind them to fn2's key store and drop the `statement` include.

**WIDE:** the served AUTHINFO/STARTTLS wrapper `nntp-auth` (4,652 lines, 1,075 exec, 199 thm). It is the outermost link of the served chain `fn-served-dispatch → fn-auth-step → fn-peer-step → fn-nntp-post-step → fn-nntp-step` (`nntp-auth.lisp:3-12`) and includes `peer-inbound`, which reaches `held-record` through `config-records → replay → store-events`. `nntp-auth-fold`, `-invariants` and `-roles` follow it. `login-binding.lisp` includes `peer-authored-accept` and `owner` directly. `acceptance-payload-ref` includes `owner`, `store-node-traces-prepare`, `history-columns-relation` and `byte-store-scan`; `acceptance-stamp-invariants` includes `store-node-invariants`; `identity-retain-carried` includes `owner-refresh-indexed` and `owner-prepare-outcome`; `injection-info-params` includes `poster-bytes` and `config`; `served-auth-wire-bridge` includes `served`. **Verdict: REWRITE the wrapper** (it is defined by the old served chain's signature, `fn-peer-step`'s, so fn2's dispatcher shape decides it). **LIFT DEFINITIONS** for the AUTHINFO state machine inside `nntp-auth` (the RFC 4643 USER/PASS/SASL step and the STARTTLS refusal rules) and for `login-binding`'s decision, rebound off `owner`.

**Host:** `auth.lisp` 96, `auth-read.lisp` 14, `auth-admin.lisp` 540, `login-bindings.lisp` 69, `keys.lisp` 104, plus `host/native-auth-host.lisp` and `native-auth-admin-host.lisp` (definterface wrappers). Small. `auth-admin` is operator surface. None calls `fnn-octet-list` more than in passing; the auth host is not where the list traffic is. Natives: `sasl`, `auth`, `starttls`, `implicit_tls`, `injection_info`, `friends_accounts` (black-box, carry); `auth_lock`, `auth_admin_fidelity` (raw, do not).

### 2.3 The durable log and its recovery refinement

Glob: `store-log*`, `byte-store*`, `frame*`, `records*`, `recovery-*`, `assumptions*`, `store-files*`, `store-octet-entry`, `store-replay-bound`, `store-open-replay*`, `store-genesis`, `store-init*`, `state-digest`.

| set | books | lines | exec | thm | certify |
|---|---|---|---|---|---|
| all | 107 | 54,047 | 8,367 | 3,223 | 1,110 s (87) |
| PURE | 42 | 17,744 | 3,310 | 1,162 | 335 s (39) |
| MID | 3 | 165 | 72 | 3 | 2 s (3) |
| WIDE | 62 | 36,138 | 4,985 | 2,058 | 773 s (45) |

**PURE (lift whole), and this is the asset:**
- **The crash model.** `byte-store` (697 lines; "a table of inodes (octet lists), a table of directories, and an ordered list of PENDING operations … fsync(fd) drains exactly that inode's pending writes … a crash keeps the durable tables and lands an arbitrary subsequence of the pending operations, each write cut into write-unit pieces that land, land as zeros, or land as garbage … a failed fsync lands a torn selection and discards the rest (fsyncgate)", `byte-store.lisp:1-14`), `byte-store-invariants` (128 thm), `-txn-name`, `-txn-seam`, `-range-read`, `-observation`.
- **The log model.** `store-log` (1,689 lines, 137 thm: FNLG frames chained by the previous trailer, kind 1/kind 2 chunks, greedy chunking under the frame bound), `store-log-kernel` (the relation `fn-lgk-relp`: one pending write at the frontier, one fence), `store-log-crash`, `-decode`, `-extend`, `-lineage`, `-programs`, `-recover`, `-segments`, `-txid`.
- **Frames.** `frame`, `frame-fields`, `frame-invariants` (87 thm), `frame-journal`, `frame-octets`, `frame-trailer`, `frame-buffer`, `frame-digest-buffer`.
- **The record codec.** `records` (the 11-tuple over deterministic CBOR), `records-shape`, `-invariants`, `-canonicality` (76 thm), `-codec-concrete`, `-seam`, `-stamp`, `-exec`, `-attach`, `-attach-concrete`.
- **The premises.** `assumptions` (the platform assumptions as named premises), `assumptions-durable`, `-pgs-host-io`, `-runtime`, `-spans`. Also `recovery-payload-view` and `recovery-refinement-pages`.

These are specifications over octet lists by design (crash-model-v2 section 1: the byte store is a model, and the host does the syscalls), so lifting them whole is correct. The one representation caveat is `records`: the encoder is a fourteen-way `append` (REPRESENTATION-HISTORY section 3.2, boundary 7 never re-done on dev). It lifts as the `:logic` side, and fn2 adds a buffer encoder against it. The crash model's known gaps travel with it: STATE.md 2026-10-28 01:14 lists 22 rows, among them no corruption at rest, no misdirected or lost writes after a successful fsync, no read outcome, no concurrency, crash-during-recovery or fail-slow. fn2 inherits a model to *extend*, not one to trust as is.

**WIDE: the concrete kernel and the recovery refinement, through three edges.**
1. `store-log-route.lisp:9` → `records-concrete`. Lines 51-53 of `records-concrete.lisp` include `store-node`, `consumer-store-projection` and `topic-history-prefix`. `records-concrete` is a correspondence-twin book ("the twins below it (fn-rcon-store-event-*, fn-rcon-sf-record-pair, fn-rcon-sn-record-bindsp, …) are their references with fn-record-p replaced", lines 22-26). It uses `fn-sn-*` eleven times. This one edge makes the following wide: `store-log-route`, `-route-programs`, `-route-phases`, `store-log-kernel-concrete` (989 lines, 110 s), `store-log-durable` (1,633), `store-log-prefix-durable` (1,093, 110 thm), `store-log-recover-copy` (2,927, 208 thm, 100 s), and on the rtc side `post-transaction-durable` and `post-transaction`.
2. `store-files.lisp:29,32` → `replay` (→ `node-invariants`, `store-events`, `hybrid-store`) and `store-records-field` (→ `history-columns`, `history-paged`, `history-records-disk`). This makes the following wide: `store-files*`, `byte-store-scan` (3,108 lines, 154 thm), `byte-store-frame`, `byte-store-programs`, `byte-store-keystones`, `store-genesis`, and **`recovery-refinement`**, whose path is `byte-store-state-checkpoint-program → byte-store-programs → store-files-traces → store-files-invariants → store-files`. With it go `recovery-refinement-concurrent`; `recovery-refinement-store`, which also includes `owner-checkpoint-writer`, `store-checkpoint-open`, `checkpoint-reserve` and `store-recover-stream` directly; and the `byte-store-k0*` and `byte-store-record-provenance*` books (→ `store-node`).
3. `store-log-buffer` → `payload-extent` → `payload-arena`, `store-intern` → `catalog-record`. Also `store-log-open-scan` → `history-totals-carried` → … → `owner-invariants-served`, and `state-digest` → `store-intern`.

**Verdict.** The kernel's *statements* are the most valuable thing in the quarry. `recovery-refinement.lisp:1-14` composes the log layer (`fn-lgk-relp`) and the page layer into one recovery refinement in Argosy's shape (Chajed et al. PLDI 2019) as DFSCQ's tree sequence. **LIFT DEFINITIONS and statements, RE-PROVE LATER** for `recovery-refinement*`, `store-log-durable`, `-prefix-durable`, `-recover-copy`, `-kernel-concrete` and `store-log-open-scan`. Their proofs route through the old store-file model and the record twins, which fn2 does not have. Cut the `records-concrete` edge (fn2 has no list twin to correspond to) and the `store-files` edge (fn2's state is columns, not the store-files record list), then re-prove. The `byte-store-scan/-frame/-programs` group models the old file layout (FNST frames, `.fnsc` checkpoints, store files). **REWRITE** it against fn2's on-disk format, keeping `byte-store` as the model it runs over.

**Host:** the log lives in `io.lisp` (10,418 lines; 81 `fnn-octet-list` calls, the most of any file): `fnn-log-take`/`-take-verdict` (POST steps 15-16), `fnn-log-pwrite` (step 18), `fnn-log-stream-segment`, the barriers. Also `checkpoint.lisp` (520), `store-identity.lisp` (113) and `host/store-host.lisp`. **REWRITE**: the syscall sequence (pwrite, fdatasync, the dirfd fsync, rename) is the part to keep, written down in `specs/storage.md` (2,232 lines, KEEP per the inventory). The list-to-vector conversions around it are the part to delete.

**Natives that judge it (black-box, carry):** `replay_determinism`, `served_crash_model`, `commit_log`, `log_compaction`, `checkpoint`, `snapshot_bless`, `store_lineage`, `store_identity`, `reclaim_seal_cost`, `reclaim_in_flight`, and the campaign `tests/campaign/native_production_kill.py` and `native_cuts.py` (kill-9 and cut injection). `slow_disk` (1,362 lines, disk-stall selector) and `recovery` drive developer selectors and in-image ACL2. They carry only if fn2 keeps the fault-injection selectors, and it should, since a stalled disk is in ember's crash model.

### 2.3a Page store and paged checkpoint (tier C foundation hold)

Glob: `pagestore*`, `paged-checkpoint*`.

| set | books | lines | exec | thm | certify |
|---|---|---|---|---|---|
| all | 24 | 16,418 | 2,843 | 1,314 | 41 s (6) |
| PURE | 18 | 12,583 | 2,361 | 976 | 41 s (6; the digest-cursor books post-date the timed run) |
| WIDE | 6 | 3,835 | 482 | 338 | none timed |

**PURE (lift whole):** `pagestore` (the model), `pagestore-exec` (3,016 lines, 203 thm; the stobj `pgs-mem`, flat table entries as words, the word BLAKE3 over table pages in place), `pagestore-words`, `-words-blake3`, `-gc`, `-reclaim`, `-refine`, `-keystones` (2,595 lines, 271 thm), and the eleven `pagestore-digest-*` cursor books. The closure outside the family is eight leaves (`blake3`, `blake3-stobj`, `cbor`, `def-buffer`, `def-loop`, `octet-window`, `octets-stobj`, `rev-onto`). This is the narrowest family in the tree and already a stobj representation. It is the natural floor for fn2's page layer.

**WIDE:** every `paged-checkpoint*` book. `paged-checkpoint` includes `owner-checkpoint-open`; `paged-checkpoint-host` includes `catalog-pages` and `catalog-availability-owner-load`; `-image` includes `history-pages-relocate`; `-open` includes `statement-recover-stream` and `consumer-event-index`. On dev `paged-checkpoint.lisp`'s `fn-pck` has 0 executable functions; the host realization is on `salvage/s-pck-host` e9baa5a99 and `lane/log-lc` d999a7fc4, both unmerged (REPRESENTATION-HISTORY 3.2). **Verdict: LIFT DEFINITIONS** (the dirty-page-plus-root checkpoint shape is D41's design). Re-prove it against fn2's root record.

### 2.4 The BP node machine ("BP is product", ember 2026-10-08)

Two globs. **bpnm** (the machine): `bp-node*`, `bp-primary*`, `bp-bundle*`, `bp-eid*`, `bp-adu`, `bp-fragment*`, `bp-clock*`. **bprest** (applications, FNBS publication, receivers, workflow, TCPCL): every other `bp-*`, plus `tcpcl-*`.

| set | books | lines | exec | thm | certify |
|---|---|---|---|---|---|
| bpnm all | 67 | 35,540 | 8,690 | 1,552 | 664 s (59) |
| bpnm PURE | 27 | 17,744 | 4,065 | 841 | 268 s (27) |
| bpnm MID | 6 | 2,257 | 895 | 77 | 97 s (6) |
| bpnm WIDE | 34 | 15,539 | 3,730 | 634 | 299 s (26) |
| bprest all | 116 | 38,195 | 11,339 | 1,690 | 1,103 s (101) |
| bprest PURE | 30 | 10,312 | 2,887 | 664 | 151 s (27) |
| bprest MID | 37 | 11,302 | 3,305 | 434 | 158 s (28) |
| bprest WIDE | 49 | 16,581 | 5,147 | 592 | 794 s (46) |

**PURE (lift whole):**
- **bpnm, BPv7 (RFC 9171) and the outbound lifecycle machine.** `bp-primary` (1,587 lines), `bp-primary-cbor`, `bp-primary-invariants`, `bp-bundle`, `bp-bundle-invariants`, `bp-adu`. The `bp-fragment*` set: `bp-fragment`, `-fast`, `-invariants`, `-job-shape`, `-resume`, `-send` (98 thm), `-sweep`. The machine: `bp-node`, `bp-node-machine` ("Outbound BP lifecycle: durable queue, contact, attempt and restart … The host calls fn-bpn-step. It may observe time, sockets and persistence outcomes, but it does not decide queue admission, retry, expiry or what bytes are sent", `bp-node-machine.lisp:1-7`), `bp-node-machine-authorization`, `-guards`, `-invariants` (2,320 lines, 129 thm), `bp-node-foundation`, `bp-node-profile`, `-records`, `-budget-input`, `-fragment-family`, `-fragment-plan`, `-host-sequence`, `-host-transfer`, `-rotation-slice`.
- **bprest, TCPCLv4 (RFC 9174) whole.** `tcpcl-session` (2,229 lines), `tcpcl-octets`, `tcpcl-records`, `tcpcl-invariants`, `tcpcl-delivery*`, `tcpcl-spool`, `tcpcl-received-source*`, `tcpcl-segment-source-cursor`, `tcpcl-frame-cursor`, `tcpcl-retained-turn`, `tcpcl-source-*`, `tcpcl-host-drive`, `tcpcl-input-materialize`, `tcpcl-received-count`.
- **bprest, also pure:** `bp-status-report` (+invariants), `bp-signed-receipt`, `bp-request-ref`, `bp-session-profile`, `bp-session-received-source`, `bp-carry-frame`, `bp-authored-wire`, `bp-contact-service`, `bp-handoff-report`, `bp-handoff-recovery-shape`, `bp-ion-lifetime`, `bp-run-class`.

**MID.**
- **Six bpnm codec books and the FNBS layer depend on `consumer-position`.** These are `bp-node-machine-codec`, `bp-node-rotation-codec`, `bp-node-receive-boundary`, `bp-node-host-machine` and `bp-clock-domain`, plus 17 `bp-fnbs-*` books through `bp-fnbs-namespace`. `consumer-position` is the E2 consumer decision kernel (1,061 lines, closure of six books). The edge is real: FNBS publication reuses the consumer-position codec. `bp-eid-shape` includes `config` and `peer-adoption-receipt-rows`.
- **The `bp-workflow*` and `bp-release*` books include `node-invariants`**, and some also include `msgid-index`.
- **Verdict: LIFT DEFINITIONS.** The codecs are small (`bp-node-machine-codec` 287 exec). Re-home the one consumer-position codec dependency, or keep `consumer-position` if fn2 keeps consumers.

**WIDE: one edge carries the node machine's whole progress half.** `bp-node-progress.lisp` includes `bp-app-handoff-time`, which includes `bp-app-handoff`, which includes `bp-native-app` and `bp-session-admission`. `bp-native-app.lisp` includes `store-observed`, `served`, `owner-feed` and `msgid-index`. That makes the following wide: `bp-node-progress` (1,976 lines, 1,625 exec), `-progress-bridge`, `-guards`, `-premises`, `-selection-invariants`, `bp-node-rotation*`, `bp-node-job-*`, `bp-node-fragment-step`, `-replacement`, `-expiry`, `-job`, `-guards`, `bp-node-forward-*`, `bp-node-receipt-send`, `-report-step`, `-retire`, `-debt`, `-dispatch`, `-busy-delivery`, `-contact-driver`, `-listener-control`, `-profile-admission`, `-profile-replay` and `bp-node-machine-gaps`. On bprest's side the same edge, plus `bp-ingress` → `store-node` and `store-intern` and `bp-receipt` → `bp-ingress`, makes all the `bp-receiver-*-invariants` books wide (10 books, 4.9K lines, about 220 thm), along with `bp-native-app*`, `bp-app-handoff*`, `bp-session-admission` (105 s), `bp-heap-command` (→ `heap-reservation`, `output-reservation`), `bp-held-payload` (→ `catalog-record`) and `bp-release-authority` (→ `hybrid-lifecycle`).

**Verdict.**
- **bpnm PURE: LIFT WHOLE.** This is the outbound machine and the bundle codec, 17.7K lines whose host contract is already "observe, do not decide".
- **bp-node-progress and its dependants: LIFT DEFINITIONS, RE-PROVE.** The progress *selection* logic does not need the application handoff. The include exists because `bp-app-handoff-time` supplies the handoff deadline. Cut that edge to a parameter and most of the 34 become narrow.
- **The receiver invariants: REWRITE** against fn2's store; they state facts about `store-node` traces.
- **bp-native-app / bp-app-handoff: REWRITE.** They are the old owner's application bridge.

**Host:** `bp-service.lisp` 1,700, `bp-node.lisp` 1,429, `bp.lisp` 902, `workflow.lisp` 846, `bp-session.lisp` 431, `bp-app.lisp` 423 (17 `fnn-octet-list`), `bp-obligation.lisp` 402, `bp-control.lisp` 248, `bp-listener-control.lisp` 101, `bp-contact.lisp` 84, `tcpcl.lisp` 1,054, `build-dtn.lisp` 534 (the DTN image). That is about 8.2K lines with 44 `fnn-octet-list` calls; **LIFT DEFINITIONS** for the socket and TCPCL framing loop and rewrite the rest. **Specs:** `specs/bp-node-machine.md` (5,238 lines, the largest spec), `bp-design.md` 1,217, `bp-primary.md` 371, `bp-path.md` 350, and smaller ones (`bp-adu`, `-ingress`, `-outbound`, `-receipt`, `-receive`, `-workflow*`, `-receiver-proofs`, `-evolving-store`).

**Interop and fixtures that carry:** `tests/bp-dtn7/` (dtn7-rs 0.21.0 at 4daf02d7ea92 pinned; golden bundles `dtn7-rs-0.21.0-authored.bundle` and `fn-authored-accepted-by-dtn7-rs-0.21.0.bundle`; drivers `run_fn_bp_interop.py`, `run_fn_tcpcl_interop.py`, `run_fn_tcpcl_spool_recovery.py`, `run_fn_bp_sequence_durability.py`, `run_fn_dtn7_app_receipt.py`, `run_fn_dtn7_interrupted_contact.py`, `run_mission_four_node.py`); `tests/ltp/` (ION-DTN BP-over-LTP feasibility lab, `fn_ltp_send.c`, `fn_ltp_stage.c`); `tools/load/faults_bp.py` (893 lines). **Natives:** `source_corpus_bp` (black-box, carries). `ion_ltp`, `ion_workflow`, `ion_receipt_recovery` drive the ION lab. The 16 `bp_*` / `bpapp_*` / `tcpcl_acquisition` modules are raw-Lisp probes of host internals (14-46 lines each); they do not carry.

### 2.5 TLS and the crypto

Glob: `tls-*`, `blake3*`, `sha256`, `hmac*`, `crypto-*`, `hybrid-signature`, `key-statements`, `served-implicit-tls`, `served-tls-prefix`, `anchor*`.

| set | books | lines | exec | thm | certify |
|---|---|---|---|---|---|
| all | 25 | 13,654 | 3,798 | 708 | 193 s (23) |
| PURE | 14 | 7,604 | 2,036 | 431 | 94 s (13) |
| MID | 3 | 1,608 | 697 | 68 | 24 s (3) |
| WIDE | 8 | 4,442 | 1,065 | 209 | 75 s (7) |

**What "our own crypto" is in this tree:**

| primitive | specification (book) | what the served image runs | trust boundary file |
|---|---|---|---|
| BLAKE3 | `blake3` (1,066 lines, 41 thm), `blake3-stobj` (proved `fn-blake3-stobj-is-blake3`), `blake3-string`, `blake3-tree` (window decomposition, 124 thm; tier C) | vendored reference C, `third_party/blake3` 1.8.7, through `fn-blake3.c` (191 lines) as `libfn-blake3`, after a start-up check against the ACL2 definition | `host/native/digest.lisp` (551) |
| SHA-256, HMAC-SHA-256 | `sha256` (544), `hmac-sha256` (386) | the ACL2 definitions (SCRAM only) | none |
| Ed25519 | `crypto-seam` (284; the constrained seam), `crypto-attach` | libsodium through `sb-alien` (`crypto.lisp:9-12`: "the stable libsodium C ABI already present on the supported development hosts") | `host/native/crypto.lisp` (243) |
| ML-DSA-65 | `hybrid-signature` (238; MID through `hybrid-profile`) | vendored PQClean, `third_party/pqclean-ml-dsa-65`, through `fn-mldsa65.c` (590) | `host/native/signatures.lisp` (383) |
| TLS 1.2/1.3, X25519MLKEM768 | `tls-key-exchange` (the policy `hybrid-preferred` / `hybrid-required` as an ACL2 decision over the observed group list), `tls-handshake-*`, `tls-self-signed`, `tls-reload`, `tls-proxy` | OpenSSL 3.5.8 shipped with the release (`tools/crypto_shipped.json`: "the shipped OpenSSL 3.5.8, no system fallback"; OpenBSD owed) through `sb-alien` (`tls.lisp:1-20`; 57 `define-alien-routine` forms) | `host/native/tls.lisp` (1,251), `tls-reload.lisp` (272) |
| DEFLATE | `deflate-inflate` (in the wire family) | zlib, `third_party/zlib`, through `fn-deflate.c` (108) | `host/native/deflate.lisp` (665) |

**PURE (lift whole):** `blake3`, `blake3-stobj`, `blake3-string`, `blake3-tree`, `sha256`, `hmac-sha256`, `crypto-seam`, `crypto-attach`, and the external freshness anchor (`anchor`, `anchor-invariants`, `anchor-record`, `anchor-replace`, `anchor-servers`, `anchor-wire`: FLR-003 and D10, the durable statement that lets a restore be shown newer than the history it claims to continue, `anchor.lisp:1-8`). They are specifications plus proved stobj twins, and fn2 should keep them as the reference the native code is checked against at start-up (the `digest.lisp` pattern).

**MID / WIDE (rewrite the policy glue, keep the decisions):**
- `tls-handshake-decision` → `connection-budget` → `heap-figure` → `owner-checkpoint-pipeline`. The TLS admission budget is computed from the old owner's heap figure.
- `tls-key-exchange.lisp` includes `native-config` and `heap-figure`.
- `tls-handshake-source` includes `native-config`, `node-config` (88-book closure), `public-exposure-rows` and `records-shape`.
- `tls-reload` → `native-control`. `tls-self-signed` → `native-config`, `nntp-responses`.
- `served-implicit-tls` and `served-tls-prefix` → `served`.
- `key-statements` → `control-authority`, `peer-authored-accept`, `history-wire` → `held-record`.

The decision functions are small: `fn-tlsk-decide` is a four-row table (`tls-key-exchange.lisp:16-26`), and `tls-handshake-decision` is 219 exec. **Verdict: LIFT DEFINITIONS** for the key-exchange policy, the handshake budget decision and the self-signed certificate rules. **REWRITE** their inputs (configuration and the memory figure) against fn2's config and resource model.

**Host:** **LIFT WHOLE, as files, for the FFI seams** `crypto.lisp`, `signatures.lisp` with `fn-mldsa65.c`, `digest.lisp` with `fn-blake3.c`, `fn-deflate.c`, and the OpenSSL binding in `tls.lisp` (alien routine table, error mapping, nonblocking read/write, the MSG_PEEK consume check). Each states its trust premises in its header and "decides nothing". `tls.lisp` has 4 `fnn-octet-list` calls and `tls-reload.lisp` 3; fix those as they lift. **What fn2 must decide:** whether "TLS with our own crypto" means this (proved specs, vendored C primitives, OpenSSL for the record layer) or an actual TLS stack of fn's own. Nothing in the quarry implements a TLS record layer or handshake. EMBER-ARCHITECTURE-WORDS records that D64's "our own thing" was a bundled OpenSSL 3.5.8.

**Natives (black-box, carry):** `tls_transport`, `tls_handshake_budget`, `tls_key_exchange`, `tls_proxy`, `tls_reload`, `starttls`, `implicit_tls`, `key_statements`, `hybrid_author`. Also carry `tests/mldsa65_interop.py`, `tests/test_blake3_exec.py` and `tests/blake3_proto.c`. `digest` and `tls_probe_off_lock` probe internals.

### 2.6 The generator / DSL layer (foundation; not on the survivor list, everything above stands on it)

Glob: `def-*`, `defrecord`, `deftransition`, `defevent`, `definterface`, `defkeystone`, `octets-stobj`, `proto/*`, `immutable-list`, `snoc-list`, `rev-onto`, `book-name-relative`, `packed-octets`, `fixed-buffer-capacity`.

| set | books | lines | exec | thm | certify |
|---|---|---|---|---|---|
| all | 39 | 30,469 | 14,106 | 1,482 | 697 s (39) |
| PURE | 35 | 28,364 | 13,281 | 1,368 | 670 s (35) |
| MID | 4 | 2,105 | 825 | 114 | 27 s (4) |

The family is 2.7% of the books by count and 8.7% of the tree's executable lines (macro bodies are code). Its closure leaves the family for 33 leaf books only (`cbor`, `decimal-text`, `blake3`, `sha256`, `pagestore`, `pagestore-words`, `octet-window`, `records*`, `frame*`, `utf8`).

**PURE (lift whole), by what each gives fn2:**
- **Representation.**
  - `octets-stobj` (1,425 lines; the abstract stobj `fn-octets`, a resizable `(unsigned-byte 8)` array whose logical value is the octet list; "the one place where a byte array is the executable and the octet list stays the logical view").
  - `def-buffer` (its congruent clones).
  - `def-representation` (2,427 lines, 2,132 exec: an abstract stobj from one schema declaration, `:scalar`, `:generic`, `:pages`, `:tree`).
  - `def-representation-paged`, `-pages`, `-pageread`, `-index`, `-index-lib`, `-lib`, `-generic`.
  - `proto/adt*`: `defadt`, typed columns plus one octet pool; marked "NOT on a served path", but it is the column-and-pool shape D41 asked for.
- **Loops.** `def-loop` (1,675 lines; the `:logic` structural recursion plus `:exec` accumulator twin, "generated instead of written"; 494 hand twins were the backlog, D62), `def-loop-run`, `def-span-scan` (3,315 lines, 1,668 exec, 454 s: loops over a span of an octet buffer with their list-model bridge, work bound and guards; CONCEPT-01 / RUNTIME-MODEL section 2), `def-cursor`, `def-cursor-batch`.
- **Proof style.** `defrecord` (the opaque-record pattern), `deftransition` (prove with the recognizer closed: 1,082 subgoals to 0.30 s), `defevent`, `defkeystone` (`defteeth`/`defkeystone`: a keystone's positive witness and per-hypothesis removal witnesses generated from the declared claim; the TEETH CONTRACT v1).
- **Host contract.** `definterface` (852 lines; one declaration per host-called entry: arity, guard kinds, byte-carrying formals; 1,934 forms in the tree per INTERFACES-TODAY), `def-carried` and `def-carried-writer` (2,481 lines; D40's carried invariants written from the world), `def-cost` (a visit cost derived from the executed body; "an unknown callee is UNACCOUNTED, never zero"), `def-keyset-check`.
- **Small.** `rev-onto`, `snoc-list`, `immutable-list`, `book-name-relative`.

**MID:**
- `def-holder` → `arena-reader-pins`. The generator ("holding is a declared relation") is right for fn2's buffer leases; its include is for one instance.
- `def-representation-tree` and `-tree-walk` → `store-tree-codec`, `store-checkpoint-codec`. The `:tree` field kind is encoded with the old checkpoint codec.
- `fixed-buffer-capacity` → `index-query-resources`, `page-read-*`.

**Verdict: LIFT WHOLE.** This is the layer ember's "metaprogramming, proof engineering, mechanical sympathy" names, and it is the least entangled code in the tree. Two cautions for fn2:
- **The generators encode the twin discipline** (`def-loop` emits a logic body and an exec body proved equal). That is fine for loops. It is the same pattern that let every buffer path land beside its list path (REPRESENTATION-HISTORY 3.1). fn2 should use `def-representation` / `def-span-scan` as the only executable path and keep the list strictly `:logic`.
- **`packed-octets`** (the bignum codec under `body-chunks`, B6) lifts but has no fn2 consumer if B6 is deleted.

### 2.7 The runtime contract, memory model and POST transaction (the new-model work; tier C)

Glob: `runtime-contract*`, `memory-*`, `admission-*`, `resource-*`, `post-transaction*`.

| set | books | lines | exec | thm | certify |
|---|---|---|---|---|---|
| all | 37 | 34,638 | 5,648 | 3,138 | 4,278 s (24) |
| PURE | 26 | 22,748 | 3,897 | 1,983 | 3,203 s (20) |
| MID | 2 | 1,313 | 235 | 142 | (1) |
| WIDE | 9 | 10,577 | 1,516 | 1,013 | 1,074 s (3) |

**PURE (lift whole):** `runtime-contract` (2,691 lines). Its header: "One executor runs many machine instances. Every effect an instance wants is an ACTION (kind id incarnation op args) handed to an I/O worker; the worker's answer is a COMPLETION … An instance learns that an effect happened only from its completion; submission establishes nothing" (`runtime-contract.lisp:1-14`). It is written once over a constrained instance machine, so instances get its theorems by `:functional-instance`. With it lift `-actions`, `-budget`, `-echo`, `-exec`, `-exec-is`, `-exhaustion`, `-host-send`, `-invariant` (+`-facts`, `-ops`), `-isolation` (4,183 lines, 361 thm), `-keystones`, `-landing`, `-layer`, `-list-facts`, `-opened`, `-pool`, `-pool-impl`, `-requests`, `-u64`, and `memory-credits`, `resource-vector` (190 thm), `resource-vector-exec`, `resource-syncer`, `resource-bp-session`.

**The cost to watch is certify time, not entanglement.** This family is 16% of the lift set's lines and about 63% of its summed certify wall (3,203 of 5,112 s). The worst books are `runtime-contract-actions` 574 s, `runtime-contract` 514 s, `-invariant` 379 s, `-budget` 329 s, `-isolation` 293 s, `-pool` 278 s and `-exec-is` 224 s. In the same run `memory-model` hit the 900 s budget (903.9 s). Under "certify is not a gate" this is information. It still says the contract's proofs are where fn2's first proof-engineering effort would pay.

**WIDE (lift definitions, re-prove):**
- `memory-model.lisp` includes `charged-totals` (→ `store-budget` → `store-node`), `heap-reservation`, `connection-budget`, `page-read-startup` and `served-plan-cursor`. It is the old store's charge accounting under the new contract. The *model* (the guardrail from W13, VmHWM 249 MB / RssAnon+Shmem 115 MB on the small preset) lifts as a statement; the charge sources are rebuilt from fn2's columns. `runtime-contract-host-pool` and `-host-lease` go wide through it. The lease array is the ARTICLE path's step 3 (`fn-hld-copy`, REPRESENTATION-HISTORY 2.3) and is a keeper.
- `post-transaction.lisp` (3,382 lines, 452 thm), `-durable`, `-sim` and `-layer`. This is landing 2's transaction machine. It goes wide through `post-transaction-durable` → `store-log-durable` → the `records-concrete` edge of section 2.3. `post-transaction-crash` (MID) reaches only `store-log`, `-crash` and `-kernel`, which are in the lift set. **LIFT DEFINITIONS:** the POST transaction is exactly what fn2 must get right (one value, one owner, socket to log), and its statement is reusable once the log edge is cut.
- `admission-memory` (→ `store-capacity-vector`, `history-totals-carried`), `admission-preallocation-resources` (MID: `index-query-resources`, `page-read-*`), `resource-output` (→ `output-reservation`).

**Host:** `host/native/rtc-exercise.lisp` (49), `heap.lisp` (753). The executor loop itself is in `owner.lisp` and `mux.lisp`, not in a file of its own; see `ENVELOPE-AND-HOST.md` in this directory. Natives: `heap_from_profile` (860 lines), `image_floor`, `image_heap`, `capacity_vector`, `bounds_join`, `credits`, `scaling`, `open_depth` (black-box resource rows, carry as fn2's guardrail tests); `heap_default_source`, `heap_graph`, `owner_measure` (internals).

### 2.8 The tier C foundation hold, book by book

CUT-INVENTORY tier C lists 73 books (32,473 lines at 49b470a99; 32,392 at dev) held because "LC / landing 2 / crypto / TLS rest on it". Placed in this survey's sets:

| where | books | lines | members |
|---|---|---|---|
| lift set (PURE) | 19 | 10,575 | `blake3-tree`, `byte-store-observation`, `records-attach`, `records-attach-concrete`, `records-exec`, `recovery-refinement-pages`, `runtime-contract-opened`, and the 12 `pagestore-digest-*` / `pagestore-{gc,keystones,reclaim,refine}` books |
| liftable, outside the set only by its name | 1 | 1,066 | `post-transaction-crash` (its closure is `store-log`, `-crash`, `-kernel`, all in the lift set) |
| log WIDE (section 2.3) | 18 | 3,463 | `recovery-refinement`, `-concurrent`, `-store`, `recovery-profile-buffer`, `-envelope`, `byte-store-initializer`, `byte-store-log-initializer`, `byte-store-arena`, `byte-store-fault-keystones`, `byte-store-observation-scan`, `byte-store-retention-publication`, `assumptions-publication`, `store-log-open-barriers`, `-rotate-spare`, `-route-phases`, `-failed-barrier`, `-buffer-cost`, `-open-scan-cost` |
| pages WIDE (2.3a) | 6 | 3,835 | the six `paged-checkpoint*` books |
| rtc WIDE (2.7) | 4 | 7,298 | `post-transaction`, `-durable`, `-layer`, `-sim` |
| auth / tls / bp WIDE | 3 | 573 | `served-auth-wire-bridge`, `served-implicit-tls`, `bp-held-payload` |
| in no candidate family | 22 | 5,582 | `catalog-pages`, `checkpoint-payload-ref`, `checkpoint-payloads`, `-payloads-extent`, `checkpoint-reserve`, `codec-attach`, `held-composite-fields`, `held-message-id-answer`, `image-world` (+ parts 1-3), `owner-batch`, `poster-bytes-invariants`, `snapshot-held-remap`, `statement-attach`, `store-finalize-carried-check`, `store-finalize-published`, `store-node-retention`, `store-observed-traces`, `store-retention-codec-invariants`, `visibility-join` |

The last row is the old store's held-row, checkpoint-payload and image-world plumbing, which tier C held only so that the rows above it would keep certifying. For fn2 it is **REWRITE / leave in the quarry**. `image-world*` is the build's umbrella and has no meaning in a fresh tree.

### 2.9 `specs/node-functionality.md`

1,122 lines. "Status: design, wave 4, written against `9321344`." It defines **F_node**, an ideal functionality in Canetti's sense (2001) written as an ACL2 state machine. The refinement claim is that "clients cannot crash us regardless of what they send" and "we implement the semantics" are two consequences of one deterministic trace refinement with the identity simulator (sections 1-2). It adds the server-robustness theorem in six parts: totality on the served path, work bounded by configuration and input length, retained memory bounded by configuration, typed refusals as the only failures, the reply stream being F_node's, and connection isolation (section 3). It includes a strawman audit of existing teeth (section 4) and the chaining plan, including composition with the BP layer `F_node × F_dtn` (5.4).

Of the 38 books it names, 34 exist at dev. **`books/ideal.lisp`, `ideal-node`, `system` and `dtn-channel` do not.** The P0 skeleton the status line mentions was deleted (the cut's tier A/B), and F_node was never realized. Of the 34 that exist: 9 are in the lift set (`acceptance`, `acceptance-invariants`, `assumptions`, `bp-primary`, `bp-primary-invariants`, `clock`, `crypto-seam`, `frame`, `wildmat-work`). 15 are MID (`nntp`, `nntp-effects`, `nntp-invariants`, `wire`, `wire-invariants`, `node`, `node-invariants`, `node-traces`, `retention`, `retention-invariants`, `clock-invariants`, `bp-workflow`, `-invariants`, `-transport-invariants`, `bp-release-invariants`). 10 are WIDE (`served`, `owner-invariants`, `store-node-invariants`, `store-node-traces`, `store-observed-traces`, `bp-ingress`, four `bp-receiver-*-invariants`).

**Verdict: LIFT WHOLE as the design document for fn2's top-level statement.** It is the most direct written form of ember's 2026-09-19 sentence it quotes ("clients cant crash us regardless of what they send us"). Its section 4 is a ready-made checklist against vacuous teeth. Re-point its book names at fn2's tree as each lands. It needs no proof work to carry.

## 3. The host (74,374 Lisp lines: `host/native` 52,119 plus 889 lines of C; `host/*.lisp` 22,255)

`fnn-octet-list` below counts the lines in each group that match `fnn-octet-list[^-a-z]`, REPRESENTATION-HISTORY's measure, comments included (271 lines over `host/native`). `ENVELOPE-AND-HOST.md` in this directory covers the host's shape; this section only says what lifts.

| group | files | lines | `fnn-octet-list` lines | verdict |
|---|---|---|---|---|
| FFI and trust-boundary seams | `tls`, `tls-reload`, `crypto`, `signatures`, `digest`, `deflate`, `fn-blake3.c`, `fn-mldsa65.c`, `fn-deflate.c`, `raw-trap`, `trace` | 4,893 | 7 | **LIFT WHOLE as files.** Each header names its premises and "decides nothing". Fix the 7 list sites on the way in. |
| socket multiplexer | `mux` | 2,362 | 0 | **LIFT DEFINITIONS.** Accept, read, write-range and the timer roster are reusable. The connection table and the dispatch into `owner.lisp` are not. |
| state, log and owner | `io`, `owner`, `extent`, `extent-decoded`, `checkpoint`, `heap`, `history-root`, `immutable-publish`, `store-identity`, `catchup-spool` | 25,004 | 142 | **REWRITE.** This is the 18-step POST path, the per-batch syncer, the `.fnsc` checkpoint and the extent cache. Keep the syscall sequences (written down in `specs/storage.md`) and the barrier order, not the code. |
| BP and TCPCL | `bp-service`, `bp-node`, `bp`, `bp-session`, `bp-app`, `bp-obligation`, `bp-control*`, `bp-listener-control`, `bp-contact`, `tcpcl`, `workflow` | 7,639 | 44 | **LIFT DEFINITIONS** for the TCPCL socket loop and the contact driver; rewrite the application bridge (`bp-app`). |
| peering, control, consumers | `pull-service`, `feed-service`, `peer-invite`, `feed-filename`, `consumer-*`, `control`, `control-transport`, `hybrid-control`, `signature-command`, `anchor`, `pattern`, `topic-local` | 5,891 | 61 | **REWRITE** (not on the survivor list except as the peering natives' subject). |
| operator and admin | `operator`, `operator-live`, `operator-control-client`, `admin`, `auth-admin`, `config`, `owner-control-turn`, `keys`, `auth`, `auth-read`, `login-bindings` | 3,851 | 14 | **LIFT DEFINITIONS** for the CLI verb table, if fn2 keeps the CLI the natives drive (section 4). |
| web reader | `web-host` | 1,120 | 3 | REWRITE (ember: "i like the web reader being inside the node"). |
| build and dev | `build`, `build-dtn`, `build-store-test`, `strip-world`, `dev-repl`, `acl2-session`, `rtc-exercise`, `reader-model-host`, `receiver-parser-turn` | 2,248 | 0 | REWRITE. The image build is tied to the old world and its stripped/reference twin. |
| ACL2-mode entries | `host/*.lisp` (58 files: `*-host.lisp`, `interfaces.lisp` 1,018 `definterface` forms, generated `interfaces-raw.lisp`) | 22,255 | n/a | **Do not lift.** fn2's entry table comes out of its own `definterface` uses; the generator lifts (section 2.6), its 1,934 instances do not. |

## 4. The natives (`tests/test_native_*.py`): 247 modules, 57,215 lines

Classified by how a module touches the node. **node**: it uses only `Node(`, `Client(`, `require_node_greeting`, `socket.create_connection` or `nntplib`. **node+internal**: it uses those and also an `Acl2Session` or a raw/mock Lisp script. **raw**: raw Lisp, mocks or `runtime_sbcl`, and no node. **source-text**: it reads `host/` or `books/` text. **other**: none of the markers; mostly operator-CLI or two-process drivers. The classification is from grep markers, so a module's name is a better guide than its class at the margins.

| class | modules | lines | carries to fn2? |
|---|---|---|---|
| node | 87 | 27,534 | **yes**: the classical gate |
| node+internal | 33 | 15,587 | the socket half yes; the in-image probes no |
| raw (Lisp / mock / `runtime_sbcl`) | 75 | 6,546 | no: they test the old host's structure (`*_source`, `*_lock`, `*_off_lock`, custody, startup source) |
| source-text | 17 | 2,722 | no |
| other | 34 | 4,463 | case by case: the CLI ones carry with the CLI |
| ACL2 session only | 1 | 363 | no (`app_journal`) |

The 120 node and node+internal modules, by product surface:

| surface | node | node+internal |
|---|---|---|
| NNTP reader/poster | 30 / 6,533 lines: `conformance` (the v0 matrix's 233 rows, re-homed), `nntp_post_probe`, `newnews_wildmat`, `over_pins`, `over_window`, `over_cursor_cost`, `header_limits`, `article_*`, `own_cancel`, `moderation_outcome`, `reader_index`, `reader_freshness`, `public_limits`, `public_exposure`, `group_authority`, `group_name_bound`, `mux`, `listener_v6`, `known_abort`, `fence_boundary`, `accept_maintenance`, `visibility_join`, `status_live_posts`, `cold_line_*`, `cold_off_loop`, `decoded_custody`, `expiry` | 8 / 2,832: **`outside_in`** (1,487 lines, 49 tests; ember 2026-09-29: "do we have a testsuite that curl can successfully do everything we think we support?"; "an INDEPENDENT oracle"), `header_lines`, `moderation`, `group_access`, `group_policy`, `post_seal_gate`, `nov_metadata`, `compress` |
| auth and TLS | 12 / 4,374: `auth`, `sasl`, `starttls`, `implicit_tls`, `injection_info`, `tls_handshake_budget`, `tls_key_exchange`, `tls_proxy`, `tls_reload`, `key_statements`, `hybrid_author`, `friends_accounts` | 1 / 221: `tls_transport` |
| peering, feeds, consumers | 14 / 6,781: `peering` (1,495), `peer_pull` (1,345), `peer_catchup`, `peer_hostile_feed`, `peer_misbehaving`, `peer_by_name`, `peer_rows_growth`, `control_across_peers`, `control_filing`, `friends_feed`, `feed_reply_cold`, `consumer_exchange`, `pattern_pubsub`, `topic_local` | 5 / 2,581: `protected_peering`, `consumer_exchange_two_nodes`, `consumer_e2`, `consumer_identity`, `control` |
| BP | 1 / 746: `source_corpus_bp` | (the BP interop drivers are in `tests/bp-dtn7`, section 2.4) |
| durability and recovery | 13 / 3,113: `replay_determinism`, `served_crash_model`, `commit_log`, `log_compaction`, `checkpoint`, `snapshot_bless`, `store_lineage`, `store_identity`, `reclaim_seal_cost`, `reclaim_in_flight`, `frozen_relocation`, `served_differential`, `page_io` | 9 / 4,417: `slow_disk`, `recovery`, `state_checkpoint`, `journal_torn`, `log_sink`, `dead_run`, `reclaim_walk`, `store_mount_identity`, `extent_identity` |
| operator and lifecycle | 6 / 1,795: `operator_walk`, `install`, `installed_start`, `start_every_preset`, `profile`, `host_lifecycle` | 4 / 1,689: `operator_cli`, `operator_verbs`, `live_reconfiguration`, `admin` |
| resource guardrails | 9 / 3,102: `heap_from_profile`, `image_floor`, `image_heap`, `capacity_vector`, `bounds_join`, `credits`, `scaling`, `open_depth`, `owner_offlock` | 5 / 3,192: `image_differential`, `owner_scheduler`, `owner`, `outcome_algebra`, `agent_wait` |
| web, corpus, harness | `web` (484), `source_corpus` (606) | `harness` (655: the harness's own tests) |

**What the black-box set depends on, and so what fn2 must keep or adapt.** `tests/native_harness.py` (1,951 lines) is the only coupling point, through these pieces:
- `Node` (`native_harness.py:1413`) writes `fn.toml` with sections `[store] path`, `[listener] host/port/tls_port/tls_cert/tls_key`, `[control] path`, `[tls]`, `[auth] protected_only` and `[resources]`. It starts `IMAGE --fn operator CONFIG run` (or an installed `bin/fn`) and waits for the greeting.
- `Client` (`:1785`) is a bounded NNTP-over-octets client with implicit TLS (RFC 8143) and STARTTLS (RFC 4642).
- `article()` and `dot_stuff()` build test articles.
- The obligations bookkeeping (`require_node_greeting`, `node_dead`) turns a dead node into a named failure.

If fn2 keeps the `fn` CLI verbs (`operator CONFIG init|run|...`), the `fn.toml` keys and a control socket, the 87 carry unchanged. Otherwise one adapter in `Node.write_config` / `Node.argv` carries them. **Recommendation:** fn2's first classical gate is the 87 node modules plus the socket halves of the 33. That is about 120 modules, against the G5 selection of 39 used on the cut. The carried reds at the cut base were `bounds_join`, `decoded_custody`, `mux`, `public_limits`, `resilience_cuts` and `status_live_posts` (`tools/cut_gate.sh:85` PREEXISTING).

## 5. The load harness and the gauntlet

`tools/load/` is 11,217 lines plus 13 hook files:
- `driver.py` (1,937 lines): cells against an image or fn-core, one process and one node at a time, loopback. Probes the image does not expose are recorded NOT-MEASURED, never estimated.
- `workloads.json` (1,715 lines): 44 workloads, 43 cells (W1, W2, W6a-c, W7, W8, W9, W13-W15, T-CMD, T-OPS, F1-F9, F2S, F4R, M-OWNER*, DESIGN-IO, ...), and 10 presets (small, development, scale, scale-1m, filled, big-articles, huge-articles, peers, index-fault, default).
- `bars.json`: 42 bars (L-HWM, L-RSS, L-POST, L-DURABLE, T-POST, T-CMD, T-SYNC, the P1/P2/P4/P5/P8 property bars on F1-F8, ...).
- `faults.py` (1,533) and `faults_bp.py` (893), with `FAULTS.md`: "F1 through F6 drive a private shipped image through NNTP and the operator control socket … No cell qualifies power loss. The product's claimed write-ordering assumption is fdatasync durability of the store filesystem".
- `peers.py` (670), `floor.c` (190: the measurement-only TCP and filesystem floor), and `sweep.py`, `cells.py`, `result.py`, `op_profile.py`, `pub_profile.py`, `w7_extent.py`.

**Verdict: LIFT WHOLE, minus `hooks/`.** The driver, workloads, bars, faults and floor speak NNTP and the control socket over loopback. The 13 `hooks/*.lisp` files (`f1-delay`, `f2-crash`, `f4-index`, `w2-lockwait`, `w6-prof`, `op-consed`, ...) are loaded into the old image (`XL_HOOK`) and do not carry; F1, F2 and F4 need fn2 equivalents (a delay, crash and index-fault selector) to stay meaningful. The judged gauntlet rows on the cut were T-CMD, T-POST, F2S, F4 and F6, with the W13 guardrail (VmHWM ≤ 249 MB, RssAnon+Shmem ≤ 115 MB, small preset). The base measured 172.9 MB and 30.4 MB, and the time rows are reported only (CUT-INVENTORY section 7). These are the baseline fn2 should be compared with on the same box and the same cells. `tests/campaign/` (232K: `native_production_kill.py`, `native_cuts.py`, `native_block_fault.py`, `native_operator_campaign.py`, `native_nntp_post_probe.py`) carries with the natives.

## 6. Closing table

Lines are `wc -l` at origin/dev 3bbfc4dca. "fn2 changes" means the old-tree structure the family depends on that fn2 replaces (section 1's list: the article as one handle and no list `:exec`; one owner with a typed root; columns plus a byte pool, wire-ready log, dirty-page checkpoint; semantics first).

| family | lines | verdict | what it depends on that fn2 changes |
|---|---|---|---|
| Generators / DSL (`def-*`, `defrecord`, `deftransition`, `defkeystone`, `definterface`, `octets-stobj`, `proto/adt*`) | 28,364 of 30,469 | **LIFT WHOLE** | Nothing structural. `def-loop`'s logic/exec twin is the pattern fn2 must keep confined to `:logic`. `def-holder`, `def-representation-tree` and `fixed-buffer-capacity` (2,105) need one include each re-pointed. `packed-octets` has no consumer once B6 goes. |
| Wire grammar and article parser (`wire-grammar`, `wire-lines`, `wildmat*`, `utf8`, `octet-text`, `mailbox`, `article*`, `cbor*`, `deflate-inflate`, `protocol-table`) | 17,503 | **LIFT WHOLE** | Octet lists as the logical model (fine as `:logic`; fn2 adds buffer execs) |
| Line codec and NNTP command surface (`wire`, `wire-scan`, `wire-span`, `nntp-*`, `string-line-*`, `wildmat-cursor`) | 25,569 | **LIFT DEFINITIONS, RE-PROVE LATER** | `wire.lisp:21` includes `body-chunks` (B6 bignum body); the dispatcher reads `group-bucket-*`, `msgid-index`, `payload-arena`, `article-arena-reads`, `reclaim-tombstone`, `index`, `control-served`, `peer-catchup-serve` |
| `protocol-served`, `wire-export`, `article-buffer`, `raw-dispatch-verdict`, `deflate-pool`, `nntp-help` | 4,988 | **REWRITE** (keep `protocol-served`'s claim as a statement) | `served`, `served-catalog-dispatch`, `login-binding-live` → `owner-config`, `state-digest` → `catalog-record`, `consumer-reason` → `held-record` |
| Identity, SASL/SCRAM, acceptance, injection kernel | 7,521 | **LIFT WHOLE** | Nothing |
| `principal`, `policy`, `accounts`, `auth-credentials` | 3,159 | **LIFT DEFINITIONS** | `statement`/`lace` keyring, `config`, `consumer-position`, `body-chunks` via `nntp-syntax` |
| AUTHINFO/STARTTLS wrapper `nntp-auth*`, `login-binding*`, `acceptance-payload-ref`, `identity-retain-carried`, `injection-info-params*`, `served-auth-wire-bridge` | 12,304 | **REWRITE the wrapper, LIFT DEFINITIONS of the RFC 4643 step** | The old served chain's signature (`fn-peer-step`), `peer-inbound` → `held-record`, `owner`, `store-node-*`, `history-columns-relation` |
| Crash model, log model, frames, record codec, assumptions (42 books) | 17,744 | **LIFT WHOLE** (extend the crash model: STATE.md's 22 gap rows) | Records encoder is a list `append` (lift as `:logic`; fn2 adds the buffer encoder) |
| Concrete log kernel and the recovery refinement (`store-log-kernel-concrete`, `-durable`, `-prefix-durable`, `-recover-copy`, `-route*`, `-open-scan`, `-buffer`, `recovery-refinement*`) | about 11,300 of the log family's 36,138 WIDE lines | **LIFT DEFINITIONS and statements, RE-PROVE LATER** | `store-log-route` → `records-concrete` (list-twin book) → `store-node`; `byte-store-state-checkpoint-program` → … → `store-files` → `history-columns`; `store-log-buffer` → `payload-extent` → `catalog-record`; `recovery-refinement-store` → `owner-checkpoint-writer` |
| Old file-layout model (`byte-store-scan/-frame/-programs/-keystones/-k0*/-record-provenance*`, `store-files*`, `store-genesis`, `store-init*`, `state-digest`) | about 18,000 | **REWRITE** against fn2's on-disk format | FNST frames, `.fnsc`, store-files record list, `store-node`, `store-intern` |
| Page store (`pagestore*`) | 12,583 | **LIFT WHOLE** | Nothing (already a stobj of words, digest in place) |
| Paged checkpoint (`paged-checkpoint*`) | 3,835 | **LIFT DEFINITIONS** | `owner-checkpoint-open`, `catalog-pages`, `history-pages-relocate`, `statement-recover-stream`, `consumer-event-index`; 0 executable functions on dev |
| BP bundle and outbound node machine (27 books) | 17,744 | **LIFT WHOLE** | Nothing |
| BP node progress, rotation, job, forward, fragment-step (34 books) | 15,539 | **LIFT DEFINITIONS, RE-PROVE** | `bp-node-progress` → `bp-app-handoff-time` → `bp-app-handoff` → `bp-native-app` → `served`, `owner-feed`, `store-observed`, `msgid-index`; `bp-route` → `config` |
| BP codecs and FNBS publication (MID, 43 books) | 13,559 | **LIFT DEFINITIONS** | `consumer-position` codec, `node-invariants`, `msgid-index` |
| BP receivers, ingress, native app (WIDE, 49 books) | 16,581 | **REWRITE** | `store-node` traces, `bp-ingress` → `store-node`/`store-intern`, `catalog-record`, `served` |
| TCPCLv4 and BP status/receipt leaves (30 books) | 10,312 | **LIFT WHOLE** | Nothing |
| Crypto specs (BLAKE3, SHA-256, HMAC, crypto seam, freshness anchor) | 7,604 | **LIFT WHOLE** | Nothing; keep as start-up-checked reference for the native primitives |
| TLS policy (`tls-*`, `key-statements`, `served-*tls*`, `hybrid-signature`) | 6,050 | **LIFT DEFINITIONS** | `connection-budget` → `heap-figure` → `owner-checkpoint-pipeline`; `native-config`, `node-config`, `native-control`, `served`, `history-wire` → `held-record` |
| Runtime contract, resource vector, memory credits (26 books) | 22,748 | **LIFT WHOLE** (certify-heavy: 3,203 s) | Nothing; instances attach by `:functional-instance` |
| Memory model, POST transaction, host lease/pool, admission (11 books) | 11,890 | **LIFT DEFINITIONS, RE-PROVE** | `charged-totals` → `store-budget` → `store-node`; `post-transaction-durable` → `store-log-durable` (the `records-concrete` edge) |
| `specs/node-functionality.md` | 1,122 | **LIFT WHOLE** as fn2's top-level statement design | Names `ideal`, `ideal-node`, `system`, `dtn-channel` (never built) and 10 WIDE books |
| Host FFI seams (`tls`, `crypto`, `signatures`, `digest`, `deflate`, three `.c` files, `raw-trap`, `trace`) | 4,893 | **LIFT WHOLE** as files | 7 `fnn-octet-list` lines |
| Host `mux.lisp` | 2,362 | **LIFT DEFINITIONS** | dispatch into `owner.lisp` |
| Host state/log/owner (`io`, `owner`, `extent`, `checkpoint`, `heap`, ...) | 25,004 | **REWRITE** (keep the syscall order, `specs/storage.md`) | 142 `fnn-octet-list` lines; 18-step POST path; cons-tuple owner |
| Host BP/TCPCL | 7,639 | **LIFT DEFINITIONS** (socket loop), rewrite `bp-app` | 44 `fnn-octet-list` lines |
| Host peering/control, operator, web, build | 13,110 | **REWRITE** (operator CLI verbs: lift definitions if fn2 keeps the CLI) | owner, image world, stripped/reference image twin |
| `host/*.lisp` entries and interfaces | 22,255 | **Do not lift** (regenerate from fn2's `definterface` uses) | the old entry set (1,934 `definterface` forms) |
| Natives, black-box (`Node`/`Client`), 87 modules | 27,534 | **CARRY** as fn2's classical gate | `fn.toml` keys, `fn --fn operator CONFIG run`, control socket (one adapter in `Node`) |
| Natives, node+internal, 33 modules | 15,587 | **CARRY the socket half** | in-image ACL2 sessions, developer selectors (`FN_NATIVE_TEST_DISK_STALL_FILE`, `FN_NATIVE_CONTROL_FAULT`) |
| Natives, raw / source-text / ACL2-only, 93 modules | 9,631 | **DROP** | the old host's internals and source text |
| Natives, other, 34 modules | 4,463 | case by case | operator CLI, two-process drivers |
| Load harness `tools/load` (minus `hooks/`) | 11,217 | **LIFT WHOLE** | F1/F2/F4 need fn2's delay/crash/index-fault selectors; `hooks/*.lisp` (13) drop |
| Wire corpus and fixtures (`source-corpus`, `fuzz-nntp`, `fuzz_nntp.py`, `interop_*`, INN pin, dtn7-rs golden bundles, ION LTP lab, `tests/campaign`) | `fuzz_nntp.py` 1,695, `interop_*` 512, plus fixture data | **LIFT WHOLE** | `fuzz_nntp.py` reads its grammar from `protocol-table` (lifts) |
| ACL2 test books whose includes are all in the lift set | 12,539 (77 books) | **LIFT WHOLE** | Nothing |

## Appendix A. The lift set (250 books, closed under include-book)

Computed by the method of section 1 at origin/dev 3bbfc4dca. Columns: books, lines, exec, theorems.

- **generators / DSL** (35 / 28,364 / 13,281 / 1,368): `book-name-relative`, `def-buffer`, `def-carried`, `def-carried-writer`, `def-cost`, `def-cursor`, `def-cursor-batch`, `def-keyset-check`, `def-loop`, `def-loop-run`, `def-representation`, `def-representation-generic`, `def-representation-index`, `def-representation-index-lib`, `def-representation-lib`, `def-representation-paged`, `def-representation-pageread`, `def-representation-pages`, `def-span-scan`, `defevent`, `definterface`, `defkeystone`, `defrecord`, `deftransition`, `immutable-list`, `octets-stobj`, `packed-octets`, `proto/adt`, `proto/adt-bytes`, `proto/adt-bytes-lib`, `proto/adt-key-lib`, `proto/adt-lib`, `proto/adt-load`, `rev-onto`, `snoc-list`
- **wire grammar and article parser** (31 / 17,503 / 4,603 / 1,004): `article`, `article-fields`, `article-header-census`, `article-header-limits`, `article-invariants`, `article-kind`, `article-kind-acceptance`, `article-kind-codec`, `article-line-bound`, `article-properties`, `article-subject`, `cancel-lock-lines`, `cbor`, `cbor-invariants`, `cbor-record-scalar`, `cbor-record-stream`, `decimal-text`, `deflate-frame`, `deflate-inflate`, `mailbox`, `nov-fields`, `octet-text`, `protocol-served-table`, `protocol-table`, `response-identity`, `utf8`, `wildmat`, `wildmat-work`, `wire-family-identity`, `wire-grammar`, `wire-lines`
- **identity, SASL, acceptance** (15 / 7,521 / 2,169 / 382): `acceptance`, `acceptance-alloc`, `acceptance-invariants`, `auth-secret`, `identity`, `identity-hex`, `identity-invariants`, `injection`, `injection-info-policy`, `injection-invariants`, `injection-path`, `injection-shape`, `posting-account`, `sasl`, `scram`
- **crash model, log, frames, records** (42 / 17,744 / 3,310 / 1,162): `assumptions`, `assumptions-durable`, `assumptions-pgs-host-io`, `assumptions-runtime`, `assumptions-spans`, `byte-store`, `byte-store-invariants`, `byte-store-observation`, `byte-store-range-read`, `byte-store-txn-name`, `byte-store-txn-seam`, `frame`, `frame-buffer`, `frame-digest-buffer`, `frame-fields`, `frame-invariants`, `frame-journal`, `frame-octets`, `frame-trailer`, `records`, `records-attach`, `records-attach-concrete`, `records-canonicality`, `records-codec-concrete`, `records-exec`, `records-invariants`, `records-seam`, `records-shape`, `records-stamp`, `recovery-payload-view`, `recovery-refinement-pages`, `store-log`, `store-log-crash`, `store-log-decode`, `store-log-extend`, `store-log-kernel`, `store-log-lineage`, `store-log-programs`, `store-log-recover`, `store-log-segments`, `store-log-txid`, `store-octet-entry`
- **page store** (18 / 12,583 / 2,361 / 976): `pagestore`, `pagestore-digest-block-predicate`, `pagestore-digest-byte-cursor`, `pagestore-digest-byte-domain`, `pagestore-digest-byte-refinement`, `pagestore-digest-cursor`, `pagestore-digest-cursor-counter`, `pagestore-digest-cursor-domain`, `pagestore-digest-cursor-progress`, `pagestore-digest-cursor-refinement`, `pagestore-digest-cursor-semantics`, `pagestore-exec`, `pagestore-gc`, `pagestore-keystones`, `pagestore-reclaim`, `pagestore-refine`, `pagestore-words`, `pagestore-words-blake3`
- **BP bundle and node machine** (27 / 17,744 / 4,065 / 841): `bp-adu`, `bp-bundle`, `bp-bundle-invariants`, `bp-fragment`, `bp-fragment-fast`, `bp-fragment-invariants`, `bp-fragment-job-shape`, `bp-fragment-resume`, `bp-fragment-send`, `bp-fragment-sweep`, `bp-node`, `bp-node-budget-input`, `bp-node-foundation`, `bp-node-fragment-family`, `bp-node-fragment-plan`, `bp-node-host-sequence`, `bp-node-host-transfer`, `bp-node-machine`, `bp-node-machine-authorization`, `bp-node-machine-guards`, `bp-node-machine-invariants`, `bp-node-profile`, `bp-node-records`, `bp-node-rotation-slice`, `bp-primary`, `bp-primary-cbor`, `bp-primary-invariants`
- **TCPCL and BP leaves** (30 / 10,312 / 2,887 / 664): `bp-authored-wire`, `bp-carry-frame`, `bp-contact-service`, `bp-handoff-recovery-shape`, `bp-handoff-report`, `bp-ion-lifetime`, `bp-request-ref`, `bp-run-class`, `bp-session-profile`, `bp-session-received-source`, `bp-signed-receipt`, `bp-status-report`, `bp-status-report-invariants`, `tcpcl-delivery`, `tcpcl-delivery-invariants`, `tcpcl-frame-cursor`, `tcpcl-host-drive`, `tcpcl-input-materialize`, `tcpcl-invariants`, `tcpcl-octets`, `tcpcl-received-count`, `tcpcl-received-source`, `tcpcl-received-source-refinement`, `tcpcl-records`, `tcpcl-retained-turn`, `tcpcl-segment-source-cursor`, `tcpcl-session`, `tcpcl-source-continuation`, `tcpcl-source-control`, `tcpcl-spool`
- **crypto specs and anchor** (14 / 7,604 / 2,036 / 431): `anchor`, `anchor-invariants`, `anchor-record`, `anchor-replace`, `anchor-servers`, `anchor-wire`, `blake3`, `blake3-stobj`, `blake3-string`, `blake3-tree`, `crypto-attach`, `crypto-seam`, `hmac-sha256`, `sha256`
- **runtime contract** (26 / 22,748 / 3,897 / 1,983): `memory-credits`, `resource-bp-session`, `resource-syncer`, `resource-vector`, `resource-vector-exec`, `runtime-contract`, `runtime-contract-actions`, `runtime-contract-budget`, `runtime-contract-echo`, `runtime-contract-exec`, `runtime-contract-exec-is`, `runtime-contract-exhaustion`, `runtime-contract-host-send`, `runtime-contract-invariant`, `runtime-contract-invariant-facts`, `runtime-contract-invariant-ops`, `runtime-contract-isolation`, `runtime-contract-keystones`, `runtime-contract-landing`, `runtime-contract-layer`, `runtime-contract-list-facts`, `runtime-contract-opened`, `runtime-contract-pool`, `runtime-contract-pool-impl`, `runtime-contract-requests`, `runtime-contract-u64`
- **other leaves pulled in** (12 / 2,740 / 741 / 149): `clock`, `journal-publish`, `node-secret`, `octet-window`, `outcome-class`, `path`, `path-update`, `payload-deflate`, `payload-kinds`, `payload-lz-value`, `profile-limits`, `snapshot-source-token`

