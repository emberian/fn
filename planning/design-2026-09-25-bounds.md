# Bounds: every cap on data, the profile that replaces them, and the build plan, 2026-09-25

Lane `lane/design-bounds`, from dev `4cfc38cd`. A design document: no book,
host or registry file changed, no ACL2 ran, no farm, no hbox. Dependent
counts are the runner's own closure (`tools/certify_books.py`
`default_books`/`local_closure`, 749 roots over 765 books at `4cfc38cd`):
the book plus every root that includes it transitively. They read 3 higher
than the audit's (records-shape 622 here, 619 in
`planning/audit-2026-09-25-twins-fanin.md:14`, taken at `67b028c7`).

ember asked (2026-09-25 ~02:20 UTC) why fn has fixed budgets at all, and
whether they come from configuration. Then D27 (dev `90158b49`,
`planning/decisions.md`, "bound work, never data") made the answer a rule. A
constant that bounds data is a defect. The operator sets those bounds in the
store profile, with validated relations and large defaults. Codec widths
never cap below any profile the operator can write. Constants that bound
work per request stay, and their comment says so. This document is the
build plan for that rule.

**The short answer to ember.**

- Configuration sets none of the caps that bind today. The store profile
  (`config.json`) is one of four hard-coded tuples
  (`books/byte-store-frame.lisp:69-84`). `fn-bs-meta-config-valuesp` (:86)
  admits exactly those four. So the operator can choose 128 or 4096
  transactions, and nothing else.
- Every other data cap is a `defconst` in a book. The article is 32768
  octets (`books/article.lisp:15`), the record 65538
  (`books/records-shape.lisp:33`), groups per article 16 (:31), the pack
  4 MiB (`books/checkpoint-compaction.lisp:12`) and the checkpoint 4 MiB
  (`books/checkpoint-codec.lisp:58`). The configuration record's own
  `max-payload` and `max-groups-per-article` slots are capped by those
  constants (`books/config.lisp:436-440`).
- Two of the profile's six fields are never enforced on the served path.
  Field 1, "capacity" (1048576), has one host accessor,
  `fnn-config-capacity` (`host/native/io.lisp:1042`), and that accessor
  has no caller. Field 2, "payload" (32768), is read only by the developer
  `store post` and the developer bench (io.lisp:2135, :2280, :2320). The
  served POST bound comes from `*fn-article-max-octets*` instead
  (`host/reader-host.lisp:34`, `books/injection.lisp:456`).
- The budgets stand in for capacity because of two roots, §3. Open replays
  the whole history with no checkpoint. The executable path holds every
  byte as a cons (16 L bytes per copy). The transaction budget exists
  because open cost grows with N (`books/store-budget.lisp:12-21`).

## 1. Inventory

Column **kind**:

- **D**: limits data. This is a defect under D27, and the value moves to the
  profile or goes.
- **W**: bounds work per request. It stays, and its comment must say so.
- **RFC**: a protocol requirement. It stays and cites the RFC section.
- **N**: a node-generated field width, bounded by construction. It stays,
  with the construction proof named.
- **dup**: a host or tool copy of an ACL2 value. It goes under the one-owner
  rule.

Column **deps** is the dependent count of the defining book, which is the
certification cost of changing the constant's value.

### 1.1 The store profile (FNSM kind 1, `books/byte-store-frame.lisp`)

Layout `(:text :nat :nat :nat :nat :text)` (:31). The numeric fields are
eight-octet frame naturals (:26-29), so the profile is already u64 wide. The
frame payload is at most 600 octets (:24). The defining book has 172 deps.

| Field | development / scale (:79-84) | Protects | Enforced by | Kind |
| --- | --- | --- | --- | --- |
| 0 format | `fn-store-experiment-7` | layout identity | `fn-profile-upgradep` equality (store-profile-upgrade.lisp:58) | W (identity) |
| 1 capacity | 1048576 / 1048576 | nothing on the native path | no caller of `fnn-config-capacity` (io.lisp:1042) | dead field; retention capacity is the `operator capacity` configuration record (store-budget.lisp:21-22) |
| 2 payload | 32768 / 32768 | developer `store post` read size | io.lisp:2135; `fn-sbud-payload-bound` (store-budget-naming.lisp:125), checked `<= *fn-record-max-payload*` (:149) | D |
| 3 aggregate replay bytes | 25165824 / 805306368 | open: total bytes replayed | `fn-profile-replay-within-boundp` (store-profile-upgrade.lisp:83), per record in `fnn-durable-records` (io.lisp:1508-1526) | D, standing in for open cost (§3) |
| 4 transactions | 128 / 4096 | open: the readdir bound; the budget | `fnn-transaction-files` (io.lisp:1256-1258); `fn-sbud-budget` (store-budget.lisp:41) | D, standing in for open cost |
| derived: record ceiling | field 3 / field 4 = 196608 (:97) | per-record publication | `fn-bs-publication-admissiblep` (:110) | D |
| 5 frontier format | `...frontier-2` | layout identity | equality (store-profile-upgrade.lisp:59) | W |

The relation `fn-bs-profile-aggregate-covers-recordsp` (:103) holds by
construction for the four tuples. `fn-profile-upgradep`
(store-profile-upgrade.lisp:53-67) already has the general shape: same
formats, no bound smaller, a ceiling no smaller. Only the preset membership
`fn-bs-meta-config-valuesp` makes it a two-preset relation.

### 1.2 Record, article and frame constants (the data path)

| Constant | Value | file:line | Protects | deps | Kind |
| --- | --- | --- | --- | --- | --- |
| `*fn-article-max-octets*` | 32768 | books/article.lisp:15 | parser input; the served POST (`fn-inj-configp`, injection.lisp:456); the signed-source bound (hybrid-signature.lisp:59); BP ingress (bp-ingress.lisp:475, :508, :641, :663) | 502 | D |
| `*fn-article-max-header-octets*` | 16384 | article.lisp:16 | header parse | 502 | D (the parse is linear in octets, so the article bound already bounds its work) |
| `*fn-article-max-header-lines*` | 256 | article.lisp:18 | header parse | 502 | D (same) |
| `*fn-article-max-fields*` | 64 | article.lisp:19 | field table | 502 | D (same; the lane checks that no step is superlinear in F, §2.3) |
| `*fn-article-max-line-octets*` | 998 | article.lisp:17 | line length | 502 | RFC 5322 §2.1.1 |
| `*fn-af-max-field-value-octets*` | 8192 | article-fields.lisp:15 | one field value | 472 | D (subsumed by the header bound) |
| `*fn-record-max-payload*` | 32768 | records-shape.lisp:29 | record recognizer `fn-record-payloadp` (:98) | 622 | D |
| `*fn-record-max-octets*` | 65538 | records-shape.lisp:33 | record codec input (records.lisp:102, :258; records-seam.lisp:87, :147, :175; records-canonicality.lisp:220, :397, :464, :691, :844); `fn-store-publication-ceiling :article` (store-events.lisp:25) | 622 | codec width (u16 byte-string cap), D |
| `*fn-record-max-groups*` | 16 | records-shape.lisp:31 | `fn-record-groupsp` (:301); records.lisp:165; native-control.lisp:29, :91; native-operator.lisp:97, :121; store-budget-naming.lisp:141 | 622 | D |
| `*fn-record-max-group-name*` | 128 | records-shape.lisp:30 | group-name domain | 622 | D (the NNTP wire allows 460: nntp-syntax.lisp:86) |
| `*fn-record-max-msgid*` | 250 | records-shape.lisp:28 | Message-ID | 622 | RFC 5536 §3.1.3 |
| `*fn-record-max-metadata*` | 256 | records-shape.lisp:32 | obligation id, subject, evidence strings | 622 | N (node-generated; provenance-codec.lisp:37) |
| `*fn-cbor-max-bytes*` / `*fn-cbor-max-input*` | 65535 / 65538 | cbor.lisp:25, :28 | the generic one-item decoder | 721 | W for the generic entry. The argument encoding is already u32 (`fn-cbor-encode-argument`, cbor.lisp:224-239; `fn-cbor-canonical-argumentp` accepts head 26, :241-247), and the bounded API takes budgets (`fn-cbor-decode-bounded`, :362; `fn-cbor-encode-bounded`, :255). A codec that uses the generic entry inherits a data cap. |
| `*fn-cbor-max-uint*` | 2^32-1 | cbor.lisp:24 | sequence, txid, frontier, charge, group count | 721 | codec width. It caps the transaction ID space at 4.29e9 reservations, burned ones included. |
| `*fn-frame-max-payload*` | 4194304 | frame-octets.lisp:28 | "keeps the cons preflight a fixed amount of work" (:26-27). The LENGTH field is 4 octets (:22), so it is u32. | 506 | W while payloads are lists; D once representation lands |
| `*fn-frame-max-blob*` | 131072 | frame-octets.lisp:32 | the `:blob` field (u32 length, frame-journal.lisp:201); the control-socket article (`*fn-nctrl-request-spec*`, native-control.lisp:20) | 506 | D (the control socket cannot carry an article above 128 KiB) |
| `*fn-frame-max-text*` | 512 | frame-octets.lisp:31 | text fields | 506 | N |
| `*fn-frame-max-store-payload*` | 196608 | frame-journal.lisp:35 | FNST physical ceiling (the kind-4 composite, :32-34); the open's per-file read (io.lisp:1510) | 488 | D |
| `*fn-frame-max-inbound-payload*` | 4194304 | frame-journal.lisp:38 | BP inbound journal | 488 | D |
| `*fn-frame-max-receipt-payload*`, `-workflow-` | 269958, 16342 | frame-journal.lisp:36-37 | journals | 488 | derived from the fields they carry; they follow P2 |
| `*fn-store-event-max-octets*` | 4096 | store-events.lisp:18 | undertake/release events | 401 | N |
| `*fn-stxa-max-octets*` | 196608 | stx-accept-records.lisp:18 | accepted-statement composite; embeds a record (:36, :125) | 419 | derived; follows the record ceiling |
| `*fn-stxk-max-octets*` / `-snapshot*` | 131072 / 65536 | stx-keyring-records.lisp:15, :17 | keyring snapshot | 420 | D: a whole-keyring snapshot per event caps the number of principals |
| `*fn-stxe-max-octets*` | 65538 | stx-evidence-records.lisp:15 | verdict evidence | 422 | N |
| `*fn-cc-max-events*` / `*fn-cc-max-octets*` | 4096 / 4194304 | checkpoint-compaction.lisp:11-12 | one pack | 10 | D: one pack holds the whole history (storage.md:128-131) |
| `*fn-cpc-max-payload*` | = frame max, 4 MiB | checkpoint-codec.lisp:58 | the whole-state checkpoint frame | 8 | D |
| `*fn-cpc-max-groups*` | = record max groups | checkpoint-codec.lisp:57 | the checkpoint's group list | 8 | follows P2 |
| `*fn-cpp-max-generations*` | 4096 | checkpoint-publish.lisp:323 | checkpoint namespace listing | 6 | W (retire keeps it small) |
| `*fn-hc-max-binary-octets*` / `*fn-hc-max-field-octets*` | 5405 / 8192 | hybrid-carrier.lisp:13-14 | carrier parse | 420 | W: a fixed nine-item carrier (identity.md:108-119) |
| signed-source length | u16 in the preimage | hybrid-signature.lisp:71; identity.md:308 | preimage injectivity (`fn-hsig-subject-body-injective`) | 423 | codec width. Today it binds at 32768 through `fn-hsig-subject-p` (:59), below the u16's 65535. |

### 1.3 Namespace counts and other data caps

| Constant | Value | file:line | Protects | deps | Kind |
| --- | --- | --- | --- | --- | --- |
| `*fn-cp-max-consumers*` | 256 | consumer-position.lisp:9 | consumers registered | 407 | D |
| `*fn-bpn-machine-max-records*` | 4096 | bp-node-machine.lisp:21 | BP rows; `*fn-bpnf-received-max-records*` = 2× (bp-fnbs-namespace.lisp:12) | 120 | D |
| `*fn-nco-max-config-observations*` | 8192 | native-config-observation.lisp:13 | configuration generations ever | 2 | D |
| `*fn-ff-max-observations*` | 8192 | feed-filename.lisp:17 | feed journal names | 2 | D |
| `*fn-native-auth-max-credentials*` / `-lines*` / `-octets*` | 128 / 1024 / 65536 | native-auth-profile.lisp:16-18 | credentials file | 9 | D |
| `*fn-ncfg-max-octets*` / `-lines*` | 16384 / 128 | native-config.lisp:13-14 | `fn.toml` (limits how many groups and peers one file names) | 26 | D |
| `*fn-pol-max-members*` | 64 | policy.lisp:59 | group policy members | 7 | D |
| `*fn-th-max-*` | 16 authors, 8 parents, 16 anchors | topic-history-metadata.lisp:12-13; topic-history-admission.lisp:7 | topic events | 413 | D (experimental) |
| `*fn-bpa-max-octets*` | 65538 | bp-adu.lisp:24 | one ADU carries one record | 156 | D: it caps a BP-carried article |
| `*fn-bpb-max-data*` / `*fn-bpb-max-input*` | 1048576 | bp-bundle.lisp:53, :62 | one bundle | 127 | D (RFC 9171 sets no bundle size; TCPCLv4, RFC 9174, segments transfers by the receiver MRU) |
| `*fn-bpf-max-length*` / `-fragments*` | 65538 / 64 | bp-fragment.lisp:50-51 | reassembly | 71 | D |
| `*fn-cpa-clone-max-entries*` / `-bytes*` | 1e6 / 1 TiB | checkpoint-auxiliary.lisp:14-15 | the auxiliary clone walk | 2 | D |

**Work bounds that stay** (say so in their comment; no packet touches them):

- NNTP: command 510, argument 497, response 512, group 460, decimal 10
  (nntp-syntax.lisp:69-90; RFC 3977 §3.1). Article number 2^31-1
  (nntp-syntax.lisp:84; RFC 3977 §6).
- wildmat 497 (wildmat.lisp:33).
- Feed wire chunk 512 (feed-wire-input.lisp:19).
- Admin and operator argv (native-admin.lisp:21-22, native-operator.lisp:14-15).
- Auth name 64 (nntp-auth.lisp:105).
- Statement item and header caps (statement.lisp:61-68).
- Key and signature octets 4096 (crypto-seam.lisp:42-43).
- Anchor wire (anchor-wire.lisp:10-12).
- TCPCL caps (tcpcl-octets.lisp:82-86).
- Poll scan 16 (consumer-poll-index.lisp:13).
- Retry counts (bp-forward-attempt.lisp:41, owner-feed.lisp:322).
- Backoff (peer-feed.lisp:64).
- `*fn-own-body-limit*` 8192 (owner.lisp:951), a pre-configuration fallback
  and not a production default (:948-950).

**Duplicates of ACL2 values (dup):**

- `host/native/signature-command.lisp:25` reads a source with the literal
  32768.
- `tools/fn_verify.py:73` `ARTICLE_MAX = 32768`, tied by
  `tests/test_fn_verify.py` `SpecBookTieTests`.
- `host/store-host.lisp:26` `*fn-store-capacity*` 1048576.
- `tools/run_store.py:34` `MAX_TRANSACTION_COUNT = 128`
  (m5-capacity-2026-09-24.md:14-17).
- `host/native/tcpcl.lisp:45` MRU 1048576.

## 2. The design

### 2.1 The store profile the operator sets

A new FNSM kind-1 layout, format `fn-store-8`, replaces the four tuples.
Every numeric field is a frame natural (u64). The payload stays well under
the existing 600-octet frame bound.

| Field | Meaning | Default at `init` | Replaces |
| --- | --- | --- | --- |
| `max_transactions` T | committed transactions admitted | 2^32 - 1, the u32 txid width (P6 raises it with the width) | field 4 |
| `max_history_octets` H | total committed record octets | 2^40 (1 TiB) | field 3 |
| `max_record_octets` R | one encoded Store event, all kinds | 64 MiB | derived ceiling field3/field4; `*fn-frame-max-store-payload*` as policy |
| `max_article_octets` A | one article (POST, feed, BP, control) | 16 MiB | field 2; `*fn-article-max-octets*` as policy |
| `max_groups_per_article` G | newsgroups on one record | 4096 | `*fn-record-max-groups*` as policy |
| `max_group_name_octets` | a group name | 460 (the NNTP wire bound) | `*fn-record-max-group-name*` |
| `max_open_suffix` K | records open replays after the selected checkpoint (§3.1) | 65536 | the role T plays at open today |
| `max_consumers`, `max_bp_rows`, `max_config_generations`, `max_credentials`, `max_policy_members` | the namespace counts of §1.3 | 2^20 each | the §1.3 constants (P5) |

Field 1 (capacity) is dropped: it is dead (§ short answer). Retention
capacity stays the configuration record it already is.

**The validity relation.** `fn-bs-profile-validp`, a new function in
byte-store-frame, replaces `fn-bs-meta-config-valuesp` everywhere it is a
hypothesis. Every relation is one comparison, and the operator verb reports
the first one that fails by name:

- `1 <= T <= *fn-cbor-max-uint*`: the txid width. This is the codec
  ceiling, and P6 widens it.
- `R <= H`.
- `R >= (fn-store-publication-ceiling k)` for every non-article kind `k`, so
  that no kind is unpublishable. Today those kinds have fixed node-generated
  sizes (store-events.lisp:23-31), and kind 4 embeds a record. So this is
  `R >= overhead-4 + article-record(A, G)`.
- `article-record(A, G) <= R`. `article-record` is the proved worst-case
  encoded length of a record, given the payload and group count
  (`fn-record-encode-length-bound`, new in P2).
- `A <= *fn-article-codec-ceiling*`, `G <= *fn-record-codec-max-groups*`,
  and `R <= *fn-frame-codec-max-payload*` (the §2.3 widths, each 2^32 - 1
  or derived from it). This is how "codec widths never cap below a profile"
  becomes a theorem: `fn-bs-profile-validp` implies every codec accepts
  every value the profile admits.
- `K <= T`.

The old relation `T × R <= H`
(`fn-bs-profile-aggregate-covers-recordsp`, :103) is dropped. It existed so
that no host aggregate became a second authority
(`specs/encoding.md:225-230`). The replacement is ACL2's own count:
`fn-sbud-bytes-used`, the sum of encoded record lengths in the file kernel,
computed exactly as `fn-sbud-used` counts records (store-budget.lisp:36).
Admission is `used < T` and `bytes-used + prospective <= H` and
`prospective <= R`. The per-POST cost stays one Θ(N) walk, the same as the
existing `len`. A carried sum on the kernel, with a preservation theorem,
removes that walk, and it belongs with the representation carries.

**Init and upgrade.**

- `operator CONFIG init` takes `--max-transactions N`,
  `--max-article-octets N` and the rest as optional flags, with the defaults
  above. `--profile development|scale` stays as a name for two fixed tuples,
  so existing tests keep their witnesses.
- `fn-profile-upgradep OLD NEW` becomes "both `fn-bs-profile-validp`, same
  formats, `NEW /= OLD`, every field `>=`".
- A format-7 → format-8 translation is admitted as an upgrade when the
  mapped fields do not shrink: T = field 4, H = field 3, R = field 3 / field
  4, A = field 2, G = 16, K = T.
- The byte program `fn-bs-profile-program` and its crash theorem are
  unchanged: they are over octets, not values.
- Shrinking a bound is refused, as today. A store admitted under the old
  profile is admitted under the new one and replays to the same state
  (`fn-profile-upgrade-keeps-*`).

**Reconfiguration stays offline.** The profile bounds the open before any
configuration record is replayed (store-budget.lisp:12-21), so a
configuration record cannot raise it. That argument is about who may raise
a bound, not about whether a bound should exist. The upgrade verb is the
raise, and it needs a stopped owner. After P3, K is the only field the open
depends on in bulk. T and H become pure admission bounds, which the owner
could read from a configuration record. That move is not in this plan.

### 2.2 Theorems restated (P1)

The statements keep their shape. `fn-bs-meta-config-valuesp` becomes
`fn-bs-profile-validp`, and field indices become named accessors:

- byte-store-frame: `fn-bs-profile-record-ceiling` (:97, now field R),
  `fn-bs-publication-admissiblep` (:110), `fn-bs-config-encode`/`-decode`
  (:285, :293, new spec).
- store-budget: `fn-sbud-budget-is-the-profile-admissibility` (:86),
  `fn-sbud-named-profile-article-budgets` (:96, kept as the preset
  witness), plus a new `fn-sbud-bytes-used` keystone. owner-store-budget's
  three keystones (:37, :44, :52) do not move, since they take `budget` as
  an argument.
- store-budget-naming: `fn-sbud-payload-bound-within-record-codec` (:149,
  now `<= A <=` the codec ceiling),
  `fn-sbud-post-boundary-refuses-exactly-past-the-profile-bound` (:162, the
  group hypothesis `<= G`), `fn-sbud-named-profile-payload-bounds` (:153,
  witness).
- store-profile-upgrade: `fn-profile-upgradep` (:53),
  `fn-profile-upgrade-keeps-txn-observation` (:129), `-keeps-replay-bound`
  (:139), `-keeps-publication-admissibility` (:144), `-budget-grows` (:149),
  `-keeps-verdict` (:157), `fn-bs-config-decode-of-encode` (:211),
  `fn-profile-upgrade-verdict-writes-only-upgrades` (:257),
  `-budget-after-reopen` (:274), `-development-to-scale` (:288, witness),
  plus a new `fn-profile-upgrade-format-7-to-8`.
- config: `fn-cfg-limit-ceiling` (config.lisp:436) reads the codec
  ceilings, not the record policy constants. Configured limits then sit
  between the codec and the profile.

**Teeth (tests/acl2/store-profile-upgrade-tests, byte-store-frame-tests):**

- A free-field profile (T = 1000, R = 300000) that no preset equals is
  valid, upgrades from development, and refuses shrink.
- One `must-fail` per validity conjunct.
- A profile with `R` below kind 4's ceiling is refused.
- A format-7 → 8 translation that shrinks is refused.

### 2.3 Codec widths (P2, P4, P6)

In every row, the constant becomes a codec ceiling at the field's physical
width, and the profile sits below it.

| Width | Today | Change | Codec version | Existing bytes |
| --- | --- | --- | --- | --- |
| Record byte strings (payload, group names) | generic CBOR entry, 65535 per item (records.lisp:350, via `fn-cbor-decode-bytes`) | the record decoder calls `fn-cbor-decode-bytes-bounded` (cbor.lisp:315) with the item budget `R`. The CBOR head for a length ≥ 65536 is already the canonical u32 head 0x5a (cbor.lisp:236, :246). cbor.lisp does not change. | **no record schema bump.** Every existing record has payload ≤ 32768, so it keeps the same canonical bytes. An old image refuses a 0x5a payload fail-closed, because its decoder caps at 65535. The store refuses old images by the profile format `fn-store-8`, which an old image does not know (byte-store-frame.lisp:86 refuses it). | unchanged |
| `*fn-record-max-octets*` | 65538 | 2^32 - 1, the FNST LENGTH field's u32 width (frame-octets.lisp:22). Every `(<= (len octets) *fn-record-max-octets*)` in records-seam and records-canonicality keeps its statement; the proofs that used `= *fn-cbor-max-input*` move to the bounded decoder's lemmas. | none | unchanged |
| `*fn-record-max-payload*`, `-groups*`, `-group-name*` | 32768, 16, 128 | derived codec ceilings. Payload is the record width minus the worst-case other fields, proved by `fn-record-encode-length-bound`. Groups are `*fn-cbor-max-uint*` (the count is a CBOR uint, records.lisp:87). Group name is 460 (the wire). | none | unchanged |
| `*fn-article-max-octets*` and header caps | 32768 / 16384 / 256 / 64 | the parser takes its bound from the injection configuration, which already carries `max-octets` (`fn-inj-config-max-octets`, injection.lisp:455-456). The constant becomes the codec ceiling, equal to the record payload ceiling. Header caps go, and the header parse is bounded by the article bound. The lane confirms that no step is superlinear in the field count before it deletes them. | none | n/a |
| Frame `:blob` | 131072 (frame-octets.lisp:32), u32 length | ceiling 2^32 - 1. Each schema passes its own cap, as `*fn-frame-max-payload*`'s comment already says (:26-27). The control socket's article cap becomes A. | FNCT spec unchanged; values only | unchanged |
| `*fn-frame-max-payload*`, `-store-payload*`, `-inbound-payload*` | 4 MiB, 192 KiB, 4 MiB | 2^32 - 1 physical, with R and the BP bound as the caller's cap. The preflight is O(L) in any case, and with a byte array it becomes O(1) (representation design, rank 4). | none | unchanged |
| Checkpoint | one frame ≤ 4 MiB (checkpoint-codec.lisp:58); TREE naturals < 2^32 | P3: a segmented checkpoint (§3.1) | `fn-c` schema 2 | old checkpoints stay readable as schema 1; they are derived and may be discarded (storage.md:227) |
| Pack | 4096 events / 4 MiB, one unit | P3: packs stop being read at open. P5: chained links (storage.md:318-345), each link ≤ a profile link size | `fn-x` version 1 with a predecessor link | version 0 packs stay the chain's first link |
| **Signed-source length** | u16 (hybrid-signature.lisp:71; identity.md:308), bound 32768 by `fn-hsig-subject-p` (:59) | P4, carrier v2 (below) | carrier version 2, domain tag `fn-authored-source-hybrid-v2` | v1 unchanged forever |
| BP ADU / bundle / fragment | 65538 / 1 MiB / 65538 × 64 | P5: ADU ≤ R, bundle ≤ a profile field, fragments by count × MRU | BP bundle bytes unchanged (RFC 9171 lengths are CBOR uints); fn's ADU record inherits the record width | unchanged |
| uint width (txid, sequence, frontier, charge) | u32 (`*fn-cbor-max-uint*`, cbor.lisp:24) | P6: u64 (CBOR head 27) | record schema bump (a record with a u64 field is a new schema octet: `fn-record-schema-octet`, records-shape.lisp:365); frontier format `...frontier-3` | old records keep schema 0/1 bytes |

**Carrier v2 (P4), the only width change that touches signatures.**

- Up to 65535 octets, no preimage change is needed. The u16 can already
  carry it. Raising `fn-hsig-subject-p`'s bound from 32768 to 65535 changes
  no signature byte. `tools/fn_verify.py:73` and `SpecBookTieTests` must
  move with it, because a verifier at 32768 would refuse valid v1 articles.
- Above 65535, v2 is needed. Carrier item 1 (version) becomes 2. The domain
  tag becomes the 28-octet ASCII `fn-authored-source-hybrid-v2`, so the
  CBOR head `58 1c` is unchanged. The profile octet `*fn-hsig-version*` is
  2, and the length field is 4 octets, u32 big-endian (`fn-cbor-u32-bytes`,
  cbor.lisp:189). Nothing else changes.
- Domain separation: the v1 and v2 tags differ, so no v1 signature verifies
  as v2 or the reverse. That needs its own theorem, stated over
  `fn-hsig-signed-preimage`: `fn-hsig-v1-v2-preimages-disjoint`.
- Injectivity (`fn-hsig-subject-body-injective`) is restated per version.
- **Existing signed records:** their carrier bytes, verdict rows (`fn-stxe`
  profile `fn-hybrid-v1`, stx-evidence-records) and `:fn-verified` lines
  keep their meaning. Nothing is re-signed or re-verified.
  `fn-stxe-profile-supportedp` admits `fn-hybrid-v2` as a second tag
  (identity.md:120-121).
- **The independent verifier** (`tools/fn_verify.py`) dispatches on carrier
  item 1. For v1 it uses the 2-octet length (:313); for v2, the 4-octet
  length and tag. `specs/identity.md` "The signed bytes" gains a v2 column.
  `SpecBookTieTests` gains the v2 constants.
- **Signers:** `hybrid-sign-carrier` emits v1 when the source is ≤ 65535,
  and v2 only above that. A v1-only verifier then keeps working for every
  article it could already check.
- **Cost:** verification holds the whole preimage (≈ A + 2 KiB). Pure
  Ed25519 and pure ML-DSA sign the message itself (identity.md:316-333),
  and the node passes one buffer (host/native/signatures.lisp). A is the
  operator's bound, so this is the per-request work that A buys.

### 2.4 The crash model when a file is no longer one bounded read

Today every durable file is read whole. In the model, `fn-bs-read` (books/byte-store.lisp:630) returns the
inode's entire content, and on the host, `fnn-read-bounded-fd` (io.lisp:406-423) reads 64 KiB chunks into
one buffer of at most the bound and refuses anything larger. The two
correspond because the store lock excludes other writers. That holds
while R fits in memory. A checkpoint of a large store (§3.1) and an
article above what one buffer should hold do not fit. The model needs four
things. P3 needs 1, 2 and 4. P6 needs all four.

1. **A range read.** `fn-bs-read-range s ino off n` = `(take n (nthcdr off
   (fn-bs-content s ino)))`, with the keystone
   `fn-bs-read-ranges-concatenate`: consecutive ranges with no intervening
   transition append to `fn-bs-read`. A read is not a transition
   (byte-store.lisp:627-631), so this is a list lemma, but it must be stated
   over the host's actual loop.
2. **A named assumption.** `A-HOST-EXCLUSIVE-READ`, an `encapsulate` in
   `books/assumptions.lisp`, states that no other process writes an inode
   between two range reads of one open. It stands for the store lock. The
   theorems that depend on it name it.
3. **Segments, not one trailer.** A streaming decoder must not act on bytes
   whose integrity is unchecked. There are two options. Option (a) reads
   twice: digest pass, then decode pass. That doubles the reads, and it
   needs 2 to cover the gap between the passes. Option (b), chosen here:
   the object is a sequence of FN frames. Each frame is at most S octets (a
   profile field, work per read) and has its own trailer, index, total
   count and the digest of its predecessor. Each segment is then an
   ordinary bounded read, and the existing per-frame theorems apply
   unchanged. The new obligation is the chain: `fn-seg-chain-okp` holds
   iff the decoded concatenation equals the encoder's input
   (`fn-seg-decode-of-encode`, `fn-seg-chain-rejects-reorder`,
   `-truncation`, `-splice`).
4. **A publish program.** Segments are written to staging, fsynced, and
   then one rename or marker makes them live, with the crash keystone in
   the shape of `fn-bs-profile-program-crash-is-old-or-new`
   (byte-store-profile-program.lisp:114): at every cut, the open sees the
   old object or the complete new one. Specs/crash-model-v2.md §1 gains the
   range read and the segment program.

## 3. The two roots

### 3.1 Whole-history replay at open (no checkpoint)

**What open does today.**

1. `fnn-recover` (io.lisp:1535) lists up to T names
   (`fnn-transaction-files`, :1256).
2. It reads every file whole (`fnn-durable-records`, :1508), converting
   each to an octet list (`fnn-octet-list`, the representation design §1).
3. It hands the list to `fn-store-sn-recover`
   (host/store-node-host.lisp:147). That function makes two whole-list
   passes, `fn-cpr-replay` (configuration node) and `fn-cpo-open-observed`.
   The latter runs `fn-sn-recover` (books/store-node.lisp:1466), which makes
   six more passes over the same records:
   - `fn-sf-recover`;
   - `fn-sf-replay-node` (articles, retention, allocation);
   - `fn-replay-identity` (keyring, statements);
   - `fn-cpe-projection-replay` (consumers);
   - `fn-th-prefix-project` (topics);
   - `fn-cei-build` (event index).

The measured cost is on the Python bridge only: 2.7 s at N = 128 and
12.7 s at N = 256, approaching Θ(N³) (planning/scale-profile.md:114-119).
Extrapolated to N = 4096 that is 14 h (m5-capacity-2026-09-24.md:176-180).
The native reopen has not been measured past N = 120. The existing
checkpoints are differential only. Open never reads them as authority
(storage.md:227; `fnn-checkpoint-report`, io.lisp:1856).

**What a checkpoint must carry.**

The checkpoint is the exact Store state after a committed prefix of S
records, not a summary. That makes this packing plus a cache, not H: no
record is removed, so D13 is not a precondition, and the obligation is the
split lemma rather than H's every-future-decision proof (storage.md
H row). Per the lifetimes table (storage.md:170-228), the state is every
`fn-sn-make-v6` slot (store-node.lisp:217-222) except the record list:

- `groups`, `capacity`.
- `node`: acceptance, retention with every open undertaking and its
  charge/subject/evidence, releases, group high-waters and per-group
  frontiers, and the Message-ID binding with the poster's bytes for D25.
- `keyring`, `index` (D21), `keyring-generation`, `verdicts`, `snapshots`,
  `identity-next`.
- `config-history`.
- `consumer`: the latest entry per consumer and `next-epoch`.
- `topic`.
- `event-index`.
- The file kernel's frontier, sequence S and successes. The committed-history
  marker counts S + suffix (storage.md table: "the summary counts as the
  records it replaces").

Article bodies are the size problem. `fn-checkpoint` carries the node with
its payload octet lists (checkpoint-codec.lisp:1-5). Until the archive
holds bodies by reference (a body is read from its record or pack by
sequence when ARTICLE asks), the checkpoint is as large as the history.
That still fixes the time and pass count, because the checkpoint decodes in
one linear pass. It does not fix memory. That is the second root (§3.2),
and it is why P3's memory figure in §4 depends on the representation
packets.

**The open that reads it.**

1. Read the selection marker (the checkpoint-publish namespace, checkpoint-publish.lisp:318-335, existing).
2. Read the selected checkpoint's segments (§2.4). Check that the checkpoint
   is consistent with the store: its S is at most the marker's count, its
   frontier is at most the allocation frontier, and its profile format
   matches.
3. List and read only the suffix names `>= S`. Pack reclaim has removed the
   covered names (PRF-073). Read at most K of them.
4. Run the eight passes over the suffix, starting from the carried slots.
5. If the checkpoint is absent or refused, fall back to full replay from
   packs and files. That is correct, because the checkpoint is derived and
   replay stays authoritative (storage.md:227). It is only slower. Whether
   the owner then refuses to serve when N > K is the only policy choice
   here. Recommendation: serve, and report `open=full-replay` in `status`.

**The crash keystone.**

- `fn-sn-recover-from-checkpoint-equals-full-recover`, stated over the
  function the host calls (`fn-store-sn-recover`'s logic core,
  `fn-cpo-open-observed`). For every committed prefix P whose recover
  succeeded and every suffix Q, restoring the captured state of P and
  recovering Q equals recovering P ++ Q.
- It is built from one append lemma per pass:
  - `fn-sn-replay-loop-append` exists (store-node-invariants.lisp:946);
  - `fn-cpe-projection-replay-append-one` exists
    (consumer-store-projection.lisp:89) and generalizes to a list;
  - `fn-replay-identity-append`, `fn-th-prefix-project-append`,
    `fn-cei-build-append` and `fn-sf-recover-append` are new;
  - `fn-cpr-replay-append` is new for the configuration pass.
- It generalizes PRF-008's `fn-checkpoint-plus-suffix-equals-full-replay`
  (checkpoint.lisp:393) from the node to the whole Store state.
- Crash: at every cut of the checkpoint publish program (segments,
  fsync, selection marker), open selects the old checkpoint or the new
  complete one. By the keystone, both give the full-replay state. The
  statement is `fn-cpp-publish-crash-open-is-full-recover`.
- Teeth: a checkpoint missing any one slot (consumer, topic, event index)
  makes the keystone fail, one `must-fail` per slot. A checkpoint whose S
  exceeds the marker is refused.

### 3.2 The octet-list representation

`planning/design-2026-09-25-representation.md` (merged at dev `5080ee73`)
ranks seven boundaries. Rank 1, the record recognizer over strings, has
landed. The ones that matter for bounds:

- Rank 4, the payload as a stobj byte array. It takes memory per copy from
  16 L bytes to L + 16 (§3 of that design). At N = 4096 with 32 KiB
  payloads that is 4.0 GiB of lists against 256 MiB.
- Rank 6, the archive body as a string or reference. It decides whether a
  checkpoint and the live node hold bodies at all.

The 15 GB at N = 1000 (m5-capacity-2026-09-24.md:183-186) is mostly the old
images' per-POST retained state, not payload. The next memory lane's first
job is the heap census that design names (§3, "room").

### 3.3 Order

D27 gives the order: representation and P1 + P2 in parallel, then P3.

1. **P1 and P2 run now**, beside the representation lanes. P1 alone
   changes nothing a running store sees until the operator raises a field,
   and the defaults are admissions, not allocations. P2 widens codecs
   without changing any existing byte (§2.3).
2. **P3 (checkpoint open) follows P1**, because it needs the profile field
   K. It runs beside representation ranks 2 to 4. A large T without P3
   makes open slow (D27: "a large transaction bound without it only makes
   open slow"). So P1 ships its defaults, and `status` reports the
   pessimistic open figure beside them until P3 lands.
3. **P4 (carrier v2) is independent** of P1 to P3. It touches only the
   hybrid books and the verifier, so it runs in parallel whenever a lane is
   free. It has users only once A > 65535, which is after P2.
4. **P5 (namespace counts, chained packs, BP widths) follows P1**, because
   it adds profile fields to byte-store-frame. It runs beside P3.
5. **P6 (segmented objects, u64 uint width) is last.** It needs P3's
   segment codec, and it is the cbor.lisp freeze (721 deps).

## 4. Pessimistic numbers after each packet, with their scope

The quantities, each stated with its scope:

- **Bytes** are what a profile admits, not what is measured.
- **Open** is the replay input.
- **Memory** is per-copy payload representation, from the representation
  design's §3 formula: 16 L bytes as lists, L + 16 as arrays, two long-lived
  copies per article.
- **Time** is measured only on the Python bridge.

| After | Largest article | Transactions | Bytes the store may hold | Open reads | Open memory, pessimistic | Open time |
| --- | --- | --- | --- | --- | --- | --- |
| today | 32768 | 128 / 4096 | 24 MiB / 768 MiB (m5-capacity-2026-09-24.md:161-162) | all N files | 32 × 8 MiB = 256 MiB / 32 × 256 MiB = 8 GiB lists (2 copies × 16 per octet, article-record bytes) | Python Θ(N³): 2.7 s at 128, 14 h extrapolated at 4096; native unmeasured past 120 |
| P1 | 32768 (P2 raises it) | operator's, up to 2^32 - 1 | operator's H, up to 2^64 - 1 (frame nat) | all N files | 32 × H. With the default H this is unbounded in practice, which is why `status` must print it | unchanged per N; N may now be larger |
| P1 + P2 | operator's A, up to about 2^32 - 1 minus record overhead | same | same | all N files | 32 × H | unchanged per N; per POST O(A) conses: one 16 MiB article is 256 MiB per list copy |
| + representation rank 4 | same | same | same | all N files | 2 × H + 32 N | unchanged |
| + P3 | same | same | same | checkpoint (one linear decode) + at most K suffix files | the checkpoint's state: 2 × H while bodies live in the node (rank 6 not landed); O(index) once bodies are references | Θ(S) decode + the suffix replay cost at K, not at N. The Θ(N³) is a property of replay, so it becomes Θ(K³) on the bridge: at K = 256, 12.7 s. The native figure is still to measure. |
| + P5 | same | same | same | same, and no pack at open | same | same |
| + P6 | operator's A with no single-read ceiling (segments of S) | up to 2^64 - 1 | same | same, S per read | per read: S octets | same |

Hard ceilings that remain after P6:

- An NNTP article number is at most 2^31 - 1 per group (RFC 3977 §6).
- A line is at most 998 octets (RFC 5322 §2.1.1).
- A Message-ID is at most 250 octets (RFC 5536 §3.1.3).
- The signed-source length is u32 (v2).

## 5. Ranked packets

"Deps" is the union of the owned books' dependents (runner closure), which
is what a certification of the packet costs. "Owns" is the file set a lane
edits. Packets whose "owns" sets are disjoint run in parallel.

| # | Packet | Owns | Deps | Theorems restated / new | Operator-visible effect | Parallel with |
| --- | --- | --- | --- | --- | --- | --- |
| 1 | **P1: the operator's profile.** Layout `fn-store-8` (§2.1), `fn-bs-profile-validp`, `fn-sbud-bytes-used`, the general upgrade, format 7 → 8, init and upgrade flags. Drop dead field 1. Retire the dup `run_store.py:34` and `store-host.lisp:26`. | books/byte-store-frame, store-budget, store-budget-naming, store-profile-upgrade, native-operator, config.lisp:436-440 (`fn-cfg-limit-ceiling` only); host/native/io.lisp (init, upgrade, `fnn-config-*`), host/native/operator.lisp, host/owner-host.lisp (`fn-owner-install-profile`), docs/operator.md, specs/storage.md "Store profile", specs/encoding.md:225-230 | 304 (172 without config) | §2.2: 17 restated by name, 3 new (`fn-bs-profile-validp-codecs-accept`, `fn-sbud-bytes-used-is-kernel-sum`, `fn-profile-upgrade-format-7-to-8`) | `init --max-transactions N --max-article-octets N ...` and `store upgrade-profile` with any larger values. `status` prints every field and `headroom bytes-used=`. `--profile development|scale` still works. | P2 (disjoint files; P2 owns the ceiling constants, P1 names them), P4, representation |
| 2 | **P2: data constants become codec ceilings.** The §2.3 rows: record, article, header, blob and frame. The record decoder moves to `fn-cbor-decode-bytes-bounded`. `fn-record-encode-length-bound`. The injection config's max-octets becomes the parser's bound. The control socket article is A. BP ingress reads A. Retire `signature-command.lisp:25`. | books/records-shape (:28-33 values), records, records-seam, records-canonicality, records-invariants, article, article-fields, frame-octets (:28, :32), frame-journal (:35, :38), store-events (:23-31), injection (:452-456), native-control (:29), native-admin (:182, :438, :443), peer-config (:169, :754), bp-ingress (:475-663) | 664 (a freeze: records-shape 622, cbor untouched) | Statements keep their symbols. Proofs that used `*fn-record-max-octets*` = `*fn-cbor-max-input*` are re-proved over the bounded decoder: records-canonicality :220, :397, :464, :691, :844; records-seam :87, :147, :175. New: `fn-record-encode-length-bound`, `fn-record-decode-bounded-of-encode`. Teeth: a 70,000-octet payload round-trips; an old-decoder `must-fail` on it. | POST, feed, BP and control accept articles up to the profile's A. Refusal names the profile bound, not a constant. | P1, P4; coordinate with the representation lane on records-shape (its `fn-rcon-*` twins name the constants symbolically) |
| 3 | **P3: open from a checkpoint.** Exact-state Store checkpoint (`fn-c` schema 2, segmented, §2.4 items 1, 2, 4), the open of §3.1, fallback to full replay, profile field K. Checkpoint publish on the owner's schedule, when the suffix reaches K/2. | books/checkpoint, checkpoint-codec, checkpoint-publish, new `store-checkpoint-open`, new `byte-store-range-read`; host/native/checkpoint.lisp, io.lisp `fnn-recover` (:1537); books/assumptions.lisp (`A-HOST-EXCLUSIVE-READ`); specs/storage.md "Checkpointing", specs/crash-model-v2.md | 10 for the owned books. The new books sit above store-node, so they are leaves. One lemma each in store-node-invariants, consumer-store-projection and topic-history, if the append lemmas land there (347 for store-files and store-node; put them in the new book to avoid that). | §3.1: `fn-sn-recover-from-checkpoint-equals-full-recover` (keystone), six append lemmas, `fn-cpp-publish-crash-open-is-full-recover`, `fn-bs-read-ranges-concatenate`. PRF-008's statement is generalized in a new event, not edited. | Open time tracks K, not N. `status` shows `open=checkpoint suffix=k`. The transaction count stops being an open-cost stand-in. | P4, P5 (P5 touches checkpoint-publish's generation bound: sequence P5 after P3 there, or give P5 that line) |
| 4 | **P4: carrier v2.** Raise the v1 bound to 65535. v2 with a u32 length and the v2 tag. Verifier dispatch. Evidence tag `fn-hybrid-v2`. | books/hybrid-signature, hybrid-carrier, stx-evidence-records (profile tag only); host/native/signatures.lisp, signature-command.lisp; tools/fn_verify.py; tests/test_fn_verify.py; specs/identity.md | 427 | `fn-hsig-subject-body-injective` (per version), new `fn-hsig-v1-v2-preimages-disjoint`, `fn-hc-decode` round trip for v2. Teeth: a v1 signature does not verify as v2; a 70,000-octet source signs as v2 and not as v1. | Signed articles up to A. Every existing signed record and verdict is unchanged. `fn_verify.py` checks both versions. | everything except P2's `*fn-article-max-octets*` (P4 reads the ceiling P2 sets; land P2 first, or P4 carries its own `*fn-hsig-v2-max-source*` = 2^32 - 1) |
| 5 | **P5: namespace counts and BP widths into the profile.** The §1.3 rows, chained packs (storage.md:318-345), ADU ≤ R, bundle ≤ a profile field, fragments by MRU, the keyring snapshot as deltas (or a profile field for the principal count). | books/consumer-position, bp-node-machine, bp-fnbs-namespace, native-config-observation, native-auth-profile, native-config, policy, stx-keyring-records, bp-adu, bp-bundle, bp-fragment, checkpoint-compaction (+ byte-store-frame layout fields after P1) | 475 | per constant: the recognizer's `(<= (len x) *c*)` becomes `(<= (len x) (fn-profile-f p))`. Each keystone that names the constant gains the profile argument. | Consumers, BP rows, config generations, credentials, policy members and fn.toml size are the operator's. BP carries any article the store accepts. | P3 (except checkpoint-publish), P4 |
| 6 | **P6: segmented objects and the u64 width.** §2.4 item 3 for articles (an article is a segment chain, not one record payload) and `*fn-cbor-max-uint*` → 2^64 - 1 with a record schema bump. | books/cbor, byte-store, new `segments`; records (schema 2) | 721 (a whole-tree freeze) | the whole CBOR uint family; `fn-record-schema-octet`; the segment chain theorems | No single-read ceiling on an article. Transaction IDs never run out in practice. | none; a freeze batch of its own |

The coordinator can launch 1, 2 and 4 now. File ownership is disjoint,
except P4 reads P2's ceiling, and P4 carries its own until P2 lands.
3 and 5 follow 1, and 6 comes last.

Neither 1 nor 2 alone makes a large store practical. That takes 3 and the
representation ranks 4 and 6. Until those land, `status` must print the
open-cost figure next to the profile values.

**Open, not decided here:**

- Whether T and H should move from the offline profile to a configuration
  record once P3 makes the open independent of them (§2.1).
- Whether the open refuses to serve when the checkpoint is missing and
  N > K (§3.1). The recommendation is to serve and report.
- Default values are proposals. ember or the coordinator sets them. The
  relation, not the numbers, is what the proofs depend on.
