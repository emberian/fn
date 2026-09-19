# Function prefix registry

Every executable definition in `books/` carries a `fn-` prefix followed by a
layer tag. This table is the authoritative map from tag to book and meaning.
Add a row before introducing a tag; a tag with no row is a review finding.
Counts are not maintained here; `tools/ledger.py` reports them.

| Tag | Books | Meaning |
| --- | --- | --- |
| `fn-state-`, `fn-pending-`, `fn-accept-`, `fn-install-`, `fn-allocate-`, `fn-initial-`, `fn-articles-`, `fn-membership(s)-`, `fn-next-`, `fn-bump-`, `fn-clear-`, `fn-find-`, `fn-all-`, `fn-advance-`, `fn-make-`, `fn-pair-`, `fn-string-`, `fn-octet-`, `fn-no-`, `fn-selection-` | `acceptance`, `acceptance-invariants` | Logical acceptance machine: staged allocation, durable completion, fences, primitive domains |
| `fn-ag-` | `acceptance-alloc` | Total executable helpers (`car`, `cdr`, `member`, `append`, `less`) that are their logical primitives by `mbe`; used in `:exec` branches across the tree |
| `fn-retain-` | `retention`, `retention-invariants` | Abstract retention accounting: pins, charges, evidence-gated release |
| `fn-node-` | `node`, `node-invariants`, `node-traces` | One-transaction composition of acceptance and retention; article-to-pin bindings; event dispatcher |
| `fn-record-` | `records`, `records-invariants`, `records-canonicality` | Schema-0 transaction record grammar over CBOR primitives |
| `fn-cbor-` | `cbor`, `cbor-invariants` | Deterministic CBOR primitives: uint32 and definite byte strings |
| `fn-replay-` | `replay`, `replay-invariants` | Contiguous record replay into a node; typed ok/fault results |
| `fn-sf-` | `store-files`, `store-files-invariants`, `store-files-traces` | Immutable-file publication kernel: allocator frontier, staged record, barriers, crash constructor, recovery gate |
| `fn-bs-` | `byte-store`, `byte-store-invariants`, `byte-store-programs` | Byte-level storage model under the file kernel (crash model v2): inodes, directories, pending writes and entry operations, per-object fences, unit-granular torn crash images, syscalls with EIO/ENOSPC outcomes, and the host's syscall sequences as programs over it |
| `fn-sn-` | `store-node`, `store-node-invariants`, `store-node-resolution` | Live file/node composition: pending record binding, actual completion, refusal and known-abort resolution, observed opening |
| `fn-snt-` | `store-node-traces` | Trace relation and preservation for the composed store/node machine |
| `fn-snrt-` | `store-node-resolution` (folded from `store-node-resolution-traces`, 2026-09-19) | Trace preservation including refusal and abort resolution |
| `fn-checkpoint-` | `checkpoint` | Logical checkpoint capture, restore and checkpoint-plus-suffix replay |
| `fn-index-` | `index` | Derived group/number index and range queries |
| `fn-journal-` | `journal` | Historical isolated-slot journal experiment; not the adapter model |
| `fn-exchange-` | `exchange`, `exchange-invariants` | Bounded atomic fact-set admission and merge |
| `fn-transfer-` | `transfer`, `transfer-invariants`, `transfer-assembly-invariants`, `transfer-work`, `transfer-public-work`, `transfer-public-bound` | Fragment reservation, assembly, missing ranges, costed shadows and bounds |
| `fn-wire-` | `wire`, `wire-invariants` | NNTP line framing, dot stuffing, bounded retained input |
| `fn-nntp-` | `nntp`, `nntp-invariants`, `nntp-effects` | Reader command dispatcher, session cursor, projection, effects |
| `fn-ng-` | `nntp` | Guard-verified executable helpers for the NNTP graph |
| `fn-nntp-index-` | `nntp-index` | Index-backed twins of the NNTP number enumerations and the generation-bound index cache |
| `fn-served-` | `served` | The served NNTP path as one logic-mode, guard-`t`-verified function: one socket read is `fn-wire-drive` then `fn-nntp-step` per framed event, with the reply concatenation, the partition law and the typed effect enumeration; the connection record (wire, session, pinned archive) and the two projections the host may take of an effect list |
| `fn-ideal-` | `ideal` | F_node, the ideal node functionality of [`specs/node-functionality.md`](../specs/node-functionality.md) section 1: the state record and the port dispatcher. SKELETON: only the reader port is real (it is `fn-served-step`); every other port is a stub returning the state with a `:todo` effect, and the robustness theorems of section 3 are written there as commented statements marked OPEN |
| `fn-dtn-` | (planned, `dtn-channel`) | The unauthenticated, adversarially scheduled bundle channel of [`specs/node-functionality.md`](../specs/node-functionality.md) section 5.4: the in-flight multiset and the adversary's delay, reorder, duplication, loss and injection. No book yet; the tag is registered so the skeleton above can name it |
| `fn-sys-` | (planned, `system`) | The composed system F_node × F_dtn: a finite map from endpoint id to node states plus one channel, and the end-to-end release theorem of section 5.4. No book yet |
| `fn-index-host-` | `host/index-host.lisp` | Trusted adapter that opens the index cache at a recovered generation and asks it; holds no enumeration logic |
| `fn-wildmat-` | `wildmat`, `wildmat-utf8-invariants`, `wildmat-parser-invariants`, `wildmat-matcher-invariants` | UTF-8 decoding, wildmat grammar parsing, dynamic-programming matcher |
| `fn-wm-` | `wildmat-matcher-invariants`, `wildmat-work` | Reference matcher and costed matcher shadow |
| `fn-article-` | `article`, `article-invariants`, `article-properties` | Bounded header/body article parser with exact source preservation |
| `fn-aw-` | `article-work-primitives`, `article-work-scanners`, `article-work`, `article-work-budget`, `article-public-work`, `article-public-bound` | Instrumented article parser shadow, value correspondence and work bounds |
| `fn-af-` | `article-fields` | Message-ID and Newsgroups field semantics over parsed views |
| `fn-frame-` | `frame`, `frame-invariants` | The one durable frame grammar (magic, version, kind, bounded length, payload, 32-octet trailer), its journal field grammar, and the constrained trailer function A-CRYPTO |
| `fn-id-`, `fn-charge-` | `identity`, `identity-invariants` | Content-identity derivation (subject and archive obligation), the hexadecimal projection, and the per-payload charge policy |
| `fn-store-` | `store-config` | The configured group table and the name/code mapping shared by every adapter |
| `fn-bp-` | `bp-workflow`, `bp-workflow-invariants`, `bp-workflow-transport-invariants`, `bp-workflow-binding-core`, `bp-workflow-binding-invariants`, `bp-workflow-records` | Sender workflow: work, attempts, intents, transport observations, journal replay |
| `fn-bpa-` | `bp-adu` | Canonical CBOR application data units: request and receipt |
| `fn-bpi-` | `bp-ingress` | Legacy article ADU ingress, routing and composed-store admission |
| `fn-bpr-` | `bp-receipt` | Receiver state: request context, receipt intent and decision, receipt ADU emission |
| `fn-bprr-` | `bp-receipt-records` | Receiver journal record application and replay |
| `fn-bprv-` | `bp-receiver-*-invariants`, `bp-receiver-evolving-*-invariants` | Receiver relation invariants over a Store, contexts, decisions and replay; the history-indexed relation over an evolving Store |
| `fn-bpr-live-` | `bp-receiver-evolving-store-invariants` | Live receiver trace model over the host's call sequence (`tools/run_bp_receive.py`): Store global, receiver global, journal on disk |
| `fn-bpo-` | `bp-outbound` | Outbound projection of sender work to request ADUs and receipt validation |
| `fn-bprl-` | `bp-release`, `bp-release-invariants` | Sender-side forwarding-obligation release: typed release evidence and term, the `:forward` pin undertaking, the release decision over the node image, and the journal wrapper for the proposed `:undertake`/`:release` records |
| `fn-relay-` | `relay`, `relay-invariants`, `relay-crash-invariants` | Relay undertaking: receiver-then-sender composition over the receiver and sender public entry points, terms table, undertakings ledger, typed `:archived`/`:forwarding` receipts, crash-then-replay over both journals |
| `fn-bprv-` | `bp-receiver-*-invariants` | Receiver relation invariants over a Store, contexts, decisions and replay |
| `fn-bpc-` | `bp-primary-cbor` | Deterministic CBOR vocabulary RFC 9171 §4.3.1 needs over `fn-cbor-`: definite arrays and text strings, unsigned integers to 2^64-1 |
| `fn-bpp-` | `bp-primary`, `bp-primary-invariants` | BPv7 primary bundle block: flags, CRC-16/CRC32C, `dtn` and `ipn` endpoint IDs, creation timestamp, lifetime, fragment fields, bundle identity, §4.4 extension block data |
| `fn-bpf-` | `bp-fragment`, `bp-fragment-invariants` | BPv7 fragmentation and ADU reassembly over identical-overlap covers; fragment primary blocks |
| `fn-clock-` | `clock`, `clock-invariants` | Host clock observations, Bundle Age anchors and the three-way bundle expiry decision |
| `fn-digest-`, `fn-sig-` | `crypto-seam` | Constrained digest and signature seam with shape-only constraints; tagged preimages; hex rendering |
| `fn-prin-` | `principal`, `principal-invariants` | Principal ids from (public key, token), key succession chains, keyrings |
| `fn-stmt-` | `statement`, `statement-invariants` | Block-shaped statement header, item-sequence codec, content id, signing, receipt payloads |
| `fn-lace-` | `lace`, `lace-invariants` | Statement sets keyed by content id: merge, canonicity, cross-canonicity, equivocation, causal closure |
| `fn-pol-` | `policy`, `policy-invariants` | Group policy statements, the policy in force, authorization, policy term and receipts |
| `fn-toy-`, `fn-t-` | `tests/acl2/*-tests` (substrate) | Test-only executable realisers attached with `defattach`, and test witnesses; never in `books/` |
| `fn-me-` | `membership-epochs`, `membership-epochs-invariants` | Group membership as epochs: commits over a base epoch, adopted chain and evidence set, the lace-shaped merge with explicit fork evidence, rosters, revocation knowledge, and the four-way admissibility decision for a late message. A policy model: no keys, no ciphertext, no digest |

Host-only wrappers in `host/*.lisp` use `fn-store-`, `fn-bpreq-`, `fn-bpwf-`,
`fn-bprj-` and similar; they are `:program` mode and outside the proof boundary.
The `fn-store-` tag is shared: `books/store-config` owns the group table under
it and `host/store-host.lisp` marshals under it. A host wrapper never decides
anything a book does not already decide.
