# Function prefix registry

Every executable definition in `books/` carries a `fn-` prefix followed by a
layer tag. This table is the authoritative map from tag to book and meaning.
Add a row before introducing a tag; a tag with no row is a review finding.
Counts are not maintained here; `tools/ledger.py` reports them.

| Tag | Books | Meaning |
| --- | --- | --- |
| `fn-state-`, `fn-pending-`, `fn-accept-`, `fn-install-`, `fn-allocate-`, `fn-initial-`, `fn-articles-`, `fn-membership(s)-`, `fn-next-`, `fn-bump-`, `fn-clear-`, `fn-find-`, `fn-all-`, `fn-advance-`, `fn-make-`, `fn-pair-`, `fn-string-`, `fn-octet-`, `fn-no-`, `fn-selection-` | `acceptance`, `acceptance-invariants` | Logical acceptance machine: staged allocation, durable completion, fences, primitive domains |
| `fn-ag-` | `acceptance` | Guard-verified executable helpers (`car`, `cdr`, `member`, `append`) used in `mbe :exec` branches of the acceptance graph |
| `fn-retain-` | `retention`, `retention-invariants` | Abstract retention accounting: pins, charges, evidence-gated release |
| `fn-node-` | `node`, `node-invariants`, `node-traces` | One-transaction composition of acceptance and retention; article-to-pin bindings; event dispatcher |
| `fn-record-` | `records`, `records-invariants`, `records-canonicality` | Schema-0 transaction record grammar over CBOR primitives |
| `fn-cbor-` | `cbor`, `cbor-invariants` | Deterministic CBOR primitives: uint32 and definite byte strings |
| `fn-replay-` | `replay`, `replay-invariants` | Contiguous record replay into a node; typed ok/fault results |
| `fn-sf-` | `store-files`, `store-files-invariants`, `store-files-traces` | Immutable-file publication kernel: allocator frontier, staged record, barriers, crash constructor, recovery gate |
| `fn-sn-` | `store-node`, `store-node-invariants`, `store-node-resolution` | Live file/node composition: pending record binding, actual completion, refusal and known-abort resolution, observed opening |
| `fn-snt-` | `store-node-traces` | Trace relation and preservation for the composed store/node machine |
| `fn-snrt-` | `store-node-resolution-traces` | Trace preservation including refusal and abort resolution |
| `fn-checkpoint-` | `checkpoint` | Logical checkpoint capture, restore and checkpoint-plus-suffix replay |
| `fn-index-` | `index` | Derived group/number index and range queries |
| `fn-journal-` | `journal` | Historical isolated-slot journal experiment; not the adapter model |
| `fn-exchange-` | `exchange`, `exchange-invariants` | Bounded atomic fact-set admission and merge |
| `fn-transfer-` | `transfer`, `transfer-invariants`, `transfer-assembly-invariants`, `transfer-work`, `transfer-public-work`, `transfer-public-bound` | Fragment reservation, assembly, missing ranges, costed shadows and bounds |
| `fn-wire-` | `wire`, `wire-invariants` | NNTP line framing, dot stuffing, bounded retained input |
| `fn-nntp-` | `nntp`, `nntp-invariants`, `nntp-effects` | Reader command dispatcher, session cursor, projection, effects |
| `fn-ng-` | `nntp` | Guard-verified executable helpers for the NNTP graph |
| `fn-wildmat-` | `wildmat`, `wildmat-utf8-invariants`, `wildmat-parser-invariants`, `wildmat-matcher-invariants` | UTF-8 decoding, wildmat grammar parsing, dynamic-programming matcher |
| `fn-wm-` | `wildmat-matcher-invariants`, `wildmat-work` | Reference matcher and costed matcher shadow |
| `fn-article-` | `article`, `article-invariants`, `article-properties` | Bounded header/body article parser with exact source preservation |
| `fn-aw-` | `article-work-primitives`, `article-work-scanners`, `article-work`, `article-work-budget`, `article-public-work`, `article-public-bound` | Instrumented article parser shadow, value correspondence and work bounds |
| `fn-af-` | `article-fields` | Message-ID and Newsgroups field semantics over parsed views |
| `fn-bp-` | `bp-workflow`, `bp-workflow-invariants`, `bp-workflow-transport-invariants`, `bp-workflow-binding-core`, `bp-workflow-binding-invariants`, `bp-workflow-records` | Sender workflow: work, attempts, intents, transport observations, journal replay |
| `fn-bpa-` | `bp-adu` | Canonical CBOR application data units: request and receipt |
| `fn-bpi-` | `bp-ingress` | Legacy article ADU ingress, routing and composed-store admission |
| `fn-bpr-` | `bp-receipt` | Receiver state: request context, receipt intent and decision, receipt ADU emission |
| `fn-bprr-` | `bp-receipt-records` | Receiver journal record application and replay |
| `fn-bprv-` | `bp-receiver-*-invariants` | Receiver relation invariants over a Store, contexts, decisions and replay |
| `fn-bpo-` | `bp-outbound` | Outbound projection of sender work to request ADUs and receipt validation |

Host-only wrappers in `host/*.lisp` use `fn-store-`, `fn-bpreq-`, `fn-bpwf-`,
`fn-bprj-` and similar; they are `:program` mode and outside the proof boundary.
