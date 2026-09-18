# Executable ACL2 books

These books define the core behavior being executed and proved. They use ordinary
ACL2 events, not a separate specification implemented again in the host.

| Book | Responsibility |
| --- | --- |
| `acceptance` | Local articles, group allocation, pending transactions, uncertainty fencing |
| `acceptance-invariants` | General acceptance state/binding/number preservation |
| `wire`, `wire-invariants` | Incremental CRLF framing, dot transformation, event-yield state/suffix accounting |
| `cbor`, `cbor-invariants` | Bounded experimental CBOR primitives and representation lemmas |
| `records`, `records-invariants`, `records-canonicality` | Guard-verified provisional codec, full value round trip and accepted-input canonicality |
| `article`, `article-invariants`, `article-properties` | Syntax views, exact source preservation, successful-output recognizer and component bounds |
| `article-fields` | Exact Message-ID and Newsgroups semantics over preserved article views; narrow proto-article routing checks |
| `wildmat` and UTF-8/parser/matcher invariant books | Bounded grammar, scalar/progress safety, output recognition and DP/reference correspondence |
| `retention`, `retention-invariants` | Finite reservation ledger, permanent history, explicit release evidence, and release preservation |
| `node`, `node-invariants`, `node-traces` | Transactional composition and preservation of acceptance, reservations, and article-to-pin bindings |
| `replay`, `replay-invariants` | Actual-node record replay, monotone transaction counter advance, typed success/fault results |
| `journal` | Abstract isolated slots, barriers, crash images, recovery experiments |
| `store-files`, `store-files-invariants`, `store-files-traces` | Immutable publication/allocator kernel, arbitrary finite trace state/history/success preservation |
| `store-node`, invariant/trace/resolution books, `store-observed` | Fixed configuration and actual node completion before acknowledgement, exact replay-extension and arbitrary mixed-trace correspondence, observed-image recovery gates |
| `exchange`, `exchange-invariants` | Portable immutable facts, admissible bounded batches, conflict-preserving merge |
| `transfer` and invariant/assembly/work books | Reserved out-of-order staging, state/accounting and assembly/gap correctness, polynomial public-operation work including validation and structural equality |
| `nntp`, `nntp-invariants`, `nntp-effects` | Reader commands, arbitrary finite session/cursor preservation and proper reply/close effects |

`make certify` lists the current integrated dependency order explicitly. A
subsystem can be certified separately with, for example:

```sh
python3 tools/certify_books.py books/acceptance books/acceptance-invariants tests/acl2/acceptance-tests
```

Dependencies must already have valid certificates or precede their dependents in
that invocation. The runner fingerprints the requested local source closure and
requires real ACL2 success. The `cbor-invariants` book also includes ACL2's
`ihs/quotient-remainder-lemmas` community book.

The [proof registry](../planning/proofs.json) tracks broader targets. A certified
book does not imply full guard verification, all promised properties, a frozen
storage schema, or a physical durability guarantee. The
[implementation status](../docs/implementation.md) records these boundaries.
