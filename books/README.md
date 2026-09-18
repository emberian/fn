# Executable ACL2 books

These books define the core behavior being executed and proved. They use ordinary
ACL2 events, not a separate specification implemented again in the host.

| Book | Responsibility |
| --- | --- |
| `acceptance` | Local articles, group allocation, pending transactions, uncertainty fencing |
| `acceptance-invariants` | General acceptance state/binding/number preservation |
| `wire` | Incremental CRLF framing, dot transformation, event-yield boundary |
| `cbor`, `cbor-invariants` | Bounded experimental CBOR primitives and representation lemmas |
| `records`, `records-invariants` | Provisional transaction-record codec and full value round trip |
| `article`, `article-invariants` | Bounded syntax views and exact successful-parse source preservation |
| `article-fields` | Exact Message-ID and Newsgroups semantics over preserved article views; narrow proto-article routing checks |
| `wildmat` | Bounded UTF-8 grammar and dynamic-programming matching |
| `retention`, `retention-invariants` | Finite reservation ledger, permanent history, explicit release evidence, and release preservation |
| `node`, `node-invariants` | Transactional composition and preservation of acceptance, reservations, and article-to-pin bindings |
| `replay`, `replay-invariants` | Actual-node record replay, monotone transaction counter advance, typed success/fault results |
| `journal` | Abstract isolated slots, barriers, crash images, recovery experiments |
| `store-files`, `store-files-invariants` | Immutable-file allocator/publication kernel, transition/crash preservation, stable-prefix and one-crash success retention |
| `exchange` | Portable immutable facts, admissible bounded batches, conflict-preserving merge |
| `nntp` | Laboratory reader, LISTGROUP ranges and filtered LIST variants over committed acceptance state |

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
