# Book navigator

Open [the searchable index](index.html) to find a book by filename, function,
namespace prefix or proof ID. Select a row for its direct includes, reverse
uses, responsibility and source evidence. [map.json](map.json) retains the
complete machine-readable roots and gaps; [catalog.json](catalog.json) contains
maintained subsystem responsibilities and explicit exceptions.

Regenerate from the selected checkout after a source wave joins:

```sh
python3 tools/book_navigator.py --write
python3 tools/book_navigator.py --check
python3 tools/book_navigator.py --book books/stx-commit-codec.lisp
python3 -m unittest discover -s tests -p test_book_navigator.py
```

Only Git-tracked canonical `books/**/*.lisp` files enter the inventory. Lane
copies and untracked work are excluded. The generator reuses the ledger reader,
call graph, interface declarations, certification roots and reverse fan-in
machinery. It records host/native loads and references, interface extraction,
logical and local proof includes, proof-registry events, test/scenario includes,
and generation-script references. Lexical mentions remain labeled as references.
Computed loaders and generated names remain explicit gaps; `extra_roots` requires
a source coordinate and explanation.

Roles are source classifications, not qualification claims:

- `served/reference`: a host/load/interface source path reaches the book.
- `proof-support`: a registry target or local proof include reaches it.
- `generation-support` and `test-support`: those root families reach it.
- `test-only`: only discovered test paths reach it.
- `unknown`: no discovered root reaches it; this is not obsolescence evidence.
- `superseded`: an explicit maintained note names replacement and evidence.

Certification listing alone grants no functional role. A source revision,
content digest and per-book hashes bind the inventory; neither a positive role
nor a certificate listing implies a proved boundary, qualified image or live
activation. The source inventory is deliberately incomplete where dynamic uses
remain. Full unresolved records are available in the map.

For a new book, record its purpose and reusable boundary, register its namespace,
and identify its actual caller, proof-only or generation use. Prefer an existing
coherent leaf when its semantics and guards fit. Subsystem patterns express
responsibility, not active agent leases or runtime authority. Maintain exceptional
roots and replacement evidence in the catalog rather than editing generated files.

Exact cross-book function-body matches are candidates for a later coordinated
review, including repeated local induction helpers. Typed field projections can
share syntax intentionally. Check callers, local/proof scope, guards, generation,
representation and custody before proposing a reusable leaf. No candidate is a
deletion allowlist. This wave makes no moves, deletions, book merges or API/include
refactors; any later cleanup needs a quiet batch and affected-root validation.
