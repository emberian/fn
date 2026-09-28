# Format-9 topic admission sources

`matched-root.source` and `matched-report.source` exactly as they were before
lane blake3-digest re-derived them (`git show 61c799aaa^:tests/fixtures/topic-history/...`):
their FN-Topic fields name the controller key set and the root by
SHA-256 (algorithm 1) identities, which is what a format-9 node signed and
stored.  `tests/test_native_format_9_every_kind.py` authors them on a
format-9 image to build a format-9 store holding a topic anchor, whose
import into format 10 is refused by name (`signed-format-9-identity`,
books/store-format-9-records.lisp).  The ML-DSA-65 pair and the Ed25519
constants are `tests/fixtures/topic-history/`'s.
