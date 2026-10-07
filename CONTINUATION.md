# cert-origin-gaps continuation (no code edited yet)
- install() is tools/certs.py:2222; decision loop (largest closure first) fills `assigned`/`refused`; second loop over `books` places pairs via install_entry.
- Helpers: entry_per_origin (2208), book_entries (605), content_hash (355), read_meta (1776), usable_origin (1200), book_sources/book_name (363/375).
- Gap 1: `held[dep]` comes only from cache entries; a resident dep .cert in the tree is never consulted. Plan: resident origin = origins of cache entries whose book.cert content_hash equals the resident's; treat as binding when held[dep] is empty (uncached dep); unknown-origin resident under a refused/mixed decision is refused by name (add to mixed_origin).
- Gap 2: second loop only iterates `books` (names-filtered), so deps outside names are never placed. Plan: expand the placement list to the union of closures of requested books (book_sources(root) filtered by closure names), or refuse the book naming dep and both origins.
- Tests to add to tests/test_certs_one_origin.py (fixtures: publish(), ORIGIN_A/B, books/base + books/mid): resident base from B with mid from A (gap 1); install(names=["books/mid"]) with resident base from B (gap 2). Run each red before fixing; record in commit message.
- Gate: python3.12 -m unittest tests.test_certs_one_origin tests.test_certs
