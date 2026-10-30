# Range primitives for B, C and D (R6a1; A/D DSL seat; present state)

`fn2/books/pool-ranges.lisp` (pool level) and their `fn2-core-*` wrappers in `fn2/books/core.lisp`
(operation set fn2-core-issue; defcosts in `fn2/books/machines-a-costs.lisp` for arms' `:uses`).
Each checks handles, owners and bounds once, then loops over the raw byte array with no per-byte
re-check. A range's length is its work: pass at most the run's byte quantum and continue across
runs. Owners are `(kind slot gen)`; a range is readable by its slot's owner in :workspace or
:leased-out, writable only in :workspace with no outstanding loan. Codes: `:ok`, `:bounds`,
`:stale`, `:state`, `:owner`.

| core wrapper | arguments | results |
|---|---|---|
| `fn2-core-copy-range` | `src sgen soff dst dgen doff len okind oslot ogen fn2-core` | `(mv code fn2-core)`; DOFF <= dst fill (no gap), DOFF+LEN <= cap; dst fill becomes max(fill, DOFF+LEN); overlap-safe within one slot |
| `fn2-core-compare` | `s1 g1 off1 k1 os1 og1 s2 g2 off2 k2 os2 og2 len fn2-core` | `(mv code result at)`: `:equal`/`:less`/`:greater` and the first differing index (LEN when equal); each range under its own owner (C's GC1) |
| `fn2-core-fold` | `slot gen off len hash okind oslot ogen fn2-core` | `(mv code hash)`: `fn2-fnv-step` over the range from HASH (u32) |
| `fn2-core-scan` | `slot gen off len target okind oslot ogen fn2-core` | `(mv code at)`: first offset relative to OFF of TARGET (a byte, or `*fn2-pool-scan-crlf*` for CR LF, both bytes in range); LEN when absent |
| `fn2-core-drop-prefix` | `slot gen k cursor limit okind oslot ogen fn2-core` | `(mv code cursor fn2-core)`: moves at most LIMIT tail bytes from CURSOR down by K; `:more` with the next cursor, `:ok` with the new fill (old fill - K) once done (D's GD4: no scratch slot; a reader that tracks its own start offset needs no compaction) |

Not yet: `fill-range` (the adapter-side bulk write the simulator needs; with the simulator port),
packed handles (R6a2), and the bytes-quantum measurement (R6a1's item 4).
