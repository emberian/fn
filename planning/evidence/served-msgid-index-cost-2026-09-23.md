# Served Message-ID index: fixed ACL2 workload

On 2026-09-23, I measured the executed `fn-own-read` path and its two lookup
primitives in one ACL2 8.7 / SBCL 2.6.8 process. The executable was
`/home/ember/fn-gates/toolchains/w25/acl2-literal` (toolchain identity
`1b4169e9c5825a4e1fc827767f00470ceafc459619e0a4fd522c48f1ba964286`).
The process loaded the certified `tests/acl2/owner-tests` closure from persvati
`run-20260923T194435Z-da6e` and stayed alive for all measurements. Source
digests of the relevant loaded files were:

| File | SHA-256 |
| --- | --- |
| `books/owner.lisp` | `53c586cfce8a14efb13be75d509da9c1f01fe417ce7d7eec39edf278cbc5cf4e` |
| `books/owner-invariants.lisp` | `9408379a5c1e8085060b73739ec021046c4cc5e6ed08793b631a3de96961a02d` |
| `books/served.lisp` | `37f99ed87ddcd07585bd1f869a8ae8c8ebecd0dfacc9c9ca2c2a5350a2a201e1` |
| `books/msgid-index.lisp` | `c6ff5f4971bf27cbaf9dca6a0b0a134eadac2cab1ddbbf6998364ebd8a88f5f2` |
| `tests/acl2/owner-tests.lisp` | `2089a0a9b2509e941f5344b19246cd9ba89e15d6e81a9ac5a18e7529004b13d6` |

I started `python3 tools/proof_repl.py start t17bench tests/acl2/owner-tests`
and added REPL-only benchmark functions. `t17-bench-owner(N)` takes the real
reader connection 5 from `*own-late*`, prepends N distinct distractor articles
to its accepted archive, builds `fn-midx-build` for that list, and replaces
only that connection's archive/index pins. Each distractor copies a real
accepted article's fields, changing its Message-ID to `<benchN@x>`; this is
a synthetic lookup workload and **not** a Store-reachable owner satisfying
`fn-own-relation`, because the copied membership numbers and stamps are not
reallocated. The base three articles and reader session are from the executed
owner test. For every size, the called `fn-own-read` on connection 5 returned
`223` to `STAT <three@example>` and the trie exactly equaled a rebuild from
the synthetic article list. Setup and trie construction were outside the hot
read timer. The query was after every distractor in the list, so a scan had
to visit N preceding articles.

The timed functions repeated a call without mutating the owner. The read
function evaluated `(fn-own-read owner 5 *own-indexed-stat*)`; the scan used
`fn-find-article` on the same pinned article list; the trie call used
`fn-midx-lookup` on the same pinned index. All three accumulated a result
counter to force evaluation. `time$` reported the following single-process
wall and CPU times for 100,000 calls; times include the recursive repetition
loop and ACL2 `value-triple` evaluation:

| Distractors + base articles | Called `fn-own-read` wall / CPU | Linear lookup wall / CPU | Trie lookup wall / CPU |
| ---: | ---: | ---: | ---: |
| 100 + 3 | 1.30 / 1.30 s | 0.07 / 0.07 s | 0.03 / 0.03 s |
| 1,000 + 3 | 1.28 / 1.27 s | 0.63 / 0.63 s | 0.03 / 0.03 s |
| 5,000 + 3 | 1.34 / 1.33 s | 3.16 / 3.11 s | 0.03 / 0.03 s |

The called reads allocated about 1.958 GB for 100,000 results at all three
sizes (about 19.6 KB/read); direct scans allocated zero bytes, and direct
trie lookups allocated about 24 MB per 100,000 calls (about 240 bytes/lookup).
The construction cost is separate: rebuilding the entire trie 100 times took
0.01, 0.07, and 0.38 s wall at 103, 1,003, and 5,003 articles, respectively,
allocating 7.5, 86.7, and 477 MB. Live `fn-midx-refresh` can extend an
append-only view; it rebuilds on a discontinuous archive change. The index/archive correspondence
is carried by the invariant, not rechecked over the whole archive at runtime.

This measures ACL2 execution of a synthetic hot reader, not socket, disk,
native deployment, per-group/range, or `NEWNEWS` cost. It establishes no
server-wide scaling bound. Under the accepted 250-octet Message-ID ceiling,
a trie lookup has at most 250 character levels plus one terminal lookup,
each scanning at most 257 keys (256 characters and the terminal keyword).
This gives a conservative 64,507 branch probes, whereas the
measured `<three@example>` key is much shorter and its lookup took about
0.3 microseconds in this process. `NEWNEWS` and per-group range retrieval
still scan the pinned archive, so those paths retain their article-count
cost until the separate group index is served.
