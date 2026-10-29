# fn2 certify times on dregg-forge (quiet box)

Measured 2026-10-29 on dregg-forge (Hetzner cpx62, 16 vCPU, 30 GiB; load average 1.5-3 from the box's other tenants), dev `615dfde78`, a fresh clone with no `.cert` files, the whole closure (121 books: 59 under `books/`, 17 under `sim/`, 45 under `tests/`) by `fn2/tools/forge-certify.sh` = `fn2/tools/certify.sh -j 8 -k` with `TIME_CERT=1`, under `swarm-build`. The ACL2 is the fn toolchain's `acl2-literal-4g-tls64k` (identity `8aeb1bea1896...`, equal to hbox's).

| | wall, whole closure at -j 8 | sum of per-book cert.pl wall | sum of per-book CPU (user+sys) |
|---|---|---|---|
| run 2 (the table below) | 175 s | 524.8 s | 523.4 s |
| run 1 (earlier fresh clone, same sha) | 173 s | 519.3 s | 517.8 s |

Beside the laptop (the two baselines on dev `8a4875e89`-era trees, `certify-times-books.md` and `certify-times-tests.md`; the laptop's load average was 40-240 throughout):

| slice | books | laptop | forge run 2 |
|---|---|---|---|
| `books/` CPU seconds (the laptop table is CPU) | the 37 in the laptop table | 129.7 s | 128.1 s |
| `tests/` certify seconds (the laptop table is wall under load, -j 2) | the 31 in the laptop table | 160.0 s | 101.3 s |

CPU per book is the same on both machines (the laptop's CPU seconds are honest; its wall seconds are the load). The box's value is that wall equals CPU: a book's wall number here is its own cost, so a regression or an improvement is readable from one run. No book is over 60 s (the largest is 32.4 s); 10 books are at or over 15 s.

Columns: cert.pl wall = the `Built ... (Ns)` line (includes loading the book's dependencies); certify-book and prove = the CERTIFY-BOOK summary in the book's `.cert.out`; CPU = user+sys of `.cert.time`. Regenerate with `python3 fn2/tools/certify-times.py` in a tree after `forge-certify.sh`.

| book | cert.pl wall s | certify-book s | prove s | CPU s |
|---|---|---|---|---|
| sim/sim-adapter-base | 32.4 | 32.2 | 29.6 | 32.4 |
| books/merkle | 28.8 | 28.5 | 26.9 | 28.8 |
| books/format-events | 25.3 | 25.1 | 12.1 | 25.3 |
| books/layout | 25.3 | 25.0 | 23.2 | 25.2 |
| books/format-check | 24.4 | 24.2 | 21.8 | 24.4 |
| books/format-storage | 17.1 | 16.9 | 7.7 | 17.1 |
| tests/core-child-assembly-callbacks | 16.8 | 16.5 | 15.0 | 16.8 |
| books/blake3 | 16.8 | 16.5 | 14.9 | 16.8 |
| sim/sim | 16.1 | 15.9 | 13.5 | 16.1 |
| books/assembly-callbacks | 15.1 | 14.9 | 13.5 | 15.1 |
| books/assembly-reference | 14.5 | 14.2 | 0.1 | 14.5 |
| tests/core-child-assembly-reference | 14.4 | 14.1 | 0.1 | 14.4 |
| books/machines | 14.1 | 13.8 | 13.2 | 14.0 |
| books/executor | 13.9 | 13.7 | 11.7 | 13.9 |
| books/vocab | 13.2 | 13.0 | 9.8 | 13.2 |
| sim/sim-state-data | 12.8 | 12.6 | 10.2 | 12.8 |
| sim/sim-state | 9.8 | 9.6 | 8.9 | 9.8 |
| tests/core-child-assembly-access | 8.1 | 7.8 | 5.7 | 8.1 |
| tests/core-child-assembly-core | 7.4 | 7.2 | 6.0 | 7.4 |
| tests/layout-unit | 7.4 | 7.2 | 4.4 | 7.4 |
| tests/columns-cost-unit | 6.8 | 6.6 | 4.1 | 6.8 |
| books/assembly-access | 6.8 | 6.6 | 4.5 | 6.8 |
| books/machines-a | 6.8 | 6.5 | 3.4 | 6.8 |
| books/assembly-core | 6.6 | 6.4 | 5.2 | 6.6 |
| books/format-physical | 6.6 | 6.4 | 3.2 | 6.5 |
| books/alloc | 5.8 | 5.7 | 3.7 | 5.8 |
| sim/sim-transfer | 5.7 | 5.5 | 3.7 | 5.7 |
| books/executor-access | 5.3 | 5.1 | 3.4 | 5.3 |
| tests/machines-a-unit | 4.5 | 4.2 | 2.3 | 4.5 |
| books/blake3-spec | 4.4 | 4.2 | 2.4 | 4.4 |
| tests/columns-cost-unit-20 | 4.3 | 4.1 | 2.2 | 4.3 |
| sim/sim-recovery | 4.3 | 4.1 | 2.1 | 4.3 |
| books/pool | 4.2 | 4.0 | 2.5 | 4.2 |
| tests/grammar-unit | 4.0 | 3.8 | 0.0 | 4.0 |
| sim/check-own | 3.5 | 3.2 | 2.3 | 3.4 |
| books/trace | 3.0 | 2.8 | 1.8 | 3.0 |
| books/sched | 2.8 | 2.6 | 1.9 | 2.8 |
| tests/core-child-assembly-dispatch | 2.8 | 2.5 | 1.5 | 2.8 |
| books/q1 | 2.5 | 2.3 | 0.0 | 2.5 |
| books/format-context | 2.5 | 2.4 | 1.0 | 2.5 |
| tests/wake-unit | 2.5 | 2.2 | 0.0 | 2.5 |
| tests/columns-cost-unit-10 | 2.4 | 2.2 | 0.9 | 2.4 |
| tests/callbacks-unit | 2.4 | 2.2 | 0.3 | 2.4 |
| sim/echo | 2.4 | 2.1 | 0.0 | 2.4 |
| books/nntp-grammar | 2.3 | 2.1 | 0.3 | 2.3 |
| tests/executor-unit | 2.2 | 2.0 | 0.0 | 2.2 |
| tests/layout-roundtrip | 2.1 | 2.0 | 0.8 | 2.1 |
| books/assembly-dispatch | 2.1 | 1.9 | 1.0 | 2.1 |
| tests/sched-unit | 2.1 | 1.9 | 0.0 | 2.1 |
| tests/work-controls | 2.1 | 1.9 | 0.0 | 2.1 |
| sim/check | 2.1 | 1.9 | 0.0 | 2.1 |
| tests/reference-unit | 2.1 | 1.9 | 0.0 | 2.1 |
| tests/sim-acquisition | 2.1 | 1.9 | 0.0 | 2.1 |
| books/grammar | 2.1 | 1.9 | 1.2 | 2.0 |
| tests/core-child-unit | 2.0 | 1.8 | 0.0 | 2.0 |
| tests/layout-teeth-unit | 2.0 | 1.8 | 0.0 | 2.0 |
| tests/declare-unit | 2.0 | 1.8 | 0.7 | 2.0 |
| sim/network | 2.0 | 1.8 | 1.0 | 2.0 |
| books/reference | 2.0 | 1.8 | 0.0 | 2.0 |
| tests/q1-unit | 2.0 | 1.8 | 0.0 | 2.0 |
| sim/check-trace | 1.9 | 1.7 | 0.0 | 1.9 |
| sim/check-work | 1.9 | 1.7 | 0.0 | 1.9 |
| tests/core-unit | 1.9 | 1.7 | 0.0 | 1.9 |
| tests/core-child-assembly-index | 1.9 | 1.7 | 0.9 | 1.9 |
| books/executor-wake | 1.9 | 1.6 | 0.1 | 1.9 |
| books/resources-owed | 1.9 | 1.6 | 0.0 | 1.9 |
| tests/core-child-assembly | 1.8 | 1.6 | 0.0 | 1.8 |
| tests/format-roundtrip | 1.7 | 1.5 | 0.0 | 1.7 |
| books/assembly | 1.7 | 1.5 | 0.0 | 1.7 |
| books/assembly-index | 1.7 | 1.4 | 0.7 | 1.7 |
| tests/staging-unit | 1.7 | 1.5 | 0.5 | 1.7 |
| tests/format-check-unit | 1.7 | 1.4 | 0.0 | 1.7 |
| tests/columns-unit | 1.7 | 1.5 | 0.6 | 1.7 |
| tests/core-child-registration | 1.6 | 1.4 | 0.5 | 1.6 |
| books/format-base | 1.5 | 1.3 | 0.6 | 1.5 |
| books/format | 1.5 | 1.2 | 0.0 | 1.4 |
| sim/storage | 1.4 | 1.2 | 0.7 | 1.3 |
| books/blake3-pool-spec | 1.3 | 1.1 | 0.7 | 1.3 |
| tests/format-unit | 1.3 | 1.1 | 0.0 | 1.3 |
| books/digests | 1.2 | 1.1 | 0.5 | 1.2 |
| sim/prng | 1.2 | 1.0 | 0.8 | 1.1 |
| books/machines-directory | 1.1 | 0.9 | 0.3 | 1.1 |
| tests/vocab-unit | 1.1 | 0.9 | 0.0 | 1.1 |
| books/columns | 1.1 | 0.9 | 0.1 | 1.0 |
| books/machines-a-run | 0.9 | 0.7 | 0.0 | 0.9 |
| books/machine-dispatch | 0.8 | 0.6 | 0.0 | 0.8 |
| books/machines-a-scribe | 0.8 | 0.5 | 0.0 | 0.7 |
| tests/pool-unit | 0.7 | 0.6 | 0.0 | 0.7 |
| sim/recover-stub | 0.7 | 0.6 | 0.2 | 0.7 |
| books/core | 0.7 | 0.5 | 0.0 | 0.7 |
| books/core-children-a | 0.7 | 0.4 | 0.0 | 0.7 |
| books/reference-state | 0.7 | 0.5 | 0.0 | 0.7 |
| tests/blake3-unit | 0.7 | 0.4 | 0.0 | 0.7 |
| books/exec-state | 0.7 | 0.5 | 0.2 | 0.7 |
| tests/check-own-unit | 0.7 | 0.4 | 0.0 | 0.6 |
| books/machines-a-access | 0.6 | 0.4 | 0.0 | 0.6 |
| books/machines-all | 0.6 | 0.4 | 0.0 | 0.6 |
| tests/merkle-unit | 0.6 | 0.4 | 0.0 | 0.6 |
| books/crash-model | 0.5 | 0.4 | 0.0 | 0.5 |
| tests/alloc-unit | 0.5 | 0.3 | 0.0 | 0.5 |
| books/core-children | 0.5 | 0.3 | 0.0 | 0.5 |
| sim/check-history | 0.4 | 0.3 | 0.0 | 0.4 |
| tests/recover-unit | 0.4 | 0.2 | 0.0 | 0.3 |
| books/declare | 0.4 | 0.2 | 0.0 | 0.3 |
| tests/crash-model-unit | 0.3 | 0.2 | 0.0 | 0.3 |
| books/log-model | 0.3 | 0.2 | 0.0 | 0.3 |
| books/squares | 0.3 | 0.1 | 0.0 | 0.3 |
| books/resources | 0.3 | 0.2 | 0.1 | 0.3 |
| tests/squares-unit | 0.3 | 0.1 | 0.0 | 0.3 |
| books/profile | 0.3 | 0.2 | 0.1 | 0.3 |
| tests/network-backpressure-unit | 0.3 | 0.1 | 0.0 | 0.3 |
| tests/owed-unit | 0.3 | 0.1 | 0.0 | 0.3 |
| books/operations | 0.3 | 0.1 | 0.0 | 0.2 |
| books/fnv | 0.3 | 0.1 | 0.0 | 0.2 |
| books/owed | 0.2 | 0.1 | 0.0 | 0.2 |
| sim/check-reclaim | 0.2 | 0.1 | 0.0 | 0.2 |
| tests/log-model-unit | 0.2 | 0.1 | 0.0 | 0.2 |
| books/tuple | 0.2 | 0.0 | 0.0 | 0.2 |
| tests/resources-unit | 0.2 | 0.0 | 0.0 | 0.2 |
| books/assumptions-integrity | 0.1 | 0.0 | 0.0 | 0.1 |
| books/assumptions-native-span | 0.1 | 0.0 | 0.0 | 0.1 |

121 books; sum of cert.pl wall 524.8 s; sum of CPU 523.4 s
