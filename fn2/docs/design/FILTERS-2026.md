# Membership filters and static hashing for fn2's identity index (Scry survey, 2026-10-28)

Found with Scry over openalex.works titles (2021-2026) and Hacker News; DOIs are OpenAlex's. The question: what the identity index of STORAGE-DESIGN.md should use for (a) skipping sorted runs on a Message-ID lookup, (b) the active overlay that takes inserts and deletes, (c) the keyed-digest "forgotten identity" set after erasure, and (d) exact identity, which no filter answers.

## The constructions, newest first
| construction | year | what it is | bits/key at 1% FP (reported) | fits |
|---|---|---|---|---|
| Ribbon (Dillinger & Walzer; TODS 2026 version 10.1145/3785417; SEA 2022 10.4230/lipics.sea.2022.4; arXiv 2103.02515) | 2021-2026 | static filter and static retrieval by linear algebra over a ribbon-shaped matrix; "practically smaller than Bloom and Xor"; in RocksDB since 6.15 | ~1.01-1.08× the information-theoretic minimum (≈7.7 bits/key at 1%) with bumped variants; queries read one cache line | (a) per-run filters, immutable, built once at run seal; the RocksDB deployment is the precedent |
| Binary Fuse (Graf & Lemire, 10.1145/3510449) | 2022 | 3- and 4-wise xor-style static filter; "fast and smaller than xor filters" | ≈1.08× minimum (3-wise), ≈1.075× (4-wise); fastest queries of the static family | (a) alternative to Ribbon when query speed matters more than the last 2% of space |
| InfiniFilter (Dayan et al., 10.1145/3589285) | 2023 | a quotient-filter variant that expands to any size without rebuild, keeping FP rate bounded | quotient-filter class, ~1.1-1.3× minimum, supports delete | (b) the active overlay: grows with the overlay, supports the deletes a withdrawn reservation needs |
| Memento (Costa, Dayan et al., 10.1145/3698820) | 2024 | a range filter: the first dynamic, robust one (no false positives on adversarial ranges), built on InfiniFilter's expansion | ~equal to InfiniFilter plus a memento per key | number-range queries over (group, number) runs if the ordered engine ever needs a range filter; not needed for Message-ID equality |
| Bamboo (10.1109/tnet.2024.3403997) | 2024 | cuckoo filter that resizes smoothly and adaptively | cuckoo class | (b) alternative to InfiniFilter where deletes dominate |
| Vector Quotient Filters (Pandey et al., 10.1145/3448016.3452841) | 2021 | quotient filter laid out for SIMD; deletes; high occupancy | ~1.1× minimum | (b) |
| Chucky (Dayan & Twitto, 10.1145/3448016.3457273) | 2021 | one succinct cuckoo filter over the whole LSM instead of one filter per run; the entry says which run | fewer total bits for the same whole-tree FP rate | (a) if the engine prefers one filter for the whole identity tree to one per run; interacts badly with run-level reclamation |
| Space lower bound for AMQ with duplicate insertions or deletions of non-elements (arXiv 2412.19249) | 2024 | the bound a deletable filter cannot beat when callers may delete what was never inserted | theory | (b) design constraint: the overlay must never delete a non-member, or pay |
| Parallel Wormhole Filters (10.1109/tpds.2025.3605780), PipeFilter (10.1109/tkde.2025.3543881) | 2025 | filters for persistent memory and pipelined CPUs | | not needed now |
| Learned Bloom / learned cuckoo filters (several, 2021-2023) | | a classifier in front of a backup filter | | NO: data-dependent FP rate is an adversarial surface for a public node |
| Attacking the privacy of AMQ filters by positive concentration (10.1109/tc.2022.3202753); privacy of multi-versioned filters (10.1109/tdsc.2023.3298967) | 2022-2023 | an observer of a filter's bits learns members | | the forgotten-identity set must be keyed (HMAC with a node secret) if the filter or run is ever exported or replicated |

## Static hashing for the exact index (not filters)
| construction | year | note |
|---|---|---|
| PTHash parallel/external (10.1109/tkde.2023.3303341), PHOBIC (10.4230/lipics.esa.2024.69), ShockHash/MorphisHash (10.1137/1.9781611977929.15; 10.4230/lipics.esa.2025.9), PtrHash (10.4230/lipics.sea.2025.21), Sphinx (10.14778/3749646.3749703, a succinct perfect-hash index for x86), the 2025 survey "Modern Minimal Perfect Hashing" (arXiv 2506.06536) | 2023-2025 | a minimal perfect hash over a sealed run maps each key to a slot in ~1.5-2.5 bits/key, so a run's exact record is found in one probe without a sorted search; the sealed, immutable run is exactly the static set MPHFs assume; PtrHash and Sphinx are the throughput leaders, ShockHash/MorphisHash the space leaders |
| Fingerprinting-based MPH revisited (10.1145/3596453) | 2023 | the fingerprint variant: faster construction, slightly more space |

## What fn2 should do (the coordinator's reading; the builder measures)
1. **Exact identity stays exact**: the sealed runs hold the full Message-ID octets, content identity and binding; a lookup ends by comparing bytes. No filter decides equality.
2. **Per-run static filter: Ribbon** (bumped, ~8 bits/key at 1/256 FP, one cache line per probe), built at run seal, stored beside the run, paged like everything else. Binary Fuse if measured query time matters more than ~2% of space. This is what skips runs on a lookup; RocksDB's deployment is the precedent.
3. **The active overlay: InfiniFilter** (expansion without rebuild, deletes for released reservations), with the 2024 lower bound respected: never delete a key that was not inserted.
4. **Per-run perfect hash: PtrHash or PHOBIC** over the sealed run's keys so an exact lookup inside a run is one probe, ~2 bits/key; measure against a plain sorted search with fence pointers before adopting, since the runs are already sorted.
5. ~~The forgotten-identity set~~ WITHDRAWN (ember 2026-10-28: Message-ID octets are kept; erasure is the operator's). No learned filters anywhere remains the rule.
6. **Range filters (Memento)**: only if the ordered engine's (group, number) runs ever need a range filter; XOVER's ranges are served by the run's own ordering and fence pointers.
Measurements to run: filter bits/key and probe ns at 1/256 and 1/1024 FP for Ribbon vs Binary Fuse on 1M and 100M keys; InfiniFilter overlay growth and delete cost; PtrHash vs sorted search inside a 64 KiB run.
