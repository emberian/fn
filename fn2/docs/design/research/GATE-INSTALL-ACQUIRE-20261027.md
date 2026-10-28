# Gate install/acquire latency, 2026-10-27

## Conclusion and measurements

The 25–45 minutes are not certification and not SSH. They are repeated whole-closure cache resolution over about 1,300 books: enumerate every usable origin of every book, open and stat/hash its certificate, port and FASL, construct and look up candidate parent/child certificate pairs, then revisit the selected entries to install them. `acquire` repeats that resolution after `install-partial`; `acquire-dtn` repeats it again in another Python process. The tank's random-file latency under load amplifies the traversal.

The exact `gate_walls.json` measurements are:

| run | hbox load at start | install | acquire | acquire-dtn | three phases |
|---|---:|---:|---:|---:|---:|
| `m1b-park-6009125b93` | 1.24 | 228 s | 69 s | 31 s | **328 s (5m28)** |
| `m1close2-d187817f6` | 4.52 | 907 s | 477 s | 375 s | **1,759 s (29m19)** |
| `gatespeed-82cc980e3` | 11.99 | 1,050 s | 700 s | 515 s | **2,265 s (37m45)** |

For `gatespeed`, install ran 21:36:13–21:53:43Z with 1,298/1,298 books installed and the following plan found **0 books to certify**. The actual default acquire step was 21:56:12–22:07:52Z (11m40), not the whole 16-minute interval to DTN; validate, host-forward and host-ld account for the remaining 4m25. DTN acquire was 22:12:17–22:20:52Z (8m35). Certification itself took 33 seconds.

The recent two runs acquired byte-for-byte the same default artifact set (`157ebd2c…`, 1,294 books) and DTN set (`8a76780f…`, 1,220 books). `tools/certs.py` and `tools/cert_alists.py` are unchanged between the fast `6009125b93` tree and slow `82cc980e3` tree. The difference is therefore cache shape and storage contention, not a newly added certification workload or a new copy implementation.

## The dominating operations

Code references below are in `build/lanes/cut/gate-speed` at `82cc980e3`, the exact revision of the measured run.

### Install: candidate enumeration and artifact reads, not the eventual copies

`hbox_native.sh:1019` invokes `certs.py install-partial` once locally on hbox. `install_partial` (`tools/certs.py:2155-2179`) walks all 1,298 required books. For each one, `book_entries` (`:696-714`) computes its closure key and `cached_entries` (`:1291-1319`) visits every origin directory. Each candidate takes an entry lock, reads `meta.json`, and calls `entry_matches_meta` (`:1168-1187`), which hashes `book.cert`, sometimes `book.port`, and `book.fasl`. This is thousands of cache directories and roughly tens of thousands of small file opens/reads/stats before the selected pairs are installed.

Selection then constructs every candidate parent/child combination (`:1733-1740`). `memoized_pair_checker` avoids repeating ACL2 probes, but still performs one SQLite `SELECT` per candidate pair (`:1079-1089`); only misses reach `cert_alists.acl2_certificate_pairs` (`:1109`). The existing counters `check.hits` and `check.probed` are not printed, so the run log cannot split this secondary cost from file I/O.

Only after selection does `install_entry` copy the chosen cert/port/FASL (`:1218-1261`). `place` is a temp-file copy plus `copystat` and rename (`:2634-2645`), with no per-file `fsync`. Thus ZFS synchronous-commit/fsync behavior is not the explanation, and the 1,298 final pair copies are not the operation identified by the profiles.

The decisive measurement is preserved in commit `817f5b32e` and the comment at `tools/certs.py:351-368`: an hbox cProfile measured **104 s of `content_hash` reads in a 238 s install**, and about **300 s in a redundant 558 s install**, across roughly 20,000 closure files at about 13 ms/read under load. A separate convergence install read 3 GB and exceeded 20 minutes before hash memoization. This is the same code path and workload shape as the 1,050 s install here.

### Acquire: a second whole-cache resolution, followed by a comparatively small ACL2 load

`proof_artifacts.acquire` calls `certs.artifact_sets` (`tools/proof_artifacts.py:261`). That repeats `required_closure`, `book_entries`, and integrity checking over the whole closure (`tools/certs.py:1438-1499`), then performs compatibility selection for complete single-origin candidates and again for the composed candidate (`:1500-1546`). Only after that does `install_artifact_set` revisit every selected entry (`:1663-1676`), and only then does ACL2 load the roots (`tools/proof_artifacts.py:277`).

The prior cProfile recorded in `817f5b32e` attributes about **450 s of a 711 s acquire** to `book_entries`/`required_closure` hashing. The current 700 s acquire has the same shape. `FN_CONTENT_HASH_FILE` now carries digest hits between processes (`tools/certs.py:374-450`), but it does not remove directory traversal, entry locks, JSON metadata reads, `stat` calls, candidate-pair construction/lookups, or hashing of newly installed local artifacts.

The ACL2 load is independently bounded by the immediately following `validate` step over the same installed roots: **43 s default and 45 s DTN**. Subtracting those loads leaves about **657 s of default acquire** and **470 s of DTN acquire** for resolution, selection and installation. DTN starts a fresh process over 1,220 books and repeats the resolution; the per-run hash memo shares digest values, not the resolved artifact plan.

### Ruled out

* **Certification:** zero books were pending in `gatespeed`; `certify` took 33 s. The nine-book comparison run certified those books in 108 s, not in the 907 s install.
* **SSH round trips:** `hbox_native.sh:1417-1450` ships the tree and one generated `run.sh`, then starts it detached. The phases run inside that one hbox process. `farm.py:586-621` uses SSH for a farm preflight, but it is not a per-book operation in this native gate. `green_check.py` is not called by these phases.
* **Per-file durable sync:** `place` does not call `fsync`; the evidence points to random reads/metadata and repeated resolution on the tank, made worse by concurrent hbox load.

## Fix and expected saving

Build **one run-scoped, reusable cache-resolution plan**, rather than making each Python entry point rediscover the cache. The plan should cover the union of default and DTN roots, retain each profile's distinct closure and resident-parent constraints, and name selected entries by cache path plus cert/port/FASL digest and toolchain. `install-partial`, default acquire and DTN acquire should resolve against the same indexed snapshot; installation must still revalidate each selected entry under its existing entry lock, and each profile must still pass its own ACL2 load. Newly certified books require resolution of their new entries and affected edges, not another unconditional scan of every old origin.

Two supporting changes attack the measured costs directly:

1. **Make the stat-keyed content-digest memo cache-scoped, not only run-tree-scoped.** At present every fresh gate starts with an empty `$T/build/.content-hashes.json` and re-reads the shared cache. A shared memo/index can reuse digests until `(dev, inode, size, mtime_ns, ctime_ns)` changes, without trusting stale bytes. Keep the final selected-entry integrity check.
2. **Index candidate metadata and batch pair-fact lookups.** Replace per-origin JSON/stat work with a cache index where sound, and replace the one-`SELECT`-per-pair loop with a batched lookup. Print elapsed time for closure construction, `book_entries`, pair hits/probes, selected-entry installation and ACL2 validation; the existing unreported `check.hits`/`check.probed` counters are the natural starting point.

The new `acquire-cached` path in `hbox_native.sh:991-1013` is not this fix: its own comment says it still re-enumerates, installs and ACL2-loads the set, and it is disabled for DTN runs. `--from-train` can already skip install/acquire for a suitable certified train tree, but it does not repair the ordinary gate path.

**Estimate:** the comparable fast run finished all three phases in 5m28; the slow run spent 37m45. At the slow run's load, a reasonable target after shared indexing plus plan reuse is **8–15 minutes total**, saving **about 23–30 minutes per default+DTN gate**. That is an engineering estimate, not a measured post-fix result: selected-entry revalidation/copies and the irreducible 88 seconds of default+DTN ACL2 validation remain. A first stage that only makes digest reuse persistent across gate trees should recover a substantial subset, but should not be expected to remove the repeated candidate and pair traversal.

