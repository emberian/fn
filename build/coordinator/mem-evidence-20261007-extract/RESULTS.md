# extract-measure M0 results (2026-10-07), lane/extract-measure on origin/dev 1e190ff19

Box: hbox, all runs under `SWARM_MEM_MAX=36G swarm-build`. The box was NOT quiet (N's CONVERGE-1 batch): load average 11.9-12.9 for the floor runs, 22-26 for the fn-core build and partial-core runs. Memory repeats within ~0.1 MB across repeats here; latency was not measured.
Runtime and SBCL_HOME are those the 3e53d7bc5 launcher names: `/tank/fn/sbcl/bin/sbcl`, `/tank/fn/sbcl/lib/sbcl/`. Options: `--dynamic-space-size 1068MB` (small preset), `--control-stack-size 1024KB --disable-ldb`, tls as stated. Scripts: `floor.sh`, `idle-core.sh` (same measurement as N's `bare.sh`: VmRSS, smaps_rollup Anonymous, smaps Rss of the core mapping, read at a fixed time while the process idles).

## M0(a): the floor (plain SBCL, stock sbcl.core, idle, read at 4 s of a 6 s sleep)

| tls-limit | VmRSS MB | anon MB | core-mapping Rss MB | runs |
|---|---|---|---|---|
| 16384 | **37.8** (37.77-37.84) | 9.0 | 32.3 | 4 (floor-run1/2.log) |
| 65536 | **39.7** (39.69-39.76) | 10.9 | 32.3 | 4 |

One first run read 18.0 MB (cold page cache; the process was still loading its core at 4 s) and is discarded; floor-run1.log keeps it. Consequence for the program table: the "34 MB bare runtime" of N's note is 37.8 here at tls 16384 with the whole 32 MB stock core resident; tls costs about 2 MB at idle (TLS pages untouched), not 11.

## M0(b): fn-core built with today's pipeline

- **No reference image or world at 1e190ff19 exists.** The newest gated image set is 3e53d7bc5 (used as FN_EXTRACT_IMAGE=.../fn-host-developer for runtime options and libs). The world-image cache (`/tank/fn/scratch/extract-cache`) has no entry for this tree's key (the tree on hbox has no certificates, so `world.py --digest` has no key to compute), and building one is an image job I was told not to start. I used the newest cached world, `world-18bcd401...` (Oct 5 04:43, source sha not recorded in the binding), by running `core-nocheck.sh` = `tools/extract/core.sh` with only the `world_binding.py check` line removed (diff in the file). So the export is: tree 1e190ff19's host files + an Oct 5 world. Treat as an approximation of today's pipeline, not as the gated result.
- Stages: host_tokens (8,082 words), export (core.json 16.5 MB, core-world.lisp 9.0 MB), cl.py (defs.lisp 10.9 MB), core_build.py, SBCL compile of clruntime and defs: all succeed (`core-m0.log`).
- **Dies at load**, as predicted: `Selected ACL2 table metadata is unavailable for FN-CARRIED`, from `(TABLE-ALIST FN-CARRIED :XL-WORLD)` under `FN-CD-RAW-PROBLEM`, during the first form of host-block.lisp (the raw-trap install, before any other host file loads). No fn-core is saved by core.sh.
- Also recorded: 9 distinct undefined-function/variable warnings in the defs compile (X2 closure gaps, `undefined-warnings.txt`): FN-PGS-FILL-FRAME, FN-DURABLE-REALIZE-LZ/-OCTET/-OCTETS, FN-CAT (variable), FN-SIG-VERIFY, FNN-COUNTERPART, FN-ARENA-STORED, CONGRUENT-STOBJ-REP. These may partly come from the older world; extract-forms' zero-warning gate will say.

## Heap inventory of the saved core BEFORE fn starts (the M1 prediction)

Because core.sh saves nothing when load dies, I built a measurement-only variant (`core-main-partial.lisp`: the one line `(load host-block.lisp)` wrapped in handler-case, core name changed; `build-partial.sh`). It is therefore **everything except the host: packages, clruntime, defs (the fn closure), core-world data; no host/native code at all** (the load died on host file 1). `inv-partial.txt` (`heap-inventory.lisp`, N's pagemap-by-type code verbatim) joined to pagemap on the freshly started core:

- saved core 79.6 MB (the ACL2 image: 251 MB). Corrected inventory `inv-partial2.txt` (heap 1068 MB, pagemap taken BEFORE any heap walk): dynamic usage 69 MB incl. the script, immobile 19.5, read-only 13.9. Objects 95.6 MB of which **43.5 MB resident at start**. (The first inventory of this lane, 160 MB / 73 MB octets / 157 MB resident, was wrong twice: it ran at heap 32000 so the pagemap buffer for the dynamic-space region was itself a 65 MB (unsigned-byte 8) vector, and it walked the heap before taking residency. Discarded; the 73 MB of octet vectors never existed. Real u8 vectors: 7.6 MB total, largest 37 KB.)
- Resident at start by type (MB, `PM` lines of inv-partial2.txt): SBCL code 11.0; conses 7.0 of 35.2 allocated; simple-vectors 6.3 of 7.6; octets 2.8 of 9.9 (incl. the script's 2 MB pagemap buffer); base strings 1.6; bit arrays 1.3; SBCL symbols 1.2; fn-books symbols 0.8. fn-books code does not appear in the top: it is in the immobile space (see REGION lines).
- Prediction: idle **51.4 MB VmRSS at tls 16384 (53.4 at 65536)** (measured, `idle-partial.log`), anon 34.3 MB, core-mapping 15.2 MB. That is the 37.8 MB stock floor plus 13.6 MB for the fn closure and world data, with no host code and no fn start. The host's ~2.1 MB of code plus startup state must fit in 8.6 MB for M1 < 60.

## Owner attribution of the cons and octet bytes (`attribute.lisp`; `attr-partial.txt` = partial core, `attr-image.txt` = the 3e53d7bc5 image before restart)

Method: walk from every symbol-value, every plist, every function closure and every code component's constants, first reach wins, with pagemap residency per object (taken before the walk). Partial core: u8 7.7 MB (all small), conses 26.1 MB attributed, other 8.5 MB.

| # | owner | MB (cons+other+u8) | resident at start | image carries the same? | lazy or profile-sized? |
|---|---|---|---|---|---|
| 1 | `acl2::*xl-props*` (hash table, core-world.lisp: the host-read world rows, 131k triples' plists) | 22.9 cons + 1.1 table = 24.0 | 0.6 | the same data is 25.8 MB in the image as three views (CURRENT-ACL2-WORLD 11.0, `*UNDO-STACK*` plist 8.2, world-key plists 6.3), so the core has one view, a net saving | already lazy: 0.6 of 24 MB resident. X3 will shrink it to the carried table rows |
| 2 | code-constants of SBCL's own code | 0.4 cons + 2.9 other + 0.06 u8 = 3.4 | 1.5 | yes (stock SBCL) | not ours |
| 3 | code-constants of fn-books code | 1.3 cons + 0.3 other = 1.6 | 0.05 | yes | no |
| 4 | `sb-vm::rsi-tn` (compiler register tables) | 0.3 + 0.9 = 1.2 | 1.1 | yes (stock) | not ours |
| 5 | code-constants of ACL2-package code | 0.35 + 0.59 = 0.94 | 0.06 | image carries ACL2 code, the core only what the closure needs | no |
| 6 | `sb-c::*backend-template-names*` | 0.1 + 0.5 = 0.6 | 0.6 | yes (stock) | not ours |
| 7 | `sb-kernel::*ctype-list-hashset*` | 0.34 + 0.03 = 0.4 | 0.4 | yes (stock) | not ours |
| 8 | `acl2::*xl-user-stobj-alist*` (live stobjs) | 0.03 u8 | 0.03 | the image's `*saved-user-stobj-alist*` is the same size | the live stobjs are small here: the fn stobjs are NOT created at preset size at load. They are created by the start path (M1/M2 measures it) |
| 9 | `sb-vm::*linkage-name-map*` | 0.17 | 0.17 | yes | stock |
| 10 | `sb-disassem::*instructions*` | 0.16 | 0.07 | yes | stock |

The partial core carries no other store-sized object: no `defconst` of any size appears above 0.01 MB. For comparison the image's top conses are `CURRENT-ACL2-WORLD` 11.0 MB, `*UNDO-STACK*` 8.2, the world-key plists 6.3 and `*fn-wgx-file-octets*` 1.3 (those are the 11.5 MB of resident prover state N found, absent from the core).

Verdict on M1: nothing in the core is large and resident except what the stock SBCL floor already pays. The one big non-stock object is `*xl-props*` (24 MB allocated, 0.6 MB resident, because it is only touched when the host reads a row). M1 < 60 is reachable if start-up touches under 8.6 MB beyond the floor + closure. The risk is the start path (stobj creation at preset size, the open), which this core cannot show: M1/M2 will.

## The 9 undefined-function warnings (X2's first findings; `undefined-warnings.txt`, from the defs.lisp compile against the Oct 5 world)

`ACL2::FN-PGS-FILL-FRAME` (2 uses), `ACL2::FN-DURABLE-REALIZE-LZ` (2), `ACL2::FN-DURABLE-REALIZE-OCTET`, `ACL2::FN-DURABLE-REALIZE-OCTETS`, `ACL2::FN-ARENA-STORED`, `ACL2::FN-SIG-VERIFY`, `ACL2::FNN-COUNTERPART`, `ACL2::CONGRUENT-STOBJ-REP`, and the variable `ACL2::FN-CAT`. The first four are in the storage line S is changing (fill-frame, durable realize); some may not exist in a world matched to 1e190ff19.

## M1: not started

`origin/lane/extract-c` does not exist yet (checked after M0). M1 needs its load fix.

## Comparison to date (same box, same options, tls 16384, heap 1068)

| what | VmRSS MB |
|---|---|
| plain SBCL, stock core, idle | 37.8 |
| fn-core without host code (partial core, idle, no start) | 51.4 |
| ACL2 image, empty open, idle (N, 2026-10-06) | 115-129 (120.0 at idle-after-close) |

## Pre-staged M1/M2 script (m1m2.py, run-m1m2.sh) and dry run (NOISY, load 12-14)

`run-m1m2.sh OUTDIR --core <fn-core launcher>` runs floor, `fn-core identity` (sampled every 10 ms to exit, last sample), fn-core empty small-preset open (6 s after LISTENING), and the 3e53d7bc5 production image empty open, 3 repeats each, tls 16384 / heap 1068 MB, one swarm-build job at 36G, 40 min timeout, kills only its own Popen PIDs. Dry run (floor + image only, `dry1-results.json`, 2026-10-07 00:55):
| step | VmRSS MB | HWM MB | anon MB | core-mapping Rss MB |
|---|---|---|---|---|
| floor | 39.8 | 39.8 | 9.0 | 34.2 |
| ACL2 image, empty open, idle 6 s after LISTENING | 107.1 | 129.0 | 12.9 | 92.0 |
The floor reads 2 MB above M0's 37.8 (read at 6 s of a 12 s sleep instead of 4 s of 6; the same stock core), so compare M1 against this script's own floor row. The image's 107 MB is the pre-open-transient figure (HWM 129 matches N's 115-129 range).
