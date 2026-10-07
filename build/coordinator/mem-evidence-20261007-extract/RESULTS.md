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

- saved core 79.6 MB (the ACL2 image: 251 MB). Dynamic usage 57.6 MB; immobile 19.5; read-only 13.9; static ~0. Objects total 159.9 MB, of which 157.7 resident when the inventory ran.
- Biggest by type (MB allocated): (unsigned-byte 8) vectors 73.2; conses 35.1 (core-world data); SBCL code 11.6; simple-vectors 7.6; fn-books code 5.6; compiled-debug-info 3.6; bit arrays 3.0; base strings 2.5; char32 strings 2.0; SBCL symbols 1.2; fn-books symbols 0.8; ACL2-package code 0.27.
- The 73 MB of octet vectors and 35 MB of conses are the thing to look at: the ACL2 image held 25.7 and 109.8 MB of those in total, so the core-world export is carrying large byte arrays (likely the carried tables and constants) that the host reads little of. Not attributed further here.
- Prediction: this core idles at **51.4 MB VmRSS at tls 16384 (53.4 at 65536)**, anon 34.3 MB, core-mapping 15.2 MB (`idle-partial.log`, 2 runs each). It is mostly ANON, not file-backed: unlike the ACL2 image, SBCL has read this core's dynamic space into private memory. The host adds its ~2.1 MB of code plus runtime state on top. **M1's < 60 MB identity target is therefore tight (51.4 + host); the lever is the 73 MB of octet vectors and the 35 MB of conses, not the code.** An mmap-able core layout would show up in the Rss-of-core column.

## M1: not started

`origin/lane/extract-c` does not exist yet (checked after M0). M1 needs its load fix.

## Comparison to date (same box, same options, tls 16384, heap 1068)

| what | VmRSS MB |
|---|---|
| plain SBCL, stock core, idle | 37.8 |
| fn-core without host code (partial core, idle, no start) | 51.4 |
| ACL2 image, empty open, idle (N, 2026-10-06) | 115-129 (120.0 at idle-after-close) |
