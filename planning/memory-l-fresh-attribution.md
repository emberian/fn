# L-FRESH: every term of both refusals, and what each start needs (Builder M, 2026-10-11)

Present state; rewritten whole when a landing moves a term. The model books evaluated here (heap-breakdown,
heap-store-figure, heap-figure, heap-reservation, heap-command, page-read-startup, peer-flight-startup,
memory-model, admission-memory, profile-limits) are byte-identical between the convergence 3119f7d32 and dev
ce629789b, so every figure below holds at dev for the same image.

## The point

1. **The node refuses L-FRESH in its launch probe, not in the memory equation.** The `:run` probe still sizes the
   heap from the profile's whole bound (the fresh store is not observed: `fn-heap-operation-observes-p :run` is
   NIL), and it compares the reservation (heap, the whole core file, every thread's stack and runtime) with
   memory.max, which bounds resident memory. The memory equation's own launch (`fn-mm-launch-decide`,
   books/memory-model.lisp) never makes that comparison: it compares resident with resident limits and the
   reservation with address-space limits only. On the same fresh store the equation admits the full C = 31 at
   1024 MB on both images, and at 256 MB on fn-core.
2. **No landing in the drain-to-convergence window changed a state term.** Every profile-bound term is equal
   to the octet in both images. Three things moved the refusals: the image grew (+1,696,752 octets of
   dynamic content and +4,915,784 octets of core file), one more fixed thread was added (12 to 13: memory
   3+4a `5f74a66f4`, the collector policy's thread), and megabyte rounding.
3. **fn-core serves L-FRESH at 1024 MB today.** At 3119f7d32 the extracted core's probe decides
   `heap=548 MB ... threads=36` under MemoryMax=1024M. It reached LISTENING, answered POST 240 and
   ARTICLE 220, peaked at VmHWM 58,352 kB, and logged `memory capacity=31 of 31 bound-by=configured sum=221 MB
   limit=1019 MB`. GAUNTLET judges L-FRESH on fn-host (the production image), so this is not a PASS of the bar.
   The image the bar names is ember's call (DECISIONS item 6).
4. **256 MB on fn-host cannot pass by shrinking the heap.** The core file (237.4 MiB) and 35 threads at 5 MiB each
   already reserve 412.4 MiB before any heap. Even in the equation, the image term alone (309.85 MiB) exceeds the
   251 MiB limit.

## Method (no hand arithmetic on the model)

- Box: hbox, tmpfs store. Each store was made with `operator init` using the cell's flags (`--profile development
  --max-transactions 16384 --max-history-octets 8388608 --max-record-octets 196608 --max-groups-per-article 16
  --max-open-suffix 128`, groups fn.letters fn.test: the small preset).
- Images: convergence fn-host `hbox:/tank/fn/scratch/integrate-20261011a/native-3119f7d3253e/tree/build/fn-host`
  (core 248,946,304 octets) and its fn-core `.../build/core/fn-core` (81,046,496); drain fn-host
  `hbox:/tank/fn/scratch/drain/native-drain-c0e35e156/tree/build/fn-host` (244,030,520).
- Reproduction: the bare probes under `systemd-run --user --scope -p MemoryMax=LIMIT -p MemorySwapMax=0` refuse
  as the acceptance did:
  - conv: `heap=594 MB` at 256 and `reservation=1121 MB` at 1024;
  - drain: `heap=592 MB` and `reservation=1106 MB`.
- The probe's call sequence was traced in each image (an SBCL trace of `fnn-call`, files `*-256.trace` and
  `*-1024.trace`), which gives each decision's inputs and the extension that refused.
- Every term was evaluated inside each image, by the image's own compiled ACL2 functions, at the observed core
  `(FILE . DYNAMIC)` (`terms.lisp` / `terms.out`). Its base terms are `fn-heap-breakdown-base`'s list, and their sum equals
  `fn-heap-store-base-octets` to the octet: "UNATTRIBUTED 0" in both images. The memory equation was
  evaluated at the run's own configure arguments, captured from `fn-adm-capacity-line` in a live run
  (`cap.lisp`, `mm.lisp`; `mm.out` for fn-host and `mm-fncore.out` for fn-core).
- Evidence directory: `planning/evidence/load/2026-10-11-m19-lfresh/`.

## The 256 MB refusal: `machine-cannot-hold-profile heap=596 MB`

The decision is `fn-heap-command-decide`. `:run` is growth class `:serves`, which is not store-opening, so it
falls through to `fn-heap-reserve-operation-decide :run` with observed NIL. Its heap is
`fn-heap-mb-of (fn-heap-store-figure-octets profile core 8388608 nil)`, the figure `fn-heap-breakdown :run`
itemises.

| term (fn-heap-breakdown) | drain fn-host, octets | conv fn-host, octets | MiB (conv) | moved by |
|---|---|---|---|---|
| image-dynamic (core content in use at the probe) | 134,992,320 | 136,689,072 | 130.36 | the image's growth across C1, +1,696,752 |
| state-history | 16,793,728 | 16,793,728 | 16.02 | - |
| state-handles | 786,432 | 786,432 | 0.75 | - |
| state-records (2 T records) | 136,314,880 | 136,314,880 | 130.00 | - |
| state-record-headers (8 H) | 67,108,864 | 67,108,864 | 64.00 | - |
| open-chunk-lists | 79,691,776 | 79,691,776 | 76.00 | - |
| open-suffix-vectors | 16,777,216 | 16,777,216 | 16.00 | - |
| open-per-record | 33,554,432 | 33,554,432 | 32.00 | - |
| inflight-lists | 7,864,320 | 7,864,320 | 7.50 | - |
| taken-submission-lists | 1,580,864 | 1,580,864 | 1.51 | - |
| octet-buffers (2 x capture budget) | 50,725,002 | 50,725,002 | 48.38 | - |
| articles | 3,441,664 | 3,441,664 | 3.28 | - |
| history-roots | 56,760,640 | 56,760,640 | 54.13 | - |
| base | 606,392,138 | 608,088,890 | 579.92 | |
| collector-room | 16,777,216 | 16,777,216 | 16.00 | - |
| figure | 623,169,354 | 624,866,106 | | |
| megabyte-rounding | 733,366 | 85,190 | | |
| **heap** | **595 MB** | **596 MB** | | |

- The profile-bound state (every row but image-dynamic) is 471,399,818 octets (449.56 MiB). It exceeds 256 MB by
  itself, so no image shrink passes this refusal.
- The acceptance read 594 to 596, and the bare probes here read 592 to 594. The dynamic usage the probe observes at
  its start varies by about 2 MB between invocations of one image, and the heap line follows it one for one. The
  change between the shas is image-dynamic only.

## The 1024 MB refusal: `machine-cannot-hold-threads reservation=1121 MB`

- At 1024 the base decision accepts: `(:heap 599 "small" 1024 1024 35)` in the trace, 596 untraced.
- The refusal comes from the served run's DEFAULT pool extension,
  `fn-prstartup-extend-default-reservation` (books/page-read-startup.lisp).
- That extension grows the heap to the launch floor `fn-prstartup-launch-floor`. The floor is
  `fn-heap-store-base-octets` over `fn-prstartup-image-bound core` = (FILE . FILE): **the whole core file
  charged as dynamic content**, 112,257,232 octets above the observed dynamic content.
- It then adds the pool's extra and checks `fn-heap-reservation-octets` against `fn-heap-machine-octets`, the
  least of the observations including memory.max.

| term | drain fn-host | conv fn-host | moved by |
|---|---|---|---|
| floor: core file as dynamic | 244,030,520 | 248,946,304 | image growth, +4,915,784 |
| floor: profile-bound state (as above) | 471,399,818 | 471,399,818 | - |
| floor: collector room (gc-nursery-mib 8) | 16,777,216 | 16,777,216 | - |
| floor | 732,207,554 | 737,123,338 | |
| pool extra: baseline heap (9 files, 4 workers) | 2,671,872 | 2,671,872 | - |
| pool extra: registration reserve | 1,008 | 1,008 | - |
| pool extra: read reserve (4 x 393,834 + queue 8,192) | 1,583,528 | 1,583,528 | - |
| grown heap (floor + extra) | 736,463,962 = 703 MB | 741,379,746 = 708 MB | rounding +327,096 |
| image outside the heap (core file) | 244,030,520 | 248,946,304 | image growth, +4,915,784 |
| threads x (1 MiB stack + 4 MiB runtime) | 34 x 5,242,880 | 35 x 5,242,880 | +1 fixed thread, memory 3+4a `5f74a66f4` (profile-limits :fixed-threads 12 to 13) |
| **reservation** | **1,159,437,368 = 1106 MB** | **1,174,838,912 = 1121 MB** | +15,401,544 |

- Thread count 35 = mux loops 2 + control clients 16 + fixed 13 + cold workers 4.
- Behind this refusal, the peer-flight extension adds 1 MB of heap and a 36th thread. The unlimited probe
  reads `heap=709 MB threads=36`, so with the DEFAULT refusal gone the 1024 line would read about
  1127 MB.
- Behind the probe sit two more checks that a direct start shows (`run-conv-1024.stderr`):
  - the run's own `fn-prstartup-peer-native-grant`, the same reservation against memory.max (`Peer flight
    startup refused: native worker reservation is not held`);
  - the cold startup's protected-runtime check, the same profile-bound state against the heap (`the process heap
    does not hold the store's protected runtime`, seen on fn-core with a 200 MB heap).

## The memory equation on the same fresh store (what the run computes at configure)

- Limit = memory.max less the pools (4,270,656 octets): 264,164,800 octets (251 MiB) at 256 MB and
  1,069,471,168 (1019 MiB) at 1024 MB.
- cfg as the run builds it: C 31, no TLS, triggers 8 MiB, over window 256, server 18 octets, config 120.

| term (fn-mm-sum) | fn-host 3119f7d32 | fn-core 3119f7d32 |
|---|---|---|
| base(img): core FILE | 248,946,304 | 81,046,496 |
| base(img): ANON (probe RssAnon) | 30,081,024 | 28,704,768 |
| base(img): 35 x THREAD | 45,875,200 (1,310,720 each) | 48,168,960 (1,376,256 each) |
| owner | 119,264 | 292,836 (one posted article) |
| connection fixed | 369,664 each | 369,664 each |
| large reply: OVER window (1 NOV line of 20,818 octets as lists) | 666,176 a holder | 666,176 a holder |
| inflight: request 9,445,184 + articles 3,441,664 | 12,886,848 | 12,886,848 |
| maintenance | 304,824 | 796,904 |
| sum at C = 0 | 358,318,414 (341.72 MiB) | 192,168,175 (183.27 MiB) |
| sum at C = 31 | 398,457,214 (380.00 MiB) | 232,306,975 (221.55 MiB) |
| reopen need | 342,497,110 | 176,669,418 |
| **at 256 MB (251 MiB)** | refused memory-cannot-hold-the-store, bound-by=store, sum=342 MB | **capacity=31 of 31**, sum=222 MB, 29.6 MiB to spare |
| **at 1024 MB (1019 MiB)** | **capacity=31 of 31**, sum=380 MB | **capacity=31 of 31**, sum=222 MB |

## What each start needs, term by term

**1024 MB on fn-host.** The reservation must fall by 97 MB, or must stop being compared with memory.max. The
equation already admits C' = 31 at 1019 MiB. The terms the probe charges that the equation does not:
- the profile-bound state, 449.56 MiB;
- the floor's whole-file charge, 107.06 MiB above the observed content;
- the 4 MiB runtime of each of 35 threads, 140 MiB of address space.

**256 MB on fn-core.** Every launch refusal above must go: the base heap, the DEFAULT floor, the peer native grant
and the cold protected runtime. The equation already admits C' = 31 with 29.6 MiB to spare, and A's *1* core
shrink (fn-core 81,013,712 to 74,262,808, -6,750,904 octets, READY vertical-core-star1) lowers the FILE term by
6.44 MiB, to 36 MiB of slack. Unmeasured: the cell also needs the POST and ARTICLE served within the cgroup.
The 1024 run's VmHWM of 58,352 kB says it is likely, not that it holds.

**256 MB on fn-host.** Even with the launch path fixed, the equation refuses: base(img) is 309.85 MiB against
251 MiB. The FILE term (237.41 MiB, every page of the core charged resident) is the only term large enough to
close the 90.7 MiB gap (sum at C = 0, 341.72 MiB, against 251 MiB). Two routes:
- fn-core as the image (-160.14 MiB);
- a FILE charge bounded by the measured resident file pages. W13 measured 65 to 108 MB of file pages for this
  image, and the bound is DECISIONS item 7's scope.
A's *1* shrink is an fn-core figure, so it does not move fn-host's term.

**The OVER window.** At L-FRESH's preset the OVER window is 666,176 octets a holder (20.7 MB at 31 holders) and
binds neither limit on either image. At `*fn-bs-profile-development*` (T 128, H 24 MiB, R 17,138,486) it is
562,557,120 octets a holder: A's measurement, 562,556,544, was taken at its own cfg. At that profile the
request term `fn-heap-request-octets` is also 551,585,280 octets, the record of R octets as lists. The sum at
C = 1 is 1,659 MiB on fn-host and 1,501 MiB on fn-core, so the development profile starts under neither limit on
either image. A's lease (HL4, fn-hl-leased-pool-within-the-large-term) and O's landing 2 retire the OVER term. No
named landing retires the request-lists term.

## The landings this names (cite this file)

1. **L-RUN-LAUNCH (Builder M; the run launch).**
   - What it does: the `:run` probe and the run's native grant are decided by the memory equation's launch
     (`fn-mm-launch-decide` over the observed totals at C', which `fn-mo-run-decide` already evaluates at
     configure).
   - What it retires for `:run`, as the twin of that launch:
     - the profile-bound store figure;
     - the DEFAULT floor's (FILE . FILE) charge;
     - the comparison of the reservation with memory.max, in the probe, the DEFAULT extension and the peer
       native grant.
   - Statement first: the launch admits exactly when the equation's gate holds at C' >= 1 and the reservation
     fits the address-space observations.
   - Predicted by the model, to be measured: fn-host serves at 1024; fn-core serves at 256 and 1024; fn-host
     still refuses at 256 (bound-by=store).
   - The books it touches beyond M's (page-read-startup, peer-flight-startup, heap-reservation) have owners to
     settle the seam with before the statement.
2. **The image L-FRESH judges** (ember; DECISIONS item 6): fn-core closes the 256 start on the model, and A's *1*
   widens the margin.
3. **The FILE term's resident charge** (DECISIONS item 7). This is the only route to 256 MB on fn-host.
4. **The development profile:** A's lease and O's landing 2 (OVER window), and an owner for the request-lists
   term.
