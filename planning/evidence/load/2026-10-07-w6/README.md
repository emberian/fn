# W6 peers (lane L6 load-peers), 2026-10-07

Harness: `tools/load/peers.py` (cells W6a catch-up, W6b feed, W6c catch-up under load). Every row below:
box hbox, filesystem tmpfs (/dev/shm), image `/tank/fn/scratch/converge-3/native-c3-0b4d3b183/tree/build/fn-host-developer`
(core sha256 5e342d1984b9...), preset `peers` (= tests/test_native_peer_catchup.py PROFILE), A and B on one box under a 16G scope,
heap decided by the image probe (A 1876-2021 MB, B 1883 MB). Raw cells.jsonl, result.json and logs: `hbox:/tank/fn/scratch/load/w6-<label>/`.

## Verdicts

| cell | label | box load at start | result | bar verdict |
|---|---|---|---|---|
| W6a@1k | l6-w6a-1k | 34.3 (loaded) | 28.67 articles/s excl node start (28.54 incl); round=done; divergence 0; chain digest equal | L-CATCHUP NOT-MEASURED (loaded); L-DIVERGE PASS |
| W6a@1k | l6-w6a-diag | 12.4 (loaded) | 33.21 articles/s; round=done | L-CATCHUP NOT-MEASURED (loaded) |
| W6a@10k | l6-w6a-10k-b | 16.5 (loaded) | round 1 failed reason=round-deadline at 600.4 s, imported=9013; round 2 done at 757.7 s; 13.2 articles/s overall (excl = incl); divergence 0, chain digest equal | L-CATCHUP NOT-MEASURED (loaded; the figure is far below 35); L-DIVERGE PASS |
| W6a@10k | l6-w6a-diag | 13.7 (loaded) | round 1 failed round-deadline at 600.6 s, imported=8810; done at 736.8 s; 13.57 articles/s | same |
| W6b | l6-w6bc | 12.2 (loaded) | 1,300 POSTs at 20/s from an empty A, B as feed peer: all 1,300 on B, divergence 0, drained 1.6 s after the last POST, feed lag max 24 articles. A POST p50/p99: 3.1/48.2 ms before the 1,024th, 3.5/103.1 ms after (n=276, so the p99 is the 3rd-worst sample) | L-DIVERGE-FEED PASS |
| W6c@1k | l6-w6bc | 11.4 (loaded) | A idle at 20/s: p50 2.8 / p99 67.4 ms (n=300); during catch-up p50 4.5 / p99 306.1 ms (n=969); ratio 4.54; catch-up 46.9 articles/s while taking POSTs; divergence 0, chain equal | L-CATCHUP-POST-P99 (proposal, <= 3x) NOT-MEASURED (loaded; value 4.54 recorded); L-DIVERGE-CATCHUP-LOAD PASS |

An earlier W6a@10k attempt (l6-w6a-10k) failed before the store existed (heap decided on the empty store refused the cold start; fixed by
re-deciding after the preload). Not a finding about the image.

Caveat on every latency/pace row: hbox load average was 11-34 (cores 16), above the harness's 8, so none is judged. The 10k shortfall (13 vs 35/s)
is 2.7x and reproduced in two runs; the 1k pace (29-33/s) sits at the bar.

## Mechanism of the slowdown with N (W6a@10k, hbox load 13-17, tmpfs, same image)

Per-1000 split seconds (l6-w6a-diag): 29.4 40.0 54.4 54.3 64.4 80.4 84.8 105.1 111.1 113.0. CPU seconds per 1000 articles:

| | 1st thousand | 10th thousand |
|---|---|---|
| A process (serving XFNCATCHUP) | 21.9 | 21.6 |
| B pull worker thread | 3.6 | 5.3 |
| B main sbcl thread | 3.5 | 20.6 |
| B owner io thread | 1.0 | 34.1 |
| B process total | 14.0 | 155.8 |
| B GC collections / GC seconds | 1,489 / 2.6 | 18,808 / 33.7 |

So per-article time grows roughly linearly with the count B holds, in B's owner side (commit/state path of each offered IHAVE), with allocation
per article growing about 12x; A and the pull worker are flat. sb-sprof windows (hook `planning/evidence/load/hooks/w6-prof.lisp`, l6-w6a-prof2)
show the same functions throughout (FN-CEI-BRANCH-GET 6.7 to 8.7% of samples, FN-CROW$C-PGET 3.8 to 6.1%, REVAPPEND, FN-CBOR-AG-CAR) with sample volume
19k to 35k per 120 s: a state-size-proportional lookup/copy per import; the flat profile does not name one caller. Filed as a dated note on
planning/repair/items/SCEN-CATCHUP-PACE.json. No host or book code changed.
