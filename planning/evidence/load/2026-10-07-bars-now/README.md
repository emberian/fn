# Load bars now, 2026-10-07 (lane load-bars-now, deputy L)

Image set under test: CONVERGE-3, dev 0b4d3b183, hbox `/tank/fn/scratch/converge-3/native-c3-0b4d3b183/tree/build/fn-host` (production) and `fn-host-developer`, linked read-only through `tools/hbox_native.sh --reuse-image`. Box: hbox, ZFS (`/tank/fn/scratch`), always loaded (load average 11-26, other tenants: N's RSS A/B, E4's M3 run). Latency and pace figures are therefore labeled LOADED and are not judged for latency; memory and refusal results are load-independent.

## Verdicts

| bar | measured | threshold | verdict | conditions |
|---|---|---|---|---|
| L-RSS | VmRSS 123.0 MiB (run 1: anon 19.9, file 103.1, HWM 158.6) and 124.6 MiB (run 2: anon 21.0, file 103.5, HWM 163.9); 1000 of 1000 POSTs admitted, 0 refused (the test asserts 340/240 on each); 31 of 32 idle connections admitted | <= 128 MiB | PASS (margin 3.4-5.0 MiB) | hbox, load 12.7 (run 1) and 16.7 (run 2), small preset, 1068 MB heap by SBCL_USER_ARGS (test's shipped-launch shape), ZFS, production image above |
| L-HWM | 158.6 and 163.9 MiB | red if > 256 MiB | reported, below 2x | same as L-RSS |
| L-LIN | 64 KiB: t(512K)/t(64K) = 5.86 and 7.25 (two runs); exponent 0.98 for sizes >= 64 KiB, 0.84 over all points | ratio <= 15.0 (target 10.0) | PASS (judged only at N = 64 KiB) | hbox, load 12-14, developer preset of the test (`--profile development`, 1 MiB max article), ZFS, production image (FN_NATIVE_HOST) |
| L-FRESH 256 MB | refused at cold start, exit 1: `refused machine-cannot-hold-profile heap=497 MB machine=256 MB` | starts, serves 1 POST + 1 ARTICLE | FAIL | hbox, load 23.0, small preset, ZFS, cgroup `MemoryMax=256M MemorySwapMax=0`, production image |
| L-FRESH 1024 MB | refused at cold start, exit 1: `refused machine-cannot-hold-threads reservation=1030 MB machine=1024 MB` | same | FAIL | same, `MemoryMax=1024M` |
| L-CATCHUP 1000 | 1000 articles, seconds_to_done 34.2 = 29.2 articles/s (includes node start; the 10-05 lane figure was 28.69 s) | >= 35 /s (mandate) | FAIL (LOADED, reported) | hbox, load 13.4-13.7, developer image, loopback, ZFS; module 5/5 OK |
| L-CATCHUP 10000 | round failed `reason=round-deadline` at imported=9954 of 10000 in the 600 s round = ~16.6 /s; test red | >= 35 /s | FAIL (LOADED, reported) | hbox, load 12-18, same |

Repair items: new `planning/repair/items/LOAD-L-FRESH-0b4d3b183.json`; dated note appended to existing `SCEN-CATCHUP-PACE.json` (it has a notes field). L-RSS and L-LIN pass: no item. The 09-27 lanedump figure (4.3-5.0 /s) is not reproduced on this image.

## L-RSS detail

`FN_RUN_IMAGE_HEAP=1 tests.test_native_image_heap`, labels heap1 and heap2, raw `heap1.log`, `heap2.log` (the `FN_IMAGE_HEAP` JSON line is in each). Last known 156.6 MB; the image now rests at 123-125 MiB, almost all of it file-backed core pages (103 MiB). Units in the JSON are KiB/1024. The earlier 440 "articles in flight" refusal (MEM-011) did not occur in either run. heap1 was started before deputy L's request to hold L-RSS until 19:00 arrived (hbox clock 18:13); heap2 ran after N's run ended (`heap2-uptime.txt`).

## L-LIN detail

Total seconds from request to terminating dot (`scaling.txt`, load per run in `scaling-load.txt`):

| size | t (s) | from run |
|---|---|---|
| 4 KiB | 0.006 | N=4096 |
| 16 KiB | 0.052 | N=16384 |
| 32 KiB | 0.059 | N=4096 (8N) |
| 64 KiB | 0.082, 0.078 | N=65536 |
| 128 KiB | 0.114, 0.117, 0.119 (120 KiB) | N=16384 (8N), N=131072, N=122880 |
| 512 KiB | 0.480, 0.568 | N=65536 |
| 960 KiB | 0.988 | N=122880 (8N) |

Ratios t(8N)/t(N): N=4 KiB 9.80, 16 KiB 2.19, 64 KiB 5.86 / 7.25, 120 KiB 8.28. Small-size points are noise-dominated at load 13 (6 ms). The log-log fit over the pooled points: exponent 0.84; over sizes >= 64 KiB 0.98, i.e. linear. N=131072 cannot run: 8N = 1 MiB plus the headers exceeds the 1 MiB `--max-article-octets` and POST is refused `441 ... the article exceeds the configured size`, so the 1 MiB point is unreachable with this test; N=122880 (960 KiB) is the largest. Only the 64 KiB run is judged against 15.0.

## L-FRESH detail

`tools/load_fresh_start.py` (stdlib; imports Client, installed_launcher, environment from tests/native_harness.py). Per limit: `operator init` with the small-preset flags (exit 0 both), the image's own heap probe (`IMAGE --fn heap -- operator CONFIG run`) under the same cgroup limit, then the installed launcher (packaging/fn, which runs the same probe and launches at the decided figure) under `systemd-run --user --scope -p MemoryMax=<n>M -p MemorySwapMax=0`. Both probes refuse; nothing reaches LISTENING, so no POST/ARTICLE and no VmRSS at LISTENING exist. Stop is by the script's own recorded PID (not needed: nothing was running). Raw: `fresh-start.json` (probe stdout, launcher stderr, exit codes), `fresh-uptime.txt`. Note the 256 MB refusal is the decided heap of the small profile (497 MB) not fitting the machine; `tests/test_native_image_floor.py::test_fresh_node_serves_in_256_mb` instead measures a floor with `node_measure.py` at explicit heap sizes, which bypasses the probe, so the two disagree on what "256 MB" means. The brief's bar is the whole-process cgroup, and by that the node does not start.

## L-CATCHUP detail

`catchup.log` (the module, FN_CATCHUP_ARTICLES default 1000), `catchup10k.tail.txt` (test_catch_up_imports_every_article with FN_CATCHUP_ARTICLES=10000, trimmed). Pace includes node start-up and the 2 s poll interval of the test. The 10000 round ran into the 600 s round deadline, so it is red on pace, not on correctness (digest not compared).
