# connection-multiplexing: served connections on I/O loops, and the capacity against memory (2026-09-26)

Lane `connection-multiplexing` (Opus), branch `lane/connection-multiplexing`
from dev `1cd889180`, dev (batch AN) merged at `4b82ebcb7`. ember's priority 5:
"we can do a smarter kind of multiplexing than thread-per-connection";
PKT-605 (public-limits: nothing checked the capacity against memory) with the
gpt-6 wave-5 review's §6 terms (live changes, handshake/output/pin costs,
trusted exemptions never bypass the global budget, containment under a stated
offered workload); hostile-input-2's PKT-639 and PKT-640 (its campaign SCN-151; numbered
PKT-631/632 in its lane before batch AN) folded in. Ids: PRF-223, HST-024, SCN-153,
PKT-644 (PKT-645 reserved, unused). No wire or delta code, no store format,
no fn.toml key.

## 1. The design

Before: `fnn-owner-accept` (and each TLS / extra listener's accept thread)
started a thread per connection (`fnn-owner-launch-client` ->
`fnn-owner-serve-client`); the thread held a control stack (64 MiB reserved
on dev's launcher, 1,192 KiB after image-floor) and 2.6-4 MiB of runtime
regions for the connection's life, slept in recv(2), in the exposure wait
(`sleep`) and in the one-second drain after its last reply, and blocked in
SSL_accept.

After: `host/native/mux.lisp`. `+fnn-mux-loops+` = 2 threads each poll(2)
the connections they own and a wake pipe (poll, not epoll/kqueue: one code
path for Linux and OpenBSD; at 1,000 descriptors per loop poll's O(n) is
below the owner step's cost). The accept threads are unchanged except that
they hand the socket to a loop (round-robin inbox + wake byte). A connection
is a record holding exactly what the worker held on its stack:

| state | bound | the worker's equivalent |
| --- | --- | --- |
| input | one `+fnn-max-read+` (512) read, or the suffix a step left | the read in hand / RETAINED |
| out | the ONE reply being written; the connection is not read or stepped while it is queued | the blocking fnn-send-all |
| resume-at | `fn-exp-charge`'s milliseconds | `sleep` in fnn-owner-exposure-wait |
| idle-at | 1 s without input -> `fn-exp-idle` | the 1 s recv timeout |
| out-deadline / hs-deadline | 10 s | fnn-send-all's / fnn-tls-accept's deadline |
| draining | shutdown(WR), read until EOF or 1 s | fnn-graceful-close |

The owner is unchanged as the single mutation owner: every decision is the
same `fnn-owner-serialized` call the worker made, in the same order per
connection (`fnn-mux-begin` = the accept/open, `fnn-mux-work`/`fnn-mux-step`
= charge then `fnn-owner-handle-chunk` then the worker's post-step body line
for line, including PKT-600's sixth value, `fnn-mux-finish` = the worker's
unwind: owner close, exposure release, TLS close, socket). Every event runs in
`fnn-mux-guarded`, whose six handlers are the worker's six. A defect of the
loop itself (an error outside any connection's event) faults the service
(exit 4), since the loop serves every connection it holds. `once` runs
through the same loop (`fnn-mux-serve-once`): one path.

TLS: `host/native/tls.lisp` gains single-attempt `fnn-tls-accept-step`,
`fnn-tls-read-now`, `fnn-tls-write-now` answering the readiness to wait for,
with SSL_MODE_ENABLE_PARTIAL_WRITE | ACCEPT_MOVING_WRITE_BUFFER |
RELEASE_BUFFERS (the collector may move the reply vector between retries;
an idle session frees its record buffers). SSL_pending is checked every
iteration so decrypted octets inside OpenSSL are never stranded. At most
`+fnn-mux-handshakes-per-loop+` = 8 handshakes per loop are in progress (16
per node). A STARTTLS upgrade (already admitted) waits for a slot in FIFO
order; an implicit-TLS socket waits UNADMITTED (a socket and a record, no
handshake work, no share of the capacity) in a queue of at most
`+fnn-mux-queued-per-loop+` = 256 for at most the 10 s handshake deadline, and
is admitted (`fn-exp-open`) only when it takes a slot, just before SSL_accept;
past the queue or the deadline it is closed and named. This is the bounded
handshake pool: the loops are the pool, and a handshake never blocks a loop
(a slow or silent peer costs a record and a timer, not a thread).

PKT-639: an implicit-TLS connection meets `fn-exp-open`
BEFORE any handshake work: the capacity, the per-address limit and the
trusted range now bound handshakes; a refused connection is closed without
SSL_accept (its 400 cannot be sent in clear on a TLS port) and logged
`tls refused reason=refused connection=0`. PKT-640: every TLS
failure of a served connection writes ACL2's line `tls refused
reason=handshake|timeout connection=N` (books/connection-budget.lisp
`fn-cbud-tls-refusal-line`) to the service log as well as stderr.

Interface with lane owner-scheduler (agreed in both LANEDUMPs,
2026-09-27T00:20Z): their `fnn-owner-handle-chunk` returns an immutable PLAN
and `(values :defer MS ...)` for the folded charge; the loop takes `:defer` as
its resume timer and pulls the plan in windows of W octets off the mutex with
`fnn-owner-render-next`, holding one window per connection. Whichever lane
merges second adapts `fnn-mux-step`/`fnn-mux-flush`; the per-connection body
lives only in mux.lisp. With windows, the reply term below becomes W
(PKT-644 (a) closes).

## 2. The memory, and the theorem (PRF-223, books/connection-budget.lisp)

Per connection (`fn-cbud-conn-octets`), A the profile's largest article:

| part | term | small/development/scale (A = 32,768) |
| --- | --- | --- |
| heap: record (loop record, socket object, owner connection and session) | measured, 16 KiB | 16,384 |
| heap: input | 2 x 512 | 1,024 |
| heap: the one reply (STATED WORKLOAD: the largest article rendered) | 2A + 1,024 | 66,560 |
| heap: parser mid-article (line + body as octet lists, 16 octets each, twice for the copy) | 32 x (512 + A) | 1,064,960 |
| native: kernel socket buffers (defaults) | measured, 208 KiB | 212,992 |
| native: TLS session (when a context is loaded) | measured, 128 KiB | 131,072 |
| total | | 1,458 KiB with TLS, 1,330 KiB without |

The parser term dominates: the D27 octet-list representation of an article in
flight is 32 octets of heap per octet. It is the worst case (every connection
mid-way through the largest article at once), which is what a hostile
workload offers.

The base: heap-figure's figure for the store (`fn-heap-figure-octets`), the
core outside the dynamic space, and THREADS = 12 fixed + 2 loops + the
control clients (16), each with its control stack and 4 MiB of runtime. The
bound B = (machine - base) / per-connection.

Theorems (certified: persvati run-20260927T015456Z-53f5, manifest
certify-20260927T015536Z-1751083, book 5.2 s and tests 2.7 s at two jobs;
an earlier revision measured 10.3 s, fixed by tighter theories):

- `fn-cbud-bound-holds-its-connections` / `fn-cbud-bound-is-the-most`: the
  base (heap-figure's figure, the core, the threads) plus n connections at
  the whole figure fits for every n up to `fn-cbud-bound`, and not one more.
- The dynamic space caps the heap (added after bounds_join, section 4):
  `fn-cbud-resident-octets` of n = min(dynamic, figure + n x heap part) +
  the rest of the base + n x native part; `fn-cbud-limit` = the larger of
  `fn-cbud-bound` and the dynamic space's bound. KEYSTONE
  `fn-cbud-limit-holds-its-connections`: `(implies (and (<= (nfix n)
  (fn-cbud-limit ...)) (fn-cbud-base-fitsp ...)) (<= (fn-cbud-resident-octets
  ... n) (nfix machine)))`; `fn-cbud-limit-is-the-most`: the resident figure
  of limit + 1 exceeds the machine.
- KEYSTONE `fn-cbud-run-decide-holds-the-capacity`: an accepted run `(:hold
  L)` has capacity <= L = the limit and the resident figure of capacity
  connections within the machine. `fn-cbud-run-decide-refuses-exactly-past-
  the-limit`: refused iff capacity > L or the base fits neither way.
- KEYSTONE `fn-cbud-admitted-connections-fit-the-machine`: with PRF-211's
  hypotheses (`fn-cfg-limits-withinp`, the failed-login rule not refusing),
  capacity <= L and the base fitting, an admission (`fn-exp-admit-decision`
  = `(:admit)`) with nconns held leaves the resident figure of nconns + 1
  within the machine. Through PRF-211's `fn-exp-open-refuses-exactly-at-
  the-capacity`, the capacity counts EVERY connection: a trusted source is
  exempt from the per-address rule only, never from this budget.
- `fn-cbud-deltas-refusal-keeps-the-capacity-held`: a live delta list the
  refusal passes leaves the applied configuration's capacity within the
  limit.
- `fn-cbud-launch-decide-keeps-the-store-figure`: the probe's figure is
  heap-figure's plus room, never less.

Teeth (tests/acl2/connection-budget-tests.lisp): the friend's node (2 GiB,
the small preset's 815 MB, 30 threads of 1,192 KiB, A = 32 KiB) holds 622
TLS-capable connections (1,458 KiB each) and not 623; a developer node on 40
GiB with the default preset's 70 TiB figure holds 26,249 by the dynamic
space's way, and on 24 GiB none; for each keystone a witness and one
must-fail per hypothesis (H1/H2 of PRF-211's hypotheses by reference to its
own teeth).

Host lines: `fn-cbud-run-decide` (over the observed dynamic space, `sb-ext:dynamic-space-size`) is called by host/owner-host.lisp
`fn-owner-connection-budget`, called by host/native/mux.lisp
`fnn-mux-budget-install`, called by host/native/owner.lisp `fnn-owner-run`
after the exposure install and before listen: `connections holds=B
per-connection=K KiB` to the service log, or `refused
connections-exceed-memory capacity=C holds=B per-connection=K KiB machine=M
MB` (stderr, the log, exit 1). `fn-cbud-deltas-refusal` is called by
host/owner-host.lisp `fn-owner-reconfigure-deltas` (the one funnel of every
live reconfiguration: native-admin's `policy set`, peer-invite, auth) with
the bound the run installed (`fn-owner-connection-bound`); a refusal answers
`:connections-exceed-memory` through the reasoned reply. `fn-cbud-launch-
decide` is called by host/native/heap.lisp `fnn-heap-decision` (the
installed launcher's `heap -- ARGV` probe, `status`, `health`).

Assurance chain: native accept (a listener's accept thread) ->
`fnn-mux-adopt` -> `fnn-mux-begin` -> `fn-owner-exposure-open` =
`fn-exp-open` (PRF-211's refinement) -> the maintained relation "live
capacity <= the bound the run held", ESTABLISHED by `fn-owner-connection-
budget` at run (the run refuses otherwise) and PRESERVED by every live
reconfiguration (`fn-owner-reconfigure-deltas` refuses a delta list whose
applied capacity passes it; no other path changes the live configuration) ->
`fn-cbud-admitted-connections-fit-the-machine` -> observed in SCN-153
(section 4). The per-connection figure's measured constants are a model
established by measurement (section 3) and re-checked by
tests/test_native_mux.py (resident cost per connection < 64 KiB); no ACL2
transition preserves them, because they are about the runtime's and the
kernel's allocations.

Scope (the stated offered workload): each connection holds at most one reply
of at most 2A + 1,024 octets (ARTICLE/HEAD/BODY and every single-line or
bounded multi-line reply); an OVER, LISTGROUP, HDR or LIST over a large range
renders a larger reply today and is outside the figure until replies are
rendered in windows (owner-scheduler, PKT-644 (a)). The "pin" cost (a
connection pins the committed view at open; `fn-own-open`) is shared
structure while the view is current and is not separately bounded here.

PKT-644 (b): the launcher sizes the dynamic space before the configuration
journal is read, so the probe cannot see the capacity row; it reserves heap
room for the connections the machine holds, at most 1,024
(`*fn-cbud-launch-connections*`). Default: the probe replays the capacity
row (the configuration journal is small) and reserves exactly for it.
Rejected: an fn.toml key (public-limits' reason: two numbers for one
capacity). What continues without it: everything; the room is an upper
reservation, and the run's decision is exact.

Merge order: this lane counts each fixed thread at its OBSERVED control
stack. On dev's launcher (64 MiB stacks) the base on a 2 GiB machine is
already past the machine (30 x 68 MiB), so a 2 GiB installed node is refused
by name at run until image-floor's 1,192 KiB stacks land: image-floor must
merge before or with this lane (tests.test_native_heap_from_profile's 2 GiB
case).

## 3. Measurements (hbox, same box state, alternating)

`tools/mux_measure.py` on hbox under `systemd-run --user --scope -p
MemoryMax=24G`, 2026-09-27 00:37-01:00Z, two rounds alternating
before/after. BEFORE: dev's host code, the throughput gate's developer image
of 6701d5753 (`native-img-6701d5753`); AFTER: this lane's r2 developer image
(`native-r2`, aa8b8f02e's tree). Development-profile store, 50 POSTs of 2
KiB, capacity 1,264, loopback. Files: `connection-multiplexing-2026-09-26/hbox/`
(`before-1.json` ... `after-2.json`, SHA256SUMS).

| | before r1 | before r2 | after r1 | after r2 |
| --- | ---: | ---: | ---: | ---: |
| node threads, at rest | 7 | 7 | 8 | 8 |
| node threads, 1,000 idle held | 1,007 | 1,007 | **8** | **8** |
| RSS per idle connection, KiB | 252.3 | 336.8 | **2.9** | **2.9** |
| RSS, 1,000 idle + 200 active readers, MiB | 2,602 | 2,898 | **269** | **465** |
| greeting p50 / p95, ms (200 connect at once, 1,000 held) | 1,145 / 2,581 | 1,355 / 2,336 | 317 / 1,335 | 113 / 1,473 |
| OVER 1-50 p50 / p95, ms (200 readers x 10) | 8,805 / 9,751 | 10,553 / 11,164 | 10,281 / 10,851 | 9,321 / 11,745 |
| 200 readers' phase, s | 89.4 | 106.4 | 103.5 | 96.1 |
| connection setup, sequential, per s | 1,102 | 1,183 | **2,243** | **2,276** |
| connection setup, 8 concurrent clients, per s | 1,361 | 1,138 | 1,566 | 1,600 |

Reading it. Memory: a held connection costs 2.9 KiB of resident memory
instead of 250-340 KiB, and no thread; under the 200 active readers the node
holds 0.27-0.47 GiB instead of 2.6-2.9 GiB (the workers' touched stacks and
their per-thread allocation regions). The resident figure the book charges
for a connection at rest (16 KiB record + 1 KiB input) is above the measured
2.9 KiB; tests/test_native_mux.py pins it below 64 KiB (r3: 27.0 and 27.6
KiB with a GROUP issued on each of 300). Latency: every reader step is
serialized on the owner mutex in both hosts, so OVER's latency is the owner's
queue: 200 readers x 10 OVERs of a 50-article range take the owner 90-106 s
either way, p95 within 10% (after r1 better, after r2 5% worse); the loops
neither add nor remove owner work. The greeting (an exposure admission per
connection) and the connection setup rate improve: no thread creation per
accept, and the two loops admit while the owner serves. The OVER p95 is not a
win and is not claimed as one; the owner's serialization (owner-scheduler's
lane) is what moves it.

Implicit TLS (`--tls`: a fresh RSA-2048 pair; 1,000 idle TLS connections
held, then 100 TLS readers at once x 5 OVERs; 01:33Z before, 01:49Z after on
the r6 image; `tls-before.json`, `tls-after-r6.json`):

| | before | after |
| --- | ---: | ---: |
| node threads, 1,000 idle TLS held | 1,008 | **9** |
| RSS, 1,000 idle TLS held, MiB | 737 (+307 KiB each over rest) | **245** (a collection ran between the readings; below rest) |
| RSS, 1,000 idle + 100 active TLS readers, MiB | 1,142 | **197** |
| greeting p50 / p95, ms (100 TLS connect at once) | 1,064 / 2,207 | 191 / 828 |
| OVER p50 / p95, ms (100 x 5, over TLS) | 3,340 / 3,867 | 4,005 / 4,564 |
| TLS setup, sequential / 8 concurrent, per s | 22.5 / 164 | 22.3 / 172 |

The TLS setup rate is the client's (the Python driver's RSA verify, 349 ms
of box CPU per handshake on the client side; the node spends 2.9 ms). OVER
over TLS is 18% slower at p95 after: the workers encrypted 100 replies on
24 cores in parallel, two loops encrypt them one after another; that is the
cost of +fnn-mux-loops+ = 2 and the knob to turn (a measured follow-up, not
made here). An r5 image refused 72 of these 100 readers (its gate closed an
implicit-TLS socket when the pool was full); r6 queues them unadmitted and
serves all 100.

The hostile campaign's TLS family on this lane's r3 images (section 4)
measured the handshake side: 200 half-open TLS connections left the node at 9
threads (hostile-input-2 measured 207 on dev), a 30 s 48-way handshake burst
ran 5,064 attempts/s at 0.13 ms of node CPU per attempt with the node at 9
threads (dev: 3,409 attempts/s, cores saturated), and a completed RSA-2048
handshake cost 2.77 ms of node CPU (44 ms wall, sequential).

## 4. Native gate (hbox, both images, `tools/hbox_native.sh --images developer,production`)

| run | commit | modules | verdict |
| --- | --- | --- | --- |
| r2 | aa8b8f02e (+ uncommitted twin) | owner; public_limits; starttls; implicit_tls | owner 17/18 (the `fn-outcome-code` raw-script harness failure, PKT-614, fixed on dev at batch AN); the rest OK (2, 4, 3) |
| r3 | 30f39c178 (dev AN merged) | mux; owner; public_limits; public_exposure; starttls; implicit_tls; served_differential; nntp_post_probe; bounds_join | 8 OK (4, 18, 2, 1, 4, 3, 7, 13); bounds_join FAILED 2: the finding below |
| r4 | 1c6e211bd, `--mem 40G` | mux; bounds_join; public_limits; owner; implicit_tls | 5 OK (4; 2 + 1 skipped: FN_SPAN_REFERENCE_HOST, the base image, harness; 2; 18; 3) |
| r5 | 0113a3371 | mux; implicit_tls; starttls; public_limits; public_exposure; owner | 6 OK (4, 3, 4, 2, 1, 18) |

Log hashes: `connection-multiplexing-2026-09-26/native-logs-SHA256.txt`
(each run's SHA256SUMS and every module log line of r3, r4, r5).

SCN-153 (tests/test_native_mux.py) on r3: holds=14,980 per-connection
figure 1,330 KiB (no TLS context), threads 8 -> 8 across 299 more held
connections, 27.0 / 27.6 KiB of RSS each with a GROUP answered on each,
the live raise past the bound refused naming connections-exceed-memory
with the capacity unchanged, the raise to 325 published and exactly 25 more
admitted, then the busy 400; a capacity of 4,000,000 refused at start with
the line on stderr and in the service log, exit 1, nothing listening.

The bounds_join finding (r3). A developer image (its launcher's 32,000 MB
dynamic space) on hbox_native's 24 GiB cgroup, with a store on the default
preset and A = 4 MiB, was refused `capacity=31 holds=0
per-connection=139506 KiB machine=24576 MB`: the default preset's history
bound (1 TiB) makes heap-figure's figure 70 TiB, which no machine holds. The
resident heap is at most the dynamic space, so the book now takes the larger
of two bounds (`fn-cbud-limit`): the figure's way, and the dynamic space's
way (all of it, plus each connection's native part). On 24 GiB that node is
still refused, correctly: 32,000 MB of dynamic space and 2 GiB of thread
reservations (dev's 64 MiB stacks) pass the machine before any connection.
Classified: environment (the module's box budget), not a defect of either
side; the batch runs `tests.test_native_bounds_join` with `--mem 40G`
(r4: OK). Note the per-connection figure at A = 4 MiB: 136 MiB, 128 of it
the parser's octet lists (D27's open representation), i.e. a 4 MiB-article
node holds about 7 connections per GiB in the worst case.

Hostile campaign (`tools/hostile_campaign.py --families
connection,pipelining,tls,transit`, capacity 31), both images: r3 found one
defect, `a legitimate reader was not served during a TLS half-open flood`:
with PKT-639's order (admission before the handshake) 200 half-open TLS
connections from 200 addresses filled the capacity for the handshake
deadline. Repaired in 0113a3371: an implicit-TLS connection arriving while
its loop's 8 handshake slots are taken was closed before admission and named
`tls refused reason=busy`, so a flood holds at most 16 of the capacity. r5:
all four families OK on both images, no defect (reports under
`connection-multiplexing-2026-09-26/hostile/`). The r5 TLS rows: half-open
x200 threads 9 -> 9, legitimate reader served; 48-way burst 4,679 / 4,750
attempts/s, 0.141 ms node CPU per attempt, 66 completed/s; a handshake 2.9 /
3.3 ms node CPU.

Still open from PKT-639: a FAILED handshake is not counted as a failure
against its source (the campaign row `failed handshake vs per-address
limit`); the per-address rule bounds concurrent connections, not a failure
rate. Counting handshake failures like failed logins (`fn-exp-observe`) is an
ACL2 change to public-exposure (its keystones), left to a continuation.

## 5. What is not done, and the packets

- OpenBSD (section 6).
- PKT-644 (a): the reply term is the stated workload's; owner-scheduler's
  windows close it. (b): the probe cannot see the capacity row (section 2).
- PKT-639 remainder: failed handshakes are not metered as failures (above).
- The owner's serialization bounds the OVER latency; this lane does not move
  it (section 3).
- Merge order: image-floor before or with this lane (the 2 GiB installed
  node counts 64 MiB stacks until image-floor's 1,192 KiB land).

## 6. OpenBSD (the VM: OpenBSD 7.9, 1 vCPU, 2 GiB, LibreSSL 4.3.0, SBCL 2.6.3)

Built in the VM (`/usr/local/fn-work/fn-cm`: this lane at 09202195a over
image-floor's certified tree; `certify_books.py --closure` over the default
profile's roots: exit 0; developer and production images built). BEFORE is
dev's host code at the merge base 951cea05d built the same way
(`/usr/local/fn-work/fn-dev`). Both run with `SBCL_USER_ARGS=--dynamic-space-size
1024MB --control-stack-size 1216KB` (image-floor's stack), root's 4 GiB
datasize, RLIMIT_NOFILE 1024. Files: `connection-multiplexing-2026-09-26/openbsd/`.

Native modules on the VM (both images each): tests.test_native_mux OK (4:
holds=2,480, threads 8 -> 8, 24.3 / 24.4 KiB per held connection);
tests.test_native_implicit_tls OK (3, LibreSSL); tests.test_native_public_limits
2 errors, `OSError: [Errno 49] Can't assign requested address`: the module
binds client sources 127.0.2.9 and 127.0.3.9, which OpenBSD's lo0 does not
answer without aliases; environment, not this lane (it passes on hbox).

Measurement, 700 idle held (the most BEFORE can hold, below), then 50 readers
x 5 OVERs:

| | before | after |
| --- | ---: | ---: |
| threads, 700 idle held | 707 | **8** |
| RSS per idle connection, KiB | 209.3 | **20.3** |
| RSS, 700 idle + 50 active, MiB | 361 | **105** |
| greeting p50 / p95, ms | 117 / 125 | 102 / 113 |
| OVER p50 / p95, ms | 11,132 / 13,343 | 11,236 / 12,128 |
| setup sequential / 8 concurrent, per s | 1,165 / 621 | 1,624 / 1,169 |

At 900 idle (`m2-*`): BEFORE's node died at the 756th connection --
`mmap: Cannot allocate memory`, `fault operator run Could not create new OS
thread.` (`before-900-owner.stderr`): one thread too many and the whole
process stopped with every connection, the uncontained failure PKT-605
names. AFTER held 900 with 8 threads (15.9 KiB each) and served the 50
readers (greeting p95 207 ms, OVER p95 15.5 s on one vCPU).
