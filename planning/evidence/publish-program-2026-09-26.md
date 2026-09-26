# The durable publication program: measured, and the cheaper marker refused by its own contract (2026-09-26)

Lane `lane/publish-program` (Fable 5.1), from dev `17ff24aa`, wave 4 lane 9
(`planning/backlog-triage-2026-09-26.md`), brief
`build/coordinator/queue/done/w4-publish-program.txt`. Ids: PRF-169, STO-022,
SCN-099, PKT-441, PKT-442; PKT-079 narrowed, PKT-143 retired, PKT-186 closed.
Harness and artefacts in `publish-program-2026-09-26/`.

## Verdict

- **The served commit costs seven barriers, and the marker's two cannot be
  taken away under the frozen A <= M <= D by any program the brief allowed.**
  A fence drains one object: the marker's stage fence covers its content and
  its root fence its entry, and neither may precede the record's directory
  barrier (M <= D) nor follow the acknowledgement (A <= M). The three cheaper
  programs are stated as constructors in
  `books/byte-store-marker-candidates.lisp` and refused there: the deferred
  marker (the brief's "written with the next reservation") by the history
  model's invariant (three theorems), the folded stage fence by discipline D1
  and a garbled crash image, the in-place overwrite by discipline D2 and the
  same image. The served program `fn-bs-marker-program` and every host line
  are unchanged; the before rows are the after rows.
- **The one sound sharing is not a marker program.** Renaming the NEXT
  reservation's frontier under the marker's root barrier, before the
  acknowledgement, saves one barrier of seven and keeps both inequalities; it
  moves the reservation into the completion window, which the file kernel's
  phases and the K0 relation do not admit today. Designed as PKT-441 with its
  proof surface; PKT-442 asks ember which lever to pull on a pool where every
  barrier is a 40 to 60 ms ZIL commit.
- **The N = 10,000 POST "stall" does not exist on the current image, and
  PKT-186's profile was the profiler.** 10,000 POSTs of 2 KiB complete in
  63.7 s on tmpfs with no POST above 135 ms. What exists is a linear term per
  POST (the median grows from 2.2 ms in the first thousand to 13.5 ms in the
  last), and an in-process sb-sprof profile with no polling thread names it:
  `fn-own-refresh` rebuilding the group index on every refresh (hot-path-scans
  finding 1, PKT-324 item 1). rep-wave-c's 79 % in `SB-IMPL::QUERY-FILE-SYSTEM`
  was its own `probe-file` loop (68 samples = 68 ms of CPU across the whole
  window: the owner was blocked, not computing); nothing on the commit path
  calls probe-file, directory or truename.

## 1. Measurement (hbox, the developer image of dev 17ff24aa)

Image: `tools/hbox_native.sh --label base-17ff24aa 17ff24aa` (w28
`acl2-literal-4g`, the certcache, the developer image under swarm-build),
`/tank/fn/scratch/publish-program/native-base-17ff24aa/tree/build/fn-host-developer`,
core sha256 `002089cd0a4c440317b87398389d3de3d8580890f17b5e6b513d1a8ccb32ffeb`.
Every run is one unit `pp-step1` (`systemd-run --user -p MemoryMax=40G`),
driver `step1.sh`, OpenSSL 3.5.8 on `LD_LIBRARY_PATH`, the client the same
tree's `tools/rep_measure.py` and `tools/msgid_measure.py` (TCP_NODELAY,
QUICKACK). The pool is `tank`: 2.48T used, 155 to 157G free (90 percent), no
SLOG; the box was NOT quiet (owner-checkpoint's measurement, a qualification
run and the mission lab were live), loadavg 5.7 at the start and 10 to 12
through the probes. Stores: tmpfs is `/dev/shm/publish-program`, ZFS is
`/tank/fn/scratch/publish-program/m`.

### 1.1 Syscalls per commit (`syncs.sh`: `store probe 100` under `strace -f -c`)

| | fsync | rename | link | unlink | commit s |
| --- | ---: | ---: | ---: | ---: | ---: |
| tmpfs | 720 | 201 | 102 | 102 | 0.108 |
| ZFS | 720 | 201 | 102 | 102 | 31.55 |

Per commit: **fsync 7, rename 2, link 1, unlink 1** (the 20 extra fsyncs, the
extra rename and the two extra links are init and the reopen's recovery
barriers), identical on both file systems; the same figures commit-regression
took on four images. The seven are the frontier's stage and root
(`fnn-advance-frontier`), the record's stage, transactions directory and
staging directory (`fnn-publish`; the last best effort), the marker's stage
and root (`fnn-mark-committed`). On ZFS the 720 fsyncs took 27.8 s of the
31.5 s (`strace -c`: 38 us of syscall time each as counted by strace, the
wait is in the ZIL commit); on tmpfs 0.4 ms in all.

### 1.2 Per-commit wall (`measure.sh`: `store probe N`, scale profile, 2 KiB x payloads)

| | N | commit s | ms per commit | reopen s | CPU s (user+sys) | max RSS | load | pool |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | --- | --- |
| tmpfs | 1,000 | 0.765 | **0.77** | 1.49 | 2.33 | 545 MiB | 9.8 | |
| ZFS | 1,000 | 417.6 | **417.6** | 10.73 | 4.09 | 543 MiB | 11.3 | 2.48T/155G |
| tmpfs | 10,000 | 17.71 | **1.77** | 52.6 | 70.45 | 1.84 GiB | 10.3 | |
| ZFS | 10,000 | PENDING (running; about 420 ms a commit, 70 min) | | | | | | |

ZFS at N = 1,000: 417.6 ms a commit at load 11, against commit-regression's
207 to 351 ms at load 4 to 7 on the same pool with 278G free; the spread is
the pool's, 1.5 to 3x between repetitions (that record's own finding). tmpfs
at N = 10,000 is 1.77 ms a commit against 0.77 at N = 1,000: the probe's
in-process reopen and `fn-store-sn-finish` are linear in N (commit-regression
cause 2, merged as chained packs); the reopen of 10,000 records takes 52.6 s.

### 1.3 100 POSTs of 2 KiB on one connection (`post.py`, scale profile, 4 KiB articles)

| | median ms | p95 ms | max ms | owner CPU ms per POST | load |
| --- | ---: | ---: | ---: | ---: | --- |
| tmpfs (rep after N = 1,000 probe) | 3.55 | 4.51 | 6.99 | 3.5 | 9.8 |
| ZFS | **160.0** | **431.9** | 705.0 | 5.3 | 11.8 |
| tmpfs (rep after N = 10,000 probe) | 2.64 | 4.60 | 6.64 | 2.6 | 10.3 |

ZFS: a POST's durable reply is 160 ms median and 432 ms p95 at N = 100 under
load, on a pool where the probe's commit is 418 ms: the served path's seven
barriers, the same syscalls. Against answers §3's 250 ms p95 target this pool
does not qualify with the current program; a six-barrier program (PKT-441)
would move the median by about one seventh, not to the target (PKT-442).

### 1.4 The N = 10,000 POST curve and the profile (`post_n.py --prof`)

`post_n.py --n 10000 --octets 2048 --profile default` (rep-wave-c's profile:
the D27 default, 16 MiB articles), tmpfs, the owner started by the launcher's
own sbcl line with `prof-owner.lisp` loaded before `(acl2::sbcl-restart)`:
`sb-sprof` in `:cpu` mode, 2 ms interval, every thread, the report written
on SIGUSR1 from the driver at the end of the load (or after PROF_SECONDS, or
when the driver sees a POST over 900 s). The waiting thread blocks on a
semaphore; nothing in the image touches the file system until the report.

| POSTs | median ms | p95 ms | max ms |
| --- | ---: | ---: | ---: |
| 0 to 999 | 2.16 | 3.62 | 16.9 |
| 1,000 to 1,999 | 2.57 | 4.42 | 11.7 |
| 2,000 to 2,999 | 2.98 | 5.53 | 12.7 |
| 3,000 to 3,999 | 3.86 | 8.96 | 14.6 |
| 4,000 to 4,999 | 4.70 | 10.09 | 18.1 |
| 5,000 to 5,999 | 5.81 | 11.89 | 134.9 |
| 6,000 to 6,999 | 5.46 | 11.45 | 18.2 |
| 7,000 to 7,999 | 6.67 | 13.42 | 72.0 |
| 8,000 to 8,999 | 11.28 | 18.37 | 29.1 |
| 9,000 to 9,999 | 13.47 | 22.61 | 120.0 |

All 10,000 completed in 63.7 s (`post-n10000-p2048.json`; every time in
`.times`), owner CPU 62.0 s (6.2 ms per POST on average, growing), RSS after
the load 790 MiB, no stall (the largest POST 135 ms at index 5,245). The
profile (`prof-post-n10000-p2048.txt`, 29,180 samples over 58.4 s of CPU,
seven threads sampled, the profiler's own thread at 0 samples):

| cumulative | function | what it is |
| ---: | --- | --- |
| 31.9 % | `FN-INDEX-BUILD` (self 4.0 %) | the group index rebuilt from every article's memberships: `fn-own-refresh` -> `fn-gidx-build visible` (`books/owner.lisp:916`) |
| 18.0 % | `FN-INDEX-MEMBERSHIP-ENTRIES` | its walk over the articles |
| 13.2 % | `FN-GIDX-BUILD-ENTRIES` / 6.9 % `FN-GIDX-PUT` | its inserts |
| 24.6 % | `FN-AG-CAR` + `FN-AG-CDR` (self) | list walking under the above |
| 16.4 % | `FN-SCAR-FEED-COUNTED` / 10.6 % `FN-SCAR-FEED-BYTE` | the article's parse, per POST, constant in N |
| 5.8 % | `FN-RETAIN-OBLIGATION-IDS` | the retention walk, linear in N |
| 3.4 % | `FN-OWN-REFRESH` (total) | the refresh itself |

The linear term is the group index: hot-path-scans measured it by allocation
(3.2 MB per POST at N = 10,000 against 0.37 at N = 1,000) and this profile
measures it by CPU on the current image. It is PKT-324 item 1, not this
lane's; nothing in the store's publish path appears above 1 % (`__write`
0.8 %, `__open64` 0.8 %, `poll` 0.5 %).

**Why rep-wave-c timed out.** Its profiler (`rep-wave-c-2026-09-25/prof-raw.lisp`)
ran a thread that looped `(probe-file (f "stop"))` every 50 ms; the stall
graph (`rounds/post-after-p2048-stall-graph.txt`) shows `PROBE-FILE` called
only from `FNP-THREAD`, and its 68 samples at 1 ms are 68 ms of CPU across
the whole stalled window, so the owner was not computing: it was waiting.
Three rounds on a box at load 11 to 16 with the after image always scheduled
second, a 600 s socket timeout, both payload sizes. On the current image at
load 7 to 10 the same load completes in 64 s. The cause of those waits is not
recoverable from that evidence (no thread states, no syscall trace were
taken); the current image shows no stall, and `post_n.py` now records thread
states and a 10 s `strace -f` if one ever appears.

## 2. Why the marker costs two barriers, and what refuses each cheaper program

The served commit (`host/native/owner.lisp` `fnn-owner-publish-prepared`,
:700) runs, after `fnn-advance-frontier` (the frontier program, 2 barriers)
and the prepare: `fnn-publish` (the record program: stage fence, link,
transactions-directory fence, unlink, staging-directory fence), then
`fnn-mark-committed` (the marker program: stage fence, rename, root fence),
then `fnn-finish` (the acknowledgement). The contract (D31, §5.6 of the
mandate; `books/store-history-required.lisp` L3-6): A <= M <= D at every cut.

- M <= D: the marker of count n+1 may not be durable before record n is, so
  the marker's entry barrier follows the record's directory barrier.
- A <= M: the acknowledgement of n may not precede a durable marker of n+1,
  so the marker's entry barrier precedes `fnn-finish`.
- The content: the byte model's `fn-bs-fsync-file` drains exactly one
  inode's pending writes (`books/byte-store.lisp`; "fsync of a file does not
  persist its directory entry" and not another file's data). A rename of an
  unfenced stage lands an entry whose content may be any octets at a crash
  (`fn-bs-tear-write`: a unit lands as old, new, zeros or garble).

So between the record's barrier and the acknowledgement the marker needs one
content fence and one entry fence, and nothing else of the commit lies in
that window to share them with. The candidates, each a constructor in
`books/byte-store-marker-candidates.lisp` with `fn-bs-marker-program` kept as
the served program and specification:

1. **`fn-bs-marker-unfenced-program`** (the brief's "stage fence folded into
   the record's staging barrier"): create, write, rename, root fence. The
   model's own discipline D1 (`fn-bs-links-only-fencedp`, "every rename names
   a source whose last write was fenced") answers nil on it (asserted in the
   book). On the K5 fixture (byte-store-k0-marker-tests' completing pair:
   two records durable, the kernel :completing sequence 1), the crash image
   after its root barrier with the pending write's eleven units garbled (the
   fixture's unit is 4 octets; `bsmc-garble-selectors` carries the garble
   unit by unit) holds `(:present G)` for any G of the frame's length: with
   G the frame of count 23 the open of the two-record store is
   `(:refused :history-short-of-marker 23)`, with G junk
   `(:refused :marker-damaged)`. Keystone 1 (`fn-bs-marker-crash-open-stays-admitted`)
   and `fn-bs-marker-crash-after-barrier-is-new` are false of it; the served
   program's image at the same cut is the new marker (asserted beside it).
2. **`fn-bs-marker-in-place-program`** (the marker-required design's option
   3, one slot): overwrite committed-history.json, fence it. D2
   (`fn-bs-never-overwrites-authorityp`, "no write-all under an authority
   directory") answers nil. From the served program's durable state (count
   2 present and fenced) the crash at `marker-written` with the overwrite
   garbled gives the same two refusals of a store that lost nothing; after
   its one fence the image is the new marker, so the window before the
   fence is the defect, not the fence. A second slot does not repair it: the
   pending slot's garble may spell a count above the history and the byte
   model has no digest assumption to exclude it (an assumption of that kind
   is what the mandate says proves nothing about real hashes).
3. **The deferred marker** (the brief's first option: commit n's marker
   renamed under commit n+1's reservation, one root barrier for both):
   `fn-hmr-deferred-commit`, the history-model step in which a live process
   answers success for record COUNT while the marker still counts COUNT.
   Three theorems, all admitted:
   - `fn-hmr-deferred-commit-leaves-the-invariant`: `(fn-hmr-invp st)` and a
     live process imply `(not (fn-hmr-invp (fn-hmr-deferred-commit st)))`:
     A = COUNT+1 over M = COUNT.
   - `fn-hmr-deferred-commit-admits-a-lost-answered-record`: from the same
     state, K = COUNT is natural, `K < A` of the end state, and
     `(fn-hmr-open-verdict profile marker K)` is `(:admitted :marked K)`:
     the exact negation of `fn-hmr-open-refuses-below-every-answered-record`'s
     conclusion, so the newest record, lost after its 240, is admitted by the
     next open. That answers the brief's question: keystone 2 does NOT hold
     at the cut where the marker lags one commit behind an answered success.
   - `fn-hmr-deferred-commit-is-not-caught-up`: `fn-hmr-catch-up` over the
     shortened history is nil: D31 case (2) writes nothing, because the
     marker already covers COUNT. Case (2) does not cover the lag.

   Teeth (`tests/acl2/byte-store-marker-candidates-tests.lisp`): the
   reachable witness (a fresh unmarked store, its open's catch-up, one
   acknowledged commit, then the deferred commit: A 2, M 1, the open at one
   record admitted, the catch-up nil), beside the served step at the same
   point (the invariant kept, the open at one record `(:refused
   :history-short-of-marker 2)`); the live hypothesis removed (a state that
   is not live: the step is the identity, the invariant holds, K is not
   below A, a marker behind the history is caught up: three `must-fail`s);
   the invariant removed as corrupted-state witnesses (a live process over a
   marker above the history: the deferred step lands on the invariant and
   the open at K refuses; a live process over a marker behind the history:
   caught up). The fixtures holding a marker frame are zero-ary functions
   (a defconst is evaluated without the SHA-256 attachment).

**What survives.** The sharing that keeps every order: after record n's
transactions-directory barrier, stage the marker (n+1) and the NEXT
reservation's frontier (T+1), fence both stage files, rename both into the
root, one root fsync, then acknowledge n; the next attempt's
`fnn-advance-frontier` finds the reservation durable and replays only the
kernel observations. A <= M and M <= D hold as today; the process-death image
is a burned reservation (keystone 1 admits it). It saves one barrier of
seven (about 45 ms of 315 to 418 on this pool) and is a change to the file
kernel and K0: `fn-sf-start-frontier` in :completing with a reserved-next
slot (`books/store-files-traces.lisp`, `fn-sf-crash-imagep`'s frontier arm,
`books/store-node.lisp` `fn-sn-file-step`), the K0 relation's root pending
pair (`books/byte-store-scan.lisp` `fn-bs-pending-shape-okp` names exactly
one root entry, the frontier's; `fn-bs-pending-matches-phase`), and the cut
theorems of byte-store-k0, -staging and -marker; on the host
`fnn-owner-publish-prepared`, `fnn-advance-frontier`, `native_program_check`'s
tie and the cut list. That is PKT-441. Bounded group commit across
connections (one set of barriers per group) is the throughput lever and
needs the owner to hold more than one prepared submission.

## 3. Assurance chain and what is claimed

- Native entry: `fnn-owner-publish-prepared` (owner.lisp:700) ->
  `fnn-mark-committed` (io.lisp:1464) is the byte program
  `fn-bs-marker-program`, tied by `tools/native_program_check.py` (unchanged,
  PASS at this head: the book-to-host pairs are as before). The executed
  ACL2 subjects are `fn-hm-after-commit`, `fn-hmr-open-verdict`,
  `fn-hmr-catch-up` (unchanged).
- The maintained relation is `fn-hmr-invp` (A <= M <= D and the live
  coverage), established at the open (`fn-hmr-catch-up`) and preserved by
  `fn-hmr-step-preserves-the-invariant` (PRF-076, untouched). This lane's
  theorems are about a step that is NOT `fn-hmr-step`'s and show it breaks
  the relation; the behavioural theorem PRF-076's keystone 2 is therefore
  the one that refuses the design, and it stays as it was.
- The byte refutations are ground crash images under the model's admissible
  choices (`fn-bs-crash-choicesp` asserted), on the K5 fixture the K0 marker
  tests already use. A counterexample refutes a universal claim; no general
  theorem over the unfenced program's images is claimed or needed.
- Not claimed: any change to the served path's programs, cuts, host lines
  or observable; a native crash case at a new cut (there is none); that the
  sound sharing is proved (it is designed).

## 4. Certification

persvati, ACL2 8.7 w25 `acl2-literal`, 2 jobs, 300 s, `--affected-by` the
two books (`--root` this worktree, `--cache /home/ember/fn-certcache`):

- `run-20260926T102908Z-0df7`, manifest
  [`certify-20260926T102932Z-378295`](manifests/certify-20260926T102932Z-378295.json):
  `books/byte-store-marker-candidates` PASSED (the three theorems admitted);
  the test book FAILED on a wrong witness (one garble selector for an
  eleven-unit write; the fixture's unit is 4 octets and a selector list
  shorter than the units drops the rest). Diagnosed by evaluating the
  conjuncts in the run's own remote root on persvati with the w25 launcher
  (no laptop REPL: `tools/proof_repl.py` refuses the homebrew launcher as
  unqualified).
- `run-20260926T103449Z-fa4d`, manifest
  [`certify-20260926T103516Z-444060`](manifests/certify-20260926T103516Z-444060.json):
  PASSED, the test book certified, the book installed at run 1's bytes; no
  book over 10 s (the book and its tests are each under 3 s).

## 5. Native gate and the gate JSON

PENDING at this revision: the four crash-model modules on the base image with
this head's tree (`tools/hbox_native.sh --no-build`), and
`tools/throughput_gate.py run` on the base image labelled `publish-program`
(`--under-load`; the box is not quiet). No host byte changes, so the base
image is this head's image.

## 6. Ids and what is not done

- The brief assigns PRF-169, STO-022, SCN-099, PKT-441, PKT-442 and this lane
  took them; `planning/backlog-triage-2026-09-26.md` had reserved PRF-170,
  STO-023, SCN-101, PKT-433..434 for lane 9 and PKT-441..442 for
  multi-peer-relay. The brief is the assignment; the deputy should reconcile
  the triage.
- Not done: a cheaper served program (refused; PKT-441 is the design), the
  after rows (there is no after), the operator's durability sentence (the
  observable is unchanged), a 32 KiB N = 10,000 curve, a second ZFS
  repetition (the pool's spread is 1.5 to 3x between repetitions; every
  figure here carries its load).
