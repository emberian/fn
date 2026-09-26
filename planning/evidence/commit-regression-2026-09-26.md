# Commit regression after dev 483987b1: none on the commit path; the 20x compared tmpfs to ZFS (2026-09-26)

Lane `lane/commit-regression` (Opus 5.5), from dev 8d4ea42c, under the Fable
mandate §14 (matched measurements). No code changed. The finding (lane
pack-chain-serve, lane/bounds-p5 record, "Native") said an image built after
merging dev 483987b1 committed about 20x slower per record: `probe 2000` in
409.6 s against "1000 in 9.1 s" before the merge.

## Verdict

**No regression on the commit path. The finding compared two filesystems.**
Its "before" figures (probe-measure-finish-carried.txt, probe-measure-after.txt)
were taken on a tmpfs store. Its "after" figure (probe-form-measure.sh,
`M=/tank/fn/scratch/bounds-p5/measure2`) was taken on ZFS. Under one harness, the
pre-merge image b30763a6 commits at 207 to 275 ms a record on ZFS, the same as
the "regressed" 205 ms. Every image makes the same durable syscalls per commit.
The 250 to 400 ms 32 KiB POST that rep-wave-d saw on ZFS is the same fsync
latency. It is not a regression either.

A second, separate difference is real, but it is not a dev regression. On
dev (483987b1 and HEAD 8d4ea42c), the offline store bridge (`store probe`,
`store post`, the developer fixtures) is about 100x the CPU of the lane images.
The reason is that lane/bounds-p5's carried prepare and finish (its "cause 2")
has not been merged to dev. The served POST path does not show this difference.

## Matched harness (hbox, 2026-09-26 06:27 to 07:06 UTC)

Scripts are in commit-regression-2026-09-26/: measure.sh, post.py, syncs.sh,
prof-run.sh and prof-probe.lisp. Setup, the same for every image:
- The developer launcher of each image, with LD_LIBRARY_PATH set to OpenSSL 3.5.8.
- Init: `operator CONFIG init --profile scale --max-transactions 1048576
  --max-article-octets 2048 fn.letters fn.test`. The POST store uses 4096.
- The run is one systemd unit with MemoryMax=24G. The order is interleaved (a, b, c, d
  × tmpfs, ZFS × 2 repetitions), so the box's load falls on all four alike.
- The client is dev's rep_measure `article`/`post` over msgid_measure `Conn`
  (TCP_NODELAY and QUICKACK). It sends 100 POSTs of 2,048 octets on one
  connection, into a fresh owner.

Probe: `store STORE probe 1000`, x payload of 2,048 octets. The ms figure is
commit_seconds / 1000. CPU is the process's user+sys under `/usr/bin/time`, and
it includes the reopen of 1 to 1.5 s.

Stores: tmpfs is /dev/shm. ZFS is /tank/fn/scratch/commit-regression, on the
pool `tank`, which is 2.46T allocated with 278G free.

The box was NOT exclusive, and the brief asked for it to be. Other lanes'
units were live throughout: owner-checkpoint meas, hot-path-scans,
bp-lifecycle-5 profile, mission_lab, qb675-chainM and p5-native-8. The CPU
columns and the syscall counts do not depend on that load. The ZFS latency
does: it varies 1.5x to 3x between repetitions of the same image.

| | (a) b30763a6 lane base, pre-merge | (b) dev 483987b1 | (c) dev HEAD 8d4ea42c | (d) 59654ce8 = (b) + bounds-p5 carried prepare/finish |
| --- | --- | --- | --- | --- |
| probe 1000, tmpfs, ms/commit (rep 1, 2) | 0.63, 0.69 | 69.3, 85.8 | 72.2, 71.1 | 0.70, 0.62 |
| probe 1000, tmpfs, CPU s | 2.10, 2.23 | 70.4, 87.1 | 73.3, 72.2 | 2.37, 2.07 |
| probe 1000, ZFS, ms/commit | 275.1, 207.4 | 286.4, 257.1 | 231.2, 351.1 | 98.2, 146.6 |
| probe 1000, ZFS, CPU s | 3.82, 3.80 | 71.1, 71.7 | 82.0, 100.5 | 3.80, 3.35 |
| allocation, probe 1000 in-process (commit + reopen) | 1.657 GB (1.66 MB/commit) | same path as (c), not profiled | 103.5 GB (103 MB/commit) | 1.658 GB (n=1000) |
| syscalls per commit (strace, probe 100, tmpfs) | fsync 7.2, rename 2, link 1, unlink 1 | the same | the same | the same |
| POST 2 KiB ×100, tmpfs, median / p95 ms | 1.85 / 3.42; 1.72 / 3.59 | 1.58 / 2.23; 2.97 / 4.03 | 1.75 / 2.28; 1.57 / 2.25 | 1.87 / 3.90; 1.62 / 3.09 |
| POST ×100, ZFS, median / p95 ms | 155.1 / 397.3; 158.4 / 476.7 | 149.5 / 357.4; 166.8 / 383.2 | 66.7 / 295.0; 121.6 / 325.1 | 74.5 / 274.4; 83.4 / 285.3 |
| owner CPU per POST, ms (all rows) | 1.9 to 4.2 | 1.8 to 3.1 | 1.7 to 4.2 | 1.8 to 4.2 |

About the allocation row: SBCL `get-bytes-consed` over `fnn-command-probe`
at N = 1000, taken on tmpfs. For (d), the same figure at N = 300 is
0.436 GB.

About the payload-copy suspect: a POST's owner CPU is 1.7 to 4.2 ms on every
image. So the brief's suspect (`fnn-subject-id-buffer` passing the payload
as an octet list through `fnn-core`) costs nothing measurable at 2 KiB. Bytes
copied per commit were not measured apart from allocation.

## Cause, named

- **ZFS wall time: durable publish.** Each commit makes 7.2 fsyncs, 2 renames,
  1 link and 1 unlink, the same on all four images. On ZFS (busy, 90% full, no
  SLOG), 7.2 fsyncs cost 100 to 350 ms a commit. On tmpfs the whole commit
  costs 0.6 ms. The CPU is below 4 ms a commit on (a) and (d). This is closed
  as **no regression**.
- **Dev's offline-bridge CPU: an unmerged fix, not a regression.** The profile
  of (c) at N = 1000 (prof-8d4ea42c-n1000.txt, 14,880 samples) puts 88.6% of
  samples under `fnn-finish` -> `fn-store-sn-finish` -> `fn-sn-finish` ->
  `fn-sn-find-record` -> `fn-sf-record-pair` -> `fn-record-p`, and 70.8%
  under `fn-sn-completion-enabledp`. That path re-recognizes every record of
  the history at each commit. It allocates 103 MB a commit at N = 1000 and grows
  quadratically. The host line is host/store-node-host.lisp `fn-store-sn-finish`
  (`(next (fn-sn-finish before))`), and `fn-store-sn-prepare`
  (`fn-spc-prepare`) has the same shape. Dev has always had it:
  (a) and (d) are lane/bounds-p5 images, and they call `fn-ccar-sn-finish` and
  `fn-pcar-spc-prepare` instead. Their equalities
  `fn-ccar-sn-finish-is-sn-finish` and `fn-pcar-spc-prepare-is-spc-prepare`
  hold with no hypothesis. The served owner is already off both walks
  (books/owner-commit-carried.lisp, owner-prepare-carried.lisp), which is why the
  POST rows match. **The repair is merging lane/bounds-p5.** This lane did not
  port its hunk, to avoid a second copy that would conflict at that merge.
- Assurance chain: nothing changed. The slice's entry is `store probe` ->
  `fnn-command-probe` -> `fnn-bridge-prepare`/`fnn-publish`/`fnn-finish` (the
  same calls as `store post`). The maintained relation and the keystones are
  those named in lane/bounds-p5's record. Observed: identical probe results
  (`status passed`, reopen counts equal) on all four images.

## Consequences

- lane/bounds-p5's N = 20,000 scale fixture (`store probe 20000 article`) on
  ZFS is bounded below by fsync latency: 20,000 × 0.1 to 0.35 s is 35 min
  to 2 h, whatever the code does. It is a fixture builder: building it on tmpfs
  (or copying a built store) takes about 20 s on the (d) image. It is not held
  by a regression.
- The comparison rule this came from: a per-commit figure names its
  filesystem. "tmpfs vs ZFS" is two orders of magnitude on this pool.

## Native gate (image of dev 8d4ea42c = this lane's code)

The lane's final commit changes no host or book file, so its image is the
(c) core adbaa363...; tools/hbox_native.sh --no-build, label img-8d4ea42c.

- First run (tree = 8d4ea42c): test_store OK (21 tests, 24.0 s); test_native_owner
  FAILED 1 of 18: `test_developer_selectors_gate_arm_the_owner_and_stop_synchronously`,
  `unbound variable *FNN-SIGHUP-COUNT*` (and `+FNN-GC-NURSERY-OCTETS+`). The cause
  is a harness defect on dev: tests/native_developer_selectors_raw.lisp loads the
  deployed `fnn-main` by name, and `fnn-main` now reads two globals that
  operator-config (7c80e4f6) and rep-wave-d-2 (c76038f9) added, but the stub
  list did not load them. Classification: harness, not implementation.
- Repair: the raw test loads those two deployed definitions by name (no stub,
  no expectation changed).
- Second run (worktree with the repair): test_native_owner OK (log sha256
  8f98927bf710b9ef25f46e72fa38b1900886250d7dbe80f0e905d49140ec086e), test_store OK
  (f25562ac3c0be61c6119a73defbdf9fd42161466d59fb89476a18ceea16c8a9f); status 0.

## Ids

The brief assigned PKT-348 (finding) and PKT-348 (fix). Both are already
taken in planning/backlog-2026-09-25.md: PKT-348 is the `health` answer
during recovery, and PKT-348 is build_native_host's ACL2-error refusal. This
lane took neither. No fix was needed, so the finding needs one id for its
closure; the deputy should assign it.

## Artifacts (sha256)

| File | sha256 |
| --- | --- |
| fn-host-developer.core (a) b30763a6 | e769f1ce21517f68e925f43f489902d5c98fca1b46db4ad8cd2da7562653e82c |
| fn-host-developer.core (b) 483987b1 | d650e2f0c8cf3f43666172b0e522943b0abfe16449e693eba733bb78c1eda407 |
| fn-host-developer.core (c) 8d4ea42c | adbaa36302240fb25bd3f048e64362ea2886e54736281408ab8e738b39da883a |
| fn-host-developer.core (d) 59654ce8 (bounds-p5 tree5) | 006a7ff65c03a9b5aa6a027ef27f919286269192fd46992883ed687212d176c5 |
| probe-m1.log | c51b2ff39f86331a47013c63df31215d08e8661af0b1e497f4163d1949cfe7a2 |
| post-m1.log | a04f2b70c9eac776297e2f0a557f988e320cb67ddc3cafcc2926bc5b9787f3f9 |
| prof-8d4ea42c-n1000.txt | 52d43ce35601afc2859cdc0b00c86812286bca717689c9c612909eaf8cb09437 |
| prof-b30763a6-n1000.txt | 4be14ebc90e109e0f4eb01c8bb5da1d390ac6fa401a63ce156ea62c74514cb07 |
| syncs-probe-{b30763a6,483987b1,8d4ea42c,p5-59654ce8}-n100.txt | 5e3c6a06..., b694353d..., 09234128..., f47b2cba... |

The images were built by tools/hbox_native.sh (w28 acl2-literal-4g, certcache
install, then certify, acquire, validate, and the developer image) in
/tank/fn/scratch/commit-regression/native-img-REV. The (a) to (c) rows for
REV's `tests.test_store.StoreImageOnly` fail on purpose: that name does not exist,
and it was used for the build only.
