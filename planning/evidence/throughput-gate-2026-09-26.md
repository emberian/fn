# Throughput gate (lane throughput-gate, 2026-09-26; PKT-407, PKT-408)

Lane `lane/throughput-gate` (Opus 5.5), from dev 0d211647, under the Fable
mandate §14 (matched measurements; a repaired candidate does not inherit
green). No book and no host file changed; no farm run.

## The result

A throughput regression can no longer reach dev through a green `make check`
without a named cause, **for the operations measured and within the scope
below**. `make check` (and `check-lane`) runs `tools/throughput_gate.py
check`. It compares the newest committed run of HEAD, or of HEAD's nearest
measured ancestor, with planning/throughput-baseline.json. A figure over
`max(base * 1.25, base + floor)` fails, unless planning/throughput-causes.json
names that run's revision with a reason. The merge routine's step (below) is
what makes a run exist for each batch. Without that step the check can only
say NOT MEASURED or STALE, and both of those pass.

## Three images, one harness (hbox, tmpfs, one unit each, 2 repetitions)

All six runs were taken **under load**. For the whole window (07:17 to 08:11
UTC), other fn lanes' units were running: qual-b6759850-matched/-mixed,
test_native_pack_chain, shi-meas, certify scopes. Box CPU busy (median) was
10% to 20% of 24 cores, with loadavg 4 to 7. Each JSON names its busy units.
Values are rep 1 / rep 2.

| | bbf52159 (release) | 483987b1 | 0d211647 (dev head) |
| --- | --- | --- | --- |
| core sha256 | e6640102... | d650e2f0... | 25913fc3... |
| probe 1000: CPU s | 70.7 / 68.7 | 67.8 / 67.6 | 74.1 / 71.7 |
| probe: ms per commit | 69.6 / 67.7 | 66.7 / 66.5 | 73.0 / 70.7 |
| probe: reopen s | 0.99 / 0.89 | 0.90 / 0.91 | 1.06 / 0.96 |
| bytes consed per commit (N=1000, in-process) | 103,341,504 | 103,341,502 | 103,341,507 |
| POST 2 KiB x100 median / p95 ms | 1.61/3.42; 1.55/2.06 | 1.58/2.41; 1.55/1.91 | 1.74/2.36; 1.72/2.49 |
| owner CPU per POST ms | 1.9 / 1.6 | 1.7 / 1.6 | 1.9 / 1.9 |
| ARTICLE x100 median / p95 ms | 2.83/5.05; 2.61/2.73 | 2.64/2.77; 2.52/2.61 | 2.79/5.11; 2.94/4.09 |
| reopen (100 articles) s | 0.158 / 0.145 | 0.153 / 0.139 | 0.163 / 0.155 |
| checkpoint at K/2 (64 x 31,744 octets): ms, octets | 377 / 350, 4,132,541 | 417 / 392, 4,132,541 | 435 / 414, 4,132,541 |

The verdict for the three images: **no throughput regression**, either
from the release to 483987b1 or from 483987b1 to dev head. Every operation
agrees within its repetition spread, and allocation per commit agrees to
the byte (±5 of 103 MB). Dev head's probe CPU is 4 to 6% above the other two
in both reps, which is inside the 25% tolerance. This table is evidence for
commit-regression's finding and agrees with it (its record,
build/lanes/commit-regression/planning/evidence/commit-regression-2026-09-26.md,
not yet merged). The "20x" compared tmpfs with ZFS. The quadratic offline
bridge (about 70 s of CPU and 103 MB per commit at N=1000, `fn-sn-finish` ->
`fn-sn-find-record`) is **in the qualified release too**: it is not a dev
regression. Its repair is lane/bounds-p5's carried prepare/finish (0.6 ms
and 1.66 MB per commit on commit-regression's image (d)). When that merges,
`check` prints IMPROVED, and the next `baseline` write lowers the figure so
the gate holds the repair (the ratchet).

What the gate would have said last night: the "20x" was a ZFS figure set
against a tmpfs one, and the gate takes every figure on tmpfs in one
harness, so the comparison that produced the alarm cannot arise inside it.
If a merge brought the quadratic walk back after bounds-p5's repair, then
probe CPU (about 2 s to about 70 s) and bytes per commit (1.66 MB to 103 MB)
would each be about 30x over the lowered baseline, and the check fails.

## What the gate measures (tools/throughput_gate.py box)

Everything runs in one `systemd-run --user` unit (swarm.slice,
MemoryMax=24G, MemorySwapMax=0), with stores under /dev/shm. Every image gets
the same client bytes (this tree's msgid_measure.py, rep_measure.py and
tests/native_process.py, shipped per run). Their digests are in the JSON.

- **quiet**: every other running user unit that is transient or fn-named
  gets its CPU sampled over 10 s. One at or above 0.05 cores is busy. By
  default a busy unit refuses the run: exit 3, and the JSON's `refused`
  names the units. The run waits up to `--wait-quiet` seconds first. Idle
  units, such as the live node and idle spike daemons, are recorded. With
  `--under-load` the run proceeds and records `quiet: false` plus the busy
  units. `check` then compares only the load-insensitive metrics: probe CPU
  seconds, bytes consed per commit and owner CPU per POST.
- **probe**: `store STORE probe 1000` through the image's launcher, on a
  scale-profile store (`--max-transactions 1048576 --max-article-octets
  2048`, commit-regression's init). It records wall time, the child's
  rusage CPU, and the reported commit and reopen seconds.
- **alloc**: `fnn-command-probe` in-process in the image's core, on a fresh
  store with the same N, bracketed by `sb-ext:get-bytes-consed`. The figure
  covers the commit loop and the reopen, divided by N. The bare core ends
  the probe's JSON write on a TYPE-ERROR after the reopen; it is recorded as
  `alloc_condition`, and any other condition yields no figure. The served
  POST/ARTICLE path reports no allocation in a stock image, since the heap
  hook needs a profiling build. It is not measured.
- **served**: `operator run` gets 100 POSTs of 2,048 octets on one
  connection (median, p95, owner CPU from /proc), then 100 ARTICLEs on a
  fresh connection. After that the owner is stopped and started, giving
  reopen = seconds to LISTENING, plus a STAT of the last article.
- **checkpoint**: a development-profile store (T = K = 128, A = 32,768)
  receives POSTs of 31,744 octets (A less 1 KiB, because Path,
  Injection-Date and Injection-Info must also fit under A). The loop stops
  when the owner publishes, which happens at suffix K/2 = 64. The gate
  reads `CHECKPOINT auto sequence= suffix= octets= ms=` from its stderr. It
  published at sequence 64 on all three images.
- **box load**: /proc/stat busy fraction and loadavg every 5 s, plus a second
  quiet sample at the end (`quiet_after`).

Floors (absolute slack per metric, next to the 25%) are 0.5 s or 0.5 ms for
the probe figures, 256 KiB for bytes per commit, 1 ms for medians, 2 ms for
p95s and 50 ms for the publication. They come from the spread between
repetitions of one image (commit-regression's POST p95: 2.2 to 4.0 ms on
image (c); this table: ARTICLE p95 2.6 to 5.1 ms). A 2x step fails at every
floor.

## The baseline and the named-cause override

- planning/throughput-baseline.json is written by `throughput_gate.py
  baseline --release RUN --dev RUN`. Each metric's value is the smaller of
  the release's figure and dev's, and both are kept beside it. It works as
  a ratchet like proof_cost's: an improvement lowers the value at the next
  write, and raising a value is refused without `--allow-regression`. A dev
  figure over the release's limit is printed and needs a cause. This
  baseline comes from the rep-2 runs (bbf52159 at 07:55, 0d211647 at 08:05),
  both `quiet: false`.
- planning/throughput-causes.json has `{"revision": ">=7 hex", "reason": ...}`
  rows. A row excuses the run of that revision only. It is empty today.
- `check` picks the run by nearest ancestry. Among runs of the same
  revision it prefers a quiet one, then the newest. It ignores refused runs
  and smoke runs (a quiet threshold other than the default). It prints
  STALE when host/ or books/ changed after the measured revision, and still
  passes, because producing a run is the merge step's job.
- tests/test_throughput_gate.py has 8 tests, all passing. They cover the
  tolerance and floor, a synthetic 20x failure, a missing metric, the cause
  override (only for its revision), nearest-ancestor selection with STALE,
  the under-load restriction with quiet preferred, refused and smoke runs
  not counting as evidence, and IMPROVED. It is in `make tooling-test`.
  `make check-lane` is green in this worktree (log in the lane scratch).

## The merge step (for NIGHT.md; the deputy adopts it)

NIGHT.md is untracked and outside this worktree, so it is not edited here.
The text to insert after step 6 ("Merge certification"):

> 6b. **Throughput gate, one run per merge batch** that changed host/ or
> books/ (PKT-408). After the batch's last merge, at its head REV:
> `tools/hbox_native.sh --name throughput-gate --label img-REV12 REV
> tests.test_throughput_gate` (run_in_background; it builds the developer
> image, and the module is pure Python), then
> `python3 tools/throughput_gate.py run --image
> /tank/fn/scratch/throughput-gate/native-img-REV12/tree/build/fn-host-developer
> --revision REV --label batch` (run_in_background; it waits up to 30 min
> for a quiet box, then takes about 5 min). Exit 3 means the box never went
> quiet. Rerun with `--under-load --wait-quiet 120`, which gates only CPU
> and allocation; say so in the commit. Commit the fetched
> planning/evidence/throughput/REV12-batch-*.json and run
> `python3 tools/throughput_gate.py check`.
> - Pass: push the batch.
> - REGRESSION: **do not push the batch**. Find the merge by running the gate
>   on each merge commit of the batch (one image each; the JSONs are
>   committed). Then either fix it (a lane, with the metric and the two
>   JSONs named), or name it in planning/throughput-causes.json with the
>   reason and the owning lane, and push.
> - IMPROVED: after the push, rewrite the baseline (`throughput_gate.py
>   baseline --release <the release run> --dev <this run>`) in its own commit.
> - A refused run is not a pass. Never lower a figure by hand, and never
>   raise one without `--allow-regression` and a named cause.
> - After each qualification, run the gate on the qualified image and write
>   the baseline with it as `--release`.

**Decision for ember (packet).** Trace: NIGHT.md step 5 says to push after
EVERY merge (ember's rule), but this brief says a regressing batch is not
pushed. Constraint: the gate's run costs about 5 min on hbox plus the image
build (about 3 min with a warm cert cache), and up to 30 min more waiting
for quiet. Default written above: merges that touch host/ or books/ are held
locally until the batch's run passes; all others push immediately.
Rejected alternative: push each merge, then revert on a regression. It
keeps ember's rule literally, but a regressed dev is live for the other
lanes in the meantime, which is the failure this gate exists to stop.
Affected: NIGHT.md steps 5 and 6b. Without the decision, the gate still
works as a post-push check; the deputy just learns of a regression after
pushing.

## Assurance chain and scope

This lane changes no ACL2 or host code, and it claims no theorem. It is a
measurement over the host-called entry points:

- `store probe`: `fnn-command-probe`, host/native/io.lisp, through
  `fnn-bridge-prepare`, `fnn-publish` and `fnn-finish`.
- the served POST/ARTICLE: `operator run`'s owner.
- the owner's publication: `fnn-owner-maybe-publish` ->
  `fnn-owner-publish-captured`, host/native/owner.lisp.

No step names a relation or a keystone. What is observed is identical
behaviour: probe `status passed` on every image, reopen STAT 223, and the
publication at sequence 64.

The scope is what it cannot see:
- ZFS or fsync-bound regressions (tmpfs by design; the per-commit fsync
  count is commit-regression's syscalls.sh);
- N-dependence past 1000 and 100;
- the scale and default profiles' K/2 at 2,048 (PKT-300 (b) is the
  qualification's);
- the production image (developer only, because probe is a developer verb);
- allocation on the served path.

Classification of what was found:
- **environment**: the box is never quiet while a wave runs. Strict quiet
  was not reached between 07:17 and 07:39 (4 to 6 busy units), which is why
  `--under-load` exists.
- **harness**: the brief's `probe 1000 article`. The verb takes COUNT only,
  and its payload is always the profile's maximum of `x`.

## Not done

- **A quiet run of any image.** Every JSON here is `quiet: false`, so the
  baseline's wall-clock figures (probe wall, POST/ARTICLE latencies,
  reopen, publication) are recorded but have never gated anything. The
  first quiet run replaces them: `check` prefers a quiet run of a revision.
- **Bytes consed on POST and ARTICLE.** A stock image has no heap hook.
- **The NIGHT.md edit.** The text is above.

## Files and artifacts

- tools/throughput_gate.py, tests/test_throughput_gate.py, Makefile (`check`,
  `tooling-test`), planning/throughput-baseline.json,
  planning/throughput-causes.json.
- planning/evidence/throughput/: six JSONs
  (bbf52159dcab-release-bbf52159-20260926T0739/0755,
  483987b19f66-dev-483987b1-20260926T0744/0800,
  0d21164752bb-dev-head-20260926T0749/0805).
- Images: bbf52159 at /tank/fn/gates/qual-bbf52159-20260925/build/fn-host-developer
  (the same core as build/images/bbf52159dcab.../, e6640102...); 483987b1
  at commit-regression's native-img-483987b1 (d650e2f0...); 0d211647 built
  here with tools/hbox_native.sh, /tank/fn/scratch/throughput-gate/native-0d21164752bb
  (core 25913fc3ae2730a980a130505a0cb2b52889b27b89e5fcd26ace8a8affbfd820;
  tests.test_proof_cost OK on it).

## Correction (deputy 4, 2026-09-26 14:05 UTC): the T-X run and PKT-477 (1)

Commit 75eb0dc2's message says the batch T-X run at bb7b2994 showed "no
regression". It did not under the rule of the day: its JSON
(`bb7b29942a84-batch-tx-under-load-20260926T133815Z.json`) has
`post_owner_cpu_ms` 3.5 against 2.6 allowed; the JSON's `passed` is the
probe's own status, not the check's verdict. The bisect on the same batch
(the three `*-bisect-{T,U,V}-under-load-*.json` files) read 2.2 ms on every
image with `probe_bytes_consed_per_commit` identical (1,406,383) across T, U
and V and 1,406,384 at bb7b2994, against the baseline's 1,651,892: the
deterministic counter improved, the CPU figure moved with the box (0.36
busy, three qualification units). PKT-477 (1), the coordinator's decision:
a run under load compares the deterministic counters only
(`DETERMINISTIC` in tools/throughput_gate.py; CPU and wall figures are
re-measured at the next quiet window, which `check` prefers). No cause row
was written for bb7b2994: the counter that decides the push held.
