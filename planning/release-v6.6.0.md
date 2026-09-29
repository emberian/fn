# Release v6.6.0: the cut checklist

**Status: NOT CUT. v6.6.0 is blocked on the fundamentals below.** ember
(relayed by the coordinator, 2026-09-27 ~02:30 UTC, of the release then
numbered 6.7.0): "no v6.7.0 for friends
yet; the fundamentals come first." The release machinery is in the tree:
the version file, `fn --version`, the tarball names, this checklist,
`tools/cut_release.sh` and `tools/changelog.py`. A cut is when every
fundamental is MET and every gate is green on one commit.

Written from the tree at dev `87dff3138` (2026-09-27, lane release-v6.7.0).
Nothing here was run except the cut script's `--dry-run` (the lane record's
section "Dry run"). This is a checklist, not a qualification record: the
cut writes that record (section 4).

## 1. The version

- **Release order is a sequence, never a number (D37).** ember,
  2026-09-27 ~22:10 UTC: "i'd like to make our first version v6.6.0 ....
  and then we'll work our way up to a v6.6.5 release, then we'll have a
  v6.7.x series, and then the final release (whenever that is) of the
  software would be v6.6.6. and then each new release would add another
  .6. that's my intention." So: 6.6.0, 6.6.1, ..., 6.6.5; then 6.7.0,
  6.7.1, ... (open-ended); then 6.6.6, the final release; then 6.6.6.6,
  6.6.6.6.6, ... (one more `.6` per release). The list and its rules are
  planning/release-sequence.json; `tools/release_sequence.py` (`position`,
  `next`, `is_next`, `cut-check`) is the only thing that decides order,
  and no tool compares version numbers. This supersedes the earlier rule
  here ("every release is 6.7.N, N rises by one").
- **The first cut is 6.6.0.** This checklist was release-v6.7.0.md; it
  was renamed when D37 made 6.6.0 the first release, and its fundamentals
  and gates are unchanged.
- **The live node's `fn 6.7.0`.** The public fsn1 node prints
  `fn 6.7.0 (18a7137a3)`: it runs a rehearsal build from before D37, when
  `VERSION` read 6.7.0. That is not a cut and no `v6.7.0` tag exists; the
  first cut is 6.6.0, and under D37 6.7.0 comes after 6.6.5.
- The version lives in ONE place: the file `VERSION` at the root of the
  tree, one line (`6.6.0`).
  - The image build reads it: host/native/build.lisp, build-dtn.lisp and
    build-store-test.lisp call `fnn-select-release-version`
    (host/native/io.lisp), which serializes it into the saved image and
    stops the build on a missing or malformed file.
  - The packaging reads it: packaging/release-tarball.sh names the tarball
    `fn-VERSION-PLATFORM.tar.gz` (`fn-6.6.0-linux-x86_64.tar.gz`) from the `VERSION` in the `git archive` of
    REV. It refuses unless the staged `bin/fn --version` prints exactly
    `fn VERSION (REV12)`. The `--frozen` form (tests, friends harness) names
    its package `fn-VERSION+REV12-PLATFORM.tar.gz`, which is not a release.
- `fn --version` prints `fn VERSION (REV12)`: the version built into the image
  and the first twelve digits of the source revision recorded beside the
  core (`libexec/fn/source-revision`). An image that records no revision
  refuses, exit 1, as before (PKT-403).
- The cut commit is tagged **`vVERSION`** by the coordinator at the cut, never
  by a lane. Gate 01 refuses a VERSION whose tag exists on another commit or
  that is not the sequence's next entry after the newest `v*` tag. After a
  cut, the next change to `VERSION` (`python3 tools/release_sequence.py next
  VERSION`; in the 6.7.x series, `--final` names 6.6.6 instead) is the first
  commit of the next release.
- `CHANGELOG.md` is generated (`python3 tools/changelog.py --write`). It has
  one line per merged lane since the previous release's tag (the newest `v*`
  tag before VERSION in the sequence; for 6.6.0, which has none, since the
  Fable mandate), grouped by capability,
  and lists reverted merges apart. Its range ends at the last lane merge, so
  the cut commit regenerates it byte for byte (gate 04). Never edit it by
  hand.

## 2. Blocking fundamentals

Each row is BLOCKING. Gate 03 reads this table from REV and is red unless
every row says `MET` and its evidence path exists at REV. The evidence is a
committed record with the measurement, its scope and the image it ran on.
A row changes to MET only in the commit that adds that evidence.

<!-- fundamentals -->
| ID | fundamental | bar (measurable) | status | evidence |
| --- | --- | --- | --- | --- |
| F1 | The records freeze landed (PKT-293, PKT-635; records-freeze) | Retained heap about 1 octet per stored payload octet plus stated per-record metadata (today 16 B/octet: the history and the acceptance node hold octet lists). A reopen of the 1,000-post store judged by F8's split: its anonymous peak (RssAnon, sampled through the reopen) at most 64 MiB; virtual size, accountable physical memory and working set reported (row J2, ruling of 2026-09-29). | OPEN | planning/evidence/fundamentals-2026-09-28-d5ab87aecc40/F1.md |
| F2 | The served machine reads through the catalog (catalog-slice step 7b/8) | GROUP/LISTGROUP/ARTICLE/OVER read v/fn-cat; R established at every host entry; the index lookups per served command measured on the served path, with the before/after at N = 10,000 | OPEN | planning/evidence/fundamentals-2026-09-28-d5ab87aecc40/F2.md |
| F3 | The storage log (storage-log-design, PKT-636) | Under 1 fsync per POST at the named rate: 8 concurrent posters, the POST/s they reach stated per disk (row J2, ruling of 2026-09-29); the gap to the design's 0.125 at batch 8 is finding F3-G below, stated in every record and never read as a pass; POST/s on the public node's edge disk stated (node-disk's mount) | OPEN | planning/evidence/fundamentals-2026-09-28-d5ab87aecc40/F3.md |
| F4 | The owner scheduler (owner-scheduler, PKT-321) | Under the mixed hour (3 tight-loop readers, 1 POST every 0.5 s), every control request answered within its 10 s client deadline, control p99 stated; F4-R: every served read and status/health answered within D_R = 3 x Q_max, in the hour and under an injected 30 s disk stall; F4-W: every POST answered within H + Q_max (planning/design-time-model-2026-09-27.md section 4; mutating control its named exception, tail stated) | OPEN | planning/evidence/fundamentals-2026-09-28-d5ab87aecc40/F4.md |
| F5 | Connection multiplexing (connection-multiplexing) | Memory per idle connection measured and stated (today one worker thread and its stack per connection, PKT-605); the capacity check against memory | MET | planning/evidence/fundamentals-2026-09-28-d5ab87aecc40/F5.md |
| F6 | Opens at scale | The owner's open of a 20,000- and a 40,000-article store in seconds, not tens of seconds (the coordinator reads the bar as under 10 s each; ember may set it), peak RSS stated; checkpoint-pipeline measured 28.8 s and 5.15 GB at 40,000 x 2 KiB | OPEN | planning/evidence/fundamentals-2026-09-28-d5ab87aecc40/F6.md |
| F7 | BP 10 MiB validated (SCN-077, PKT-630 (7); bp-fragments-10mib) | tests.test_bp_fragment_node_native wholly OK on dtn and dtn-developer, SCN-077 delivering a 10 MiB ADU into a Store profiled for it | MET | planning/evidence/fundamentals-2026-09-28-d5ab87aecc40/F7.md |
| F8 | The memory target (D35) | The split (adopted 2026-09-28): after 1,000 posts on the release image, accountable physical memory (the anonymous pages) at most 256 MiB and working set (VmRSS) at most 128 MiB, virtual address space reported; AND a reopen of that store under 256 MB. The old "under 256 MB reserved" verdict is recorded beside them, visibly unmet, and judges nothing | OPEN | planning/evidence/fundamentals-2026-09-28-d5ab87aecc40/F8.md |
<!-- end fundamentals -->

Findings (measured, not bars; each stays in every record until it closes):

- **F3-G, the batching gap** (row J2): 0.31 to 0.47 fsyncs per POST at 8
  posters (117 to 225 POST/s on the edge; 0.469 NVMe and 0.344 ZFS on
  d5ab87aecc40) against the storage-log design's 0.125 at batch 8, 2.5 to
  3.8 times the design. F3's bar (under 1) is met by these figures; the
  design's figure is not, and `tools/fundamentals.py` prints the gap as
  `FINDING F3-G ... OPEN` in F3.md until a record shows it at or under
  `--f3-design-per-post`. Owner: the storage log (group commit's batch
  formation under 8 posters).

Measured on ONE image, dev `33bbfae9c` (hbox, 2026-09-27 16:14Z to 17:22Z,
load 17 to 39, rows pinned to cores 20 to 23; lane fundamentals-scoreboard;
the common conditions in planning/evidence/fundamentals-2026-09-27/README.md):

- **F1 MET.** The retained heap is 1.0 to 1.3 B per payload octet, plus
  3.6 KB per record after a reopen (9.5 KB while posting). At 2 KiB that is
  3.0 B per octet in all. The 1,000-post reopen on the production image is
  60.2 MiB RSS, with a high-water mark of 109.3 MiB.
- **F2 OPEN.** OVER 1-2000 takes 372 to 386 ms and ARTICLE 1.1 to 1.2 ms at
  N = 10,000. Two things are missing:
  - R at every host entry: lane sca-join.
  - A per-command lookup count: unowned.

  No before image opens today's store.
- **F3 OPEN.** Clause 1 is met: 0.30 fsync per POST on NVMe and 0.34 on ZFS
  at 8 posters. POST/s is 257 on NVMe and 36 on tank. The edge disk's POST/s
  is unmeasured (PKT-751, no access), and unowned.
- **F4 OPEN.** All 284 of 284 control requests were answered within 10 s,
  the maximum being 8.0 s. The control p99 is 6.1 s. The read maximum is
  10.35 s, and no work-quantum bound is defined. ember is to name the bound.
- **F5 MET.** An idle connection costs 7.7 to 9.2 KiB, with 9 threads at
  1,000 connections. The capacity check refuses at start on both images.
- **F6 OPEN.** 20k opens in 7.9 to 8.1 s. 40k opens in 16.2 s from a fresh
  checkpoint and 22.3 s from the fixture's own checkpoint. Peak RSS is
  850 MiB at 20k and 1.19 to 1.70 GiB at 40k. The 40k open is over the 10 s
  reading and unowned.
- **F7 OPEN.** SCN-077 passes on dtn, dtn-developer and developer. The module
  is 7/7 on dtn-developer but 6/7 on dtn: its rotation test needs a
  developer-only cut. ember is to decide the reading. Under "SCN-077 on dtn,
  the module on dtn-developer", this evidence meets it.
- **F8 OPEN.** The reservation is 672 MB empty and 1,407 MB after 1k, against
  a bar of 256 MB; that belongs to lane reservation-figure. In use after 1k is
  114.1 MiB RSS (high-water mark 142.2 MiB). The reopen floor is 138 MB.
- **F8 bar "the small profile fits 1.5 GB": UNMET** (lane heap-bounds, row B2,
  model; recorded as ember's F8 ruling recorded the reserved verdict). With
  the records' term derived from the profile's limits the small preset's
  first run reserves 1,872 MB on the release image (1,906 MB on the
  image-floor core; 1,263 MB with the 12 KiB constant, which long headers
  exceeded), so a 1,500 MB budget (a 2 GiB machine after the system's share,
  OpenBSD's 1,536M login class) refuses it by name. The tests take the budget
  from the figure (tests.test_native_image_floor's small_budget); the way
  down is B9 (the reservation as a base and a credited pool).

## 2b. The prerelease convergence checklist (runs ONCE, before the cut)

ember (2026-09-28 18:15Z): "we're spending a LOT of time doing work that we
only need to do once, during the prerelease convergence checklist." During
development the batch runs, per merge, only the union cite of the affected
roots, `make check` and the natives the lane named (GREEN is two coordinates,
planning/how-we-work.md rule 7). Everything below runs once, in this order,
on one frozen candidate REV; a red returns the candidate to development and
the checklist restarts at the first row whose inputs changed (unchanged
evidence is reused; a green is never transferred to changed bytes). Times
are rough, from 2026-09-28's runs.

| # | what | tool | pass bar | box | rough time |
| --- | --- | --- | --- | --- | --- |
| 1 | Freeze: every change that alters store bytes has landed, including the one-format rename to `fn-store-1` (lane one-format: no legacy formats, no migration code; fresh deploys) | git; `tools/fixtures.py rebuild --image build/fn-host-developer --rev REV` on a hbox_native tree of REV | every registered fixture rebuilt at REV in `fn-store-1`, including the scale-curve fixture at capacity 300,000 (tools/scale_curve.py's; 1k-100k built in 18.8 s) (`tools/fixtures.py check --rev REV` clean); nothing format-9/10 left in tests | hbox | 1 h (fixtures) |
| 2 | BOOK GREEN at REV | union cite of every root split hbox/persvati (`tools/farm.py`), `tools/green_check.py --strict` and `--profile default --strict`, `tools/remote_check.sh hbox --target check --install-certs`, `tools/resource_contract.py --check --strict` (the resource contract's release form: every book a row of docs/resource-contract.md cites is green at its current digest) | green_check owes nothing; make check every step green; the resource contract owes nothing | both | 1-2 h cold, minutes warm |
| 3 | The quiet 2-job D26 measurement and the AGGREGATE budget (GPT-6 review 2026-09-28) | `tools/farm.py --all --jobs 2` on a quiet persvati (no other run on the box), then `tools/proof_cost.py --write-baseline --near 5` and `tools/proof_cost.py --write-aggregate` (the aggregate: prover-steps sum over every root-closure book and the heaviest include chain by steps; refused partial, refused over the recorded figure's tolerance without `--allow-regression`) | no book over 10 s at 2 jobs; no near-5 row's steps over +10%; the aggregate recorded (total 2-job certification seconds, the critical path, the high-fan-out interface books' cost) and not above the previous convergence's by more than the stated tolerance (proposed 10%; ember sets it) | persvati | 2-3 h |
| 4 | The OpenBSD guest certifies the default closure | orfbld on hbox (FIX-FORWARDS "THE OPENBSD GUEST CERT"; the cut's gate 13 later builds the tarball in cutbld) | `or-cert.sh` CERTIFY EXIT 0, every book passed | hbox (VM) | 10-15 min |
| 5 | NATIVE GREEN: the full native set on REV's six images | `tools/hbox_native.sh --images developer,production,dtn,dtn-developer,reference,developer-stripped REV <every tests.test_native_* module>` with the format and open-depth fixtures' env (open_depth at 100k) | every module OK; each per-test skip listed with its reason (section 3's notes); a red is classified, never re-expected | hbox | 1.5 h |
| 6 | The fail-closed extraction gate | `make extract-check` (lane extract-gate's tools/extract/gate.py, on dev since e5e9b2a22) | PASS by the fail-closed gate (tools/extract/gate.py: every child status checked, expected-case manifests, exactly-once vectors, zero vectors fail, undeclared blockers fail): build, transcripts, probes, the store differential, the per-function vectors with 0 disagreeing | hbox | 30 min |
| 6b | The extraction's declared blocker ACL2::FN-SIG-VERIFY (tools/extract/declared-blockers.json): ACCEPTED for the read-only extracted build (constrained, no attachment there, fails by name); a WRITABLE extracted build must first bind it (FFI to the same ML-DSA library the images use) | extract-gate's manifest; the binding's own differential | read-only: listed and failing by name; writable: bound, with a differential against the image | hbox | with row 6 |
| 7 | The v0 protocol-conformance rows | `tests.test_native_conformance` plus the owners [the row table](evidence/python-diet-2-2026-09-28/v0-row-owners.md) names (test_native_peering, test_native_protected_peering, tools/inn_lab.py, test_native_reader_clients, tests/interop_nntplib.py); tools/v0_matrix.py was retired by python-diet T2b once every exercised row had one | every exercised row's owner OK in row 5's run or its lab; every planned row still named with its owner; 0 unexplained not-exercised rows | hbox | with row 5 (+ the INN lab) |
| 8 | GPT-6's integrated crash campaign: a pinned old reader, new accepted writes, a snapshot publication, cache pressure and eviction, a delayed page read or durability completion, a crash, recovery -- in ONE scenario, with swapped equal-count snapshots and refused-by-name old-format evidence | to build (extend `tools/power_loss.py`; the owning lane names the tool here) | accepted history stays accepted; damage is never ordinary absence; uncertainty is never retroactively refusal; no live or fallback root loses a page | hbox | 2 h (est.) |
| 9 | Fundamentals F1-F8 with the ADOPTED bars | `tools/fundamentals.py run --tree TREE --revision REV --write` (plus the F8/F4 bars below as its parameters) | section 2's rows, with **F8 split**: virtual address space (reported), accountable physical memory <= 256 MiB, working set <= 128 MiB under a named small profile and active-request mix; the old reserved-memory verdict recorded, unmet. **F4**: cached health/inspection p99 <= 250 ms, and <= 1 s under the injected disk stall; warm reads <= 1 s; cold reads a declared dependency timeout of 5 s; D = 5 s; H = 30 s + <= 1 s notification slack (planning/design-time-model-2026-09-27.md says H = 60 s: adopting 30 s is a default change, made there first) | hbox (quiet) | 70 min |
| 10 | Scale by curve, plus ONE held-out 1M run | `tools/scale_curve.py` (1k, 2k, 5k, 10k, 25k, 50k, 100k per served command, open, checkpoint, export/import, status/obligations; standard and transition-forcing probes, five-model fits with threshold/ambiguity flags; the standard set at all 7 N takes about 147 s); then ONE held-out 1M run predicted from the fit before it runs | every curve's fit and range stated; the 1M measurement inside the fit's stated band (GPT-6: across resize thresholds, with a bounded cache) before 1M is advertised | hbox | 30 min curves + 1-2 h the 1M run |
| 10b | Diagnose `store reclaim --dry-run`: superlinear on the curve (485 s at 100k; lane scale-curve) | tools/scale_curve.py's reclaim probe, then the owning lane's fix | linear or better on the 1k-100k curve, or the cause named and scoped in section 6 | hbox | TBD |
| 11 | Qualify the quiet candidate: the cut's gates 01-17 (section 3) | `tools/cut_release.sh --rev REV` from a detached worktree (section 4) | `VERDICT GREEN`; planning/evidence/qual-vVERSION-DATE.md written from it | hbox, quiet | 4-6 h |
| 12 | The tag | gate 17's line (`git tag -a vVERSION ...`) | ember's go | local | minutes |

## 3. The gates, in order

`tools/cut_release.sh` runs gates 01 to 17 in this order and stops at the
first red. It writes `build/cut/vVERSION-REV12/verdict.txt`, whose last line
is `VERDICT GREEN ...` or `VERDICT RED at NN NAME`, and one log per gate.
Run it from a clean checkout at REV (a `git worktree add --detach`), never
from the shared ~/dev/fn. `--dry-run` runs the read-only local gates and
prints every other gate's commands and checks the box preconditions it can
(the glibc-floor runtime, the OpenBSD build VM provisioned and stopped,
`sudo -n`). `--from N` resumes at gate N; `--to N` stops after gate N
(`VERDICT PARTIAL`: one gate run for real, never a cut).

| # | gate | green when | where |
| --- | --- | --- | --- |
| 01 | version | `VERSION` at REV is the next entry of the release sequence (D37) after the newest `v*` tag by sequence position, or 6.6.0 when there is none (`tools/release_sequence.py cut-check`; no numeric comparison); the tag `vVERSION` is free or already at REV; this checklist exists as planning/release-vVERSION.md | local |
| 02 | tree | HEAD is REV with no tracked change | local |
| 03 | fundamentals | every row of section 2 is MET with its evidence at REV | local |
| 04 | changelog | `CHANGELOG.md` at REV is what `tools/changelog.py --rev REV` writes, twice alike, and what it writes regenerates byte for byte at a scratch commit of it onto REV (`git commit-tree`: no ref moves) | local |
| 05 | closure certified at the cut | `tools/green_check.py --strict` (every book green at its current digest in a committed manifest) and `--profile default --strict` (the image's closure). The batch cite that certified REV's closure is the manifest this reads. | local |
| 06 | make check | the registries, the current view, proof cost and the throughput comparison, as `make check` runs them | local |
| 07 | docs_check | `tools/docs_check.py --check`: every command the docs name exists with the grammar the docs give | local |
| 08 | runpath check (static) | `tools/runpath_check.py`: every process site in host/ listed, no Python in the shipped packaging | local |
| 09 | the six images; every native module | `tools/hbox_native.sh --images developer,production,dtn,dtn-developer,reference,developer-stripped REV` builds fn-host, fn-host-developer, fn-host-dtn, fn-host-dtn-developer and tests.test_native_image_differential's pair (fn-host-reference, the production image with its full world; fn-host-developer-stripped) from `git archive REV`, then runs every `tests/test_*native*.py` and `tests/test_bp_*.py` module except the `exclude` lines of planning/release-native-gate.txt, with its `env` opt-ins; status 0: no module FAILED, none wholly SKIPPED | hbox |
| 10 | the throughput gate, quiet | `tools/throughput_gate.py run` on REV's developer image with `--wait-quiet 1800` (never `--under-load`: a cut is measured on a quiet box), then `check` within planning/throughput-baseline.json | hbox |
| 11 | the hostile campaign | `tools/hostile_campaign.py` on REV's developer image, every family (malformed, header, body, connection, pipelining, transit, tls, bp); exit 0 = no defect | hbox |
| 12 | the Linux tarball (glibc floor) | packaging/release-tarball.sh `--runtime-from` the glibc-floor runtime builds `fn-VERSION-linux-x86_64.tar.gz` from the archive (its own green_check, acquire, validate, production image, runpath `--tree`, `--version` check); `runpath_check.py --tarball`; installed fresh from the tarball and SHA256SUMS with `install.sh --no-service`; tests.test_release_tarball `OK` with no skip (the format-7 fixture given); `fn --version` in a bare `debian:12` container with only libssl3 prints `fn VERSION (REV12)` | hbox + docker |
| 13 | the OpenBSD tarball | in the cut's OpenBSD 7.9 build VM on hbox (`--openbsd-vm`, default `cutbld`: a tools/power_loss_openbsd.py configuration whose root is a copy of openbsd-release-fixes' orfbld; provisioning in the header of tools/cut_release.sh): REV's default closure certified in the guest, `fn-VERSION-openbsd-amd64.tar.gz` built by packaging/release-tarball.sh, runpath `--tarball`, installed fresh, tests.test_release_tarball `OK`, the installed `fn --version` under root's login limits and under both stock login classes (datasize 4096M `daemon`, 1536M `default`) prints `fn VERSION (REV12)`, and `tools/openbsd_smoke.sh` (init, run, a POST and its ARTICLE, kill -9, recover, the article again) passes under 4096M; the VM is booted and shut down by the gate, and a VM already running (someone's) is red, never taken | hbox (the VM) |
| 14 | the power-loss cut list on the release image | tools/power_loss.py's reproduction (planning/evidence/power-loss-2026-09-26.md section 7): rig, workload of 600 POSTs, index, the cut plan `init=8,post=150,checkpoint=60,compact=60,reclaim=50,control=8` with recovery cut at 0.2, on the INSTALLED tarball's launcher; the summary's `all` row: 0 violations, controls caught > 0, 0 harness errors | hbox (sudo -n for the block layer) |
| 15 | the friends session from the tarball | tests.test_native_friends_feed with `FN_FRIEND_FN` the fresh install's `bin/fn` (the friend) and the developer image as the author: `OK` with no skip | hbox |
| 16 | extract-check | `make extract-check` (lane extract-2's N-version differential) when REV's Makefile has the target; `SKIPPED` (never green) until it does | local |
| 17 | the tag | prints `git tag -a vVERSION -m 'fn VERSION' REV` for the coordinator; the script creates no tag | local |

What the gates do not decide (the cut's qualification record, section 4):

- **Per-test skips inside an OK module** are not evidence. The notes
  `tools/native_env.py plan` prints today name them: FN_INN_SRC (the INN
  lab), FN_DTN7_REPO (dtn7-rs interop), FN_BUILD_OPENSSL_PREFIX
  (frozen_relocation). The record lists each one as unexercised with its
  reason.
- **The per-image split.** hbox_native.sh gives each module the variables
  it reads for the six images. A module that picks one image runs on that
  image only. The qualification of 69046a76 ran the non-BP modules on prod
  and dev and the BP modules on dtn and dtndev by hand (`env.sh`,
  PKT-499 (d)). The record says which modules ran on which image.
- **A red is classified, never re-expected.** Implementation,
  model/refinement, harness, environment, or unexercised capability, as in
  planning/evidence/qual-69046a76-2026-09-26.md section 4. The cut's module
  table is the evidence.
- **The load gates** that are measurements, not pass/fail (the mixed hour,
  the opens at scale, the memory target) are the fundamentals, measured once
  on the cut's image and cited from section 2.

## 4. The cut, step by step (the coordinator)

1. Every fundamental MET on dev (section 2), each with its record:
   `python3 tools/fundamentals.py run --image TREE --revision REV` on a
   hbox_native tree of the candidate (the four images) measures F1 to F8
   with the scoreboard's methods, writes
   planning/evidence/fundamentals-DATE-REV12/ and updates the table's rows
   it measured (MET only when that evidence meets the bar; the bars that
   need a reading are its parameters, printed in the record).
2. `python3 tools/changelog.py --write`; commit CHANGELOG.md (and VERSION if
   it changes) on dev. That commit is REV.
3. `git worktree add --detach build/cut-VERSION REV`; there, `tools/cut_release.sh
   --dry-run --rev REV`, then `tools/cut_release.sh --rev REV` (start it in
   the background; gates 09 to 15 take hours).
4. On `VERDICT GREEN`: write planning/evidence/qual-vVERSION-DATE.md from the
   verdict, the logs and the module table (the shape of
   qual-69046a76-2026-09-26.md). Commit the throughput JSON gate 10 wrote
   under planning/evidence/throughput/, the verdict and the tarballs'
   SHA256SUMS.
5. Tag `vVERSION` at REV (gate 17's line); push the tag.
6. The release notes (section 7), final, beside the tarballs. ember's go
   before any friend is sent a link.

## 5. Deploy notes (fresh install per D34)

A deploy is a reinstall from the release: stop, `store export`, remove,
install, `init` or `store import`, start. No upgrade path exists (D34).
For a node installed from v6.6.0:

1. **The node secret.** Before the first start, `fn store ROOT node-secret
   create`: the node-written Cancel-Lock keys come from it (lane
   newsreader-cancel-3; **not on dev at 87dff3138**, READY FOR BATCH).
   `store export` excludes `keys/`, so an imported store needs it too, and
   the secret must survive a reinstall to keep old locks cancellable
   (PKT-618's decision: STORE/keys/node-secret.key).
2. **Imported stores: rebind the file system once.** A store made before the
   store identity record needs `fn store ROOT rebind-filesystem` once after
   the import (lane store-mount-identity; **not on dev at 87dff3138**).
3. **Barriers on.** The store's file system honours fsync with write
   barriers: ext4 with its default barriers (never `barrier=0` or
   `nobarrier`), ZFS `sync=standard`, no volatile cache that ignores flushes
   (docs/operator.md "Storage requirements"). fn does not yet refuse a
   detectable bad mount at start (PKT-648, a decision for ember).
4. **MODE STREAM.** Peers are fed with `MODE STREAM` and `CHECK`/`TAKETHIS`
   when their peer record's streaming flag is `true` (transit-streaming,
   transit-pipelining: two articles in one read are both answered,
   PKT-600 fixed). A peer that answers `MODE STREAM` with anything but 203
   is stopped for the owner's run with a log line: re-add it with `false`.
5. **Infrastructure (ember's hand step).** The Ashburn anchor's
   systemd-networkd enable; the public node's certificate by Let's Encrypt
   (D36); `tls reload` after each renewal (no restart).

## 6. Known limitations (for the release notes)

State each in the notes with its packet. Reread the backlog's open packets
(planning/backlog-2026-09-25.md) at the cut: a fundamental that lands
removes its line here.

Capacity and cost:

- **Memory per stored octet.** The history and the acceptance node hold
  articles as octet lists: about 16 octets of heap per stored payload octet
  until the records freeze (F1; PKT-293, PKT-635). A node's heap is sized
  from its profile (heap-from-profile), not its data.
- **fsyncs per commit.** Every POST is its own durable transaction: 7
  barriers per commit. On hbox's ZFS pool with no SLOG a POST's median is
  446 ms (planning/performance-2026-09-26.md row 3), until the storage log
  and group commit (F3; PKT-636).
- **Control requests under a mixed load.** Under saturating reads, control
  socket requests can wait past their 10 s deadline and answer uncertain
  (PKT-321), until the scheduler (F4). Correctness held in the measured hour.
- **Per-connection memory.** One thread per connection (PKT-605); the
  connection cap is not checked against memory (F5).
- **Open time at scale** (F6), **the reopen's memory** (F8).
- **Linear reader folds.** HDR/XHDR, GROUP, NEXT, LAST and NEWNEWS walk the
  archive per command (NNTP gap inventory R8). OVER and reads by number are
  indexed.

Protocol and peering:

- **BP: a 10 MiB ADU is not yet validated** end to end (SCN-077, PKT-630
  (7); F7). **ION's TCPCL is not supported**: fn speaks TCPCLv4 only
  (specs/tcpcl.md section 6, "§4.3 version fallback to TCPCLv3 | deferred"),
  and ION 4.2.0 speaks TCPCLv3 only, so no exchange is possible (bp-cursors;
  PKT-650 names a spurious MSG_REJECT after the version mismatch). By
  decision, not by defect.
- **INN pushing into a login-required, TLS-only node** is not possible
  (innfeed sends AUTHINFO without TLS; PKT-611). An INN peer must be a
  source-address peer. Peers named by a dynamic IP break at renumbering
  (PKT-613).
- **TLS handshakes are not metered** by the exposure limits (the handshake
  precedes the exposure open; PKT-639), and handshake refusals go to stderr,
  not the service log (PKT-640).
- **Not served:** COMPRESS DEFLATE, AUTHINFO SASL (never, until a client
  needs SCRAM), LIST MODERATORS, moderated groups (P3), XGTITLE/XROVER/
  XTHREAD/XINDEX, newgroup/rmgroup by control article (D29). Distribution is
  ignored (P4); refused offers are not remembered (T1).
- **Header ceilings.** 64 header fields, 256 header lines and 16,384 header
  octets per article (books/article.lisp; P9, D27 debt): friends' posts fit,
  some relayed Usenet articles do not.
- **Own-post cancel from an ordinary newsreader** (Cancel-Lock, RFC 8315)
  and Injection-Info with a posting account arrive with newsreader-cancel-3
  and usenet-headers-3 (READY, not on dev at 87dff3138). Until then a
  cancel from tin files but withdraws nothing unless it is a verified signed
  cancel with a grant.
- **An anonymous read-only level** is not separate from open posting
  (PKT-405).

Operation:

- **Fresh deploys only** (D34): no in-place upgrade. A reinstall keeps data
  through `store export`/`store import`. A checkpoint file from another
  release is refused and the store replays in full.
- **An interrupted `operator CONFIG init` strands the operator**
  (`recover` faults, `init` refuses STORE-EXISTS; PKT-647): remove the
  half-made store and init again.
- **No expiry.** Articles are released only by the operator's explicit rule
  (D03); there is no per-group expiry (O3).
- **Platforms.** Linux x86-64 with glibc 2.36 or later and the system libssl
  (OpenSSL 3.0 or later); OpenBSD 7.9 amd64 with LibreSSL, from a file system
  mounted `wxallowed` (/usr/local by default). No macOS release.

## 7. Release notes (DRAFT; not for friends until the cut)

> **fn 6.6.0** (draft)
>
> fn is a news server. You and your friends read and post with an ordinary
> newsreader (tin, slrn, Thunderbird) over TLS, and your node trades
> articles with your friends' nodes. Every decision it makes about an
> article, a login, a peer or its store is taken by code that is proved
> correct in ACL2 and ships inside the program.
>
> **What you get.** One file for your machine, `fn-6.6.0-linux-x86_64.tar.gz`
> (Debian 12, Ubuntu 24.04 or newer) or `fn-6.6.0-openbsd-amd64.tar.gz`
> (OpenBSD 7.9), with its own runtime inside. Nothing else to install but
> your system's TLS library. `sh fn/install.sh` puts it in `/opt/fn`
> (`/usr/local/fn`) and sets up the service; docs/install.md walks you from
> the download to a node your friends reach.
>
> **What it does.**
> - Serves newsgroups to readers over TLS, with logins; a friend joins with
>   an invitation code, no config edit and no restart.
> - Peers with other fn nodes (and with INN) over NNTP streaming, both push
>   and pull; a node behind NAT pulls.
> - Never loses a post it said yes to: an article is accepted only once it
>   is on disk, and power cuts at 1,281 points under a busy node lost
>   nothing acknowledged (with write barriers on).
> - Shows who wrote a signed post, what evidence carried it and what your
>   node knows about the key, as separate facts.
> - Tells you what is wrong: `fn operator CONFIG health` names one of eight
>   states with its own exit code.
> - Stays up when strangers probe it: per-address limits and named refusals.
>
> **What to know first.** Updating means reinstalling and importing your
> store (`store export`, then `store import`). Keep your disk's write
> barriers on. Large nodes need more memory than they should (about 16 bytes
> per stored byte today). Section 6 of the release checklist lists
> everything else we know is missing.
>
> `fn --version` prints `fn 6.6.0 (REV)`; the source is tagged `v6.6.0`.
