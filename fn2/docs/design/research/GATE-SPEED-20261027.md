# Gate speed measurements — 2026-10-27

Stage 1 only. Source of truth: `cut/breaking` in `build/lanes/cut/breaking`; timings below come from existing laptop and hbox logs. No hbox jobs were started.

## 1. Gate construction and phase boundaries

`tools/cut_gate.sh` unconditionally launches `tools/hbox_native.sh` with `--images production,developer,dtn,dtn-developer,reference,developer-stripped` (`tools/cut_gate.sh:97-101`). It then runs, in order: hbox image acquisition/build plus selected native modules; hbox gauntlet cells F2S/F4/F6/W13; a production-core copy to persvati; three repetitions of the six default time cells; table generation and the final guardrail verdict (`tools/cut_gate.sh:119-180`, `:273-284`). `--no-gauntlet` skips the whole second block, including the time rows.

The hbox half has its own timed steps: `sbcl-check`; static world/interface/host checks; certificate install; incremental certify plan and certify; box wire generation; default and DTN artifact acquisition/validation; host translation checks; image library build; six `image-*` saves; image stamping; then module setup/execution (`tools/hbox_native.sh:926-1087`, `:1133-1144`). The existing logs must supply the durations of phases whose plan commands are not wrapped in `step` (notably the certify-plan line).

Current `hbox_native.sh` is not structurally serial: for more than one non-`prof` image it chooses `pstep` for every `image-*` step and emits `pwait`, unless `FN_NATIVE_SERIAL_IMAGES=1`; shared foreign libraries are built once first (`tools/hbox_native.sh:1046-1081`). The measured runs below determine whether that path was active and how the saves overlapped.

## 2. Which modules use which image

Scope: the 39 G5 modules in `build/cut-gate/cut-m1close-d187817f6/modules.txt` at d187817f6. The mapping below combines direct selector reads in the tests, `tools/native_env.py`'s transitive helper analysis, and the actual fallback in `tests/native_harness.py`. A `--families` selection can add modules and therefore add image requirements; this is not a claim about every `test_native_*` module.

| Images launched | Modules |
|---|---|
| production only | `test_native_control_across_peers`, `test_native_feed_fair_round`, `test_native_feed_idle`, `test_native_feed_temporary`, `test_native_friends_feed`, `test_native_peer_hostile_feed`, `test_native_peer_misbehaving`, `test_native_peering` |
| developer only | `test_native_bp_carry_abandon`, `test_native_bp_pin_carry`, `test_native_feed_reply_cold`, `test_native_peer_rows_growth` |
| production + developer | `test_native_feed_tls_read`, `test_native_feed_tls_ready`, `test_native_peer_by_name`, `test_native_peer_catchup`, `test_native_peer_invite`, `test_native_peer_pull`, `test_native_protected_peering` |
| no saved native image | `test_native_bp_app_clock`, `test_native_bp_app_tally`, `test_native_bp_channel_admission`, `test_native_bp_heap_source`, `test_native_bp_listener_off_lock`, `test_native_bp_node_admission_lock`, `test_native_bp_open_custody`, `test_native_bp_owner_startup_source`, `test_native_bp_prefix_probe_source`, `test_native_bp_profile`, `test_native_bp_resume`, `test_native_bp_send_boundary`, `test_native_bp_transit_identity`, `test_native_bpapp_acquisition`, `test_native_catchup_spool_source`, `test_native_feed_credential`, `test_native_peer_round_driver`, `test_native_pull_append`, `test_native_pull_journal_registry`, `test_native_tcpcl_acquisition` |

Thus the default G5 gate needs only **production and developer**. No selected module launches dtn, reference, or developer-stripped. The gauntlet and time rows also use production (`tools/cut_gate.sh:122-128`, `:135-181`).

The selector rules are centralized at `tools/native_env.py:112-124`: `FN_NATIVE_HOST` selects production; `FN_NATIVE_DEVELOPER_HOST` and `FN_NATIVE_CRASH_HOST` select developer; `FN_NATIVE_REFERENCE_HOST` selects reference; `FN_NATIVE_DEVELOPER_STRIPPED_HOST` selects developer-stripped; the BP/contact variables select dtn then dtn-developer, except the two named BP fault-injection modules that prefer dtn-developer. `FN_NATIVE_DTN_HOST` selects dtn and `FN_NATIVE_DTN_DEVELOPER_HOST` selects dtn-developer.

`native_env.py images --images ''` currently derives `developer,production,dtn-developer` for these 39 modules. That is conservative, not minimal: it adds both variables read by `Acl2Session` in one planning pass. The implementation first uses `FN_NATIVE_DEVELOPER_HOST` and falls back to `FN_NATIVE_DTN_DEVELOPER_HOST` only when the developer launcher is not executable (`tests/native_harness.py:819-824`). Since the gate supplies developer, dtn-developer is not used. Only `test_native_feed_tls_read`, `test_native_feed_tls_ready`, `test_native_peer_by_name`, and `test_native_protected_peering` reach that fallback through `Acl2Session`; none reads a DTN-only selector in its own test file.

The planner already has the intended derivation entry point, `needed_images` (`tools/native_env.py:443-460`), but `cut_gate.sh` bypasses it by passing all six names explicitly. Correct selective building should use the planner and fix the `Acl2Session` alternative-scope over-approximation rather than hard-code this G5 list.

## 3. One complete gate, measured: `cut-wave2-40015b3f8`

This is the latest complete six-cell, three-repetition gate in the breaking worktree's existing logs. It requested four images (production, developer, dtn, dtn-developer), not the six now hard-coded. Times in the hbox table are UTC; outer-gate times are laptop local time. Durations are differences between the recorded timestamps, rounded to the log's one-second resolution. hbox load average at run start was 11.90/11.93/11.09.

**Outer phases (`build/cut-gate/cut-wave2-40015b3f8/gate.log`)**

| Phase | Timestamps | Wall |
|---|---:|---:|
| gate launch through hbox natives complete | 00:59:22–01:30:55 | **31m33s** |
| hbox gauntlet F2S/F4/F6/W13 | 01:30:55–01:34:39 | **3m44s** |
| copy production image hbox → persvati and verify core hash | 01:34:39–01:35:23 | **44s** |
| install/wait/copy three reps of six time cells; make table | 01:35:23–01:48:54 | **13m31s** |
| guardrail + summary | 01:48:54–01:48:55 | **1s** |
| **whole gate** | 00:59:22–01:48:55 | **49m33s** |

**Hbox image and native phases (`native-cut-wave2-40015b3f8/run.log`)**

| Step | Start (UTC) | Wall |
|---|---:|---:|
| launch/ship/preflight before `sbcl-check` (local gate start to hbox start) | 04:59:22–04:59:48 | 26s |
| `sbcl-check` | 04:59:48 | 1s |
| `world-check` | 04:59:49 | 4s |
| `interfaces-check` | 04:59:53 | 47s |
| `host-books` | 05:00:40 | 18s |
| `attach-order` | 05:00:58 | 6s |
| `one-world` | 05:01:04 | 28s |
| **certificate install + incremental certify plan** | 05:01:32 | **6m05s** |
| certify (0 books pending of 1,298) | 05:07:37 | 13s |
| `box-wire` | 05:07:50 | 1s |
| default `acquire` | 05:07:51 | 32s |
| default `validate` | 05:08:23 | 11s |
| `host-forward` | 05:08:34 | 11s |
| default `host-ld` | 05:08:45 | 1m00s |
| DTN `acquire` | 05:09:45 | 30s |
| DTN `validate` | 05:10:15 | 11s |
| DTN `host-ld` | 05:10:26 | 19s |
| shared `image-libs` | 05:10:45 | 4s |
| **all four image saves, parallel** | 05:10:49–05:12:07 | **1m18s** |
| `stamp-images` + `box-stamp` | 05:12:07–05:12:09 | 2s |
| 39 native modules, serial (`modules: 39, 1 at a time`) | 05:12:09–05:30:44 | **18m35s** |

Per-image walls all begin at 05:10:49Z: production 1m18s (exit 05:12:07), developer 1m18s (05:12:07), dtn 45s (05:11:34), dtn-developer 45s (05:11:34). The image phase is the maximum, 1m18s, not their 3m36s sum.

The 31m33s outer hbox phase consists of 26s launch/ship, 12m21s from `sbcl-check` to module start, 18m35s live modules, and about 11s of attach/status/log collection. The dominant pre-image interval is install + certify planning (6m05s), even with zero books left to certify; natives are the largest single outer phase.

`certify_plan` prints its pending-book line directly to `run.log` but is not a `step`; `install` is a step. Consequently the existing timestamp format cannot split the 6m05s combined interval into install versus plan. `tools/gate_walls.py:8-14`, `:95-104` explicitly defines ordinary step wall as start-to-next-step-start. Separating them requires adding a timed plan step in Stage 2 or new instrumentation; no such timestamp exists in this log.

## 4. Six-image M1-close run and serial/parallel verdict

**The six builds run concurrently, not serially.** In `native-cut-m1close2-d187817f6/run.log`, all six have the same 20:41:24Z start and the annotation `(parallel, at most 6)`. `hbox_native.sh` emits `pstep` + `pwait` whenever more than one non-prof image is requested, unless `FN_NATIVE_SERIAL_IMAGES=1` (`tools/hbox_native.sh:1046-1081`). No serial override appears in the gate launch log.

| M1-close2 phase | Start (UTC) | Wall |
|---|---:|---:|
| `sbcl-check` | 20:06:52 | 1s |
| `world-check` | 20:06:53 | <1s (next step same second) |
| `interfaces-check` | 20:06:53 | 1s |
| `host-books` | 20:06:54 | 1s |
| `attach-order` | 20:06:55 | <1s |
| `one-world` | 20:06:55 | 4s |
| **install + certify plan (9 pending of 1,298)** | 20:06:59 | **15m07s** |
| certify | 20:22:06 | 1m48s |
| `box-wire` | 20:23:54 | 7s |
| default `acquire` | 20:24:01 | **7m57s** |
| default `validate` | 20:31:58 | 12s |
| `host-forward` | 20:32:10 | 55s |
| default `host-ld` | 20:33:05 | 54s |
| DTN `acquire` | 20:33:59 | **6m15s** |
| DTN `validate` | 20:40:14 | 45s |
| DTN `host-ld` | 20:40:59 | 20s |
| shared `image-libs` | 20:41:19 | 5s |
| **all six image saves, parallel** | 20:41:24–20:44:14 | **2m50s** |
| `stamp-images` + `box-stamp` | 20:44:14–20:44:23 | 9s |
| **pre-native total from `sbcl-check`** | 20:06:52–20:44:23 | **37m31s** |

Each image's measured wall:

| Image | Start–exit (UTC) | Wall |
|---|---:|---:|
| production | 20:41:24–20:44:07 | 2m43s |
| developer | 20:41:24–20:44:07 | 2m43s |
| dtn | 20:41:24–20:44:12 | 2m48s |
| dtn-developer | 20:41:24–20:44:14 | 2m50s |
| reference | 20:41:24–20:44:07 | 2m43s |
| developer-stripped | 20:41:24–20:44:07 | 2m43s |

Their sum is 16m30s; actual parallel occupancy is 2m50s. The gate start was 16:03:47 local (20:03:47Z), so launch/ship took 3m05s and images were stamped 40m34s after gate launch. The run log had reached serial native modules at 20:44:23Z but had no module or run completion when read; this is not a completed whole-gate baseline.

The earlier `cut-m1close-d187817f6` attempt at the same revision did **not** spend 34 minutes building images: it built none. It spent 12m45s in install + certify planning, then certification failed after about 16m56s; the outer gate went red at 33m55s (`certify exit 1`, 10 books pending, including the generated image worlds and `host/interfaces`). hbox load at start was 32.33/22.72/18.45, and the certify planner reported background load 75.8.

A second complete four-image run, `cut-m1b-reads-31d9e8c95`, gives the load-sensitive comparison: install + plan 3m00s, default + DTN acquire 1m23s, four parallel images 2m25s (production 2m18s, developer 2m25s, dtn 1m40s, dtn-developer 1m45s), serial natives 20m00s, and whole gate 47m19s. Its hbox start load was 1.80/3.15/2.87. These runs are not controlled benchmarks; use the timestamped phases, not a load-adjusted performance model.

**Stage 1 timing conclusion:** the often-quoted ~34-minute “image build” is the pre-native gate, not six serial SBCL saves. In the six-image run the saves were 2m50s of 37m31s pre-native work. The large addressable costs are repeated certificate installation/planning and artifact acquisition; image-selection work still matters because the default G5 selection needs only two of the six images, but parallelizing the saves is already present.

## 5. What `--reuse-image` does today

`cut_gate.sh` initializes `REUSE=` and passes `--reuse-image` only when the caller explicitly supplies it (`tools/cut_gate.sh:43`, `:53`, `:98-100`). There is no automatic lookup or content comparison. This is why a normal gate rebuilds: reuse is an opt-in path to one operator-named earlier run.

Mechanically, `hbox_native.sh --reuse-image RUN` sets `BUILD=0` (`tools/hbox_native.sh:550-556`). That skips the entire world-check/install/certify/acquire/host-check/image-build block. After `sbcl-check`, it runs `image_set.py link-run RUN TREE IMAGE...` (`:1098-1102`), then box stamping, image identity, and the modules. `link-run`:

- requires the earlier run's `run.log` source line and each requested launcher + core;
- requires an affirmative `paged` catalog;
- symlinks the launchers, cores, optional world-deps, and `lib/` into the new tree;
- writes the earlier source to `build/REUSED_SOURCE` (`tools/image_set.py:359-403`).

It does **not** compare the current revision, closure, host bytes, certificates, toolchain, or image hashes with the earlier run. Unlike published `--image-set` linking, `link-run` does not verify a `SHA256SUMS` manifest. The caller alone decides whether old images are coherent with the new test tree. The gate only checks that `tree/build/fn-host.core` exists (`tools/cut_gate.sh:103-108`), so it does not add a coherence check either.

There is also a current breadth restriction: `--reuse-image` and `--image-set` accept only production, developer, dtn, and dtn-developer; reference and developer-stripped are refused at launch (`tools/hbox_native.sh:645-650`). Simply adding `--reuse-image` to today's six-image gate therefore fails before linking. Selectively requesting production + developer avoids that mismatch; extending the mechanism is the alternative.

**Measured reuse:** `cut-base-49b470a99` explicitly reused `/tank/fn/scratch/integrate-devctl-20261015/native-devctl-49b470a991f9`. Its `image-reuse` step linked production, developer, and dtn in the same second as `sbcl-check` (23:12:51Z), and modules began at 23:12:57Z: **6 seconds from SBCL check to native start**, with zero certification, acquisition, or saves. The serial natives still took **19m07s** (23:12:57–23:32:04); outer gate launch-to-natives was 20m41s. The current test tree was 6f1d52e1 while the linked images recorded source 49b470a99, demonstrating that source-incoherent reuse is permitted as a deliberate baseline control, not prevented by the tool.

The separate `--image-set SHA` path verifies published artifact hashes and the recorded commit source (`tools/image_set.py:297-345`), but its key is the commit SHA, not image-input content. It is not what `--reuse-image` does.

A content-keyed implementation has an in-tree model: `tools/extract/world.py digest` hashes generated world files, followed host files, every included book's `.cert` and `.fasl`, the ACL2 launcher, and qualified toolchain identity (`tools/extract/world.py:382-411`). `tools/extract/world_image.sh:22-47` caches a `save-exec` world by that digest and checks a source/variant/launcher/core binding on hits. Native-image reuse needs the same content discipline, extended to the native build scripts and raw host files, image profile/world flavor, foreign-library inputs, and launcher-rewriting inputs; a git SHA alone unnecessarily invalidates unchanged images.

Finally, image reuse alone cannot make the **whole existing gate** a three-minute operation: the measured serial natives were 18–20 minutes, the gauntlet about 4 minutes, and the time rows 9.5–13.5 minutes. The Stage 2 image work addresses the pre-native interval; native verdict reuse/selection and the load rows are separate outer-loop costs.

## 6. Incremental build from a saved base core

**Stage 1 does not clear the proposed “load changed books into the last saved full base core” optimization as sound.** It would either leave ACL2's logical world unchanged or attempt to redefine an already-loaded book; neither reconstructs the clean-build world. A saved base can be sound only as a **dependency-prefix checkpoint** that excludes every changed book and every book depending on it, followed by replay of the remaining world and host build.

The current order is:

1. Include the generated `books/image-world` umbrella first. It holds the entire default image closure, through a TLS-bounded chain of three generated links (`host/native/build.lisp:12-25`; `tools/extract/world.py:50-80`). DTN uses the analogous `image-world-dtn` (`host/native/build-dtn.lisp:25-38`).
2. Record the include-book count and disable the compiler. Subsequent explicit includes are logically redundant; the host `:program` files are `ld`'d in a specified order, followed by `host/interfaces.lisp`, raw-dispatch verdicts, and `def-carried-host-check` (`host/native/build.lisp:365-479`).
3. Assert `FN_IMAGE_WORLD_CLOSED`: no include after the umbrella may add a book (`:475-483`). The world generator explicitly orders pure books before host books because replaying host wrapper definitions in the other order is refused (`tools/extract/world.py:178-193`).
4. Open the sole native-host trust tag, enter raw mode, install and then seal raw dispatch, and load raw host files in their dependency order (`host/native/build.lisp:485-680`). Several forms between loads initialize libraries, select the build-time profile/version, and install lifecycle wrappers; this is not an unordered set of independent files.
5. Retire the trust tag, emit readiness/stack/TLS markers, leave LP, optionally strip the world and prover state, and `save-exec` with `:return-from-lp '(fn-native-entry state)` (`:681-714`). DTN has the same terminal shape (`host/native/build-dtn.lisp:501-534`).

A restarted production or developer **host** core therefore enters `fn-native-entry`; it is not a checkpoint waiting for more build forms. Production/developer-stripped cores additionally remove prover/session state (`host/native/strip-world.lisp:246-276`, `:337-352`). Even a full-world developer/reference core has already run the host `ld`s, installed/sealed raw dispatch, and loaded the raw host. It is not a valid base for replacing books.

The generated umbrella links are not incremental checkpoints. Their boundaries minimize TLS use from measured per-include costs, not dependency stability (`tools/extract/world.py:50-80`, `:201-229`). A book or ordering change can move link boundaries. Retaining `image-world-part-1` while replacing a later part is valid only if the retained part is outside the changed book's dependent closure; the current generator provides no such stability guarantee.

What the host order *does* permit is a deliberately constructed checkpoint **before the first host `ld`**, over a certified dependency prefix, with a resume script that loads the remaining books in clean-build order and then reruns all host checks, all host `ld`s, the complete raw block, stripping, launcher rewriting, and validation. Changing an early book invalidates its dependents even when their own source bytes are unchanged, so “unchanged files in the base” is not a sufficient cache criterion. The correctness control must be equivalence to a from-scratch build at the same content key, not merely a successful save.

There is already proof that a saved ACL2 `save-exec` image can be restarted for more input when it is saved with an LP entry: `tools/extract/world_image.sh:32-47` saves the extraction world + ACL2-mode host wrappers, and `tools/extract/core.sh:81-103` later feeds that cached image export forms. That mechanism reuses an **identical content-keyed world**; it never loads changed books into an old world. It is evidence for content-keyed whole-world/image caching, not for incremental replacement.

**Recommendation for Stage 2:** implement selective images and content-keyed whole-image reuse first; do not implement naive incremental loading into the previous native host core. Treat dependency-prefix resume as a separate design needing a stable world generator, a resume-entry core, invalidation of all dependents, and a clean-build equivalence witness.
