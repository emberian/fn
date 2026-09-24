# v0 audit: P10 and P11, re-verified at `6d3ed90b` (2026-09-24)

Scope: the "Exists" and "Missing" cells of P10 and P11 in
`planning/plan-2026-09-22-trajectory.md:137-138`, checked against the tree at
`6d3ed90b`, with the DONE definitions of T5, T12 and T16 (`:207`, `:215`,
`:219`). Tools run, all read-only: `tools/green_check.py --summary` and
`--table`, `tools/reach_check.py` (no flags), and
`tests.campaign.native_cuts.verify_native_cut_map()` as a static check. No
ACL2, farm or native runs.

Tree-wide facts used below:

- `green_check --summary`: 673 of 673 closure books green at their current
  digest, 0 RED. 70 greens have a dependency that has moved since their run.
  Every BP progress book (`bp-node-progress*`, `bp-node-debt*`, `bp-forward-*`,
  `bp-fnbs-forward-*`) is green from `certify-20260924T105922Z-3604838`
  (persvati) with "3 to 6 deps moved since". Green at a digest is not a
  certificate of the current closure.
- Host `1a9dd747` to `6d3ed90b`: `git diff --stat 1a9dd747 6d3ed90b -- host`
  is empty, so the `1a9dd747` image carries today's host code.
- `reach_check`: orphans in PRF-041 (4) and PRF-045 (2), listed below.

---

## P10: every process-death cut is a model crash point; campaign on the production image; durability qualified

### What the cell says exists, re-checked

**K1 to K4 (PRF-041).** Status `in-progress`, 34 events
(`planning/proofs.json`, PRF-041). `books/byte-store-keystones` is **green**
at digest `1443e5ee` (certify-20260924T102224Z-3270826, persvati), along with
`byte-store-scan`, `byte-store-relation` and `byte-store-program-invariants`.
The "red" in the Missing cell is out of date. Its progress note says the book
was red from `4857c648` until the identity/topic premise repair.

reach_check reports four PRF-041 events with no host-reached subject:
`fn-bs-crash-image-frontier-decodes-to-a-natural`,
`-namespace-is-contiguous`, `-reads-the-config` and
`fn-bs-store-crash-image-is-kernel-admissible` (`books/byte-store-scan.lisp`).
This follows from how the stack is built. The byte programs
(`fn-bs-frontier-program`, `fn-bs-record-program` and the rest, in
`books/byte-store-programs.lisp`) are models. No host line calls them.
`grep "'fn-bs-" host` finds only `fn-bs-pack-reclaim-plan`
(`host/native/checkpoint.lisp:164`). Under the rule that the theorem subject
is the function the host calls, the byte keystones therefore hold only
through a transcription argument, and that argument is not mechanised for
the native host:

- `tools/transcribe_check.py:1-35` compares syscall sequences against the
  Python host (`faults.at`, `ast`). Its `UNMODELLED_PATHS`
  (`:102-115`) names Python functions.
- For the native host, the only check is
  `tests/campaign/native_cuts.py:107-121` (`verify_native_cut_map`). It checks
  that each cut name is declared in `host/native/io.lisp`
  (`+fnn-post-model-cuts+` :1791, `+fnn-recovery-model-cuts+` :1746) and is a
  `:cut` of the named program. It also checks recovery order (`:124-146`).
  It does not compare the syscall sequence of `fnn-publish`
  (`host/native/io.lisp:1548-1596`) with `fn-bs-record-program`.

**`native_cuts.py` names a `fn-bs-*-program` coordinate per cut.** I ran
`verify_native_cut_map()` and it passes: 13 POST cuts and 7 RECOVERY cuts.

| Family | Cuts | Coordinate | Checked by |
| --- | --- | --- | --- |
| POST (`native_cuts.py:26-38`) | frontier-staged-durable, -replaced, -attempted, -durable, -reserved; record-staged-durable, -linked, -attempted, -durable, -completing, -staging-cleaned; finish-consumed, -durable | `fn-bs-frontier-program` / `fn-bs-record-program` / `fn-bs-finish-program` | name map + model names |
| RECOVERY (`:47-53`) | recover-replayed, recover-barrier-1..5, recovery-stage-unlinked | `fn-bs-recover-program`, then `fn-bs-recover-stage-cleanup-program` | name map + order |
| CHECKPOINT (`:60-69`) | candidate-file/-link/-directory, selection-file/-replace/-directory | **`fn-cpp-publication-step` / `fn-cpp-marker-step`**: phase machines in `books/checkpoint-publish.lisp`, not byte programs | only the hook text (`:148-159`) |
| CHECKPOINT | pack-reclaim-unlink, -directory | `fn-bs-pack-reclaim-program`/`-steps` in `books/byte-store-compaction-correspondence.lisp:32` | model names |

So 22 of 28 table cuts carry a `fn-bs-*` coordinate. The six checkpoint
cuts do not. `fn-bs-checkpoint-publish-program` and
`fn-bs-checkpoint-select-program` are defined in `byte-store-programs.lisp`,
but nothing names them: no theorem, test or cut.

**Process deaths the tree takes outside the table.** The host's developer
selector list (`host/native/io.lisp:2499-2518`, 34 names) includes kill or
pause cuts that `native_cuts.py` does not list:

- `FN_BP_NODE_TEST_PAUSE_AFTER_KIND_{FIVE,SEVEN,TEN}`,
  `_OUTBOX` and `_REPORT_OUTBOX` (`host/native/bp-node.lisp:184,338,373,414,515`;
  used by `tests/test_bp_node_native.py:581-738`).
- `FN_BP_APP_TEST_PAUSE_AFTER_DECISION` (`host/native/bp-app.lisp:176`).
- `FN_TCPCL_TEST_*` (`host/native/tcpcl.lisp:136`).
- `FN_NATIVE_OWNER_TEST_SIGTERM` (`host/native/owner.lisp:1672`).
- `FN_NATIVE_FEED_TEST_STOP_AFTER_SENT` (`host/native/feed-service.lisp:387`).
- `FN_APP_JOURNAL_TEST_FAIL_RELEASE_NAMESPACE` (`host/native/bp-obligation.lisp:56-59`).
- The two-Store join's command-boundary deaths.

The FNBS cuts have a byte model of their own. `books/bp-fnbs-byte-invariants.lisp`
has 12 theorems, including `fn-bpnf-actual-link-crash-is-absent-or-exact`
and `fn-bpnf-durable-cut-recovers-exact-record`. That model is not a
`fn-bs-*-program`, and no table maps a selector to it. The TCPCL, feed and
owner-SIGTERM cuts have no stated model coordinate. Under AGENTS.md ("A test
that kills the host at a boundary the model cannot express is a fidelity
defect"), each one is either an unmapped cut or a defect. Nothing in the
tree says which.

**K7 (four authority boundaries).** Exists in
`books/byte-store-fault-keystones.lisp` (`specs/crash-model-v2.md:2189`).
Green.

### What the cell says is missing, re-checked

**"The campaign has run in no image at the current cuts."** This is partly
out of date:

- `git diff --stat daa6c15e 6d3ed90b` shows that `native_cuts.py`,
  `test_native_crash_model.py`, `test_native_served_crash_model.py`,
  `model_images.py` and `byte-store-programs.lisp` are unchanged since
  `daa6c15e`.
- On the `daa6c15e` developer image,
  `test_all_native_post_process_death_cuts` passed. It uses the ACL2
  differential `model_images.ModelBridge` (`tests/test_native_crash_model.py:77-148`).
  Log: `planning/evidence/t2-native-daa6c15e-logs/test_native_crash_model.log`,
  6 tests OK.
- `test_five_served_recovery_barriers_are_distinct_model_cuts` also passed
  there (`…/test_native_served_crash_model.log`, 2 tests OK).
- Since then, `host/native/io.lisp` (+82 lines) and `host/native/owner.lisp`
  (+339 lines) have changed. The campaign did **not** run on `1a9dd747`: its
  record lists three cases only (`planning/evidence/native-cut-1a9dd747-2026-09-24.md:62-78`).
- The `da5fd8cb` operator campaign ran 16 cuts on the developer image and
  states that "the ACL2 differential against the byte model did not run"
  (`planning/evidence/campaign-da5fd8cb-2026-09-23.md:9-15`).

**"Passes on the production image."** This cannot be done as literally
written. The production image refuses every developer selector at start
(exit 5; `campaign-da5fd8cb…md:180-182,203-206`; gate at
`host/native/io.lisp:2436`). No cut can be selected on it. A production
claim therefore needs one of two things:

- an argument that the developer and production images share every book and
  every host write path, differing only in the selector gate; or
- an external-kill campaign against the production image (SIGKILL at
  syscall boundaries under `strace -e inject` or a stopped tracee, the way
  `tests/campaign/native_block_fault.py` stops at pair 10).

Neither exists.

**K0 general preservation.** Open. `fn-bs-program-step-preserves-relation`
is not defined anywhere in `books/`. What exists instead is bounded K0
slices:

- 183 `fn-bs-k0-*` theorems in `books/byte-store-record-provenance.lisp` and
  6 in `byte-store-relation.lisp`, all green.
- The pair-10 `fn-bs-k0-record-attempted-cut-establishes-relation`, the
  frontier EIO apply/drop/choice runs, and the retention record-directory
  EIO cut (`planning/evidence/k0-retention-record-directory-2026-09-24.md:1-24`).
- `specs/crash-model-v2.md:2182` lists what remains open: general syscall
  preservation, recovery establishment, retained-history composition,
  config-history refinement, existing/retry init, and the relation at every
  served call entry.

**K5.** Proved. The Missing cell is out of date here. The theorem, from
`books/byte-store-stable-prefix.lisp:23-31`:

```lisp
(defthm fn-bs-stable-prefix-retained-by-byte-crash
  (implies (and (fn-bs-store-relation bs ks) (fn-bs-crash-imagep bs image))
           (and (fn-sf-prefixp (fn-bs-durable-records bs)
                               (fn-bs-scan-records (fn-bs-scan-store image)))
                (<= (len (fn-bs-scan-records (fn-bs-scan-store image)))
                    (1+ (len (fn-bs-durable-records bs)))))))
```

Teeth: `tests/acl2/byte-store-stable-prefix-tests.lisp` has 3 must-fails,
covering the relation and crash-image hypotheses, and a second
`record-linked` witness. It is **not a registry event**: the name appears in
PRF-041's statement text but not in its `events`. Its subject is not
host-called.

**K8.** Proved. Also out of date in the Missing cell. The theorem is
`fn-bs-k8-issued-link-fence-crash-scans-exact-candidate`
(`books/byte-store-record-fence.lisp:568-577`). Under a related
`:record-attempted` state with a pending transactions op, every crash image
of `(fn-bs-fence-dir bs :transactions)` scans to
`(append (fn-sf-records ks) (list (fn-sf-record-candidate ks)))`. Teeth:
6 must-fails in `byte-store-record-fence-tests`. It is **not a registry
event**, and its subject is not host-called.

**K6.** Partial. It covers the actual P-RECORD file-fence and linked raw-frame
cuts (`fn-bs-k6-*`, 9 PRF-041 events; 63 must-fails in
`byte-store-record-provenance-tests`). Whole-list post-crash scanner
provenance is open (`specs/crash-model-v2.md:2189`).

**Platform profile (T16b).**
`planning/evidence/t16-private-publication-profile-2026-09-24.md` records
what was observed:

- ext4 on a tmpfs-backed loop device with private `dm-flakey`, on hbox.
- Three cases run on the `863c2141` developer image: record-dir EIO, record
  SIGKILL at pair 10, and a copied-backing "snapshot" that drops volatile
  writes. All three recovered with exit 0.
- `frontier-dir-eio` is "source-ready but unrun".

What the record says it does not claim: power loss, completed-barrier
survival, hbox **ZFS**, or A-DURABILITY / A-WRITE-ISOLATION.

`specs/failures.md:58-75` carries the profile as error-handling scope only.
T16(b) also requires "torn-write injection through the model's image
constructor applied to real files" and a run on a scratch pool. Neither
exists. The node's page does not carry the profile.

### Packet: P10

1. **Proof lane (Fable).** Close K0 over the served path, one keystone per
   program, not one universal statement:
   `(implies (and (fn-bs-store-relation bs ks) (fn-bs-<p>-inputp bs ks in)) (fn-bs-store-relation-at-every-pair (fn-bs-run bs (fn-bs-<p>-program in)) ks'))`
   for `<p>` ∈ frontier, record, finish and recover. The recover program
   also needs a call-entry establishment theorem. It should start from
   `fn-sn-open-observed`'s scanned image, so that the "related physical
   state at entry" premise is discharged, not assumed. Teeth: one
   must-fail per hypothesis per program, plus a reachable
   `frontier-replaced` witness (the known counterexample to unqualified K0,
   `crash-model-v2.md:2177`).
2. **Registry (root).** Add `fn-bs-stable-prefix-retained-by-byte-crash`
   (K5) and `fn-bs-k8-issued-link-fence-crash-scans-exact-candidate` (K8)
   as PRF-041 events through `tools/ledger.py --write`. Mark all byte-model
   events with the transcription caveat. reach_check will flag them, which
   is correct until item 3 lands.
3. **Host/tool lane (Opus).** Build a native transcription check: extend
   `transcribe_check.py`, or add a sibling, that reads the durable syscall
   sequence of `fnn-publish`, `fnn-recover`, the frontier writer and the
   checkpoint publisher in `host/native/io.lisp` and `checkpoint.lisp`, and
   compares it with `fn-bs-*-program`. This is the only thing that makes the
   byte keystones' subject "what the host calls".
4. **Host/test lane.** Re-point the six checkpoint cuts at
   `fn-bs-checkpoint-publish-program` and `fn-bs-checkpoint-select-program`,
   or prove `fn-cpp-*` refines them. Add a `BP_CUTS`/`OTHER_CUTS` table that
   maps every selector at `io.lisp:2499-2518` to a model coordinate
   (`fn-bpnf-byte-*` for FNBS, or a named program), or retire the selector.
   `verify_native_cut_map` then iterates the whole selector list.
5. **Native-run lane.** Run `test_native_crash_model` and
   `test_native_served_crash_model` (with the ACL2 bridge) on the current
   developer image (`1a9dd747` or later), across all 28 table cuts. Add a
   production external-kill run: SIGKILL at the POST/RECOVERY boundaries via
   a stopped tracee, as `native_block_fault.py` already does, with the
   `model_images` differential.
6. **Platform lane (Opus, hbox).** Run `frontier-dir-eio` on a matching
   image, then torn-write injection through `model_images` applied to real
   files (§5.1, §5.2), then one dm-flakey or ZFS scratch-pool run. Write the
   profile into `specs/failures.md` and the node page, quoting its scope.

**Obstruction:** "passes on the production image" cannot be met by
selectors, by design. It needs item 5's external-kill run or a proved
image-equivalence statement. General K0 is the long pole, at 6 to 10
lane-days (T16a).

| P10 | theorem: K1-K4, K5 (`fn-bs-stable-prefix-retained-by-byte-crash`), K8 (`fn-bs-k8-issued-link-fence-crash-scans-exact-candidate`), K7 proved; K6 partial; general K0 (`fn-bs-program-step-preserves-relation`) absent | subject: byte-model programs; no host line calls them; no native transcription check; 4 PRF-041 reach orphans | teeth: K5 3, K8 6, K6 63 must-fails; K5 and K8 not registry events | observed: 20 POST/RECOVERY cuts with differential passed on `daa6c15e` dev image; not rerun on `1a9dd747`; production cannot select cuts; T16 3 ext4/tmpfs cases, no ZFS/power | obstruction: general K0; production-image kill method; 6 checkpoint cuts and about 12 BP/TCPCL/owner selectors without a `fn-bs-*` coordinate |

---

## P11: bundles across an outage, only through the node machine

### The machine now

The Missing cell's "`fn-bpn-step` … none exists" is **out of date**.
`specs/bp-design.md:456-491` (§1.5.1) is superseded by
`specs/bp-node-machine.md`. Three layers exist and are green:

- `fn-bpn-step`: the base lifecycle machine (`books/bp-node-machine.lisp:965-971`,
  with `fn-bpn-trace` at `:973`).
- `fn-bpnf-step`: the foundation layer, covering held bundles, delivery,
  FNBS recovery and families (`books/bp-node-foundation.lisp:551`).
- `fn-bpnp-step`: the progress, forwarding and session layer
  (`books/bp-node-progress.lisp:1011-1086`).

**The host calls `fn-bpnp-step`, not `fn-bpn-step`.**
`fnn-bps-foundation-step` (`host/native/bp-service.lisp:167-176`) calls
`(fnn-core 'fn-bpnp-step …)`, and `fnn-bps-step` (`:178-179`) wraps its
event as `(:base e)`. Every native BP event goes through it:

- `:enqueue` (`bp-service.lisp:812-815`)
- `:clock` (`:776`)
- `:contact` (`:779`)
- `:forward-result` (`:430-431`)
- `:progress` (`host/native/bp-node.lisp:135-138`)
- `:session` (`:237-238`, `:258-260`)
- `:forward-result` (`:253-256`)
- `:expire-held` (`:366-368`)
- `:deliver-result` (`:176-177`)

The images include the guard book (`host/native/build.lisp:98`, `:219-220`).

Consequences of that routing:

- `fn-bpn-step`'s keystones hold of a function the host reaches only through
  `fn-bpnp-step` → `fn-bpnp-delegate-with-credit` → `fn-bpnf-step` →
  `(:base e)`. That covers `fn-bpn-step-preserves-lifecycle-invariant`
  (`bp-node-machine-authorization.lisp:737`, whose comment "dispatcher
  called by fnn-bps-step" is stale), `fn-bpn-step-cl-send-is-authorized-by-durable-attempt-record`
  (`:802`), `fn-bpn-step-emits-no-release` (`bp-node-machine.lisp:997`) and
  `-from-actual-effects` (`bp-node-machine-invariants.lisp:1242`).
- The only bridge is `fn-bpnf-base-step-is-fn-bpn-step`
  (`bp-node-foundation.lisp:675-682`). It covers the **state** only, not the
  effects. It requires `(not (fn-bpnf-issued st))`, and it is about
  `fn-bpnf-step`, not `fn-bpnp-step`. No theorem equates `fn-bpnp-step` on
  `(:base e)` with `fn-bpnf-step`.
- PRF-046's `pending_subject` reads "The native host directly calls
  fn-bpn-step". That is false at `6d3ed90b`. **PRF-046 has no `events`
  key**, and `planning/proof-events.json` has 0 PRF-046 entries. So none of
  the machine theorems is a registry event.

Theorems whose subject is the called `fn-bpnp-step`, all green:

- `fn-bpnp-step-preserves-guard-premises` (`bp-node-progress-premises.lisp:556-561`):
  `(implies (and (fn-bpnp-step-guard-premisesp st) (fn-bpnp-host-eventp event)) (fn-bpnp-step-guard-premisesp (fn-bpnf-answer-state (fn-bpnp-step st event))))`.
  Teeth: 5 must-fails in `bp-node-progress-premises-tests`.
  Siblings at `:578-596`.
- `fn-bpnp-step-progress-preserves-held` (`bp-node-progress-selection-invariants.lisp:194`)
  and `fn-bpnp-step-progress-issued-unchanged-or-pending-dispatch` (`:220`).
  For a `:progress` event, the held list is unchanged, and `issued` is
  either unchanged or a fresh `:dispatch :pending` operation. Teeth are in
  `bp-node-machine-teeth-tests` (6 must-fails in total).
- `fn-bpnp-oldest-eligible-skips-blocked-older` (`:9`), a selection helper.

`fn-bpnp-step` itself is `:verify-guards nil` in its definition
(`bp-node-progress.lisp:1016`). `bp-node-progress-guards` is green and
included in the image.

### T1..T6 of `specs/bp-design.md` §1.6 and `bp-node-machine.md` §5

None of the 12 names in `bp-design.md:499-580` exists. Of the 29 theorem
names in `bp-node-machine.md` §5 (`:1293-1860`), 5 exist:

- `fn-bpf-fragment-then-reassemble-is-identity` (`bp-fragment-invariants`)
- `fn-bpf-fragment-fast-is-fragment` and `fn-bpf-reassemble-fast-is-reassemble`
  (`bp-fragment-fast`)
- `fn-bpn-step-preserves-lifecycle-invariant` and
  `fn-bpn-trace-preserves-lifecycle-invariant`
  (`bp-node-machine-authorization`), both over the sibling `fn-bpn-step`

24 are missing. T1 (deliver names a validated whole live bundle), T2
(deletion only by expiry), T3 (`fn-bpn-expiry-deletion-is-decided-by-the-events-observation`,
`-uncertain-clock-deletes-nothing-by-expiry`), T5 (status report is only an
observation), T6 replay (`fn-bpn-durable-projection-is-replay-of-the-confirmed-journal`,
`-recovery-is-normalized-replay-…`, `-restart-reanchors-every-held-bundle`,
`-recovered-owed-work-has-a-continuation`) and the confinement pair
`fn-bpn-step-emits-no-release-and-no-receipt-prepare` do not exist over any
layer. **T1 to T6 are unproved** over the called subject.

Expiry has only helper-level keystones. M3,
`fn-bpn-find-expired-requires-expired-decision`
(`bp-node-machine.lisp:1016-1024`), is about a list scan. The refinement
`fn-bpnp-held-expiry-refines-a3` (`bp-node-progress-invariants.lisp:33`) is
an equation between two expiry functions. Staging exhaustion is a
`(:refused :capacity)` branch (`bp-node-progress.lisp:409-412`) plus the
debt-cover lemmas `fn-bpnd-*-preserves-cover` (`books/bp-node-debt.lisp`).
No theorem says every capacity refusal is the machine's decision over
`fn-bpnp-step`.

### Creation-sequence non-reuse (PRF-045)

PRF-045 is `in-progress` with 2 events, `fn-bpn-sf-step-preserves-nonreuse`
and `fn-bpn-sf-trace-preserves-safety`. reach_check flags both as orphans.
The model (`books/bp-sequence-fidelity.lisp:1-8`) cites
`host/native/bp.lisp:132-170`, but the allocator now sits at `:152`
(`fnn-bp-reserve-sequence`), so the citation has drifted. The bridges
`fn-bpn-sf-host-reserve-is-core-reserve` and `-host-recover-is-core-recover`
(`:278-311`) equate the model's own wrappers with
`fn-bpn-sequence-reserve`/`-recover`. The host calls those core functions
through `fn-bpn-host-sequence-recover`/`-reserve`, which are defined in the
uncertified `host/bp-node-host.lisp:83-104` and called at
`host/native/bp.lisp:168-174` and `bp-service.lisp:158`.

One host path is not in the model: `fn-bpn-host-existing-sequence`
(`host/bp-node-machine-host.lisp:21`, called at `bp-service.lisp:799-806`)
reuses a sequence for the same work, attempt and generation. That reuse is
intended for an idempotent retry, but no theorem shows it never returns a
sequence bound to a *different* bundle. The native test is
`test_death_after_durable_outbox_does_not_allocate_second_sequence`
(`tests/test_bp_node_native.py:634`). It is not recorded on `1a9dd747`.

### Scheduler

`books/scheduler` has **no native caller**. `host/scheduler-host.lisp` is
loaded only by `tools/scheduler.py:268` and `tools/labs.py:207`. Neither
native build file loads it (`host/native/build.lisp`,
`build-dtn.lisp`). What the native host now calls is a different
contact-window book, `books/bp-contact-service`
(`host/native/bp-contact.lisp` → `fn-bpsc-contact-decision`, in
`build.lisp:74,220`), keystone `fn-bpsc-open-needs-ready-peer-and-window`
(`planning/evidence/bp-contact-native-2026-09-23.md:3-22`).

`tools/scheduler.py:3-15` says it computes no decision: every choice is an
ACL2 call through `scheduler-host.lisp`, so it is not a decision twin by its
own statement. It does own a **durable decision log** in Python
(`:13-14`). That persistence boundary contradicts the "retire the Python
host" direction and T12(c)'s "`tools/scheduler.py` retired". Two contact
authorities now exist, `scheduler` (FNWF, Python-driven) and
`bp-contact-service` (FNBS, native), and no decision records which one is
authoritative.

### Receipt discharge and `fn-retain-release`

Something in the BP path now releases pins, which the cell said was absent.
The native path:

1. `fnn-bpnode-receipt-result` (`host/native/bp-node.lisp:73-99`) takes the
   node machine's delivered `:receipt` view.
2. It gates on `fn-owner-bp-receipt-trustedp`.
3. It calls `fnn-workflow-accept-receipt-octets` (`host/native/workflow.lisp:444-455`,
   profile `"trusted-local-observation-v0"` only).
4. That calls `fn-workflow-release-record` → `fn-bprl-release-record-for-journal`
   (`host/workflow-host.lisp:91-94`).
5. Then `fnn-bpo-canonical-release` (`host/native/bp-obligation.lisp:50-73`)
   → `fn-owner-workflow-store-release` (`host/bp-release-owner-host.lisp:50-62`),
   which emits a Store `:release` event that `fn-retain-release` applies.

The call happens in `books/bp-release.lisp:249`. Nothing in `fn-bpn*` or
`fn-bpnp*` calls it, which is the machine's intended confinement.

Theorems on this path: `fn-bprl-release-removes-the-forward-pin`
(`bp-release-invariants.lisp:467`),
`fn-bprl-no-receipt-no-release-no-peer-reliance` (`:882`) and
`fn-bprl-release-record-replays-decision-by-definition` (`:948`, a
by-definition bridge). Teeth: 7 must-fails in `bp-release-tests`. None is a
PRF-012 event: PRF-012 has 24 events and none is `fn-bprl-*`.

RET-004's typed evidence (issuer, nonce, incarnation) and receipt
authentication (D09) stay open. The only profile is a trusted local
observation.

"Never a carrier ACK" rests on `fn-bpn-step-emits-no-release`, which is
about the sibling `fn-bpn-step`. No confinement theorem over `fn-bpnp-step`
exists. Native evidence:
`test_request_retry_queues_distinct_receipt_carriers_and_releases_pin` and
`test_absent_bp_trust_refuses_receipt_release`
(`tests/test_bp_node_native.py:453,525`). Neither is recorded on
`1a9dd747`.

### Real BPA and the interrupted contact

- dtn7-rs: one exchange each way (`bp-dtn7-w11-2026-09-21.md`) and an
  ingress/exchange lab (`tests/bp-dtn7/README.md:19-40`). No contact
  interruption.
- The four-node lab is `mock_bpa` only, and its pinned-BPA path raises
  `NotImplementedError` by design (`tests/evidence/2026-09-21-four-node-lab.md:19,143`).
- ION: an FNWF attempt/observation binding in ACL2 only. "Native image
  execution, death/reopen testing and authenticated receipt return remain
  open" (`planning/handoff-2026-09-24-winddown.md:47-51`).
- Native fn-to-fn interruption exists as tests:
  `test_outage_restart_duplicate_and_conflict`,
  `test_wall_jump_after_interrupted_contact_retains_anchored_work`
  (`tests/test_bp_service_native.py:63,92`),
  `test_closed_window_interruption_and_anchored_wall_jump`
  (`tests/test_bp_contact_native.py:50`) and `test_bp_fragment_node_native`.
  **Only the fragment case and N03 ran on `1a9dd747`**
  (`native-cut-1a9dd747-2026-09-24.md:67-71`).
- No run exists with two DTN images plus a relay on one box: the v0.3 gate.

### The kind-8 liveness gap

`planning/evidence/bp-forwarding-2026-09-24.md:45-50`: process death after a
durable kind 8 and before kind 9 replays a `:forwarding` row. Recovery
clears the session and pending image, the selector never re-offers that row,
and its reserved debt is stranded. The host side matches: a transport
failure after a durable attempt raises `fnn-indeterminate`
(`host/native/bp-node.lisp:246-266`).

No theorem, test or label names this gap. A grep for
"strand|liveness|retry polic" over `books/bp-node*`, `bp-forward*` and the
BP tests finds only settlement comments. Among the spec theorems,
`fn-bpn-recovered-owed-work-has-a-continuation` (the T6 continuation) is
the statement that would expose it, and it does not exist.

A recovery settlement/retry policy must prove three things:

1. **Continuation.** After `:recover-fnbs`, every held row whose last
   durable record is kind 8 without kind 9 is either enabled for selection
   or waiting on a named wakeup (`blocked-with-wakeup`, §11.1 "T6
   re-anchoring").
2. **Duplicate control.** A re-offered attempt carries the same bundle
   identity: same source, creation timestamp and sequence, and the same
   wire bytes. The receiver's admission is then idempotent on that
   identity, as N13's handoff is. Formally: over `fn-bpnp-step` traces, the
   `:cl-send` effects for one held row all carry equal
   `fn-bpp-adu-key`/wire. A new kind 8 for that row appears only after a
   recovery-settled kind 9 of outcome `:unknown`, so that a possible earlier
   send is recorded as uncertain and never as refused.
3. **Debt.** The settlement kind 9 releases exactly the reserved debt
   (`fn-bpnd-*` cover preserved), so N05's inequality survives recovery.

### §11.1 counterexample suite: labels in `tests/acl2/bp-*tests.lisp`

| Label | Test with that label | State |
| --- | --- | --- |
| N03 | `bp-node-machine-teeth-tests.lisp:71,136` | positive witness; "PENDING N03 general two-tick theorem" (`:338`) |
| N04 | `bp-node-forwarding-teeth-tests.lisp:1` (executable fixtures over `fn-bpnp-step`, 2 must-fails), `bp-forward-live-tests.lisp:2`; machine-teeth `:339` PENDING | fixtures, no theorem |
| N05 | `bp-node-forwarding-teeth-tests.lisp:1`, `bp-node-debt-tests.lisp:3` ("remain open"), machine-teeth `:342` PENDING | partial |
| N09 | `bp-fragment-tests.lisp:193,229` | present |
| N01, N02, N06, N07, N08, N10-N18 | none | **missing (14)** |
| BP-R01 to BP-R24 | none in any `tests/acl2/*.lisp` | **missing (24)**; the labels exist only in specs and reviews |

Three of these carry an unkept obligation:

- **N06** is the FNBS physical publisher witness. The spec calls it open
  until executable.
- **N16** is rotation, slice E.
- **N18** is owner `:uncertain` forever.

### Packet: P11

1. **Proof lane (Fable): subject repair.** Prove
   `fn-bpnp-step-base-is-fn-bpnf-step`:
   `(implies (and (fn-bpnp-step-guard-premisesp st) (not (member (car e) '(:session :resume :forward-result :progress :persist-result)))) (equal (fn-bpnf-base (fn-bpnf-answer-state (fn-bpnp-step st (list :base e)))) (fn-bpn-answer-state (fn-bpn-step (fn-bpnf-base st) e))))`,
   together with its **effects** conjunct. Alternatively, restate M1 and
   the lifecycle keystone directly over `fn-bpnp-step`. Then fix PRF-046's
   `pending_subject` and give it an `events` list.
2. **Proof lane: confinement.** State
   `fn-bpnp-step-emits-no-release-and-no-receipt-prepare`:
   `(implies (and (fn-bpnp-step-guard-premisesp st) (fn-bpnp-host-eventp e)) (and (not (fn-bpn-effect-kind-memberp :release (fn-bpnf-answer-effects (fn-bpnp-step st e)))) (not (fn-bpn-effect-kind-memberp :receipt-prepare …))))`.
   Tooth: a mutant step that maps `:forward-result :accepted` to
   `:release`.
3. **Proof lanes: T1, T2, T3 and T5 over `fn-bpnp-step`** (§5 names,
   subject changed). T3 is the core:
   `(implies (and (fn-bpnp-step-guard-premisesp st) (member-equal (list :persist (list :bundle-deleted id :lifetime-expired)) effects)) (and (member (car e) '(:clock :expire-held :progress)) (equal (fn-clock-expiry-decision … (obs-of e)) :expired)))`.
   Teeth: the §11.1 T1, T2, T3 and T5 rows. Each first commit writes N01,
   N02, N08, N10, N11 and N12 as must-fails.
4. **Proof lane: T6 replay and continuation.**
   `fn-bpn-durable-projection-is-replay-of-the-confirmed-journal` over
   `fn-bpnf-recover-fnbs-step`, and
   `fn-bpn-recovered-owed-work-has-a-continuation` including kind-8 rows,
   which carries the duplicate-control and debt obligations above. Teeth:
   N06 (two byte crash cuts via `fn-bpnf-byte-*`), N07, N08, and a
   stranded-kind-8 must-fail against today's selector (it must fail today).
5. **Proof lane: PRF-045 join.** Move `fn-bpn-host-sequence-*` from
   `host/bp-node-host.lisp` into a certified book, so the bridge names the
   called function. Add `fn-bpn-host-existing-sequence-binds-one-bundle`.
   Fix the stale line cite.
6. **Host lane (Opus): scheduler.** Record which authority is canonical,
   `bp-contact-service` or `scheduler`. Either delete the
   `scheduler`/`tools/scheduler.py` path from v0 scope, or give it a native
   caller in `bp-service.lisp` and retire the Python decision log.
7. **Host/registry lane: receipts.** Add the `fn-bprl-*` events to PRF-012
   with teeth counts. Type RET-004 evidence. Keep the
   `trusted-local-observation-v0` scope sentence until D09 is decided.
8. **Test lane: labels.** Put BP-R01 to R24 and the 14 missing N labels
   into the owning test books as must-fails or pending forms, per §11.1.
   Slice E (N16) and B (N18, BP-R08, R09, R15, R20, R24) remain behaviour
   work.
9. **Native-run lane (hbox).** On one image past `1a9dd747`: all of
   `test_bp_service_native`, `test_bp_node_native`, `test_bp_contact_native`
   and `test_bp_obligation_native`, plus a native N04 interrupted-contact
   restart. Then the v0.3 gate: two DTN images and a relay on one box, an
   interrupted contact, an expiry, staging exhaustion, and receipts back,
   recorded. The dtn7-rs interruption run is a separate row. ION native
   execution stays open.

**Obstruction:** P11 cannot be DONE until the kind-8 recovery policy exists,
because "across an outage" includes a death mid-send. That policy needs an
ember-level decision on duplicate control, meaning retry after a possible
send, before its theorem can be stated. Every other item is lane work.

| P11 | theorem: `fn-bpnp-step` exists and is host-called; 5 of 29 §5 theorems exist (fragment and lifecycle-over-`fn-bpn-step`); T1-T3, T5, T6-replay and T6-continuation absent; PRF-045 model-only; `fn-bprl-release-removes-the-forward-pin` exists | subject: host calls `fn-bpnp-step` (`bp-service.lisp:172`); keystones M1 and lifecycle are over sibling `fn-bpn-step` with only a state-only `fn-bpnf` bridge; PRF-046 has no events and says "calls fn-bpn-step"; PRF-045 2 reach orphans | teeth: guard-premises 5, machine-teeth 6, release 7 must-fails; N03, N04, N05 partial; N09 present; 14 N and 24 BP-R labels missing | observed: N03 and interrupted-fragment on `1a9dd747`; other BP native tests not on a current image; no real-BPA interruption; scheduler not native | obstruction: kind-8 death strands the row, and the retry/duplicate-control policy is undecided |
