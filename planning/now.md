# Now — 2026-09-24

The one page a new agent reads first. It says where dev is, what the night
is for and who is working on what; everything else is linked. The previous
log that lived here is [archive/now-2026-09-24.md](archive/now-2026-09-24.md).

## Where things stand

- **Read [the current view](current.md) first.** It is generated from the
  tree and a small sidecar, and gives each capability (P1 to P11, M4, M5, M6,
  T17) its contract, the host line that calls its subject, its keystone and
  certificate, the image that tested it, whether the live node carries it,
  and one line each for the latest result, the obstruction and the next
  gate. Superseded image records are listed there and stay in
  [`evidence/`](evidence/), immutable.
- **Live node:** hbox `/tank/fn/node` on `18c91321` since ~21:50 UTC
  ([node record](evidence/node-hbox-18c91321-2026-09-24.md),
  [qualification](evidence/qual-18c91321-2026-09-24.md)), upgraded in place
  with the store kept and its profile upgraded to scale (4096);
  `fn-47bdb9a4` and `fn-da5fd8cb` stay beside it for rollback.
- The [wind-down handoff](handoff-2026-09-24-winddown.md) is the restart
  record; [gpt-6's direction review](review-2026-09-24-gpt6-direction.md)
  names the next development cycle.

## The goal now: v0 deployed, then the milestones (re-pointed 2026-09-24 ~11:30 EDT)

ember's correction: the v0 push had become an audit of the present state.
The plan's forward work is what the lanes point at from here, with the
[scoreboard](v0-scoreboard.md) as the check, not the goal:

1. **T0, the deployed node: done.** It runs `18c91321` (above); which
   capabilities it carries is the "deployed" column of
   [the current view](current.md).
2. **M4, disconnected exchange.** The kind-8 retry policy (default adopted,
   pending ember), death-after-kind-8 exactly-once on a DTN image, an
   interrupted contact on a real BPA (dtn7-rs lab), the four-node lab.
3. **v1 (b), the Message-ID index on the served path** (T17) with its
   measured cost sentence.
4. **M6, the human web interface** ember, yue and tulip can use against the
   deployed node.
5. **M5, bounded long-lived operation**: headroom and refusal explicit and
   observed; compaction with its preservation proof.

Decisions for ember stay listed on the scoreboard; defaults are adopted where
the plan or the M4 evidence already implies one, and marked as such.

## Lanes

Lanes run on Claude Opus 5.5 in `build/lanes/<name>` on branch `lane/<name>`
from a named dev revision; Claude Fable coordinates, reviews and merges. How
lanes coordinate is on the [swarm board](swarm-board.md). The night lanes
(image, join, cost, planning) are in the [restart record](handoff-2026-09-24-night.md).

**v0 push, landed** (each row's evidence is in [the scoreboard](v0-scoreboard.md)
and the merge message):

| Lane | Result |
| --- | --- |
| audit-p1-p6, audit-p7-p9, audit-p10-p11 | every §2.1 cell re-verified; packets per P (`planning/v0-audit-*.md`) |
| matrix-1a9dd747 | 188 rows reached, 0 disagreed, 0 faulted, INN 33/33; three matrix-tool defects fixed ([record](evidence/matrix-1a9dd747-2026-09-24.md)) |
| campaign-1a9dd747 | 20/20 cuts pass on the developer twin; production refuses selectors; NNTP wire probe found W1, W2, W3 ([record](evidence/campaign-1a9dd747-2026-09-24.md)) |
| bp-d1b-disposition | every commit already on dev; worktree retired ([record](evidence/bp-d1b-disposition-2026-09-24.md)) |
| host-translate-check | `tools/host_shape_check.py` in `make check`; `make check-host-translate` |
| cost-4 | five more books under 10 s; baseline 5 |
| p9-retention | refusal and keep-until-release over the called prepare and finish; PRF-004 +6 |
| p6-reconfig | half-change theorem over the called publication path; delta constructor moved into ACL2 |
| p2-p3-p5-owner | 240 keystone over `fn-own-finish` (host must install it), T6 pinned view, open-at-bound and fault wrapper |
| p7-peering | loop freedom over `fn-own-submission-targets`; Path tail kept; PRF-029 +4, PRF-058 +2 |
| p8-verdict | kind-4 finish records its verdict; `HDR :fn-verified` over `fn-own-read`; PRF-026 has events |
| p1-auth | 480/483/posting allowance over `fn-auth-step-pinned` and `fn-served-dispatch`; PRF-031 +6 |
| p11-bridge | `fn-bpnp-step` refines `fn-bpn-step` on base events; no release without a receipt; counterexample suite started; recovery-clears-sessions bug found |

**Landed since:** each lane's result is in its record under
[`evidence/`](evidence/) and its merge message; what they add up to per
capability is in [the current view](current.md).

**Not merged, kept for a follow-up:** `lane/p11-machine-gaps` at `8b273f87`
(worktree `build/lanes/p11-machine-gaps`): N07 as a recovery-event boot-domain
gate and N11 as a kind-14 conflict record with its codec (certified), but the
keystone book `books/bp-node-machine-gaps.lisp` times out at the local lemma
`bpgap-conflict-held-under-hypotheses`, and the host must drive the new
`:persist-conflict` effect (bp-service.lisp `fnn-bps-drive-effects`, the
TCPCL receive callback, and the N07 gate at :75-114 / :752) before any image
carries the branch. Its LANEDUMP has the exact list.

**Stopped mid-flight by the laptop's OOM crash (2026-09-25 ~03:05 UTC),
each with its work committed in its worktree; resume by re-briefing from the
worktree's commits and LANEDUMP (the coordinator's SendMessage ids died with
the session):**

| Lane (worktree under build/lanes/) | State at the crash |
| --- | --- |
| rep-sha256 (Fable): SHA-256 on a word stobj | 0 commits; REPL work only; restart from the brief in the merge message of planning/design-2026-09-25-representation.md §5 |
| rep-records-2: records-concrete-2 and the trie | 2 commits ahead |
| rep-heap: the heap census and the payload holder | 1 commit ahead, 2 files modified (uncommitted) |
| bounds-p1-profile: the operator's profile (format 8) | 0 commits, 4 files modified (uncommitted) |
| bounds-p2-ceilings: data constants become codec ceilings | 3 commits ahead |
| bounds-p4-carrier: carrier v2 | 2 commits ahead; its persvati run (hybrid-* affected-by) was still certifying |
| control-c1: file control articles, never execute | 5 commits ahead |

Push dev after every merge (ember, 2026-09-25): a merge certification
still runs and lands its manifest, but never gates the push.

Rule from the crash (cause and cap in
`planning/evidence/laptop-oom-2026-09-25.md`): ACL2 on the laptop only
through `tools/acl2` or `tools/proof_repl.py`, which now cap each process at
8,000 MB and pool six; never a bare `acl2 <`; images, owners and censuses on
hbox under `swarm-build` or a `systemd-run` memory cap, or on persvati.

**The megaspike (D28, from ~07:45 UTC 2026-09-25):** `spike/mega` from dev;
eight spike lanes on `spike/<name>` in build/lanes/spike-<name>: control (C2 to
C4 end to end), peering (invite/accept, succession, revocation, pull feeds,
INN stranger), mission (the four-node lab and demo on hbox), operator (one
`fn` command, upgrade/rollback/backup/restore, alerts, mission profiles),
storage (reclaim under D13, chained packs, rotation cleanup, 64-bit widths,
N=100k numbers), reader (threading, search, composer, a third-party client,
operator page), bp (routed queued jobs, fragmentation, multi-relay and ION,
production DTN labs, N16-F1), representation (waves B and C on the spike
for numbers). Dev lanes still running: bp-budgets-receipts (the connection-
local uncertain receipt transfer), bounds-p3-checkpoint, python-store-f8,
signed-path. The spike never merges into dev; each spike record lists its
deferrals for the proved re-implementation.

## State at the weekly API limit (2026-09-25 ~11:30 UTC; resets Sep 26 09:00 New York)

The night deputy and about a dozen of its lanes were terminated by the
account's weekly rate limit. Nothing was lost: every lane's commits are in
its worktree under build/lanes/, the deputy's state is in
build/coordinator/NIGHT-STATE.md and its routine in build/coordinator/
NIGHT.md, the backlog it swept is planning/backlog-2026-09-25.md. When the
limit resets, start a fresh deputy from those two files; it resumes each
terminated lane by re-briefing from the worktree (the agent ids are dead).

Landed on dev tonight by the deputy (18 merges, two merge certifications
green): bp-routing-2, peer-carriage, dtn-build, native-drift,
bounds-profile, k0-rest, operator-verdicts, path-and-login (D32: a
client-supplied Path accepted; login bound to principal), reclaim-d13 (the
proved half), bounds-blob, control-c3 (the decision), rep-octets-stobj,
carry-kind, k0-steps (K4 bridges), k0-cuts, live-status, marker-required,
plus the coordinator's own merges earlier (owner-checkpoint-open,
bp-budgets-receipts with the connection-local receipt transfer, control C2).
On spike/mega: operator, reader, peering, control, bp, representation; the
mission lab and the storage spike (a 100k-article run, 4 to 5 hours) were
still running on hbox when the limit hit.

Terminated mid-flight, worktrees intact, to resume: reader-surface, pbb-d32
(Fable), bounds-p5 native continuation (needs LD_LIBRARY_PATH for OpenSSL
on hbox), bp-n16-prod, control-c3b (the served withdrawal with K1 restated),
reclaim-host, peer-keys, peer-invite, status-join, rep-wave-c (Fable; its
correspondence chain was proving), checkpoint-cost, the bounds-p6 record-
ceiling fix. Held merges: bounds-p6 (the width half; blocked until the
record ceiling fix lands: a saved format-8 profile with R = 17,138,486
would fail validation), python-store-f8 (green but its quiet rerun of the
timed-out modules was pending), bounds-p5 (chained packs; one native test
red on packing nothing).

Dev's merged bytes are RED at four books (the deputy's third merge
certification, hbox run-20260925T102957Z-2118, manifest
certify-20260925T103038Z-3156842, 516 of 520 passed): books/poster-bytes-
buffer and tests/acl2/octets-stobj-tests (the octets-stobj consumer against
D32's supplied Path: the terminated Fable lane pbb-d32 was proving the
repaired chain), books/store-reclaim and its tests (the reclamation books
against the same merges). Both are join defects to fix first at the reset,
before any cut.

Update 2026-09-25 ~18:45 UTC: the limit lifted; the first deputy was resumed
in place and told to resume its lanes by message. The python-store-f8 quiet
rerun is RED (test_store 1 failure and 16 errors, test_checkpoint 1 error;
test_store_corruption was interrupted by the coordinator's own mistake and
not rerun): the lane needs a continuation before it merges. PKT-162: the
Python bridge starts ACL2 outside the pool and heap cap.

Update 2026-09-25 ~18:55 UTC (deputy): since the reset, merged into dev:
python-store-f8 (on the deputy's own sequential rerun at the lane head
dac828e5: test_store_corruption 7/7, test_checkpoint 7/7, test_store 21/21,
logs in planning/evidence/python-store-f8-2026-09-25/; the coordinator's red
rerun finished at 14:33 EDT, the minute the deputy merged and removed that
worktree under it, so its errors are not evidence either way: a third rerun
at merged dev is running in build/lanes/pyf8-check-a48e9072), reader-surface
(XPAT, ACL2-rendered POST refusal text; native owed), reclaim-d32fix (the
store-reclaim join repaired), control-c3b (C3's served withdrawal: 430 to a
fresh reader, pinned reader keeps it, natively green), bounds-p6 (u64 widths;
the record ceiling at runtime widths so saved profiles open), rep-wave-c (the
subject digest from the buffer), checkpoint-cost (open 2 to 4x faster, the
publication off the mutex). Remaining join defect: poster-bytes-buffer
(pbb-d32, Fable, running): no image builds until it lands. Merge
certification run 4 (persvati run-20260925T184414Z-fdae, 651 books) is
running at the merged head. Held: bounds-p5 (its pack-chain native module;
continuation running), peer-keys (a crash cut the model lacks; continuation
running), status-join (native owed after pbb-d32).

Not done tonight: no cut, qualification or deploy (dev never converged: P6
held, C3's served half and wave C in flight); segmented articles (P6's
second half) not started; the node is still on c3420013 with a format-7
store. What waits on ember: nothing new beyond the three decisions
recorded as D29 to D31 (all taken).

## Night report, 2026-09-25 (the night deputy; written ~20:30 UTC for ember and a gpt-6 review)

Covers dev `24591e11` to `ed7866d2`: 117 first-parent commits, 37 lane merges.
Every merge message states what was proved, the numbers and what stays open;
each lane's record is under [`evidence/`](evidence/). The backlog is
[backlog-2026-09-25.md](backlog-2026-09-25.md) (PKT-001 to PKT-163).

### 1. State

- **dev `ed7866d2`, pushed, `make check` green.** Six merge certifications of
  merged bytes ran. Runs 1, 2, 5 and 6 were fully green:
  - run 5: persvati `certify-20260925T191657Z-265615`, 564 books, 0 failed;
  - run 6: `certify-20260925T195406Z-616568`, 316 books.

  Runs 3 and 4 were red on two join defects, since fixed (§3).
- **Cut `e747dbcc`.** The combined closure passed on hbox:
  `certify-20260925T194254Z-3661260`, 602 certified over 828 roots, 0 failed.
  Gate: `/tank/fn/gates/qual-e747dbcc-20260925`. All four images built.
  **qual-e747dbcc is running.** It follows qual-c3420013's shape plus an
  upgrade rehearsal on a copy of the live store: format 7 to 8, then the
  marker-required two-step with its snapshot rollback.
- **Live node unchanged:** `c3420013`, format-7 store. No deploy yet.
  - The deploy follows the in-place shape when the verdict is "deployable".
  - After a marker-required migration, c3420013 cannot open the store; the
    pre-migration snapshot is the only rollback.
  - The deputy's default: format 8 unmarked tonight, migrate after a day,
    unless ember says otherwise.
- **Not in `e747dbcc` (merged after the cut):** status-join, peer-invite,
  reclaim-host part one, peer-pull. A second cut follows.

### 2. Landed, by goal item

- **Bounds (D27):**
  - bounds-blob: the frame blob width per schema; `operator post` carries
    articles above 131,072 octets, natively up to the profile's A.
  - bounds-profile: config generations and credentials come from the profile.
    It also fixed a writer that could write generation 8193 and then fail
    every open.
  - bounds-p6: u64 widths, record schema 2, the translation keystone; the
    record ceiling stays at the runtime's widths, so the saved presets open.
- **Representation B and C:**
  - rep-octets-stobj: the `fn-octets` abstract stobj.
  - pbb-d32: the buffer twin follows D32's v3 source, compared in place.
  - rep-wave-c: the subject digest read from the buffer. Per 2 KiB POST,
    list conversions went from 30 to 24 calls and SHA-256 calls from 9 to 6;
    32 KiB POST wall time went from 18.9 to 17.0 ms.
  - carry-kind: event fields read once; the signed POST no longer runs the
    whole-store step.
- **Owner opens from the checkpoint and publishes its own:**
  owner-checkpoint-open, then checkpoint-cost. At N=4096, owner start went
  from 30.0 to 9.3 s, and the first greeting during a publication from 10.0
  to 2.9 s.
- **Reclamation (D13):**
  - reclaim-d13: the rule, the decision, and the tombstone with its
    preservation theorems; 423/430 served.
  - reclaim-host part one: every duplicate test is reclaim-aware; OVER and
    NEWNEWS skip reclaimed articles; status counts; tombstone-shaped payloads
    proved refused at ingress. It fixed a defect: nothing was ever
    reclaimable on a live store.
- **Marker (D31):** marker-required (an absent marker is damage, plus the
  retry-resolution protection); native 12/12.
- **K0:** k0-cuts, k0-steps (the K4 node correspondence), k0-rest, and
  k0-recovery (the recovery window, the recovery program, the re-recovery at
  admin.lisp:107, and the pre-init relation).
- **BP:**
  - bp-budgets-receipts.
  - bp-routing-2: routed queued jobs, route-gated sessions, and **once per
    contact as a theorem**; native 26/26.
- **Control:** control-c2c3, control-c3, control-c3b, control-c3d:
  - C2 authority rows;
  - signed control articles filed;
  - the served withdrawal, with K1 restated;
  - each cancel decided under its own txid's configuration, live and at
    recovery;
  - Supersedes;
  - the two-node native cases green.
- **Peering with strangers:**
  - peer-invite: once-only consumption across a crash; native 3/3.
  - peer-keys: succession, revocation and the `:revoked` verdict, with the
    executor's crash cut modelled; native 2/2.
  - peer-carriage: the budget and the refusal classes.
  - peer-pull: the ack-bounded cursor, recovered at every cut; native 3/3
    against fn and INN.
- **Operator and reader, from the spike:**
  - live-status.
  - status-join: large numbers had printed as 0.
  - operator-verdicts: the unnamed 441 is gone; needs-upgrade and
    rollback-check.
  - path-and-login: D32, and tin posts, replies and cancels.
  - reader-surface: XPAT, ACL2-rendered refusal text.
- **Also:**
  - python-store-f8: green three times, the last at merged dev.
  - native-drift and dtn-build. The new `included` build-list rule has
    caught two more DTN omissions since.
  - ten-second-3: six books under 10 s by hint repairs alone.
- **Spike:** operator, reader, peering, control, bp and representation are
  merged into spike/mega. Every deferral list became dev lanes.

### 3. Red, and why

- **Two D32 join defects** blocked every image for about three hours:
  `poster-bytes-buffer` (fixed by pbb-d32) and `store-reclaim` (arity; fixed
  by reclaim-d32fix). Lesson: an interface change to a shared definition gets
  a merge certification before the next dependent merge.
- **Eight ID collisions** (PRF, NNT, SCN, STO numbers), each renumbered on the
  lane before its merge. Briefs should assign requirement and scenario
  numbers as well as the PRF.
- **The weekly API limit** stopped the deputy and about 13 lanes at about
  11:30 UTC. All were resumed from their transcripts, and nothing was lost.
- **hbox load (up to 19)** doubled wall times while CPU time matched
  persvati's. The cost baseline was widened with each run and load named,
  and ten-second-3's quiet re-measure shrank it again. Merge certifications
  moved to persvati.
- Lane dumps were committed at the root three times; a shared scratch
  message file was overwritten between agents. Both are fixed in the brief.
- **Test iteration time (ember):** the Python store modules take 1857 to
  2283 s each, about 90 s per ACL2 boot, apparently one per test.
  `test_bp_node_native` takes 909 to 1134 s. The test-latency lane is finding
  the cause by examining the harness and bridges, then fixing it. Target:
  each module under 3 minutes, one test under 20 s cold, and a per-module
  budget check.

### 4. Held, and why

- **bounds-p5 (chained packs):** proved and certified. Its native module
  timed out building its fixture: the commit path was O(N²) (fixed; 1800 s
  down to 22 s). The N=20,000 chain module is running.
- **bp-n16-prod (N16-F1, generation retirement):** certified, native 25/26.
  The control-article case needs a default developer image. A continuation
  reruns it whole, removes a block doubled in `host/native/bp-node.lisp`, then
  starts fragmentation.
- **operator-config:** three packets certified. `books/native-mission` times
  out at `fn-native-mission-run-init`; a continuation is running.
- **Running:** control-c3e (the 423/430/`HDR :fn-control` reader answers into
  the NNTP step, plus a Message-ID-to-txid index), qual-e747dbcc,
  test-latency.

### 5. Decisions for ember (none blocks the deploy)

1. **PKT-011 / PRF-072** ([bounds-blob](evidence/bounds-blob-2026-09-25.md)).
   Deriving the pre-check figures (65,538; 196,608) from A and G makes
   `fn-profile-upgrade-keeps-verdict` false: raising A or R without H makes
   the history check stricter. Options:
   - (a) a hypothesis on the theorem;
   - (b) `fn-profile-upgradep` refuses raising A or R without raising H,
     which changes the deploy procedure;
   - (c) keep the fixed figures as a documented pre-check ceiling.
2. **PKT-100, restore of a news-only store**
   ([operator-verdicts](evidence/operator-verdicts-2026-09-25.md)). An old
   backup would reuse article numbers readers have seen. Options:
   - (a) advance every group's counter past a gap;
   - (b) a new numbering epoch;
   - (c) same-identity restore from a latest-known backup only.
3. **Profile field 13, policy members**
   ([bounds-profile](evidence/bounds-profile-2026-09-25.md)). The count sits
   inside a signed statement's codec; a per-node limit lets two nodes
   disagree on one statement's validity. Options: keep it a protocol work
   bound, or version the codec.
4. **Refused signed articles**
   ([peer-carriage](evidence/peer-carriage-2026-09-25.md)). Hold them with a
   durable `:unverified` verdict naming the class (a new kind-4 composite),
   or keep today's refuse-and-log?
5. **The pull cursor as files, `<store>/pull/*.fnpl`**
   ([peer-pull](evidence/peer-pull-2026-09-25.md)). A Store record family
   would touch about 25 books; the configuration history would use up
   `max-config-generations`.
6. **A keystone gained a hypothesis**
   ([bounds-p6](evidence/bounds-p6-2026-09-25.md)).
   `fn-bs-profile-admits-every-article-record` now requires that the record
   fits u32 widths. That runtime records fit is stated, not proved; a wider
   one is refused at the publish gate. Accept, or make it a theorem?
7. **peer-keys' reopen** ([peer-keys](evidence/peer-keys-2026-09-25.md)). A
   declined key statement that is still the newest record is decided again
   at the next open, so a `keys` grant added across a restart lets it act.
   Intended, or should a decline be durable?
8. **Plaintext pull.** The pull client has no TLS. Acceptable for v0?

### 6. What near-completeness still lacks

- **Bounds:** chained packs merged; segmented articles (wave D boundary 10;
  a 1 GiB article costs 16 GiB per list copy); txids beyond u32 (frontier-3);
  charge above u32; the remaining data caps: consumers (field 9), BP rows
  (field 10), BP ADU bounds, the receipt and app journals, the held BP bundle
  image.
- **Representation:** the owner state as the buffer; boundaries 7 to 10; the
  status report and the BP, TCPCL and feed codecs as bytes.
- **Reclamation:** the `store reclaim` verb with its K0 cuts (through the
  compaction pack, after chained packs); charge release; feed and FNBS; the
  native campaign.
- **BP:** fragmentation without the 65,538 × 64 caps; N16 §3.6 (chunks,
  manifest kind 21, `:quiesce`); production DTN labs; ION (a dtn7-to-ION UDP
  hop); PKT-064.
- **Control:** the reader answers into the NNTP step (running); C4 deferred
  by D29.
- **Peering:** decisions 4 and 8; `peer add` still separate after confirm.
- **Marker:** the cheaper publication program (PKT-143).
- **K0 still open:**
  - the initializer after the frontier link;
  - a directory fsync error with an authority entry pending;
  - `(:recover)` from `:replaying` with an entry pending;
  - the admin publication byte program (the relation at admin.lisp:107 is a
    hypothesis).
- **Operator:** node-health (queued); operator-config (held); the spike's
  `packaging/fn` wrapper.
- **Cost:**
  - owner-invariants 10.6 to 12.8 s;
  - two quadratic checks at open (`fn-articles-freshp`,
    `fn-node-articles-have-archive-bindingsp`; reopen about N^1.6);
  - the greeting costs 1.4 s at N=4096 under the owner mutex;
  - test iteration time.

The deputy's working state, with agent ids and queued briefs, is local in
`build/coordinator/NIGHT-STATE.md` and `build/coordinator/queue/`.

## Where to read next

- [Current view](current.md): per capability, the four evidence
  coordinates and the next positive gate.
- [Restart record for the Claude night](handoff-2026-09-24-night.md): the
  numbers, the findings, what remains open, how to restart.
- [Wind-down handoff](handoff-2026-09-24-winddown.md): gpt-6's record of the
  integrated capabilities and their limits, and its final cut.
- [How we work](how-we-work.md): the loop, the compute budget, convergence.
- [AGENTS.md](../AGENTS.md): the assurance rules. They apply in full.
- [Decisions](decisions.md): what ember has decided and when.
- [Trajectory plan](plan-2026-09-22-trajectory.md) §0 to §2 and §6: release
  scope, v0 and v1, and what v0 does not claim.
- Evidence: dated records in [`planning/evidence/`](evidence/) and certify
  manifests in [`planning/evidence/manifests/`](evidence/manifests/).
- [Milestones](milestones.md): M0 to M6 and the current-task line.
