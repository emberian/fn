# bp-lifecycle (wave 2, 2026-09-25): fragment reassembly without a family-size ceiling

Lane `lane/bp-lifecycle` from dev `483987b1`. Brief:
`build/coordinator/queue/w2-bp-lifecycle.txt`. Ids: PRF-121, SCN-067,
PKT-171 (the packet below). Model: Opus 5.5.

## What now works

A BP node reassembles a fragment family of any fragment count and any ADU
length in work linear in the octets it holds. Before, the executed
reassembler checked two data ceilings, 65,538 octets and 64 fragments, and
its work was (total x fragments). Numbers:

- A 10 MiB ADU arriving as 5,120 4 KiB fragments, each fragment twice and
  in no particular order, reassembles in 0.62 s with 673 MB allocated.
  This was one run in a proof session on persvati, over octet lists. It is
  not a native-image measurement.
- The node's family selector now plans each family once per host call
  instead of once per member. That removes a factor of the family size from
  every scheduling step.
- A native case exists for a family of 70 fragments, beyond the old
  64-fragment ceiling, with the receiver killed by SIGKILL after fragment
  35 (SCN-067). It ran in the continuation and is **blocked** by the
  held-row capacity (64 rows): see "Continuation: bp-lifecycle-2".

The brief's user-visible result, a 10 MiB article carried through 4 KiB
fragments, is **not** reached. Four other ceilings still bound a family
before reassembly:

- the held-image cap `*fn-bpnf-max-held-image*` on the whole bundle;
- the bundle decoder's 1 MiB input (`*fn-bpb-max-input*`,
  bp-bundle.lisp:62);
- the ADU record's 65,538 octets (`*fn-bpa-max-octets*`, bp-adu.lisp:24);
- `*fn-bpa-max-article*` (32,768).

These are P5 of `planning/design-2026-09-25-bounds.md` and PKT-171 below.

## Salvage (item 1)

`git log dev..lane/bp-n16-prod` is empty. The N16 lane merged at
`acac63d8`, with:

- the doubled block in host/native/bp-node.lisp removed (5e852264);
- generation retirement, every step a model crash point;
- test_bp_node_native 26/26, later 27/27;
- MRU fragmentation (PRF-114).

Nothing was cherry-picked. The N16 record's open items are still open:

- a killed rotation's unselected new-generation directory is kept and never
  retired;
- the removal model is an alist, not K0's byte store;
- the retirement functions run as logic-mode counterparts, not
  guard-verified.

## The assurance chain

**Native entry.** `host/native/bp-service.lisp` `fnn-bps-fragment-progress`
calls `(fnn-core 'fn-bpnf-family-next state observation)`. On `(:ready A)`
it steps `(:family A observation)` through `fnn-bps-foundation-step`, which
calls `fn-bpnf-fragment-step`. That calls `fn-bpnf-family-propose-step`,
then `fn-bpnf-family-plan-at`, then `fn-bpnf-family-plan`, then
`fn-bpnf-fragment-query`, then `fn-bpfw-reassemble`.

**Executed subject.** Two functions:

- `fn-bpfw-reassemble` (books/bp-fragment-sweep.lisp; guard t,
  guard-verified). It merge-sorts the fragments by offset, sweeps once,
  tail-recursively, over positions 0..total-1, keeping per position the
  suffixes of the extents that cover it, then scans the outcome as the
  reference does.
- `fn-bpnf-family-next`. Its `:exec` branch is `fn-bpnf-family-next-memo`.

**Refinement.**

- `fn-bpfw-reassemble-is-spec`: on every input, the reassembler equals
  `fn-bpfw-spec`.
- `fn-bpf-reassemble-is-capped-spec`: the old reference is `fn-bpfw-spec`
  when the input is within its caps, and `(:invalid :bounds)` otherwise.
- `fn-bpnf-fragment-query-is-reference` (restated): the node query equals
  `fn-bpfw-spec` over the family's cells and the anchor's total.
- `fn-bpnf-family-next-memo-is-aux`: the memo selector equals the
  per-member selector, anchor included. Its guard obligation is discharged
  at the `mbe` in `fn-bpnf-family-next`.

**Maintained relation.** The memo's invariant is
`fn-bpnf-family-tried-okp`: every tried row is a held active fragment whose
plan is not `:ready`. The empty tried list at the call establishes it. The
memo's two recursive calls preserve it: a row whose family was tried is
skipped, and a row whose plan was not ready is added. The sweep's relation
is `fn-bpfw-view`: at position I, the merge of the active suffixes and the
queue equals the canvas from I on.
- `fn-bpfw-view-of-admit` preserves it at admission.
- `fn-bpfw-view-of-advance` preserves it at the advance.
- `fn-bpfw-cell-at-before-every-offset`: sortedness makes the queue
  contribute nothing at I.

**Behavioural theorems.**

- `fn-bpfw-exact-canvas-reassembles`: under `fn-bpfw-inputsp`, a family
  whose canvas is an octet list reassembles to exactly that canvas.
- `fn-bpfs-plan-fragments-reassemble-uncapped`: the sender's plan
  (`fn-bpfs-plan`, PRF-114) of a whole parent reassembles to exactly the
  parent's payload, for every payload length and fragment count.
- `fn-bpnf-family-plan-at-of-member`: every member of one family has the
  same plan. This is what lets the memo skip a family.

**Observed.** Nothing native yet (see "Runs").

## Statements

`fn-bpfw-spec` is the reference's own body with `fn-bpfw-inputsp` in place
of `fn-bpf-inputsp`. The inputs must be:
- well-formed fragments `(:fn-bp-fragment offset bytes total)`, each with
  natural offset, non-empty octets and offset + length <= total;
- a positive total;
- a non-empty list;
- one total for every fragment.

The inputs are **not** capped by 65,538 or 64. The outcome function
`fn-bpfw-outcome` is the reference's:
- conflict before gap, the least conflicting index;
- `(:missing lo hi)` with the least gap and its run;
- `(:ok canvas)`.
So the four outcomes stay distinct.

## Teeth

`tests/acl2/bp-fragment-sweep-tests.lisp`:

- A 70,000-octet ADU in 100 fragments. It is above both caps, in
  descending offset order. It passes `fn-bpfw-inputsp` and fails
  `fn-bpf-inputsp`. The executed reassembler answers the exact payload; the
  capped reference answers `(:invalid :bounds)`.
- The same family plus a second cut at another chunk size plus its reverse
  (overlap), which reassembles exactly.
- Every outcome on small families, each equal to the spec: `:ok`,
  `(:conflict 4)`, `(:missing 3 5)`, a conflict after a gap reported as the
  conflict, a wrong total, an empty list and a zero total.
- For `fn-bpfw-exact-canvas-reassembles`:
  - the positive witness above the caps;
  - without `fn-bpfw-inputsp`: total 0 has an (empty) octet canvas and is
    refused, not `(:ok nil)`;
  - without the octet canvas: a gapped family is valid input and answers
    `:missing`.

`tests/acl2/bp-fragment-send-tests.lisp` adds:

- the uncapped reassembler on the 100-fragment and 70,000-octet plans that
  the capped reference refuses;
- a must-fail per hypothesis of `fn-bpfs-plan-fragments-reassemble-uncapped`:
  a whole answer has no fragments; a fragment parent's pieces carry its
  total, 3,000.

`fn-bpfw-reassemble-is-spec`, `fn-bpf-reassemble-is-capped-spec` and
`fn-bpnf-family-next-memo-is-aux` at its call are equalities without
hypotheses. Their teeth are the witnesses of both sides.

## Proof cost

None of the final commit's books is certified by a manifest yet (see
"Runs"). The final sweep book's event times sum to 7.02 s in a fresh proof
session on hbox; at r2 the book was 10.20 s. Moving
the generic lemmas into `local` was necessary:
- the nthcdr and nth rewrites;
- the merge-cell algebra and the disable of `fn-bpf-merge-cell`;
- `fn-bpfw-inputsp-with-caps`.

Exported, these lemmas made downstream guard proofs ten times slower in a
REPL measurement:
- `verify-guards fn-bpnf-family-plan`: 10.7 s against 1.16 s on dev;
- `verify-guards fn-bpnf-offset-zero-source`: 10.4 s against 0.72 s on dev.

The capped-spec keystone is `:rule-classes nil`.

## Not done, and why

(As of the first session. The continuation's own "Not done" at the end of
this record supersedes it where they differ: the fragment part of item 3
and the rotation under load are done there.)

Budget: one session and three farm runs. Fragment reassembly without a data
ceiling was the brief's first new item, and it was the one the native path
could exercise. The rest, in brief order:

- **Item 2, the remainder.**
  - Charge conservation and ownership over a family replacement are stated
    by the existing kind-18 books (`bp-node-fragment-replacement`,
    `bp-fnbs-family-*`), which this lane did not change. They now sit over
    the uncapped query.
  - A per-step work bound on reassembly itself is not proved. The work is
    O(n log n + total + the sum of the lengths) per completion attempt: one
    attempt per ready candidate, and the memo allows at most one per family
    per host call. There is no theorem counting it.
  - The 10 MiB transfer needs PKT-171.
- **Item 3, the job-table relation.** Six things are separate lemmas today,
  not one relation over the job table preserved by every step:
  - durable kind-8 attempts;
  - re-offer after a crash;
  - duplicate handling at the receiver;
  - durable retry counts;
  - stranded obligations;
  - explicit resume.

  Next exact action: state
  `fn-bpnp-job-table-coherent st` over `fn-bpnp-step`'s state (a kind-8 row
  without kind 9 is exactly a stranded or uncertain obligation; a retry
  count equals the durable attempts; a resumed row has its kind-8 identity)
  and prove it preserved by each event of `fn-bpnp-host-eventp`.
- **Item 4, N16 §3.6** (kind-19 chunks, kind-21 manifest, `:quiesce`): not
  started. The design is in specs/bp-node-machine.md §3.6.
- **Item 5, distinct exit codes.** The BP verbs map every outcome to three
  codes: `fnn-bps-exit-code` and `fnn-bp-exit-code` give ok 0, refused 1,
  uncertain 3. Expiry, a clock-domain change, no route, busy delivery and a
  connection-local failure are named on stdout (for example
  `BP fragment family publication refused`), not in the exit code. Next
  action:
  - an ACL2 `fn-bpn-host-exit-class` over the run's tally, answering
    `:expired`, `:clock-domain`, `:no-route`, `:busy`, `:connection` or
    `:uncertain-store`;
  - new codes 6 to 10 in host/native/io.lisp;
  - operator.md's table.
- **Native, item 6.** Only SCN-067 and the two regression modules ran.
  These did not:
  - the 10 MiB transfer with a kill and EIO at every cut;
  - the rotation under load.

## PKT-171: the ceilings between a BP article and its reassembly

**Trace.** A 10 MiB article carried by BP crosses the following, in order.
Each must admit it:

1. the sender's ADU record: `*fn-bpa-max-article*` 32,768 and
   `*fn-bpa-max-octets*` 65,538 (bp-adu.lisp:24, :31);
2. the sender's bundle encoder and the receiver's decoder,
   `*fn-bpb-max-input*` 1 MiB (bp-bundle.lisp:62);
3. the receiver's held image per fragment (fine at 4 KiB);
4. the reassembled whole bundle as one held image,
   `*fn-bpnf-max-held-image*`;
5. the machine's octet budget;
6. the reassembler (now uncapped);
7. before all of these on the receiver, the held-row capacity
   `*fn-bpn-machine-max-jobs*` (64 rows, bp-node-machine.lisp:18): the
   receive arm refuses the 65th held fragment of one family (observed on
   the image 2026-09-26, XFER_REFUSE No Resources). P5 moves it into the
   profile with the others.

**Constraints.**

- D27: capacity is the operator's, and work is bounded per step.
- The profile's A (16 MiB default, bounds design §2.2) is the article
  bound.
- RFC 9171 sets no bundle size.
- TCPCLv4 segments by MRU.

**Default recommendation.** P5 as designed:
- the ADU record admits A;
- the bundle bound becomes a profile field;
- the whole reassembled bundle is never materialised as one held image:
  kind 18 retires the fragments and hands the ADU to the application in
  chunks (N16 §3.6's chunk records).

**Rejected alternative.** Raise the constants to 16 MiB. The cost:
- a 16 MiB held image;
- a 16 MiB octet list per copy, about 256 MB of conses;
- no work bound.

**Affected.**
- Formats: bp-adu, bp-bundle, FNBS kind 18 and the chunk kinds.
- Proofs: `fn-bpn-limits-compose` (bp-limits.lisp), which asserts the ADU
  cap equals the fragment cap, and every recognizer that names these
  constants.
- Callers: bp ingress, `fn-bpnf-family-plan`.

**What continues without it.** Families up to the held-image cap already
reassemble without the fragment ceiling. That includes more than 64
fragments of any request the Store accepts today.

## Runs

Farm runs, all on hbox, `--affected-by books/bp-fragment-sweep`, 2 jobs,
300 s. Manifests are in `planning/evidence/manifests/`:

| run | commit | manifest | result |
| --- | --- | --- | --- |
| r1 `run-20260925T235154Z-37c4` | f79fe679 | `certify-20260925T235236Z-4052629.json` | red. `fn-bpnf-same-family-selects-same-rows` timed out; repaired with narrow theories. The sweep book, its teeth, send, send-tests, family, plan and family-tests certified. |
| r2 `run-20260926T000937Z-56e1` | 4e9d3d5d | `certify-20260926T001016Z-4091270.json` | red, two defects. `verify-guards fn-bpnf-family-next`'s theory lacked `fn-bpnf-family-tried-okp`. The sweep teeth's `bpfwt-frags` measure had lost a global nthcdr lemma. Cost regressions: route-step 36.5 s against 7.09 on dev, machine-gaps 28.6 against 6.44, debt-cache-invariants 24.8 against 6.94, fragment-replacement 20.1 against 6.78, fragment-guards 26.2. Cause: the sweep's exported generic rules, above all `fn-bpfw-fragmentp-fields`, a rewrite on `(true-listp f)` that backchains through an enabled recognizer. Those rules were made local. A scratch certification on hbox then measured fragment-replacement at 7.15 s. |
| r3 `run-20260926T002156Z-319a` | fd13d1d4 | `certify-20260926T002231Z-4118107.json` | red. `fn-bpfw-sortedp-of-merge` hit the 300 s timeout (log `/tank/fn/gates/bp-lifecycle-r3/build/acl2/certify-20260926T002231Z-4118107/books--bp-fragment-sweep.certify.log`). Every other red book in the run is a cascade from it. A hint that disabled `fn-bpfw-all-at-least-of-merge` was checked in a proof session that already held the theorem, so the check was circular. Repaired at the final commit with explicit expansions: 0.87 s in a fresh session, 7.02 s for the whole book. |

The brief's three runs are spent. **The final commit is not certified.** (Superseded: r4 certified it green; see "Continuation: bp-lifecycle-2".)

The native campaign at fd13d1d4
(`/tank/fn/scratch/bp-lifecycle/native-fd13d1d4.out`) stopped at
`VALIDATE-FAILED dtn` for the same sweep book. No image was built, and
neither native module ran.

Laptop: `make check` is green in the worktree, with planning/ledger.* and
planning/current.md regenerated there and not committed.
`fn-bpfs-canvas-of-extents` was dropped from PRF-114's proof events. Its
subject had been reached only through the capped reassembler's success
path. The served claim now goes through
`fn-bpfs-plan-fragments-reassemble-uncapped` (PRF-121), and
`reach_check --strict` passes.

**Next exact actions** (done in the continuation):
1. One farm run at the lane head, the same command with `--remote-root
   /tank/fn/gates/bp-lifecycle-r4`. Expected: the sweep book about 7 s. The
   guards book's `fn-bpnf-family-next` guard has not been checked since its
   hint was repaired. Watch route-step, machine-gaps, debt-cache and
   fragment-replacement for a return to dev's times.
2. `sh planning/evidence/bp-lifecycle-2026-09-25/native.sh REV` on hbox at
   that commit, from a `git archive` into `/tank/fn/scratch/bp-lifecycle/tREV`,
   under `systemd-run --user -p MemoryMax=24G`. It runs:
   - `test_bp_fragment_node_native`, which includes SCN-067;
   - `test_bp_node_native`.
3. With both green, set SCN-067 and the record to observed.

## Continuation: bp-lifecycle-2 (2026-09-26)

Same branch, same ids (PRF-121, SCN-067, PKT-171). Commits 7d450923,
f50e2678 and the record commit after them.

### Certification

| run | commit | manifest | result |
| --- | --- | --- | --- |
| r4 `run-20260926T004017Z-3401` | 0069b282 | `certify-20260926T004054Z-4151228.json` | green: 74 books, 0 failures, `--affected-by` the six bp-fragment books. Slowest book 8.84 s (tests/acl2/bp-node-forwarding-teeth-tests); bp-fragment-sweep 7.08 s; bp-node-fragment-step 8.34 s; bp-node-fragment-guards 6.48 s (its family-next guard hint certified). The four r2 regressions are back at dev's figures: route-step 6.68 s (dev 7.09), machine-gaps 6.38 (6.44), debt-cache-invariants 6.53 (6.94), fragment-replacement 6.88 (6.78). |
| r5 `run-20260926T010240Z-23ee` | f50e2678 | `certify-20260926T010304Z-7053.json` | green: 2 books, 0 failures, `--affected-by` the new jobs book and its tests: books/bp-node-fragment-jobs 4.73 s, tests/acl2/bp-node-fragment-jobs-tests 5.43 s. Two runs, no timeout raised, no statement weakened, no baseline edited. |

### Native

All on hbox under `systemd-run --user -p MemoryMax=24G` in
/tank/fn/scratch/bp-lifecycle (never /tank/fn/node), through
`planning/evidence/bp-lifecycle-2026-09-25/native.sh REV` (dtn and default
roots installed from the cache, nothing left to certify, both images built
with no undefined lines).

| image / run | module or case | result | log SHA-256 |
| --- | --- | --- | --- |
| 0069b282 (`logs-0069b282/`); fn-host-dtn-developer 9624cf51783435c2edb0c526ea5d5e6fb0427bbb4ad97571419cd6ff4134b26e, core d49189e6755385b8f833f32553c7243349e77e650c9d4653772beaf80d18bb02 | test_bp_node_native | OK, 27/27 | 6debdaed8561e6b9d07461940fce301c7d84c4fe7da96ea8347cd7191f36a155 |
| 0069b282 | test_bp_fragment_node_native (SCN-067 at 70) | FAILED: sender exit 1 at the 65th held fragment | 5444101a1a8111801e92a4ed87714c701fafd0df1a789785d760ad06a7be8560 |
| 0069b282 | the 70-fragment case with the sender's stdout (diag-70.log) | XFER_REFUSE reason 2 (No Resources) for fragment 5, the 65th held | 32917329d315488750e2312e9874cfe1979d1a01cf9657d761a9a8bdb9a266ec |
| 0069b282 | 64 fragments across a kill, first harness (diag-64.log) | FAILED, harness: SIGTERM cut the Store handoff | a94d1d25601ba698b6760559692e697f8d60600ed50a872fcf1cb268cc16518f |
| 0069b282 | the module with the harness fix (diag-64b.log) | OK, 2 passed, 1 skipped | 06ef5ee8a6c542c983bc43e3da44d2a286ffbc94a933ca5c75eba8c1b9b0a633 |
| **f50e2678** (`logs-f50e2678/`): fn-host-dtn-developer b90be0b9aa93e777659779f85b7b6d7fc74d799f8500ec81c9a1db4b52f7043e, core da60a14fb40a07db4edf117a7c37eb158b266da1804060deed8e05169b860e5b; fn-host-developer d4e088500b3c87328f516c58f7ee6f468f4c67cf4027e5ed6a8d7b428236552c, core bc3871b3e96597bf17c2e504b00b8b1967bcdcace529bcf35e3fa7f5dcf64f38 | test_bp_fragment_node_native | OK: nonzero-then-restart, 64 fragments across a kill, rotation with a family in flight; SCN-067 skipped | 53d94912adbde1b708834156c3ec21090c2dc1db401902dd26d693b4e6b68192 |
| f50e2678 | test_bp_node_native | OK, 27/27 | 41e2056f49e99db34f84d950df52bfd9e73b53714eae72e6050ee0c734fe9986 |

**SCN-067 is blocked, not passed.** On the 0069b282 image the receiver
refused the 65th held fragment of the 70-fragment family with XFER_REFUSE
reason 2 (No Resources): the held list is capped at
`*fn-bpn-machine-max-jobs*` (64 rows, bp-node-machine.lisp:18), checked by
the receive arm of `fn-bpnf-step` before custody. Classification:
implementation, a capacity constant in the served machine, the same class
as PKT-171's ceilings; the reassembler's own ceiling is gone but a family
of more than 64 fragments cannot be held at once. The constant is not
raised (brief); it belongs in PKT-171's P5 (constants into the profile).
The test is kept as SCN-067's specification and skipped with that reason.
What the image does show: a 64-fragment family, highest offset first,
across a SIGKILL after 32, reassembles once through the uncapped sweep and
the once-per-family selector (one family publication, one Store handoff,
one article). The first attempt at that case failed as a harness defect:
the test sent SIGTERM right after the last fragment and cut the node's
Store handoff (`BP node source direct` was the last line); the last
fragment now goes to a one-session receiver, which exits after its
post-session work.

### Item 3: the family's rows and the job table agree

The job table is the held list: slots 10 to 13 of a held row are its
dispatch record, next hop, job state and kind-8 attempt. The progress
selector never dispatches a fragment (`fn-bpnp-live-pendingp` and
`fn-bpnp-oldest-uncertain-local` require a non-fragment), so a fragment's
one job is reassembly. `books/bp-node-fragment-jobs.lisp`:

- `fn-bpnf-family-jobs-agreep HELD`: every active fragment row carries
  exactly the reassembly job: `(:dispatch-pending)`, no dispatch record,
  no next hop, no attempt.
- **Keystone** `fn-bpnf-family-apply-conserves-jobs`: under the relation,
  a `:ready` `fn-bpnf-family-apply` (the one rule both the live kind-18
  persist and ordered replay call) consumes only rows whose one job was
  reassembly (`fn-bpnf-rows-job-onlyp` of the consumed list), installs the
  whole row with `(:dispatch-pending)`, and the new held list satisfies
  the relation. Discarding the carriers erases no unfinished job; the
  family's job moves to the whole row.
- **Host step** `fn-bpnp-step-family-events-keep-jobs-agreeing`:
  `fn-bpnp-step`, which `fnn-bps-foundation-step` calls, preserves the
  relation on the two events of `fnn-bps-fragment-progress`: `(:family A
  OBS)` and `(:persist-result EPOCH OP RESULT)` while a kind-18 operation
  is issued, through every wrapper (credit admission and refusal, the
  publication-fault branch, the runtime slots).
- Established: `fn-bpnf-family-jobs-agree-when-empty` (a cold start's empty
  held list). **Not proved**: establishment by recovery replay (the
  boot-domain entry `:recover-fnbs`), and preservation by the dispatch,
  forward, delivery, busy and deletion arms. Those arms select only
  non-fragment rows at proposal time but apply their persisted records by
  arrival, so the missing lemma is an issued-record invariant: an issued
  dispatch, attempt or delivery record names a non-fragment row. No
  whole-table revalidation was added to any command.
- Every event certifies in well under a second in a REPL session on hbox;
  the book's cost is its include of bp-node-progress (4.3 s).

Teeth, `tests/acl2/bp-node-fragment-jobs-tests.lisp`:
- reachable positive witness: the plan fixture's held list satisfies the
  relation; the family applies, consuming both fragments; all three
  conclusions hold; the same through `fn-bpnp-step` on `(:family 0 OBS)`
  (`:persist-family`) and the durable `(:persist-result 3 0 :durable)`
  (`:family-ready`), with the credit counters recovery installs;
- the relation removed: the offset-zero fragment carries a forwarding job
  (next hop, `(:forward-pending)`, a kind-8 attempt); the relation fails,
  the replacement still applies, the consumed rows include the forwarding
  row, and the conclusion fails (`must-fail`); through `fn-bpnp-step` the
  durable replacement removes that row from the held list;
- `:ready` removed: a refused application (wrong arrival) has no whole row
  carrying a job.

### Item 5: rotation under load

`test_rotation_with_a_family_in_flight_loses_no_fragment`
(tests/test_bp_fragment_node_native.py): seven of eight fragments held;
`bp-node checkpoint` killed after the rename, killed inside the retirement
program (after its second step), then clean (the old generation retired);
every reopen recovers seven held rows; the offset-zero fragment then
completes the family once, one Store handoff, one article. It lives in the
fragment module rather than test_bp_node_native.py because that module has
the Store, the receipts journal and the fragment author; the verb and the
developer cuts (`FN_BP_ROTATION_TEST_STOP`) are the same.

### Item 4: distinct exit codes, not done

Not started, for budget: the change spans six native modules' expectations.
A finding refines the design. The conflation is in the TCPCL connection's
outcome word: `fnn-tclc-outcome :uncertain` is set both by a Store
indeterminate inside the delivery callback (host/native/tcpcl.lisp, the
`fnn-store-indeterminate` handler) and by a transfer-level failure
(`:outbound-failed`, and the delivery plan's `:uncertain`). ACL2's
`fn-bpn-host-run-outcome` (host/bp-node-host.lisp) makes any operational
`:uncertain` the run's `:uncertain`, so `bp send` over a severed contact
exits 3, the code for a publication whose outcome is unknown, although the
sender's durable state is certain and RETRY re-offers the same identity.
Next exact action: split the connection's outcome into `:uncertain-store`
and `:interrupted`; add an ACL2 `fn-bpn-host-run-class` returning
`:uncertain` (3) > `:interrupted` (6) > `:refused` (1) > `:no-route` (7) >
`:busy` (8) > `:expired` (9) > `:accepted` (0), with `fn-bpn-host-exit-code`
the mapping, called by `fnn-bp-exit-code` and `fnn-bps-exit-code`; count
held, busy and expired answers in the tally from the effects ACL2 already
emits; clock-domain disagreement (10) at `fnn-bps-open`'s fence; update
specs/host.md's table, docs/operator.md, and the native expectations in
test_bp_contact_native, test_bp_service_native, test_bp_contact_relay_native,
test_bp_app_native, test_bp_node_native and test_bp_receive_integrity_native.

### What a node can now do

- Reassemble a fragment family with no fragment-count or ADU-length check
  in the reassembler, in work O(n log n + total + the octets held), and
  choose among families planning each at most once per host call; on the
  image, a 64-fragment family (the held-row capacity) survives a SIGKILL
  mid-family and is reassembled and handed to the Store exactly once.
- Rotate and retire its journal generations while a family is in flight,
  killed at the rename and inside retirement, without losing a held
  fragment; the family completes afterwards.
- Replace a family (kind 18) knowing, by proof over the served step, that
  under the jobs relation no consumed row had an unfinished job.

### Not done (the continuation's honest list)

- **SCN-067 (70 fragments) is blocked** by `*fn-bpn-machine-max-jobs*`
  (64 held rows); skipped with the reason. No constant was raised.
- **The 10 MiB transfer** stays blocked by the ADU record's cap
  (`*fn-bpa-max-octets*`, 65,538), the bundle decoder's 1 MiB input
  (`*fn-bpb-max-input*`), the held-image cap and the held-row capacity.
  PKT-171 recommends P5 (constants into the profile), not raising them.
- **Item 3, the rest**: the relation's establishment by recovery replay
  and its preservation by the non-family arms (the issued-record invariant
  above); the wider job-table relation over kind-8 attempts, retry counts,
  stranded rows and resume (the first session's design) is untouched.
- **Item 4, distinct exit codes**: not started; design and the conflation
  point above.
- **N16 §3.6** (chunks, kind-21 manifest, `:quiesce`): for a later lane.
- EIO at every cut of a large transfer: not run.
