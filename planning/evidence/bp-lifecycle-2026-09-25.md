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
- Natively, a family of 70 fragments is reassembled once and handed off
  once, with the receiver killed by SIGKILL after fragment 35 (SCN-067;
  results below). 70 is beyond the old 64-fragment ceiling.

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

**Observed.** SCN-067 natively (below).

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

The lane's books are all under 10 s at two jobs (manifest below). Moving
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
6. the reassembler (now uncapped).

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
