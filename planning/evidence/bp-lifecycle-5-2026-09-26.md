# bp-lifecycle-5 (wave 2, 2026-09-26): one BP arrival costs its fragment, not every held bundle

Lane `lane/bp-lifecycle-5` from dev `7f7f980c` (continuation of bp-lifecycle-4;
dev merged in at `8fdd7890`, store books only). Brief:
`build/coordinator/queue/w2-bp-lifecycle-5.txt`. Ids: PRF-136, PKT-308;
SCN-077 (existing). Model: Opus 5.5.

Commits: `7f743ab0`, `1ce7422a`, `248ec666` (the measurement instrument),
`f72f258d` (the selector), `3466cb10` (delivery and report scans, registry,
specs), `cfa9140f` (a slow lemma; r1 manifest), `aec4a14a` (the expiry scan;
r2 manifest), `45e63b0e` (a slow guard; r3 manifest), and the record commit.

## What now works

A BP node's `bp-node serve` session with a fragment family in flight costs
about 60 ms at any held-row count measured (64, 128, 256), where it cost
3.7, 6.8 and 15.9 s; nothing on the session path re-encodes a held bundle
per row any more. Before, each session re-encoded every held row eight times:
five in the family selector and three in the post-session scans for local
deliveries, received status reports and expired carriers.

## Measured first (item 1)

Instrument: the developer selector `FN_BP_TEST_PROFILE="64 128 256"` (developer
image only; `host/native/bp.lisp`, `fnn-bp-profile-*`) wraps every executable
counterpart of a BP function and the named raw functions in SBCL's
deterministic profiler and, after a `bp-node serve` session whose arrival
leaves that many rows held, prints the session's and the arrival's wall time
and the call table. The driver (`/tank/fn/scratch/bp-lifecycle-5/profile.py`,
subclassing `tests/test_bp_fragment_node_native.py`) authors SCN-077's
10,486,094-octet ADU as 2,622 fragments, raises the profile (4,096 rows,
16 MiB held, 11 MiB ADU, 1 MiB bundle) and sends the first 257 in SCN-077's
order (descending offset, so offset zero is not held), four `tcpcl send`
workers into one receiver. hbox, DTN developer image, `systemd-run --scope -p
MemoryMax=24G`. Profiler overhead is included in every row, before and after.

Session wall time, arrival wall time (ms) and `fn-bpb-encode` calls per session:

| held rows | before (tree `before248`) | after the selector (`248ec666`) | after the scans (`3466cb10`) | after the expiry scan (`aec4a14a`) |
| --- | --- | --- | --- | --- |
| 64 | 3,679 / 2,348 | 1,396 / 64 | 922 / 63 | 57 / 55 |
| 128 | 6,807 / 4,296 | 2,488 / 58 | 2,124 / 75 | 58 / 57 |
| 256 | 15,880 / 9,882; 2,054 encodes | 5,804 / 74; 775 encodes | 3,372 / 60; 519 encodes | 72 / 71; 7 encodes |

`before248` is `248ec666`'s tree with `1ce7422a`'s bp-node-fragment-step,
-guards and -step-tests (the selector before this lane; the same instrument).
At 256 rows before: `fn-bpb-encode` 2,054 calls, 15.7 s of 15.9 profiled
(6.4 to 7.6 ms per 4 KiB bundle), `fn-bpnf-heldp` 2,051: eight per row. The
`*1*` guard checks the host's calls make are not a cost:
`fn-bpn-machine-statep` 16 calls, under 1 ms in all (the record's inference
of a whole-table guard check per call is refuted; the guards check the base
machine and `true-listp` of the held list). `fn-bpnf-held-octets` (the receive
step's walk of each held wire's length) is 1.6 to 2.0 ms at 256 rows.

The per-arrival rows from `7f743ab0`/`1ce7422a` (deliver only) agree: 1,955 /
3,968 / 8,487 ms and 2,394 / 4,091 / 8,000 ms at 64 / 128 / 256 rows before;
67 / 64 / 62 ms after the selector (`f72f258d`).

Where the eight came from: `fn-bpnf-family-next`'s memo asked
`fn-bpnf-active-fragmentp` (whose `fn-bpnf-heldp` re-encodes) of every row
and `fn-bpnf-same-fragment-family-p` (two more) of every row in the tried
check and the active set: about five per row. After the session,
`fnn-bpnode-dispatch-pending`'s `fn-bpah-select-oldest-at` and
`-uncertain-at` ask `fn-bpah-local-pendingp` per row and
`fnn-bpnode-observe-reports`'s `fn-bpn-report-observe-next` asks
`fn-bpn-report-observe-held` per row (three), and
`fnn-bpnode-delete-expired`'s `fn-bpn-report-find-expired-held` asks
`fn-bpn-report-held-delete-pendingp` and `fn-bpah-held-expiry` per row (two,
visible once the other six were gone).

Logs (`/tank/fn/scratch/bp-lifecycle-5/logs-REV/profile-table.txt`):
before248 `f71d78a5…`, 248ec666 `583caa3c…`, 3466cb10 `b2aec955…`,
aec4a14a `317d4a20…`; 1ce7422a `cc5ed06b…`, f72f258d `40c8c264…`,
7f743ab0 `7414688c…`.

## The fix (item 2) and PRF-136

No maintained state index: every change is an executable body that answers
exactly what the existing definition answers, proved, with the host still
calling the same function.

- **The selector** (`books/bp-node-fragment-step.lisp`). Host
  `fnn-bps-fragment-progress` (host/native/bp-service.lisp; called by
  `fnn-bps-receive` after each accepted arrival and by `fnn-bps-open`) calls
  `fn-bpnf-family-next`, whose `:exec` is now `(fn-bpnf-family-select st
  (fn-bpnf-held-list st) observation nil (fn-bpnf-zero-family-keys
  (fn-bpnf-held-list st)))`. One pass reads each row's primary block and
  collects the family keys (principal, ADU key, coherence key) of the
  offset-zero candidates; the walk plans a row, which re-encodes it and
  reassembles its family, only when the row's family key is among them, and
  remembers a planned family that is not ready by its key.
  - `fn-bpnf-family-select-is-aux` (keystone): with HELD a subset of the held
    list, TRIED satisfying `fn-bpnf-family-keys-not-readyp` (every active row
    whose key is tried has a plan that is not ready; true of nil,
    `fn-bpnf-family-keys-not-readyp-of-nil`) and ZERO the held list's
    offset-zero keys, the select equals `fn-bpnf-family-next-aux`, anchor
    included. The maintained relation is the call's own: TRIED is
    established empty by the host's call and preserved by each step of the
    walk (planned and not ready, `fn-bpnf-family-plan-at-of-member`); ZERO is
    computed from the held list at the call. Nothing is carried across calls,
    so no transition has to preserve anything.
  - `fn-bpnf-family-without-zero-key-is-not-ready`: a held active row whose
    family key has no offset-zero candidate is not ready (from PRF-134's
    `fn-bpnf-family-without-offset-zero-is-not-ready`, through
    `fn-bpnf-active-fragment-is-candidate` and the key equality).
  - `fn-bpnf-family-select-plans-bound` (keystone, the work bound): the rows
    the select re-encodes and plans are at most the candidate rows whose
    family key is in ZERO. `fn-bpnf-family-select-steps-bound` (keystone): a
    call that plans no row makes at most |held| x (1 + |zero| + |tried|)
    header steps; `fn-bpnf-zero-family-keys-bound`: |zero| <= |held|. The
    counting functions (`fn-bpnf-family-select-plans`, `-steps`) follow the
    select's own control flow, the way books/article-work-primitives count.
  - The plan's own work is PRF-121's (`fn-bpfw-reassemble-is-spec`: linear in
    the family's octets); PRF-134's profile theorems are unchanged.
- **The post-session scans**, each an `mbe` whose `:logic` is the existing
  body (every statement about it unchanged) and whose `:exec` asks a header
  question first:
  - `fn-bpah-local-pendingp` (books/bp-app-handoff.lisp; host
    `fnn-bpnode-dispatch-pending`): `fn-bpnf-held-nonfragment-headerp`;
    `fn-bpah-local-pendingp-has-a-nonfragment-header`.
  - `fn-bpn-report-observe-held` (books/bp-report-observe.lisp; host
    `fnn-bpnode-observe-reports`): `fn-bpnf-held-administrative-headerp`;
    `fn-bpn-report-observe-held-needs-an-administrative-header`.
  - `fn-bpn-report-find-expired-held` (books/bp-report-deletion.lisp; host
    `fnn-bpnode-delete-expired`): `fn-bpah-held-expiry-header`, the same
    clock decision read from the primary block and the anchor
    (books/bp-app-handoff-time.lisp); `fn-bpah-held-expiry-header-of-held`
    equates it with `fn-bpah-held-expiry` on every held row.
  - `fn-bpnf-heldp-primary-blockp` (books/bp-node-foundation.lisp): a held
    row's primary block is a block, which is why each prefilter refuses only
    rows the definition refuses.
- Guards: every new executable function is guard verified
  (bp-node-fragment-guards, bp-node-foundation, bp-app-handoff,
  bp-app-handoff-time, bp-report-guards, bp-report-deletion); no raw-Lisp fast
  path, no host decision, no data cap.

## Teeth

- tests/acl2/bp-node-fragment-step-tests: the host's call on the family
  fixture (p3, q3, pbad, p0, deleted, consumed): all three hypotheses hold
  and select, reference and `fn-bpnf-family-next` answer `(:ready 0)`. Per
  hypothesis, a witness that checks the other two, the omitted one false and
  the answers different: ZERO nil; p3's ready family marked tried; a
  non-held copy of p3 (another token) ahead of the held list. Plans bound:
  one row planned of the two in offset-zero families; the SCN-077 shape
  (offset zero not held) plans none. Steps bound: one row, one step; without
  the no-plan hypothesis, p0's family alone planned and tried makes the next
  row's comparisons exceed the bound (5 > 4).
- tests/acl2/bp-app-handoff-tests: the pending request carrier is
  local-pending with a non-fragment header; the held fragment carrier has
  neither.
- tests/acl2/bp-report-observe-tests: a non-administrative carrier is no
  report; the held status report has an administrative header and is
  observed.
- tests/acl2/bp-app-handoff-time-tests: on a held carrier the header decision
  is the decision (`:live`); the same row with its wire dropped is not held,
  the definition answers `:uncertain` and the header still `:live`.

## Certification (hbox, w28 acl2-literal-4g, 2 jobs, 300 s)

| run | rev | manifest | result |
| --- | --- | --- | --- |
| r1 `run-20260926T061624Z-8e15` | 3466cb10 | `certify-20260926T061654Z-546487.json` | 139 certified, 0 failed; bp-node-fragment-step 13.9 s (6.2 s in `fn-bpnf-zero-family-keys-bound`, fixed in cfa9140f) |
| r2 `run-20260926T062827Z-80e6` | cfa9140f | `certify-20260926T062922Z-582231.json` | 56 certified, 0 failed; no book over 10 s |
| r3 `run-20260926T063236Z-7f31` | aec4a14a | `certify-20260926T063303Z-591565.json` | 81 certified, 0 failed; bp-app-handoff-time 20.8 s (the defun verified its own guards, 19 s; fixed in 45e63b0e) |
| r4 `run-20260926T063830Z-8cee` | 45e63b0e | `certify-20260926T063856Z-608753.json` | 81 certified, 0 failed; no book over 10 s (every book this lane changed is certified at its final bytes across r2 and r4) |

## Native (item 3; hbox, /tank/fn/scratch/bp-lifecycle-5, `native.sh aec4a14a`)

NATIVE_SECTION

## Assurance chain

Native entry `fnn-bps-receive` (after kind-5 custody) and the session loop in
`fnn-command-bp-node` → executed ACL2 subjects `fn-bpnf-family-next`
(`:exec` `fn-bpnf-family-select`), `fn-bpah-select-oldest-at`/`-uncertain-at`
(per row `fn-bpah-local-pendingp`), `fn-bpn-report-observe-next` (per row
`fn-bpn-report-observe-held`), `fn-bpn-report-find-expired-held` →
refinement: guard-verified `mbe` equalities, `fn-bpnf-family-select-is-aux`
with `fn-bpnf-family-next-memo-is-aux` → maintained relation: the select's
TRIED invariant, established empty at each host call, preserved per step →
behavioural theorems: PRF-121's reassembly spec, PRF-134's family readiness,
the plans and steps bounds → observed: the session rows above and SCN-077.

## PKT-294 item 1, retired by name

`fn-bpnf-family-select-is-aux`, `fn-bpnf-family-select-plans-bound`,
`fn-bpnf-family-select-steps-bound` (the selector), and
`fn-bpah-local-pendingp-has-a-nonfragment-header`,
`fn-bpn-report-observe-held-needs-an-administrative-header`,
`fn-bpah-held-expiry-header-of-held` (the session's scans).

## PKT-308: found and not finished

1. A family whose offset-zero fragment is held is planned on every arrival
   until it is complete (PKT-294 item 2): a family arriving in offset order
   costs its octets per arrival. A coverage precheck needs either a
   maintained per-family extent sum or the pigeonhole lemma (sum of extents
   below the total ⇒ not covered); neither is done. SCN-077 sends in
   descending offset order, which this lane made cheap.
2. The receive step still walks every held wire's length
   (`fn-bpnf-held-octets`, 1.6 to 2 ms at 256 rows of 4 KiB) and compares
   every held key (`fn-bpnf-find-held`); a maintained octet count would make
   it constant. Outside PRF-136.
3. The work bound is a theorem about the selector's executable body and the
   three scans' prefilters; there is no single counting theorem over a whole
   `bp-node serve` session.
4. PKT-309 to PKT-311 (sender job image, resumable decode, profile edges) and
   tools/run_bp_receive.py's 65,538 are untouched.

## Also done

specs/bp-node-machine.md no longer cites the retired `fn-bpn-limits-compose`
(four places, and the D-9 row now says the ADU bound is the profile's ADU
octets since 9ebf5f0e): PKT-312's citation half, `3466cb10`.
