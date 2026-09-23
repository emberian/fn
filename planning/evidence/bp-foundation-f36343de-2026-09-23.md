# Finite BP A1 foundation, 2026-09-23

Source: `implement/bp-foundation` `f36343de` from `df5097b6`.
The checked host entry remains `host/native/bp-service.lisp:110-116` to
`fn-bpn-step`. The new `fn-bpnf-step` is a named, unhosted refinement of that
outbound step and a validated-bundle reception kernel. It does not claim the
native BP receive path, FNBS publication, replay or two-process round trip.

The schema is in `books/bp-node-foundation.lisp`. Its held row keeps admitted
ingress principal, RFC bundle id, arrival, ingress provenance, submission,
lineage, exact bundle and wire, anchor, dispatch, next hop, constraints,
attempt, deletion and token in distinct slots. `fn-bpnf-outcome` and
`fn-bpnf-handoff` are separate authoritative shapes; the correlation slot is
separate and evictable in the future machine. `fn-bpnf-operation` contains a
process epoch and operation id, which must both match a publication callback;
the state owns a monotone `next-op` and allocates the id on proposal, so no
caller chooses or reuses it within an epoch. Its status distinguishes pending
from uncertain. `fn-bpnf-wait` names an
obligation, action, dependency, observed version and condition. The wait
predicate invalidates a cached decision when the named version changes; it
does not yet prove full action eligibility or a wake-up liveness claim.

The proved safety facts are scoped to this kernel:

- `fn-bpnf-base-step-is-fn-bpn-step`: with no issued operation, the base
  projection of a `(:base event)` step equals the actual `fn-bpn-step` result.
  This is a bridge, not a new host call.
- `fn-bpnf-other-principal-does-not-match`: a single held entry under a
  different admitted principal cannot make reception a duplicate or conflict
  for the incoming principal. The test constructs two valid bundles with the
  same RFC identity and different payload, admits one principal, and checks
  the other principal is fresh for both variants before durably installing its
  own copy. Ingress principal is assumed already admitted; neither the
  announced peer EID nor the source EID selects it here.
- `fn-bpnf-receive-proposal-does-not-install-held`: an incoming valid bundle
  proposes publication without changing held evidence.
  `fn-bpnf-stale-publication-does-not-install-held` and
  `fn-bpnf-install-requires-matched-durable-publication`: an installation
  requires a matching epoch and operation id, a durable outcome and a pending
  operation. The test checks an old epoch and wrong id leave state/effects
  unchanged, while the matching durable callback stores the held row.
- `fn-bpnf-stale-operation-cannot-match` and
  `fn-bpnf-unchanged-dependency-does-not-wake` establish the exact correlation
  and unchanged-version branches. The tests show matching operations and a
  changed route generation as their counterexamples.
- `fn-bpnf-uncertain-issued-fences-every-step`: an issued operation marked
  uncertain leaves the state unchanged under every ordinary event, including
  a later matching `:refused` or `:durable` callback. The reachable test follows
  uncertain → late refused → another receive and checks the receive is still
  busy, with no accepted held entry. A still-pending operation is the negative
  tooth: its matching refused result does change the state.
- `fn-bpnf-receive-proposal-consumes-next-operation-id` and
  `fn-bpnf-next-operation-id-never-decreases`: a proposed receive carries the
  state's current id and increments it; no step lowers the frontier. A
  definite refusal followed by another receive issues id 1 after id 0, and
  a late callback for id 0 cannot complete the new operation. An invalid
  receive with no proposal is the exact negative for the first theorem's
  `:persist` hypothesis.

The kernel bounds an admitted image at 131,072 encoded octets and checks live
slot and byte capacity before proposing. An issued operation fences both
new reception and delegation to the outbound base machine. An uncertain
callback leaves its issued record for recovery and installs no held entry.
An uncertain operation has no ordinary resolution transition; A2 must add
an explicit recovery transition after inspecting FNBS authority. The process
epoch is separate from the operation frontier and from journal generation.
The tests include the exact-wire refusal and a live-slot capacity refusal.
No whole-held-list recognizer runs at the step entry; the individual incoming
bundle and its encoded wire are validated on that event. The foundation has
not yet been wired to a bounded octet decoder or a journal credit budget.
The book sets guard-verification eagerness to zero and has no `verify-guards`
events for the new functions. Certification admits their logic but does not
verify their guards. They are not ready for a native host call.

Evidence: `python3 tools/farm.py submit hbox books/bp-node-foundation
tests/acl2/bp-node-foundation-tests --jobs 2 --timeout-seconds 300
--remote-root /tank/fn/gates/takeover-bp-foundation --acl2
/tank/fn/toolchains/w28/acl2-literal-4g --cache /tank/fn/certcache`, run
`run-20260923T143554Z-55f9`, manifest
`planning/evidence/manifests/certify-20260923T143556Z-3860868.json`.
ACL2 8.7 on SBCL 2.6.8, toolchain identity
`d5f2b9f0d2cf68c6074ea7046f4bd2e560d2984fe22d7e03f93045975ac889f0`.
The manifest reports both requested roots passed in 3.749 seconds at the
recorded source digests, with 26 dependencies installed from the matching
cache. The earlier
`run-20260923T141801Z-5993` was interrupted on a 311-second accidental
unfold of `fn-bpn-step` in the bridge proof; disabling that unrelated body
reduced the bridge to a 0.01-second proof in `proof_repl`. The intermediate
`run-20260923T142534Z-64cf` passed before the uncertainty and operation-id
repair and is superseded; `run-20260923T143245Z-1dce` passed before the
theorem naming correction. At the final source the book digest is
`a24961a300fbee5e15fbc22b3cbb5f15ea5c90db9fa7c58312b9b3b1d3752913`
and the test book digest is
`604d455bb50437507e3578e3785f08e4a22ad6dc887962d84dea7f64b4346f7f`.
`green_check.py --changed-since df5097b6 --strict` reports
both changed roots green and no ungreen changed root. `make check` passed
after local ledger regeneration. The generated ledger/registry changes are
left to root's integration batch.

For A2, the interface to refine is the issued tuple
`(epoch, state-allocated-operation-id, :store, held, :pending/:uncertain)`,
its `:persist` effect, the monotone `next-op` frontier and the matched durable
installation. An uncertain tuple is recovery-only: a later callback cannot
clear it. Recovery must establish a new process epoch and a non-reused
operation frontier from authoritative bytes before the service issues work.
A2 needs an FNBS-specific
publisher relation over encoded kind-5 records and `fn-bs-crash-imagep`,
with inherited-prefix versus current-epoch delta stated explicitly. The
article Store K3/K4 theorems do not instantiate that byte relation. The
zero-event recovery, visible record after uncertainty, and distinct byte
crash choices remain open tests. This foundation also leaves outcome and
handoff transitions, post-discard deduplication, dependency-complete wakes,
fragment family actions, journal debt, principal admission, application
receipts and the TCPCL final-ACK path open. The N04/N05 fixture descriptions
in `specs/bp-node-machine.md` are corrected and expressly remain open until
the corresponding transition and exact witnesses certify.
