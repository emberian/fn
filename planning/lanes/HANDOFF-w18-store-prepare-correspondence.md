# W18 live-store prepare correspondence handoff

## Source packet

Branch `w18/store-prepare-correspondence`, implementation commit `41dfd02`,
based on frozen `76901c1`. The substantive files are:

* `books/store-prepare-correspondence.lisp`
* `tests/acl2/store-prepare-correspondence-tests.lisp`
* `host/store-node-host.lisp`
* `Makefile`
* `docs/prefixes.md`
* `specs/store-refinement.md`
* the PRF-001, PRF-014, HST-004, and SCN-015 registry updates

The ledger files are generated and should be regenerated after integration.
The evidence record is
`planning/evidence/store-prepare-correspondence-w18-2026-09-21.md`.

## What lands

`fn-store-sn-prepare`, the actual wrapper called by `fnn-bridge-prepare`, now
calls `fn-spc-prepare`. Its executable body omits only the
`fn-sf-history-recoverablep` replay of the appended candidate history. It
retains the exact local candidate-counter, record, phase, empty-stage, and
pending-node binding checks. It adds no host cache, raw semantic twin,
relation test, whole-state recognizer, assumption, trust tag, `skip-proofs`,
or `defaxiom`.

The exact correspondence is
`fn-spc-prepare-equals-specification-under-relation`. The proof bridge is
`fn-spc-related-candidate-is-recoverable`; preservation is carried through
the actual post-open mutation family by `fn-spc-step-preserves-relation` and
`fn-spc-run-preserves-relation`; successful observed open establishes the
hypothesis in `fn-spc-observed-open-run-maintains-relation`. Recovery remains
the replaying authority.

The test book's reachable witness has one durable record before the optimized
prepare. The separating tooth uses the same nonempty files with a stale empty
node: it is structurally valid but not related, and the fast/specification
results differ. Wrong-sequence and pending-binding refusal witnesses pin the
executable checks that remain.

## Validation

* Clean implementation commit: `certify-20260921T094728Z-56739`, both owned
  roots passed with ACL2 8.7/SBCL 2.6.8.
* Current-main overlay at `399d4730`:
  `certify-20260921T094840Z-57318`, 36-book closure passed, including the
  newer staging-sweep limit; targeted host check loaded
  `host/store-node-host.lisp` alone (`1/1`).
* Production saved image built; all seven
  `tests.test_native_storage_codec` tests passed in 24.299 seconds.
* Matched test-only scale image: 50 sequential commits took 3.5060 seconds
  total; 400 took 31.1020 seconds total. This is 8.87 times total work for
  eight times the records on this Mac, versus W16's 98.6-fold total increase
  on its Linux host. The evidence record preserves the platform distinction
  and makes no cross-host absolute-time or asymptotic claim.
* `make check` passes. Full `host_check.py` still reports unrelated existing
  host files; the affected `host/store-node-host.lisp` passes targeted load.

## Join notes and open scope

Main changed `books/store-sweep.lisp` and added native staging wrappers after
this lane forked. Those changes are semantically covered by the existing
`:sweep-staging` arm and its preservation theorem; the current-main overlay
certifies. The checkpoint callback mutates private native recovery globals
after authoritative replay and does not alter the installed ACL2 store state.

The implementation and main both edit `Makefile`, `host/store-node-host.lisp`,
the registries, specifications, and generated ledgers. The host additions are
orthogonal: retain main's staging-observation wrappers and add the new include
plus the one prepare-call replacement. Merge registry prose by meaning, then
run `python3 tools/ledger.py --write`; do not resolve generated ledger files by
choosing either side.

Native owner embedding remains a separate obligation and is not claimed by
this packet. The retained `fn-sf-candidatep` and node preparation may still
scan retained state, so the two-point probe is not a whole-path complexity
proof. Full recovery replay, refusal, and ambiguous-persistence handling stay
unchanged.
