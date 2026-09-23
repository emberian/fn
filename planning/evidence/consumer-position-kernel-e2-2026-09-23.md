# E2 consumer-position decision kernel, 2026-09-23

This packet adds [`books/consumer-position.lisp`](../../books/consumer-position.lisp)
and [its executable teeth](../../tests/acl2/consumer-position-tests.lisp).
It is an **unserved, non-durable leaf kernel**. No host line calls it, and no
Store record kind persists its proposed events. The selected E2 contract is
[`specs/consumer-progress.md`](../../specs/consumer-progress.md); the
sleeping-agent and crash traces remain specified but unexecuted.

The v1 cursor codec accepts only at most 512 octets, checks octets before
parsing, rejects unknown version/trailing bytes, and has five nonempty IDs of
at most 64 octets plus four unsigned 32-bit fields. A concrete all-maximal
cursor encodes to 346 octets and round-trips. There is no general certified
round-trip or length theorem yet. This profile does not seal cursor fields;
its authenticated transport and eventual caller binding remain open.

`fn-cp-register`, `fn-cp-ack`, `fn-cp-rebase`, and `fn-cp-unregister` return
`:write` event proposals, `:no-op`, or `:refused`. `fn-cp-apply` is the
projection after a hypothetical committed proposal, never a publication
decision. The certified decision keystones say: an ack proposal cannot pass
the state's committed frontier; it carries the current registration epoch;
and a cursor with another epoch is refused before mutation. The apply
keystones say applying any event leaves the committed frontier untouched,
advances the scalar next epoch by zero or one, and preserves the 256-entry
table bound if it held before the event. That final bound uses the lemma that
removing a found consumer strictly decreases entry count. These properties
concern the leaf functions named here, not a host-called owner step.

The test book reaches register, ack, equal-ack no-op, backwards/future/scope
refusal, rebase, unregister and re-register with a delayed stale ack. It also
reaches capacity through 256 distinct successful registrations, rebases at
capacity, tests the 346-octet maximal cursor, and checks malformed, trailing,
unknown-version, overlong and overlong-ID inputs. `must-fail` forms remove
the write-arm premises, the stale-epoch mismatch and the initial capacity
bound; the positive witnesses execute the write arm. The codec's general
canonicality and parser work theorem, state recognizer/guard verification,
arbitrary-trace preservation, and physical persistence remain open.

The source-matched farm run was
[`run-20260923T172803Z-cdcd`](manifests/certify-20260923T172805Z-2201463.json)
on persvati, ACL2 8.7 / SBCL 2.6.8, executable SHA-256
`346b7ee183e8c291cb61cf31be75a332caf329fa74b4995921cbb224208f2c08`,
toolchain identity
`1b4169e9c5825a4e1fc827767f00470ceafc459619e0a4fd522c48f1ba964286`.
Invocation: `python3 tools/farm.py submit persvati --jobs 2 --remote-root
/home/ember/fn-lanes/consumer-kernel --cache /home/ember/fn-certcache
books/consumer-position tests/acl2/consumer-position-tests`; incremental,
no closure, zero roots installed from cache, both certified. The source
SHA-256 digests in that manifest are
`401009253a40b889ad91d68e727827f0cd88bd61a94b43992abec1e6d510eba6`
for the book and
`470a100b891ce4f6e49d286864adddf199f15f6c3e3cd1cab710af61c3a823f0`
for the tests. The snapshot started from `83232c83` with lane changes;
the manifest's `git_revision` is null, so the content digests identify the
tested bytes. Local ACL2 certification of both roots also
passed at `build/acl2/certify-20260923T172734Z-79466`.

`make check` failed only on two missing manifest targets cited by the
preexisting `planning/evidence/store-identity-sequence-t4-2026-09-23.md`:
`certify-20260923T170608Z-2002708.json` and
`certify-20260923T170852Z-2027792.json`. Both targets were already absent
at this lane's base `83232c83`; the lane did not alter that evidence file.
`python3 tools/ledger.py --write` regenerated the ledger for the new book and
test roots.

Store integration order is concrete: add a versioned consumer event kind and
codec to `books/store-events.lisp`; route sequence and txid through the one
Store namespace; replay the global epoch/entries through
`fn-replay-apply-record`; join Store prepare/finish/observed open and
checkpoint/compaction migration; then expose an owner wrapper beside
`fn-owner-chunk` in `host/owner-host.lisp` that the native host actually calls.
Only durable completion may turn `:write` into `accepted`; an ambiguous
publication fences requests until recovery. Store restoration must change
incarnation unless it proves the same prefix mapping. The future owner policy
projection supplies query/view versions, and its poll scan supplies candidate
positions. The process-death cuts and two-database observations are named in
the contract and trace file. No server API, image or node operation was run.
