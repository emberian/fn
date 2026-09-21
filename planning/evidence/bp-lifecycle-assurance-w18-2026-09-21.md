# W18 BP lifecycle authorization proof transcript

The certified functional source is commit
`ff80403ea5ae54a899d8ca7a194f621bfde2affc` on
`w18/bp-lifecycle-assurance`.  The theorem subject is the function the
native host calls: `fnn-bps-step` calls `fn-bpn-step` directly at
`host/native/bp-service.lisp:102`, installs its returned state, and returns its
effects.

`fn-bpn-lifecycle-invariantp` combines valid bounded machine state with an
exact pending-proposal relation.  For each pending record that relation fixes
the success, refusal, and uncertainty effects.  An `:attempting` proposal is
bound to the retained job's exact route, peer, key, and wire; a `:queued`
proposal is bound to the exact durable queue acknowledgement.  The actual
dispatcher establishes or preserves the relation through initial state,
enqueue, contact/resume, persistence results, forward results, expiry, and
restart.

The named keystones are:

* `fn-bpn-step-preserves-lifecycle-invariant`, under a maintained
  `fn-bpn-lifecycle-invariantp` input and a `fn-bpn-machine-eventp` event;
* `fn-bpn-step-cl-send-is-authorized-by-durable-attempt-record`, under the
  lifecycle invariant and the observation of a `:cl-send` effect;
* `fn-bpn-step-queue-acceptance-is-durable-or-exact-duplicate`, under the
  lifecycle invariant and the observation of queue acceptance;
* `fn-bpn-step-effects-are-typed`, with no output-typing premise;
* `fn-bpn-step-emits-no-release-from-actual-effects` and
  `fn-bpn-step-emits-no-receipt-prepare`, both unconditional over the actual
  dispatcher effects.

The queue theorem keeps its two authorities distinct.  A new `:durable`
acceptance follows only from a matching durable `:queued` pending record.  A
`:duplicate` acknowledgement requires an already-retained exact job with the
same work, attempt, generation, sequence, route, peer, bundle, and wire.

The test book constructs a reachable non-degenerate execution through
enqueue, durable queued-record publication, contact, durable attempting-record
publication, exact `:cl-send`, uncertain transport, durable requeue, and
restart from the durable queued and attempting records.  The restarted job is
queued with the same work key, peer, route, bundle, wire, age anchor, and
sequence.  Its four `must-fail` teeth remove, respectively, the maintained
input invariant, the 4096-record restart-event bound, pending send
authorization, and pending acceptance authorization.  The latter two start
from well-typed machine states and emit the forbidden fabricated effect, so
effect typing alone cannot satisfy either authorization claim.

The owned certification command was:

```sh
python3 tools/farm.py --jobs 4 --closure --timeout-seconds 600 submit HOST \
  books/bp-node-machine-authorization \
  tests/acl2/bp-node-machine-authorization-tests
```

The recovered hbox manifest
`certify-20260921T112003Z-2095559.json` records a passed 17-of-17 source
closure in 937.437 seconds with 16 slots and ACL2 8.7.  Every recorded source
digest matches `ff80403e`, including the authorization book and its test book.
The manifest's `git_revision` is null, so this statement rests on those exact
per-file digests rather than an inferred checkout name.  The executable was
`/tank/fn/acl2-8.7/saved_acl2`, SHA-256
`64030dda0b03bbb6cf50984889f5ce1e2ba867b6ce3c9a65403afc44f9b4fdb5`.

A duplicate persvati attempt, manifest
`certify-20260921T112252Z-3226604.json`, failed after
`books/bp-primary-invariants` exceeded its 600-second per-book timeout.  Its
17 recorded source digests also match `ff80403e`; it passed the other 16 roots.
That timeout is retained as a failed duplicate attempt and does not replace or
extend the exact hbox result.

The host bounds the lifecycle namespace to
`fn-bpn-host-machine-max-records` before reading frames and therefore before
constructing `(:restart records sequence-ready)`.  It bounds each frame before
ACL2 decoding.  Other event arms are validated by `fn-bpn-step`; retained job
count and octets remain bounded by the machine state's configured
`max-jobs`/`max-octets`.  The new predicates are logical proof invariants and
add no whole-state recognizer call to the served native path.

This packet treats the host's `:durable`, `:refused`, and `:uncertain`
publication observations as explicit inputs.  It does not prove filesystem,
kernel, device, or power-loss behavior; peer honesty; or transport delivery.
Those physical claims remain under `A-DURABILITY` and `A-WRITE-ISOLATION` and
the native publication correspondence.  It proves confinement only for this
outbound lifecycle machine's effects: transport completion and expiry cannot
emit `:release` or `:receipt-prepare`; it does not claim application delivery.
No native image, full gate, deployment, or network interoperability matrix was
run in this lane.
