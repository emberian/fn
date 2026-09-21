# W18 BP lifecycle shared publisher handoff

Functional source: `668130deebba1cf37ed02d3e13029ddd868e99f1`

`fnn-bps-persist-record` now executes the same ACL2-owned immutable
no-replace publication machine as the application journal, BP receive evidence,
and checkpoint candidate publisher.  The BP-specific authorization is
`fn-bpn-lifecycle-publication-authorize`: it accepts only the exact token and
record currently pending in the host-called `fn-bpn-step`, requires that token
to equal the machine frontier, and records the trusted host observations that
the lifecycle lock is held and the canonical final name is absent.  The host checks
the returned token/record echo, invokes `fnn-immutable-publish-effect`, and
passes its result unchanged back as `(:persist-result token outcome)`.

Outcome boundaries are now the shared `fn-jpub` boundaries:

- stage creation/write or staged-file barrier failure is `:refused` because no
  final-name mutation was attempted;
- any non-EEXIST link error or final-directory barrier error after link begins
  is `:uncertain`; a visible equal final is not inspected to infer durability;
- durability is established by the successful final-directory barrier;
- stage unlink and its cleanup-directory barrier are post-authority best
  effort.  Their failure does not retract `:durable`.  This is safe for the BP
  lifecycle namespace because its bounded recovery plan explicitly retains
  hidden stage evidence and ignores it when reconstructing the contiguous
  committed-record frontier.

This is an intentional refinement of the former conservative cleanup-barrier
uncertainty.  The first, authority-establishing final-directory barrier still
returns `:uncertain` on failure.  A cleanup-only barrier failure after that
successful authority barrier returns `:durable`.  Clean runs still unlink the
stage and barrier the cleanup directory; a cleanup failure can only leave
bounded hidden evidence and cannot make the already-barriered final record
ambiguous.

The authorizer declares `fn-bpn-machine-statep` as its guard and retains that
recognizer as its logical premise, while an `mbe` executable branch consumes
the service's maintained machine invariant instead of traversing all retained
jobs and obligations per publication.  The machine recognizer itself does not
have verified guards, so this packet does not claim a new guard-verification
event for the authorizer.  The
native service installs only initial/recovered states and answer states returned
by `fn-bpn-step`.  PRF-046 is expected to supply the preservation theorem for
that host-called step; it was still in the wire-composition lane when this
packet froze, so this packet does not claim that theorem as its evidence.

Sharing the `fn-jpub` interpreter establishes the outcome boundaries described
above; it is not a claim that every raw host phase has a complete model.  The
lock-held and final-absent inputs are trusted observations supplied by the
native service, not unforgeable capabilities.

Evidence:

- `planning/evidence/manifests/certify-20260921T100625Z-2012954.json`: hbox,
  ACL2 8.7, source-pinned certification of
  `books/bp-node-machine-codec` and `tests/acl2/bp-node-machine-tests`, both
  passed.  Teeth cover the exact pending token/record echo, lock ownership, and
  final-name absence.
- `planning/evidence/native-host-build-w18-bp-publisher.log`: DTN saved-image
  build on hbox from the functional source.  The initially missing integrated
  `bp-receive-evidence` certificate was installed with the separate targeted
  passing manifest `certify-20260921T095758Z-1999525.json`; no image-wide
  closure was launched for this packet.
- `planning/evidence/native-bp-publisher-w18-tests.log`: 11/11 actual BP
  service tests passed.  The production action loop reaches stage refusal,
  final-directory uncertainty followed by restart, cleanup-barrier durability
  followed by restart, and the existing core-fault exit-4 path.
- `planning/evidence/native-bp-publisher-w18-shared-tests.log`: 11/11 native
  application-journal and BP receive-integrity tests passed against the same
  image, covering the other live consumers of the shared executor.

The packet changes no wire effect or durability event vocabulary.  PRF-046 can
continue to reason about the exact `:persist token record` request and
`:persist-result token outcome` observation; cleanup-only failure never creates
an extra `:uncertain` event.
