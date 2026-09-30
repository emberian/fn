# Retirement: current path and bounded successor contract

The original S9 operator contract is `retire [--drain SECONDS]`: refuse new
connections, pause pulls, let feeds drain through the admitted window,
report every configured peer's undelivered/dropped work and the individual
obligation ledger, take the final checkpoint and stop. Retained obligations
require the existing explicit waiver for release. A socket outcome does not
release a durable obligation.

Current served functions are `fn-oret-drain-step` and `fn-oret-report` in
`books/owner-retire.lisp`, through `fn-owner-retire-step` and
`fn-owner-retire-report` in `host/owner-host.lisp`. They still scan the peer
queues and render the complete report. Their existing PRF-1029 logical
properties do not establish bounded scheduling work or bounded allocation.

## Selected served successor: maintained scalars

The concrete inventory showed that a concurrent captured table keeps the
entire peer/config/feed/message/evidence graph and older immutable versions
live. The selected served drain therefore uses maintained exact per-feed
undelivered and retry-bound-dropped scalars, plus an owner aggregate pending
count. The cursor below remains a bounded cold/rebuild/reference component;
it is not a reason to activate an unfunded concurrent snapshot.

The pending meaning stays exactly the current one: undelivered minus drops
whose reason is `:retry-bound`; another dropped reason still contributes to
this report's pending count. Actual successful enqueue increases undelivered;
an actual final in-flight outcome decreases it; a first retry-bound give-up
increases the retry-bound drop count. Backoff, loss, reconnect, restart,
offer/sent transitions and refused mutations preserve those quantities.
Peer addition/removal/reconfiguration and every native feed-port installation
must compose exact aggregate deltas. Cold/open/rebuild/journal replay must
establish the carried relation with bounded work, never a whole-table fold
in a served installer. Source support now exists in `peer-feed-counts.lisp` and
`owner-feed-counts.lisp` (HST-041 / PRF-1138 / SCN-1047). The in-memory
constructor has nine slots; the two derived fields are rebuilt by actual
replay transitions, while durable journal encodings retain their semantic
fields. Counted target enqueue returns the original table and the updated
aggregate from one fold. FNFD peer port results carry the exact signed
aggregate delta. Protected source admissions and model fixtures do not
establish publication/recovery, guarded served entry or final drain. These
remain implementation obligations, not yet completion claims.

A scalar zero alone cannot authorize final drained success. Intake first
stops, then a real producer fence settles/joins outstanding accept/commit
producers or carries their pending obligations; they cannot add work after
the final zero. Deadline observation has independent bounded work and keeps
timeout distinct. After the final join, the report streams the existing
frozen owner graph at an explicit coordinate, with owner lifetime, staged
disk and scratch funding. No old concurrent versions are retained solely
for this report. Scalar widths, admission funding, mutation preservation,
the producer fence and report streaming all remain open.

The current source shutdown seam distinguishes the physical log writer's
`:joined`, `:absent` and `:timeout` observations. ACL2's
`fn-ort-log-close-action` permits journal close and report observation only
after a joined/absent writer with zero accounted lines/octets and no queued
job. A held writer retains its journal descriptor, suppresses report
publication and returns uncertain through `fn-ort-log-close-exit`. Literal
mutation fixtures cover each unsettled observation. These source admissions
do not establish the complete native producer fence or funded report.
The outer operator caller and the direct run-line writer also consult
`fn-ort-log-caller-action`: the retained writer slot forbids both direct
stopped-line I/O and descriptor close. A timeout does not relinquish that
slot; only definite join clears it.

With the producer observation still unsettled, the actual tick uses the
clock-only entry: `fn-ort-window-step-is-unsettled-counted-step` equates it
to the complete counted decision for every pending value. It acquires no
semantic owner mutex and performs no free-space filesystem query. The
accept loop observes this decision before maintenance and admits no new
maintenance after retirement begins. Existing maintenance can still block
the accept loop; an independent, funded observer or nonblocking maintenance
continuation remains required. This conservatively disabled early success
does not replace the required complete producer fence and early drain.
Fixed retirement metadata is observed and published under the short roster
lock, without semantic locking. `fn-ort-retire-publish` is idempotent and
preserves completed metadata after a stale wait, so concurrent observers
cannot replace the completed record or encounter the transient two-to-three
field publication without the stop request. An independent observer remains
unactivated until its ticking and retained-job lifetime are established.

`tests/recording/retirement` preserves actual-function regression snapshots,
source hashes and logs for the held log writer and held semantic mutex.
Recording I/O/core stubs and real SBCL synchronization are their exact scope;
they are not an ACL2 proof, matching image or disk/native qualification.

## Unactivated cursor contract

`books/owner-retire-cursor.lisp` is an independently admitted source
contract, not an installed served path. `fn-orc-start` captures a table
reference and a natural mutation coordinate. `fn-orc-next` loads one peer's
queue, consumes one queue entry, or returns a completed cursor; it never
loads a peer and consumes its first queue entry in the same transition.
An entry with exactly `(:dropped :retry-bound)` contributes no pending
work; every other queue entry contributes one. Dropped work stays
undelivered in the eventual report.

`fn-orc-next-preserves-snapshot-pending-tally` conserves the accumulated
pending count plus the logical pending count of the unconsumed table and
queue. `fn-orc-complete-zero-has-no-remaining-pending` requires the complete,
current zero predicate; a partial accumulator is never a result. The model
fold is not an executable served call. Equality to the existing
`fn-oret-pending-total` is a separate, not-yet-admitted boundary theorem.

Activation requires all of the following, which remain open:

- Every relevant feed mutation advances the carried mutation coordinate;
  irrelevant clock observation must not prevent a quiescent scan from
  finishing. Installation footprint/frame proofs and witnesses change with
  that state. No whole-table equality detects mutation on the served path.
- Coordinate representation never wraps or aliases an earlier capture.
  Profile/runtime representation and each scheduling quantum's scalar work
  must be justified before using the model's natural coordinate in a host.
- Capture is admitted against exact retained table/ledger nodes and bytes,
  including older immutable spines made live by concurrent writers. A
  scalar pin or article count is not physical lease funding. Cancellation,
  invalidation, completion and failure carry retirement debt until no cursor
  alias can retain the snapshot. No snapshot is acquired without funding.
- Drain zero requires a complete scan with the current coordinate.
  Deadline evaluation has bounded independent work, even during churn.
  Eventual zero needs a finite relevant-mutation interval and fair cursor
  scheduling; neither premise is assumed from a quiet socket.
- The final report's coordinate is frozen after stop/join. Peer fields,
  all individual obligation fields and the original outcome/release lines
  stream into a staged file in bounded octet windows. An arbitrarily long
  field resumes; no field or ledger is truncated, and a page is not produced
  by first rendering the whole report or line.
- Publication retains staging, file and directory barriers. Ambiguous
  persistence failure is recovery/uncertainty, not refusal or success.
  Every newly introduced process-death cut needs a model crash point.

The source prototypes now carry nine-slot feed counts through live/replay
mutations, one guarded target enqueue fold, all durable outcome variants and
the existing configuration retire/install/scope reconstruction. Their source
refinements preserve complete prior results and exact aggregate/count relations;
no certification or matching-image result is implied. Intake refuses new mux,
bound-control and BP submissions once retirement is published. A clock-only
precheck runs before the semantic owner mutex, and final report observation
moves after joins and close hooks. The actual producer-settled observation is
still deliberately NIL, so zero cannot authorize `drained` yet. The deadline
path remains available.

Frozen report rendering is still a whole-buffer source path. The unactivated
`owner-retire-stream` proposal shares existing tails after joins, but its
full report byte conservation now has a narrow source admission under maintained
feed counts, pin string/natural fields and natural reserved. Staged output
disk/runtime/lifetime funding and installed invariant-to-domain carriage are open.
The current proposal schedules fixed descriptor spines and uses the guarded
field emitter to emit NIL or one octet per turn; it renders no whole line.
Its guard, start/preservation invariant and output quantum have narrow source
admissions. Literal getter/reference extraction preserves original definition
forms and record layouts. The additive reference leaf proves actual cursor STEP conservation and complete
RUN equality to literal fn-oret-report under those explicit data hypotheses.
These admissions have no host activation or native qualification claim. Final checkpoint and all crash cuts,
installed composite preservation, scalar-width/coexistence funding and the
matching native whole-slice scenario remain required. This progress does not
close S9, R16 work debt, physical funding or native qualification.

The actual field emitter now carries borrowed-field provenance: during decimal
preparation, its quotient remains bounded by the original natural descriptor,
and retained digit cells plus at least one remaining binary-width unit fit in
one plus the original binary width. Each actual step preserves that relation;
zero reserves its final digit. The normal six-book source certificate is
`certify-20260930T112806Z-1655367`. This source storage bound supplies no
supported-profile operand ceiling or selected-runtime division/frame/GC tariff.
It also supplies no report-stage or old/new cursor coexistence lifetime grant.
The actual frozen report writer and CLI reader still require bounded consumers.

The frozen cursor carries the emitter provenance/scratch relation through all
actual descriptor scheduling and STEP branches. Its execution guard checks a
fixed ten-slot prefix and the current emitter prefix; full field and digit
relations remain carried ghost invariants. Current guard/refinement/space and
complete literal report bridge are normally certified by
`certify-20260930T114500Z-1836457`. A malformed later field demonstrates that
ready checks the current prefix without claiming that corrupted state is valid.
Profile, primitive and coexistence/staging lifetime funding remain separate.
