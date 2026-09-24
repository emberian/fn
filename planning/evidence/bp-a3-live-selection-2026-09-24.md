# A3 local live selection under per-carrier clock uncertainty

The native owner calls `fn-bpah-pending-decision-at` at
`host/native/bp-node.lisp:131` before its existing `:deliver` step. The
selector now chooses the least-arrival eligible local whole carrier whose
current expiry is `:live`. If none exists, it returns the oldest local
clock-uncertain carrier as `:uncertain`; an expired carrier is skipped.
The owner still stops on `:uncertain` and dispatches only `:ready`.

The ACL2 witness in `tests/acl2/bp-app-handoff-time-tests.lisp` creates two
kind-5 proposals through `fn-bpnf-step` and supplies matched durable
publication results. Both exact wires are first accepted by `fn-bpn-receive`
under their arrival observations. The older bundle has no Bundle Age block:
it is admitted under an accurate wall reading, then its later wall-less
observation is `:uncertain`. The newer bundle has a
persisted Bundle Age anchor and is `:live`. Both held rows are valid local
pending carriers, with distinct bundle IDs and strict arrival order. The
test selects the newer key, checks a `:deliver` effect, and checks that the
older held row is unchanged. It separately checks the all-uncertain result.
The theorem `fn-bpah-select-oldest-at-is-live` proves that a nonempty scan
from a nil or live seed returns a live row; its test book checks the full
positive antecedent and counterexamples for each dropped premise.

Clock uncertainty is not publication uncertainty. The test constructs an
uncertain issued FNBS operation and checks that the foundation step leaves
the state unchanged and emits no `:deliver`, even though the read-only
clock selector can still describe a live carrier. The host also checks
`fnn-bps-outcome :uncertain` before issuing a delivery event. This test does
not qualify a new native image or prove the host check itself.

The first selected persvati ACL2 8.7 / SBCL 2.6.8 run,
`run-20260924T033603Z-3cbf`, used two jobs and a 90-second per-book cap at
`/home/ember/fn-gates/bp-counterexample-20260924`. The new selector theorem
admitted in 0.05 seconds, but the old by-definition ready theorem stalled
after the decision shape changed. The test root then failed to include the
uncertified book. The later source revision makes the ready branch select
only live rows and cites the selector theorem directly. Certification and
source-matched native qualification of that revision are pending.

This is one actual A3 local application selection step. It does not satisfy
N03's route wait and four-progress-event trace, N04's forwarding MRU trace,
or N05's journal debt theorem and measured pressure trace. Those A1/E rows
remain open in `specs/bp-node-machine.md` §11.1.
