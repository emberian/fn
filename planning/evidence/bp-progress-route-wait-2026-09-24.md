# BP held progress route-wait slice

Source `62c1e171` on `11c91419`, with recovery correction `1d207ddb`,
changes the native `bp-node` caller to issue
`(:progress node observation routes generation)` through its existing
`fnn-bps-foundation-step` handle. That handle now calls `fn-bpnp-step`, which
delegates ordinary events to `fn-bpn-report-author-step` on the same FNBS
state. For the first native profile, `routes=nil` and `generation=0`. The
event selects the least-arrival live whole pending held row; a route-less
transit row gets a per-key volatile `:route` wait, so a later event can select
a younger local request and use the existing durable kind-7 application path.
Successful cold recovery clears these waits; a recovery fault retains them
and leaves the underlying uncertainty fence in place. A changed route
generation reconsiders a
route wait. The host prints a stable wait line only from the ACL2 effect.

The served selection scans fixed held slots and the persisted expiry anchor.
It neither re-encodes retained wire nor decodes every retained ADU. ADU class
is checked once for a selected local row; an unsupported row gets a volatile
per-key `:class` wait, allowing younger work to be considered. The
`fn-bpnp-held-expiry-refines-a3` and `fn-bpnp-local-class-refines-a3` theorems
connect those projections to the earlier A3 selectors under the admitted
held-row invariant. `books/bp-node-progress-guards.lisp` verifies the exact
host-called outer step's guard using the already maintained base-state
premise; there is no whole-state recognizer in the executable body.
The selector still performs quadratic retained-set work in the worst case:
wait pruning scans held rows per wait, and eligibility scans waits per held
row. The native owner configures at most 64 held rows; the 64-route snapshot
limit is a separate bound and does not bound this work. A linear indexed
selector and its correspondence proof remain a later cost obligation.

The selected persvati run `run-20260924T043223Z-9fa3`,
[manifest](manifests/certify-20260924T043228Z-116619.json), passed
`books/bp-node-progress`, `books/bp-node-progress-invariants`, and
`books/bp-node-progress-guards` at these source bytes. It used ACL2 8.7,
toolchain identity
`1b4169e9c5825a4e1fc827767f00470ceafc459619e0a4fd522c48f1ba964286`,
one job and a 90-second per-book cap; the manifest contains each source and
dependency digest. The first run failed on a missing include, and the next
run exposed shallow-selector correspondence and the outer event guard. Those
were repaired with a direct selector equality, admitted-primary shape lemma,
and narrow event-boundary lemma. The selected run passed at the initial
guarded source bytes. The recovery correction was recertified on persvati in
`run-20260924T043911Z-2091`,
[manifest](manifests/certify-20260924T043918Z-178337.json): the same three
progress roots passed at the corrected source bytes under the same ACL2
toolchain identity and a 90-second per-book cap.
The edited native `bp-node.lisp` and `bp-service.lisp` also passed an SBCL
reader check with `sb-bsd-sockets` and `sb-posix` loaded; this checks source
syntax, not saved-image behavior.

The separately owned `fn-bpnp-step-progress-preserves-held-and-issued`
theorem in `books/bp-node-progress-selection-invariants.lisp` proves that a
single `:progress` event on the exact outer step called by
`fnn-bps-foundation-step` (`host/native/bp-service.lisp`) leaves the held
obligations and issued durable operation unchanged. Its only hypothesis is
the event kind; the test drops it with a reachable matched kind-5 callback
that changes the held list. The `bp-node-machine-teeth-tests` fixture first
reaches two durable kind-5 receives through that same outer step, then a
per-key route wait and local delivery with a matched durable kind-7 callback.
The older row remains held. A changed route generation rechecks it rather
than delivering the younger row; that exact negative is under `must-fail`.
A failed cold-recovery event preserves the state and route wait, while a
successful replay with the recovered held rows clears the volatile wait.
The selected persvati run `run-20260924T044201Z-f12a`,
[manifest](manifests/certify-20260924T044207Z-205038.json), passed the
selection-invariant book, and `run-20260924T044340Z-bc7e`,
[manifest](manifests/certify-20260924T044347Z-220667.json), passed its
test book at the same progress-source digest. Both used ACL2 8.7,
toolchain identity
`1b4169e9c5825a4e1fc827767f00470ceafc459619e0a4fd522c48f1ba964286`,
one job, and source-digest-matched cached dependencies. The native same-handle
interrupted-contact fixture is source-present and awaits a shared matching
image. This packet proves neither N03's four-class fairness nor N04 MRU
forwarding or N05 journal debt. A routeable transit row currently waits for
the later session/forwarding slice; session availability does not independently
wake it. No source-matched image has yet qualified this new native caller.
