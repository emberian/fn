# BP held progress route-wait slice

Source `62c1e171` on `11c91419` changes the native `bp-node` caller to issue
`(:progress node observation routes generation)` through its existing
`fnn-bps-foundation-step` handle. That handle now calls `fn-bpnp-step`, which
delegates ordinary events to `fn-bpn-report-author-step` on the same FNBS
state. For the first native profile, `routes=nil` and `generation=0`. The
event selects the least-arrival live whole pending held row; a route-less
transit row gets a per-key volatile `:route` wait, so a later event can select
a younger local request and use the existing durable kind-7 application path.
Cold recovery clears these waits. A changed route generation reconsiders a
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
and narrow event-boundary lemma. The final exact-source selected run passed.
The edited native `bp-node.lisp` and `bp-service.lisp` also passed an SBCL
reader check with `sb-bsd-sockets` and `sb-posix` loaded; this checks source
syntax, not saved-image behavior.

The separately owned `bp-node-machine-teeth-tests` fixture reaches two
durable kind-5 receives through the actual outer step, then route wait and
local delivery with matched durable kind-7 callback. Its source-matched
recertification and native same-handle interrupted-contact fixture are
pending. This packet proves neither N03's four-class fairness nor N04 MRU
forwarding or N05 journal debt. A routeable transit row currently waits for
the later session/forwarding slice; session availability does not independently
wake it. No source-matched image has yet qualified this new native caller.
