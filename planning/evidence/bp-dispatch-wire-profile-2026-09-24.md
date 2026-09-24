# BP received dispatch wire profile checkpoint

This source defines only the versioned FNBS codec for a future durable held
dispatch. A logical kind-6 dispatch uses frame version 2 and kind 6 under an
epoch-operation received-row name. The existing boot-domain marker remains
frame version 1 and kind 6 under `clock-domain.fnb`. The two specialized
decoders each reject the other's frame in the executable test book, while a
canonical dispatch example decodes exactly. The byte grammar is declared in
`specs/bp-node-machine.md` §3.3 and the code lives in
`books/bp-fnbs-dispatch-codec.lisp`.

Persvati run `run-20260924T045918Z-f5e6`,
[manifest](manifests/certify-20260924T045927Z-360587.json), passed the codec
and test roots plus four shifted dependencies using ACL2 8.7 and toolchain
identity `1b4169e9c5825a4e1fc827767f00470ceafc459619e0a4fd522c48f1ba964286`.
The manifest records source digests and the 90-second per-book cap.

No current native caller publishes version-2 dispatch bytes, and the ordered
FNBS replay does not yet accept them. General roundtrip and byte-publication
theorems, exact journal-debt admission, and session/MRU forwarding remain
open. This checkpoint alone earns no N04 or N05 runtime claim.
