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

The follow-up now derives those prerequisites from every
`fn-bpnp-dispatch-recordp` row: `fn-bpnp-dispatch-record-values-ok`,
`fn-bpnp-dispatch-record-frame-input`, and
`fn-bpnp-dispatch-record-reconstructs` establish typed fields, bounded
payload and exact EID reconstruction. `fn-bpnp-dispatch-frame-is-seal`
binds the actual encoder to the protected header plus trailer, and
`fn-bpnp-dispatch-record-round-trip` proves that its specialized decoder
returns the original row. The actual codec functions and inherited EID byte
accessors have verified guards in the invariant book. A maximal 1024-octet
identity, IPN and null EIDs decode exactly; a 1025-octet identity is refused,
with a `must-fail` roundtrip witness. The selected invariant root passed
persvati run `run-20260924T053209Z-dc34`,
[manifest](manifests/certify-20260924T053213Z-678017.json); the corrected
test root passed `run-20260924T053406Z-51cb`,
[manifest](manifests/certify-20260924T053409Z-697169.json). Both use the
same ACL2 toolchain. The earlier conditional theorem passed run
`run-20260924T051753Z-9a54`,
[manifest](manifests/certify-20260924T051757Z-542583.json).

No current native caller publishes version-2 dispatch bytes, and the ordered
FNBS replay does not yet accept them. Host publication, exact journal-debt
admission and session/MRU forwarding remain open. This checkpoint alone
earns no N04 or N05 runtime claim.
