# FNBS A2 kind-5 byte slice, 2026-09-23

The executable subject is the typed `fn-bpnf-step` receive proposal and its
`(:persist epoch op-id held)` effect. `fn-bpnf-stored-record-frame` creates
the exact FNBS kind-5 octets for that effect; `fn-bpnf-stored-record-unframe`
reads those octets. The host native receive path is not yet switched to this
publisher, so this evidence covers a model component, not the served native
caller.

`fn-bpnf-stored-values-reconstruct-held` proves the field-value inverse for
typed ingress, bounded exact wire, valid bundle, and the explicit BP/peer
round-trip hypotheses. `fn-bpnf-stored-frame-is-fnbs-seal` equates the
executable frame builder to the sealed FNBS frame when its field values are
valid and payload octets fit the 134144-octet bound. Neither theorem alone
proves a byte crash/replay relation. The byte-store tests exercise a nonempty
inherited final record with zero new events, a torn private stage, both
possible link-before-directory-barrier images, durable publication, an
uncertain callback that keeps the issued A1 operation fenced, a second crash,
and an occupied malformed final name. These are concrete witnesses, not a
universal physical-cut theorem.

ACL2 8.7 on hbox, `/tank/fn/toolchains/w28/acl2-literal-4g`, executable
SHA-256 `9f73da2a84d664516033fb6e944c55b55d1f7206e9599cac46ca2b208de26aa8`,
toolchain identity `d5f2b9f0d2cf68c6074ea7046f4bd2e560d2984fe22d7e03f93045975ac889f0`;
`tools/farm.py submit hbox ROOTS --jobs 2 --timeout-seconds 90
--remote-root /tank/fn/gates/lane-bp-persistence
--acl2 /tank/fn/toolchains/w28/acl2-literal-4g --cache /tank/fn/certcache`.
The manifests carry per-book input digests, source audit, and certificate
digests:

- `manifests/certify-20260923T165008Z-3941298.json`: nonempty and second-crash counterexample book passed.
- `manifests/certify-20260923T165532Z-3949791.json`: codec and codec tests passed.
- `manifests/certify-20260923T170933Z-3971064.json`: codec, codec tests, byte publisher, and byte-publisher tests passed at the later codec bytes; the not-yet-finished invariant root in this same exploratory run failed and is not claimed green by that run.
- `manifests/certify-20260923T171907Z-3991674.json`: the completed codec-invariant root passed.
- `manifests/certify-20260923T172808Z-4003205.json`: the codec-invariant root passed with the canonical frame-decode/held-value inverse at the later bytes.
- `manifests/certify-20260923T172854Z-4004558.json`: the new physical crash lemma book and its dependent byte-publisher test book passed.
- `manifests/certify-20260923T173231Z-4010248.json`: `bp-fnbs-replay` passed; the first test attempt in this exploratory run failed because ACL2 cannot evaluate the constrained digest in a `defconst`.
- `manifests/certify-20260923T173320Z-4011208.json`: the corrected byte-replay test book passed with its frame construction in functions.
- `manifests/certify-20260923T173616Z-4013704.json`: the revised foundation transition and its test book passed.
- `manifests/certify-20260923T173842Z-4015926.json`: byte replay, byte-to-recovery composition theorems, and replay tests passed at the revised foundation bytes.
- `manifests/certify-20260923T173915Z-4016748.json`: replay tests passed after including the composition invariant book.
- `manifests/certify-20260923T174029Z-4018611.json`: the four remaining changed dependent FNBS byte/invariant/test roots passed at the combined foundation and replay bytes; five of nine requested roots were already installed at those exact bytes.

`fn-bpnf-stored-unframe-of-canonical-frame` connects the actual decoder to
the canonical frame and held record under valid fields, a fitting frame,
the reconstruction premise, and frame equality. `fn-bpnf-byte-crash-keeps-
canonical-kind-five` then says that for **any** `fn-bs-crash-imagep`, if the
published inode was file-fenced, its durable content was that canonical
frame, and the crash image selected that inode at the final name, the
recovery slot is the identical kind-5 record. The name-selection premise is
material: before the directory barrier, the tests witness both an absent
and a present crash image. This theorem does not yet derive the name
selection from a publisher trace or cover a whole replayed history.
`fn-bpnf-replay-rows` reads canonical `(name octets)` rows in strictly
increasing `(epoch, operation-id)` order, checks each kind-5 held arrival and
freshness, and enforces held count/octet budgets. A two-row witness restores
nonempty inherited held state; malformed name/frame, reversed order and
capacity overflow fault. `fn-bpnf-recover-event` computes its event argument
from those exact bytes, and `fn-bpnf-step` is the sole transition that
atomically installs the held projection with a successful outbound base
restart. `fn-bpnf-recover-ready-bytes-install-held` is the composition check under a
ready byte result, valid cold held/budgets, a successful base restart, and a
fresh epoch; `fn-bpnf-recover-fault-bytes-keep-state` says a failed byte
replay leaves the prior uncertain state unchanged. Tests exercise both paths
and a stale prior-epoch callback after recovery. The event-builder result is
the byte binding; a raw recovery event supplied by an arbitrary caller would
not have that binding.

Open A2 work is a full noncircular `fn-bs-crash-imagep` relation for inherited
history and a new kind-5 publication, multi-kind replay with durable
frontier restoration, and the native publisher and recovery join. No FNBS-to-observed-journal or T6
crash-recovery claim is made yet.
