# BP observed-channel admission, finite loopback slice

The native `bp-node serve` adapter now captures the accepted socket's local
IPv4 address/port and remote IPv4 address. `fn-bpaj-session-principal` in
`books/bp-session-admission.lisp` selects a single durable peer profile from
that observed channel before comparing the TCPCL announced EID to its
configured `transport-bp` row. The operator's `bp-boundary add` command writes
the profile through the existing configuration-history `:set-peer` delta.
The selector requires the complete peer row group to decode through
`fn-cfg-peer-find` with BP transport; stray trust rows cannot admit a peer.
The loopback profile declares `all-co-resident`, so every process able to
connect through that loopback boundary is in its trusted originator set.

At application delivery, the host reads `fn-ocfg-config` through
`fn-owner-config`. Both request and receipt handoffs require the carried
principal to name a current durable BP peer, the carried generation to equal
the live generation, and the bundle source EID to equal that peer's configured
BP EID. A nil principal can retain BP custody but cannot enter the Store
request join or release a workflow pin. Peer name and EID remain separate.

Hbox ACL2 8.7 incremental evidence: native admin/operator book and tests
passed in `certify-20260923T211202Z-157776.json`; the later complete-peer
admin witness passed in `certify-20260923T213036Z-204816.json`. The final
admission/handoff books and tests passed in
`certify-20260923T212944Z-202250.json`. Each is archived under
`planning/evidence/manifests/`; the manifests carry source/toolchain hashes,
invocations, installed origins, and wall time. `make check` and Python syntax
validation ran on the lane source. The changed native image has not yet been
built or run; the native positive and absent-trust request/receipt cases in
`tests/test_bp_node_native.py` await a source-matched developer image.

This finite slice does not prove A-BP-PATH or implement the general K6
`fn-peer-decide-transfer` transit-policy join. It does not authenticate an
individual local process and does not qualify private-network or tunnel
boundaries. The host still checks one configured TCPCL peer EID for its
session; that CLI check supplies consistency, not the admitted principal.
