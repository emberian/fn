# Consumer projection through topic Store records

`host/owner-host.lisp:411` submits the ACL2-authored topic event as a Store
owner step; `fn-own-store-step` in `books/owner.lisp:1489` calls the decoded
Store dispatcher `fn-snrt-step`. Its `:prepare-topic` arm is therefore a
consumer-invariant obligation. In `books/consumer-store-invariants.lisp`,
`fn-csi-prepare-topic-preserves-consumer-relation` proves that a Store satisfying
`fn-sn-statep`, a natural completed identity sequence, the Store sequence
invariant, and `fn-snt-consumerp` still satisfies `fn-snt-consumerp` after the
actual topic prepare. `fn-csi-normal-step-preserves-consumer-relation` carries
that fact through non-crash dispatcher steps; the existing
`fn-csi-store-step-preserves-full-relation` remains the phase-aware theorem
covering crash and recovery. The topic case needs the finite-frontier facts
`fn-csi-record-count-below-next-lower` and
`fn-csi-candidate-sequence-below-max`. These are proof-side reachability
relations, never whole-history checks on a served command.

[`consumer-topic-store-tests.lisp`](../../tests/acl2/consumer-topic-store-tests.lisp)
builds one Store through the public transitions: E2 bootstrap and registration,
T10 keyring enrollment and exact root-source acceptance, then the valid local
administrator event at the actual `fn-snrt-step :prepare-topic` branch. The
test checks `fn-csi-livep` and `fn-csi-full-relationp` before and after this
preparation. It next commits the administrator, anchor, second accepted T10
source and report admission. At the completed frontier of eight records, the
consumer projection equals strict replay of that exact journal, while the
registered consumer's ACK remains zero. Observed reopen reconstructs the same
projection and ACK. The two accepted source events show this is a mixed
article/topic history; the trace does not claim consumer delivery or
application processing.

The isolated source was based on `dev` `ca692d9b` and then combined with the
consumer proof repair. Both certification manifests record the same
`books/consumer-store-invariants.lisp` SHA-256,
`ce6e0556147071698c60d68d872063ac98eec23d143385abab1562457d3a4a05`;
the final test SHA-256 is
`5b4086dd7d9ed70c5631f0ef38c657076e6c8c75b347ac3a3ce572acf36efbee`.
On hbox, ACL2 8.7 using `/tank/fn/toolchains/w28/acl2-literal-4g` (toolchain
identity `d5f2b9f0d2cf68c6074ea7046fbd2e560d2984fe22d7e03f93045975ac889f0`)
passed the [invariant and original witness roots](manifests/certify-20260924T044417Z-908525.json)
in 34.029 s, with 81 compatible cached dependencies, and the [combined
topic/consumer trace](manifests/certify-20260924T044728Z-912706.json) in
3.250 s, with 91 compatible cached dependencies. The manifests record exact
commands, source digests before and after certification, and individual book
verdicts. No native saved image, host syscall refinement, remote policy, or
consumer-owned transaction/ACK/reply join follows from this ACL2 trace.
