# W18 native initializer composition handoff

Head: `e84331b evidence: certify initializer link uncertainty witness`, with
implementation commits `c1663c0 native: model initializer immutable-link retries`,
`a993623 proof: reject unexpected initializer link success`, and `e62abd6 fix:
close native initializer publication handler`.

The production anchors are `fnn-publish-initial-file` and `fnn-initialize` in
`host/native/io.lisp`. A real immutable `link(2)` EEXIST returns `:existing`
and is modeled by `:link-eexist`; no other link error is accepted as a retry.
`fn-bsi-existing-init-program` covers valid config/frontier finals and
`fn-bsi-history-retry-program` covers the selected history-fenced/no-frontier
restart. The history race is explicitly uncertain; lock contention is refused
before metadata publication.

The hbox 118-book default-image closure passed at
`certify-20260921T093534Z-1966193`; its acquired artifact set built native
`fn-host`, then 18 initializer/codec runtime tests passed. The final
issued-link model witness certified in
`certify-20260921T095918Z-2002274`. Exact commands, digests, and limits are in
`planning/evidence/native-initializer-composition-w18-2026-09-21.md`.

Remaining scope: no physical power-loss/link-EIO qualification, arbitrary
preexisting-layout, lock-fairness, all helper/read syscall, K0, or
recovery-executor physical-state correspondence claim. Root assigned the next,
separate U13 transaction-namespace recovery consolidation; do not fold it into
this initializer evidence packet.
