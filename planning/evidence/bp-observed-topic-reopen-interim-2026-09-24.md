# BP observed reopen after topic Store events: conditional repair

The actual Store observed opener now requires a successful topic-prefix replay in
addition to article, identity, and consumer replay.  The BP receiver's
`fn-bprv-observed-reopen-facts`,
`fn-bprv-evolving-invariant-survives-observed-reopen`, and
`fn-bpr-live-receipt-regenerated-after-restart` therefore carry the opener's
`fn-sn-observed-topic-okp(records)` premise explicitly.  The first theorem is
the keystone used by the latter two.  No BP receiver event manufactures topic
events, and the consumer relation does not imply topic replay.

`tests/acl2/store-observed-tests.lisp` has two individually well-formed
administrator-install records that pass observed history, recoverability,
identity, and consumer replay but fail topic replay; the actual
`fn-sn-open-observed` returns `(:error :replay)`.  This separates the replay
checks.  It does not, by itself, establish that those records are a crash image
of a Store satisfying the BP theorem's full state relation.  Deriving topic
replay from a maintained Store topic/crash relation for reachable images is
the remaining composition obligation.  Until that bridge certifies, the BP
reopen statements are conditional and do not support an unconditional
receipt-recovery claim.

The changed BP book passed the selected ACL2 8.7 persvati run
`run-20260924T050508Z-0ab3` in
[`certify-20260924T050516Z-418207.json`](manifests/certify-20260924T050516Z-418207.json).
Its dependent test root passed run `run-20260924T050837Z-7af1` in
[`certify-20260924T050842Z-451728.json`](manifests/certify-20260924T050842Z-451728.json).
Both used the source in this packet and the same ACL2 toolchain identity
`1b4169e9c5825a4e1fc827767f00470ceafc459619e0a4fd522c48f1ba964286`.
