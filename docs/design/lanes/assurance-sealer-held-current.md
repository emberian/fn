# Current-source sealer cleanup donor

Source donor is based on `072b8b316` (parent cold integration), preserving its
actual pool query-reference implementation. No pool, core, loader-I/O, observer,
boot or live-adoption implementation is imported. Four production books change:
`runs`, `sealer`, `machines-c-sealer-kind`, `machines-c-sealer-events`.

The existing release body is extracted by installed-row owner. Pool acceptance
precedes consuming the cache/overlay handle. `:held` retains the complete handle
and retries; ordinary `:credit` remains a retained refusal. INSTALL publishes
once, then separate phase-gated overlay/hash returns advance only on `:ok` or
`:retired`. A second INSTALL call refuses. Current actor answer/dispatch grammar
handles the additional outcomes without adding a second actor or core.

`tools/seal_cleanup_current_projection.py` reuses the original structural
transformations against a separate immutable current-source fixture. The
historical fixtures remain intact. It excludes the historical physical-loader
preflight and observer adaptations absent from this parent. Seven current
projection controls pass; original successful bodies and pool bytes are retained.

`tests/seal-release-row-held-unit.lisp` directly includes the actual `sealer`
and `pool-credit` books plus system B*. Its 132-book project closure includes no
callback assembly or adoption implementation (the lower summary-state carrier
is inherited by the current prefix). Its prepared operation assertions acquire
actual query references, check complete source retention on `:held`, close the
last reference, retry once, accept retired cleanup, refuse credit-tagged ordinary
release, and check held overlay/hash cleanup after one installation. The queried
cache is an adversarial component input, not a claim about the current TxnOffer
producer. Snapshot columns come from the actual current declarations, including
pool `query-ref-count`; historical absent copy fields/version-floor are excluded.

Read-only local cache inventory on this source found 8/132 plain-world closure
keys represented by 15 entries; 124 keys have no local plain entry. This is not a
compiled/toolchain-qualified artifact set. Exact per-book keys and counts were
written to `/tmp/reclamation-cleanup-cache-inventory.json`; no remote cache was
inventoried and no ACL2, native, farm or remote job was started.

Next execution gate, after the parent grants resources: inspect the designated
box's compatible cache for these exact keys, reuse its actual canonical prefix,
then run this one operation fixture. Do not pull in the 309-book full handoff
closure for this component control. Admission/execution, frame proofs and the
full live-publication/adoption antecedent remain unqualified. Parent's actual
application baseline has priority; this source donor grants no activation/FREE.
