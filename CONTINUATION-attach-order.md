# lane/attach-order: status

Tip c3847ec7f on origin/lane/attach-order (base origin/dev 71069c72d). Not READY-FOR-IMAGE: the hbox certify of the touched host books is running.

## What the lane does
Certified host files attach the image's stobj implementation before the generic, the order is checked, and the owner refuses to start on an arena mismatch (CONVERGE-1 red 1).

- 12 host files (owner-host, store-host, store-node-host, page-read-host, page-window-executor-host, payload-view-host, index-reader-request-host, index-connection-repin-prepare-host, owner-exposure-host, receiver-repin-source-host, receiver-source-gate-host, runtime-receiver-source-host) include-book books/payload-arena-attach and books/history-paged-attach first. Commit 9f77efa26.
- tools/attach_order_check.py: 22 findings on origin/dev, 0 on this lane (laptop, source walk). Enforced by native_preflight gate `attach-order`, hbox_native.sh, `make check`, tests/test_attach_order_check.py (5 tests pass).
- Owner check: host/native/owner.lisp fnn-owner-arena-identity-check, entry fn-owner-arena-count in host/owner-host.lisp, declared in host/interfaces.lisp; tests/test_native_arena_identity.py (4 pass). Commit c3847ec7f.

## Gaps
- Scope is the four image-world umbrellas' host files; books/* above a generic are not checked (by design) and defattach seams (codec, records, crypto) are order-insensitive.
- Not run in an image: test_native_commit_log, multipost.py (N's gate).
- Other generated ledgers (planning/cost-obligations.json, coverage-baseline.json) were not regenerated for the new entry fn-owner-arena-count; run `make check-lane` on a box to see if any is stale. Owner: integrator.
- Red #3 is lane/image-manifest, not here.

## Next
hbox certify run: log /tmp/hcld2-sub6.log, scratch /tank/fn/gates/attach-c3847ec7f. On green: index the manifest with tools/evidence_manifests.py add, then write READY-FOR-IMAGE c3847ec7f here and message Deputy C2 (acc55b2d131781175) and N (a455310f1b46d51fd).
