# TOP-002 installed-generation v2 checkpoint (unqualified)

This isolated branch starts at `67d026ad`; it is **not** a landed behavior or
native image claim. The experimental v1 `fnto` anchor retains its eight-field
ID-only historical meaning and exact version-1 codec. A fresh local proposal
now forms a nine-field version-2 anchor with the installed administrator event
generation at field 8. Version-2 historical replay compares both the installed
ID and generation. The Store fresh-topic prepare gate rejects v1 anchors, so
current publication cannot downgrade a new anchor to the historical format.
Version-1 admin-install and report event bytes remain version 1. Unknown future
versions and cross-version item shapes are refused.

The owner calls `fn-owner-topic-propose` → `fn-th-local-propose`; Store prepare
calls `fn-sn-prepare-topic` → `fn-th-prefix-step`; observed reopen invokes the
same prefix projector. The version-2 local proposal theorem and prefix replay
theorem were admitted in bounded persvati proof sessions before scoped
certification. ACL2 8.7, persvati w25 toolchain identity
`1b4169e9c5825a4e1fc827767f00470ceafc459619e0a4fd522c48f1ba964286`,
one job, 120-second per-book limit, no `--closure`:

- `run-20260924T050334Z-6384`, local-admin book/test passed:
  `manifests/certify-20260924T050342Z-401750.json`.
- `run-20260924T050424Z-f023`, topic codec book/test passed:
  `manifests/certify-20260924T050433Z-409954.json`.
- `run-20260924T050514Z-82e8`, Store event union dependency passed:
  `manifests/certify-20260924T050524Z-419236.json`.
- `run-20260924T050622Z-b3eb`, topic prefix book/test passed:
  `manifests/certify-20260924T050631Z-430575.json`.

The changed Store fresh-prepare gate, owner-called proposal theorem and their
dependent invariants have not certified, and no dual-image v1-to-v2 migration
test has run. `tests/test_native_topic_local.py` still exercises only the v1
source-matched shape at the frozen image; a dual-image test must create a v1
Store using an exact pre-v2 image and reopen it under a qualified v2 image.
Root paused further v2 activation because the shared byte/BP crash-image
assurance must first derive observed topic replay success from a maintained
actual Store relation, rather than assuming it for arbitrary physical scans.
