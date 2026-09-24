# Read-only fragment expiry selector

`books/bp-node-fragment-expiry.lisp` adds a read-only family proposal selector
that requires every row in the existing principal/coherence active set to be
`:live` at one ACL2 clock observation. It does not filter source rows,
change the active set, install a whole bundle, or enable fragment reception.
`fn-bpnf-family-plan-at-ready-binds-live-source-rows` proves the actual
selector's ready result binds all selected rows to that live decision. The
test has a complete family whose legacy unknown anchors block, a live family,
and an expired family that blocks despite the old plan being complete.

Selected hbox certification `run-20260924T005928Z-a532` passed both new
roots and their required dependencies with ACL2 8.7/toolchain identity
`d5f2b9f0d2cf68c6074ea7046f4bd2e560d2984fe22d7e03f93045975ac889f0`.
Manifest: `planning/evidence/manifests/certify-20260924T005937Z-654262.json`.
`make check` passed. This is an independent decision kernel for the later
versioned kind-18 admission/replay join; no native fragmentation is claimed.
