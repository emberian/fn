# LANEDUMP native-drift (2026-09-25, night deputy) -- DONE, with three open reds

Commits: d1902191 (tests), 32842f50 (host), record commit. Record:
planning/evidence/native-drift-2026-09-25.md. No PRF, no book changed.

Fixed: peer-report and fn-sn-io source-text drift (repointed, same checks
plus more); raw-stub harness (image's SBCL via tests/native_process.runtime_sbcl;
marker-cut and state-checkpoint stubs from the deployed/book definitions);
body-limit wording (code: fn-owner-install-profile sets the served POST bound
to A). Non-ASCII already fixed on dev. Owner "acl2 not found" = set FN_ACL2.

Evidence: farm run-20260925T100637Z-1430 (manifest certify-20260925T100705Z-3116225),
images at /tank/fn/scratch/native-drift/src2 (prod b7048de9, dev 2e09b662),
native-modules.log 85 run / 3 fail / 4 skip, every brief red green.

OPEN (for the deputy):
1. ac70f38d images report max-history-octets=0 for H >= ~2^34 (default 2^40);
   pure ACL2 decode is correct; green on d9203155 image. Breaks two
   NativeOperatorCapacityTests. Executable-path defect; needs a REPL lane.
2. OperatorFieldsTests.test_a_raise... red on both images.
3. DTN image does not build: build-dtn.lisp lacks books/octets-stobj.
