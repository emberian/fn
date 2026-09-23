# Native workflow constructor and FNWF join, 2026-09-23

Source packet: `d1229690` (branch `implement/workflow-join`, based on
`b5672043`). The native workflow caller at `host/native/workflow.lisp:307`,
`:321`, and `:330` now reaches the corresponding program-mode wrappers in
`host/workflow-host.lisp`. Those wrappers call ACL2-owned constructors in
`books/bp-workflow-constructors.lisp`; replay, preflight and apply use the
release-aware `fn-bprl-*` interpreter. The append-only FNWF kind table adds
codes 8 (`:undertake`) and 9 (`:release`) while the old seven codes remain
unchanged. The receipt constructor requires an exact canonical ADU, a local
trusted-observation flag, and acceptance by the current ACL2 workflow state.
The flag is a host-selected policy boundary, not verified peer cryptography.
Release records carry the exact recomputed decision and do not themselves
authorize the Store retention mutation.

Targeted certification ran on `persvati` with ACL2 8.7, toolchain identity
`1b4169e9c5825a4e1fc827767f00470ceafc459619e0a4fd522c48f1ba964286`,
two jobs, `/home/ember/fn-gates/toolchains/w25/acl2-literal`, and cache
`/home/ember/fn-certcache`. The invocation form was
`python3 tools/farm.py --jobs 2 --root /Users/ember/dev/fn/build/lanes/workflow-join --remote-root /home/ember/fn-gates/workflow-join --acl2 /home/ember/fn-gates/toolchains/w25/acl2-literal --cache /home/ember/fn-certcache submit persvati ROOTS`, followed by
`python3 tools/farm.py --root /Users/ember/dev/fn/build/lanes/workflow-join --remote-root /home/ember/fn-gates/workflow-join wait persvati RUN-ID`.
The manifests include exact root lists, source SHA-256 digests, ACL2 version,
toolchain, result, and per-book cost:

- [Initial frame and release closure](manifests/certify-20260923T172201Z-2143639.json): passed 10 roots, 12.193 certification wall seconds. Later source edits supersede this run for the constructor, release comment and final frame vector.
- [Final constructor and release tests at those bytes](manifests/certify-20260923T172347Z-2160027.json): passed 2 roots, 2.902 seconds.
- [Final release closure at those bytes](manifests/certify-20260923T172648Z-2189247.json): passed 4 roots, 5.318 seconds.
- [Final exact frame vectors at those bytes](manifests/certify-20260923T172738Z-2197528.json): passed 1 root, 0.941 seconds.

`host/workflow-host.lisp` loaded in an ACL2 source smoke session;
`tests/test_bp_app_native.py` compiles, but the native application test has
not run against a rebuilt shared image. No full dependent-root closure is
claimed here; the central `books/frame-journal.lisp` table change affects
many roots, and the integrated batch owns that run. `make check` on this
lane fails because the pre-existing T4 evidence note points to two missing
manifests and the generated ledger is stale; this lane did not hand-edit
ledger output. The original PRF-034 replay theorem concerns
`fn-bp-replay-journal`; the follow-up host-called refinement is recorded
below.

The follow-up book `books/bp-release-replay-status.lisp` proves
`fn-bprl-replay-work-status-is-durable-status-restarted` over the actual
`fn-bprl-replay-journal` caller. Its successful-replay premise means the
installed work status is exactly the one-restart status of the precrash fold
of the extended ACL2 interpreter, including `:undertake` and `:release`.
`tests/acl2/bp-release-tests.lisp` has a reached history with both new kinds,
and a malformed-suffix `must-fail` witness for dropping success. ACL2 8.7 on
`persvati` passed [the replay book](manifests/certify-20260923T173933Z-2312844.json)
in 2.801 certification wall seconds and [its test book](manifests/certify-20260923T174038Z-2322911.json)
in 1.504 seconds, using the same two-job toolchain and farm invocation form
above with `--timeout-seconds 60` for run `run-20260923T173930Z-73d0`
and `--timeout-seconds 90` for run `run-20260923T174035Z-6285`.
This proof narrows the prior replay assurance gap; a rebuilt native image and
full dependent-root closure remain the integrated batch's evidence.
