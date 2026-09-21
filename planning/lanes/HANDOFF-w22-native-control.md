# Handoff: W22 native local control

The public `fn operator CONFIG post` path is now a native AF_UNIX client. ACL2
owns the bounded argv plan, the sealed FNCT request and reply grammar, request
field validation, the result vocabulary, the adjacent control-lease path, and
CLI status and exit projections. Raw Lisp reads one bounded regular article
file and transports those octets; it never opens the Store.

The server enters `fn-owner-control-submit` while holding
`fnn-owner-serialized`, then calls the shared
`fnn-owner-complete-bound-submission` sequence: ACL2 admission, `:taken-control`,
durable FNFD intent, the actual `fnn-owner-attempt` Store call, durable
resolution, and `fn-owner-control-outcome`. Posting disablement updates the one
owner injection configuration used by both NNTP POST and control admission.

The resource lifecycle lists are `*fnn-owner-start-hooks*`,
`*fnn-owner-stop-hooks*`, and `*fnn-owner-close-hooks*`; each callback receives
the owner service. Semantic `*fnn-owner-startup-hooks*` run after recovery and
before listener bind. Resource start runs after bind and before accept, stop
runs inside the owner stop boundary, and close runs after owner workers join
but before FNFD and Store close.

SIGTERM while owner mode is active sets one process-global monotonic request
flag and calls raw `shutdown(2)` on the captured, still-open listener fd. The
owner and control listeners use the same one-second bounded, nonblocking accept
observation, so an ordinary owner thread consumes the request even where
shutdown does not wake a blocking accept. That thread performs stop,
shutdown-only client wakeups, worker joins, module close, FNFD/Store close,
clears the signal-visible fd, closes the listener, and restores the prior
globals. Worker threads remain the sole final closers of client sockets,
preventing a cached raw descriptor from being reused underneath their I/O.

Before stale-socket removal, control holds a nonblocking exclusive flock on
the ACL2-derived adjacent `.lock` regular file opened with `O_NOFOLLOW`. The
lease inode persists and remains held through listener and worker shutdown,
socket dev/inode cleanup, and final close. A second Store configured with the
same control path is refused. This assumes the configured parent directory is
protected from an independent entry-replacement attacker.

The exact owned ACL2 closure ran locally with:

```text
python3 tools/certify_books.py --jobs 4 --closure books/native-control tests/acl2/native-control-tests tests/acl2/native-control-host-tests books/native-config tests/acl2/native-config-tests books/native-operator tests/acl2/native-operator-tests tests/acl2/native-operator-host-tests books/owner tests/acl2/owner-tests
```

All requested roots and their closure passed. The source-pinned manifest is
`planning/evidence/manifests/certify-20260921T104008Z-6541.json` (SHA-256
`e9eede4e8cb46064c2d3a503a7e355064d0c22bf9fb4b62bb86399d03db750a2`). It
records the exact ACL2/SBCL versions, source digests, and per-book results.

Focused native runtime evidence covers two concurrent successful clients with
exact stored bytes, a different Store refused from stealing the same control
path, posting disabled for both control and NNTP, a lost reply after durable
submission reported as uncertain and recovered after restart, SIGTERM with
active NNTP and partial-frame control clients, a repeated SIGTERM during
cleanup, a pre-listener SIGTERM that starts no resource module, and immediate
native reopen with 200/205 service. The runtime command and platform evidence
for the exact raw source are in
`planning/evidence/native-control-ea20ed2c-2026-09-21-tests.log`; all five tests
passed on Darwin 25.6.0 in 17.202 seconds. The preceding blocking-accept failure,
the repair, and the local image-build limitation are recorded in
`planning/evidence/native-control-accept-shutdown-2026-09-21.md`.

The bounded-transport successor makes each frame use one absolute ten-second
deadline, requests at most the remaining allowance plus one sentinel from the
shared bounded receive primitive, retains chunks without prefix copying, and
performs one final vector copy at EOF. ACL2 projects the 16-active-client
ceiling; the accept thread returns ACL2's sealed `:busy` status without
creating a seventeenth worker. The focused successor closure was:

```text
python3 tools/certify_books.py --jobs 2 --closure books/native-control tests/acl2/native-control-tests tests/acl2/native-control-host-tests
```

All 24 closure books passed. The source-pinned manifest is
`planning/evidence/manifests/certify-20260921T111015Z-28175.json`
(SHA-256 `3bb1f1c5792b634170b9ceed2b376349a8f435eb0d5419d8557e9cdce150dfcd`).
`sbcl --script tests/native_io_progress.lisp` passed, including validation
that the caller's limit controls allocation before the read syscall. The
expanded seven-case native suite passed on Darwin 25.6.0 in 37.941 seconds;
its exact command and output are in
`planning/evidence/native-control-resource-b0dfdf55-2026-09-21-tests.log`.
As with the earlier local saved-image trace, the raw behavior is exact but the
local image build is not the clean build gate because unrelated copied
certificates have different absolute book names.

The final exact-source Linux gate then certified the remaining native build
roots, built the 282 MiB saved image with no uncertified-book marker, and ran
the same seven cases 7/7 in 14.445 seconds. Commands, source and manifest
digests, platform versions, result, and the one compiled-object fallback are
recorded in
`planning/evidence/native-control-linux-build-2026-09-21.md`; the exact runtime
output is `planning/evidence/native-control-linux-4ef765a6-2026-09-21-tests.log`.
