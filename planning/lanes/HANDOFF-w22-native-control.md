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
ordinary owner thread performs stop, shutdown-only client wakeups, worker joins,
module close, FNFD/Store close, clears the signal-visible fd, closes the
listener, and restores the prior globals. Worker threads remain the sole final
closers of client sockets, preventing a cached raw descriptor from being
reused underneath their I/O.

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
`build/acl2/certify-20260921T104008Z-6541/manifest.json` (SHA-256
`e9eede4e8cb46064c2d3a503a7e355064d0c22bf9fb4b62bb86399d03db750a2`). It
records the exact ACL2/SBCL versions, source digests, and per-book results.

Focused native runtime evidence covers two concurrent successful clients with
exact stored bytes, a different Store refused from stealing the same control
path, posting disabled for both control and NNTP, a lost reply after durable
submission reported as uncertain and recovered after restart, SIGTERM with
active NNTP and partial-frame control clients, a repeated SIGTERM during
cleanup, a pre-listener SIGTERM that starts no resource module, and immediate
native reopen with 200/205 service. The runtime command and platform evidence
are appended when the saved-image run completes.
