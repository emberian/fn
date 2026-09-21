# Native TCP connect deadline boundary

Source: `b8b0eeebe2ebf6df2bb8c522e91a288eda169390` on
`w25/native-connect-deadline`, tested on macOS arm64 with SBCL 2.6.8 and ACL2
8.7.

`host/native/io.lisp` now creates a TCP socket, sets `O_NONBLOCK`, performs one
`connect(2)`, and on `EINPROGRESS` waits for output readiness under one absolute
deadline before inspecting `SO_ERROR`. A successful socket is already
nonblocking and is owned by its caller. A timeout or nonzero `SO_ERROR` closes
the private socket and reports the kernel errno as `fnn-os-error`; it does not
convert refusal into a timeout. `host/native/feed-service.lisp` obtains its
10-second completion policy from ACL2's `fn-owner-feed-connect-timeout` and
passes it explicitly to that shared helper.

Commands and results:

```sh
sbcl --noinform --script tests/native_io_progress.lisp
# native-io-progress: ok

tests/test_native_feed_service_raw.sh
# native feed raw phase/sequencing test passed

FN_ACL2=$(command -v acl2) tests/test_owner_feed_connection_host.sh
# owner feed connection host wrapper test passed (including failing-load rejection)

FN_ACL2=$(command -v acl2) python3 tools/host_check.py host/owner-host.lisp
# host_check: 1/1 host files load alone
```

`native_io_progress.lisp` makes a real loopback TCP connection, verifies that
its returned descriptor retained `O_NONBLOCK`, and verifies that a closed
loopback listener reports `ECONNREFUSED`. It also injects pending completion to
show one `connect(2)`, output readiness under the original deadline, a pending
state that cannot reset that deadline, and a zero-time poll that does not spin.
The feed raw harness verifies that the ACL2 dial plan's timeout reaches
`fnn-connect` as its `:timeout` argument.

This is raw-boundary evidence, not a saved-native-image or two-node feed gate.
The timeout begins only after synchronous DNS resolution; `getaddrinfo` can
still block the sole feed worker, and no resolver thread is terminated. The
worker also visits peers sequentially, so many peers can delay when a later
peer's TCP attempt starts. Those are remaining availability and scheduling
limits, not covered by the per-attempt TCP deadline.
