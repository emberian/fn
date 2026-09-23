# T9a: bounded feed port replay, 2026-09-23

`books/feed-port-replay.lisp` relates the record batches returned by
`fn-feed-live-port-step` to the feed state that same step maintains. Its
inductive keystone, `fn-feed-port-history-reconstructs-live`, says that for
an `fn-feedp` initial feed, replaying every accepted port record batch has
the same durable projection as the port's live run. Refused port steps keep
the feed and emit neither records nor effects. The final
`fn-feed-port-replay-is-live-modulo-inflight` has one premise: `records` is
exactly `fn-feed-port-history` for the event sequence. It then equates
`fn-feed-restart` of the replay and live states. That normalization clears
the socket and returns `:offered` or `:sent` entries to `:queued`; it retains
the queue, retired attempt frontier, entry ticks and backoff.

The native call path is `host/native/feed-service.lisp` `fnn-feed-tick` to
`host/owner-host.lisp` `fn-owner-feed-tick`, which calls
`fn-own-feed-port-tick-peer`. The existing
`fn-own-feed-port-peer-ready-is-live-port-step` equates this wrapper to the
bounded port. The new `fn-own-feed-port-tick-replays-the-live-tick` states
the exact one-tick replay equation over that host-called wrapper, the
selected feed and its representable FNFD batch. `fn-feed-live-next` calls
`fn-feed-tick-step` on a tick; `fn-feed-live-records` returns its offer
record. The host flushes that batch through `fnn-owner-feed-flush` before
copying command octets to the socket. Startup scans each FNFD frame through
`fn-owner-feed-journal-scan`, folds it through the owner's `:feed-replay`
transition, reconciles intents and appends a restart record before dialing.

`tests/acl2/feed-port-replay-tests.lisp` reaches five queued articles,
completes two, then stops after the third `:feed-sent` and before an outcome.
Replay plus restart queues the third and its first reopened command is
`CHECK`; the remaining two articles are still queued. The `must-fail` adds
a fabricated durable `239` for the third attempt, violating the crash-image
premise and separating the two restarted states. The same test checks all
durable fields via full feed equality. `tests/acl2/owner-feed-tests.lisp`
adds the two PRF-029 teeth: a valid non-target peer, and a malformed table
with a duplicate key that makes the target name resolve to a different,
non-offerable record.

Certification on persvati used ACL2 Version 8.7, toolchain identity
`1b4169e9c5825a4e1fc827767f00470ceafc459619e0a4fd522c48f1ba964286`,
`/home/ember/fn-gates/toolchains/w25/acl2-literal`, and
`/home/ember/fn-certcache`. The incremental selected-root run
`run-20260923T141851Z-e213` passed `books/feed-port-replay` and
`tests/acl2/feed-port-replay-tests` in 3.316 s of certification wall time;
the [source and closure manifest](manifests/certify-20260923T141854Z-530438.json)
records the exact bytes, dependency origins and result. The separate
`run-20260923T141718Z-b3c3` passed the changed PRF-029 test in 1.712 s;
its [manifest](manifests/certify-20260923T141720Z-515445.json) records
those bytes. `make check` reached the generated-ledger check and reported
stale `planning/ledger.json` and `.md`; root owns their generated update
during integration.

This is logical correspondence for the ACL2 port's generated record image.
It does not establish that a physical FNFD append produced that exact image
after process death, that the host's acceptance-time enqueue/commit records
equal a port-generated enqueue history for every owner transition, or that a
remote peer stores one copy. The protected two-node kill/restart gate is
being measured separately; it must count recipient Store articles apart
from outbound transport attempts and report accepted, refused and uncertain
outcomes distinctly.
