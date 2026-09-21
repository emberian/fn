# W22 native outbound feed phase handoff

Source: `8ebf77ca4999adee638f6d78434282e0625838ec` on
`w22/native-outbound-feed`; the phase/framer slices are `87796b51` and
`fb114842`, the carried-table proof is `86abeac1`, and this correction is
`8ebf77ca`. The clean-source correction certification is
[`certify-20260921T110534Z-24326.json`](../evidence/manifests/certify-20260921T110534Z-24326.json).
The earlier component manifest
[`certify-20260921T104133Z-7518.json`](../evidence/manifests/certify-20260921T104133Z-7518.json)
covers the original framer and phase roots.

`books/feed-wire-input.lisp` owns bounded reply-line framing. It accepts at
most 512 observed octets per call and yields one event per call; a caller must
pass `nil` to drain a retained complete line before supplying more input.
`books/feed-connection.lisp` owns the connection phase on that state. Only
200 or 201 opens a session. A configured streaming peer emits ACL2's exact
`MODE STREAM` bytes and becomes ready only after 203; there is no fallback.
Before ready, a framed response never reaches `fn-owner-feed-octets` and no
feed tick can offer an article.

`host/owner-host.lisp` exposes `fn-owner-feed-dial-open`,
`fn-owner-feed-reply-chunk`, and `fn-owner-feed-lost`. The wrapper calls the
connection machine once per event and calls the established feed port only on
its `:reply` result. `host/native/feed-service.lisp` owns nonblocking sockets,
monotonic observations, worker lifecycle, and copying ACL2-authorized command
octets only after `fnn-owner-feed-flush` has durably appended FNFD records.
It has no raw CRLF scan, reply-code parser, greeting decision, MODE rendering,
or delivery decision.

The correction removes whole-table recognition from every served dial, reply,
and loss call. `books/feed-connection-invariants.lisp` establishes the empty
carried table and preserves it through put/remove; the reply path validates
only its selected `fn-fc-statep`. A valid negative greeting or MODE result is
mapped by the actual host wrapper to `:connection-refused`, distinct from the
feed port's `:refused`, so it closes the peer without re-flushing an unrelated
FNFD batch. `fnn-recv` now accepts an optional positive maximum and sizes its
buffer before `read(2)`; the feed supplies ACL2's 512-octet limit. The stop
hook only shuts down live sockets while its runtime lock excludes final close;
the worker's unwind-protect performs the sole close and rejects a dial that
finishes after stop.

The Makefile adds both books and their test roots; `host/native/build.lisp`
includes the books so the saved image has the same ACL2 subjects as the host
wrapper. The native raw module is **not activated by this source alone**. Its
load after `host/native/owner.lisp` and registration through the frozen
`*fnn-owner-{start,stop,close}-hooks*` are owned by the inbound/lifecycle
integration, where hooks start after listener bind, wake nonblockingly at the
serialized stop boundary, and join before Store/FNFD close.

Validation on macOS arm64, ACL2 8.7 / SBCL 2.6.8:

```sh
python3 tools/certify_books.py --jobs 1 \
  books/feed-wire-input tests/acl2/feed-wire-input-tests \
  books/feed-connection tests/acl2/feed-connection-tests
python3 tools/certify_books.py --jobs 1 \
  books/feed-connection-invariants tests/acl2/feed-connection-invariants-tests
FN_ACL2=acl2 python3 tools/host_check.py host/owner-host.lisp
tests/test_owner_feed_connection_host.sh
tests/test_native_feed_service_raw.sh
sbcl --noinform --script tests/native_io_progress.lisp
```

The certified tests cover split CR/LF, two coalesced lines drained one at a
time, exact 510/511 boundary behavior, split greeting and 203, rejected
200/201 and MODE replies, and lost-connection closure. The correction invariant tests establish
selected-state and put/remove preservation with premise teeth. The actual
host-wrapper `ld` witness checks greeting 400 and MODE 500 map to
`:connection-refused`, while a ready reply retains its port tag. The raw SBCL
harness checks split/coalesced phase drains, no tick before ready, one flush per
post-ready line, no reflush on connection refusal, stop-time shutdown without
close, worker-owned final close, dial-after-stop rejection, and the bounded
`read(2)` allocation. These are not native-image or peer interoperability
evidence.

The remaining concrete dependency for a two-native-node feed gate is the
owner ingress lane's source-address peer opening and transit handler. The
current native reader listener does not accept `IHAVE`; using a Python node or
reader socket would not test this feed path. After that integration builds a
source-matched image, the live gate must observe split/coalesced greeting and
203 input, absence of an offer before `:ready`, one real native article
transfer, and a lost-reply/restart duplicate outcome under the existing ACL2
feed proofs.
