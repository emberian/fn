# PRF-068 native consumer status codec

The host's `fn-native-control-host-consumer-status-reply-encode` and
`fn-native-control-host-consumer-status-reply-decode` call the exact ACL2
functions `fn-ncl-status-reply-encode` and `fn-ncl-status-reply-decode`
(`host/native-control-host.lisp:108-115`). Native control invokes those
wrappers at `host/native/control.lisp:125` and `:636`. In
`books/consumer-local-control.lisp`,
`fn-ncl-status-accepted-reply-roundtrip` proves that decode of encode returns
the original accepted ACK, committed frontier and event-distance when ACK and
frontier are uint32 values, ACK is no greater than frontier, and the gap is
exactly frontier minus ACK. `fn-ncl-status-nonaccepted-reply-roundtrip` proves
the same value direction for refused, uncertain and fault replies with empty
fields. These are general theorems over the host-called codec, not enumerated
vectors. The frame bridge uses `fn-frame-decode-of-host-framing` and the
existing bounded uint32 parser roundtrip. It depends on the constrained
32-octet frame-digest shape, not on a proof of a concrete hash algorithm or
collision resistance.

`tests/acl2/consumer-local-control-tests.lisp` reaches a positive accepted
reply with ACK 3, frontier 11 and gap 8, plus a frontier at the uint32 ceiling.
Its four `must-fail` cases separately drop the accepted theorem's ACK uint32,
frontier uint32, ordering and exact-gap premises while keeping the other
premises true. Refused, uncertain and fault roundtrips have concrete witnesses;
an unrecognized status is the `must-fail` tooth for their membership premise.
The test book also retains malformed-gap and overbound-frame refusal cases.

The source is the isolated worktree based on `dev` at
`8c61c098954e19396e2d0c529d097a1d8b2d33dc`. The certified SHA-256 file
digests are `e0b1beca8a20090659f76dcdfae41ded8ad35308f77babfaf09e35bea1d00891`
for `books/consumer-local-control.lisp` and
`3ee0f9503215549885c3dc3ea146ad57560d2aa78b1c45bc4e69fd6a3b1bc08c`
for its test book; the manifest records the same before and after values.
The exact selected invocation was
`python3 tools/farm.py submit hbox --jobs 2 --timeout-seconds 90 --remote-root /tank/fn/lanes/native-consumer-status-codec-8c61 books/consumer-local-control tests/acl2/consumer-local-control-tests`.
Run `run-20260924T035420Z-eeaf` passed both roots in
[`certify-20260924T035424Z-832192.json`](manifests/certify-20260924T035424Z-832192.json).
It installed or kept 95 of 97 exact source/toolchain dependencies from 12
cache origins and certified the two changed roots. The toolchain was ACL2 8.7
at `/tank/fn/toolchains/w28/acl2-literal-4g`, identity
`d5f2b9f0d2cf68c6074ea7046fbd2e560d2984fe22d7e03f93045975ac889f0`,
with Python 3.12.7 for the runner.

The reverse dependency check also selected the host wrapper test root. Run
`run-20260924T035733Z-99ec` passed both
`host/native-control-host` and `tests/acl2/native-control-host-tests` in
[`certify-20260924T035738Z-838647.json`](manifests/certify-20260924T035738Z-838647.json).
`python3 tools/green_check.py --changed-since 8c61c098 --strict --summary`
then reported two changed books and their one dependent green at these bytes.
After the curated proof events regenerated the ledger and both manifests were
filed, `make check` exited 0; the later `cite_check --summary --strict` and
`ledger.py --check` also exited 0 after the current-work note was updated.

The five added proof events each took at most 0.03 seconds in certification.
The book took 12.17 seconds, mostly the existing decoder guard proof at 8.8
seconds plus ACL2 load and compilation overhead; this packet adds no served
path work. An earlier scoped run, `run-20260924T035147Z-eced`, failed because
two supporting theorems had `:rule-classes nil` yet their names remained in a
hint's disable list. The hint was corrected and both main theorems were
re-admitted in a fresh bounded hbox proof session before the passing run.

This packet does not change executable codec definitions. The earlier
`e160442f` image exercised status with a durable ACK, but no new native image
was built for these proof-only bytes. The joined topic/index composition's
native qualification remains separate. PRF-068 therefore remains in progress;
these codec theorems make no claim about filesystem recovery or unread article
counts.
