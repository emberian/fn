# Handoff: `w14/wire-roundtrip`

Lane branch `w14/wire-roundtrip` closes the universal outbound-block / wire
driver proof left open by `HANDOFF-w12-wire-block.md`.  The implementation and
teeth checkpoints are `490fe35`, `c68a1fb`, and `35c1a3c`.

## Proved composition

`fn-wire-feed-proper-of-rendered-block-lines` is the cumulative induction over
the real byte feeder.  From a quiescent article state, clean source lines, the
cumulative decoded-body bound, and the physical-line profile
`body-limit + 1 <= line-limit`, it feeds every octet of
`fn-wire-render-lines` and the final dot CRLF through `fn-wire-feed-proper`.
It returns to command mode with one article event containing the exact prior
body plus every new source line in order.  Dot-only, dot-leading, empty, and
trailing-empty lines use the same theorem; there is no second parser.

`fn-wire-drive-of-successful-render-block-preserves-source` lifts that fold
through `fn-wire-drive-is-feed-proper`.  For every positive receiver body
limit, every successful `fn-wire-render-block article article-limit`, and
`article-limit <= body-limit`, the actual rendered octets produce exactly one
article event containing the scanner's source lines, and
`fn-wire-source-lines` of those lines equals `article`.  The theorem carries
the exact receiver framing limits: physical lines are capped at
`body-limit + 1`, while decoded retained input is capped at `body-limit`.

`fn-wire-drive-of-host-rendered-article-preserves-source` names the full
host-renderer composition.  Its outbound subject is
`fn-wire-render-feed-command`, called by `host/owner-host.lisp:483`.  Its
receiver start is the result of the same
`fn-wire-begin-article-with-line-limit` expression used at
`books/served.lisp:346`, proved equal to the receiver profile by
`fn-wire-served-article-profile-is-outbound-receiver-start`.  Its article-arm
hypotheses exclude the host's nil no-command sentinel and the CHECK, IHAVE,
and TAKETHIS command arms.  Under renderer success and
`article-limit <= body-limit`, it reaches the same exact event/source result.

The non-degenerate witness in `tests/acl2/wire-outbound-tests.lisp` contains
an ordinary line, an empty separator, a dot-leading line, a dot-only line, and
two trailing empty lines.  The test book has one `must-fail` counterexample
per premise of both exported composition theorems: positive command/body
profiles, nonempty article-arm selection, each excluded command prefix,
renderer success, and the article/receiver limit relation.

## Certification evidence

The owned source-pinned ACL2 closure ran on hbox with four jobs:

```text
python3 tools/farm.py --jobs 4 --closure \
  --remote-root /tank/fn/lanes/w14-wire-roundtrip \
  submit hbox tests/acl2/wire-outbound-tests
python3 tools/farm.py --wait-seconds 60 \
  wait hbox run-20260921T090359Z-cb57
```

Manifest `certify-20260921T090412Z-1906989` reports `status: passed`, no book
failures, ACL2 8.7/SBCL 2.6.8 on hbox, four effective jobs, and 45.787 seconds
wall time.  Its requested closure contains `books/wire`,
`books/wire-invariants`, `books/wire-outbound-invariants`, and
`tests/acl2/wire-outbound-tests`; all four passed.  The local-source audit
found none of `defaxiom`, `defttag`, `include-raw`, `set-raw-mode`, or
`skip-proofs`.

| source | SHA-256 |
| --- | --- |
| `books/wire.lisp` | `69faa44d2125fbf005a2e8bb0287fc779cd14d5b5ef4881fc2b78fb11ae23ef2` |
| `books/wire-invariants.lisp` | `f80efbfba1d072d73036348ceab355e35376ef0310430eb5af0b99aa69013aba` |
| `books/wire-outbound-invariants.lisp` | `1139d5dadf0fe494a989d2e6058b274631495c1f297dbdb97c18e896de068ea7` |
| `tests/acl2/wire-outbound-tests.lisp` | `77a9639f4d0ea606d76c678d4553d5976c5f12b08a33e52e671c54f05853e088` |

The archive runner did not preserve Git revision/dirty fields, so the source
digests above are the content pin.  Local ACL2 8.7 also passed the theorem
book (`certify-20260921T085913Z-16081`) and teeth book
(`certify-20260921T090339Z-19709`).

## Scope boundary

This lane proves byte-for-byte source preservation through the requested
`fn-wire-drive` adapter-loop semantics and bridges the exact served article
profile.  The production reader host calls `fn-served-step`, which dispatches
the resulting article event into authentication and injection state.  This
lane does not claim a new theorem about that later dispatch or durable
submission; those remain covered by the served, POST, and injection books.

