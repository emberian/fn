# Handoff: `w12/wire-block`

Lane branch `w12/wire-block`, started at `8b474e2`.  The implementation
checkpoint is `c3b5aae8a20a2d021e0a630982f4c54d2ed624ad`; this handoff and
the bounded receiver-composition evidence are the follow-up packet.

## Boundary contract

`books/wire.lisp` owns outbound framing.  Its executable
`fn-wire-render-feed-command` takes the complete ACL2 feed effect and returns
either `(:ok octets)` or `(:refused reason)`.

- Article source is accepted only as a proper, bounded octet list made from
  complete CRLF lines.  The renderer preserves every source octet and every
  trailing empty line, stuffs each line-leading dot, then appends the NNTP
  block terminator `(46 13 10)`.
- Empty source is valid and renders to that terminator alone.  Bare LF,
  malformed CR, a non-octet, improper list, unterminated source and source
  exhaustion are distinct refusals.  Command-line splitting is bounded
  independently; an offer command carrying an article suffix is refused.
- `CHECK` and `IHAVE` remain their ACL2-issued command line; `TAKETHIS` keeps
  that line and renders the following article block.  Other feed effects are
  rendered as article blocks.

The host projection is deliberately narrow.  `fn-owner-feed-render-command`
in `host/owner-host.lisp` calls the renderer with
`*fn-nntp-max-initial-line-octets*` and `*fn-store-max-payload*`.
`fn-owner-feed-install-feed` stores only the resulting octets and the
separate status.  `Acl2Owner.feed_command` refuses a non-`ok` status, and
`Owner.feed_write` supplies the exact bytes to `Session.send_block`.
`Session.send_block` now does exactly `sock.sendall(rendered)`: it makes no
line, dot-stuffing, terminator or trimming decision.

When merging with feed durability, retain its fence exactly:
`if self.feed_uncertain or not command: return`.  This lane's intended body
after that guard is only `feed.session.send_block(command)`.  The shared
`fn-owner-feed-install-feed` globals need both lanes' fields; no Journal or
trailer decision belongs to this packet.

## Evidence

The source-pinned ACL2 closure was run on hbox, no more than four jobs:

```
python3 tools/farm.py submit hbox --jobs 4 \
  --remote-root /tank/fn/lanes/w12-wire-block \
  --closure tests/acl2/wire-tests
python3 tools/farm.py wait hbox run-20260921T064010Z-4382
```

Manifest `certify-20260921T064014Z-1667226` reports `status: passed`, the
three requested roots `books/wire`, `books/wire-invariants`, and
`tests/acl2/wire-tests` all passed, zero failures, ACL2 8.7/SBCL 2.6.8 on
hbox, 2.055 s wall, and no forbidden facility in the local closure audit.
Its certified bytes are SHA-256:

| source | SHA-256 |
| --- | --- |
| `books/wire.lisp` | `5bd3191d76a7a1b7546b0b94854c41723579bb86508ff870a63cec4cf8c8a09d` |
| `books/wire-invariants.lisp` | `262352e5d7f0dccc6950d145f8a1046c29040cf8e245e65aecf1cd26456727c3` |
| `tests/acl2/wire-tests.lisp` | `7112f45dc9bbfef8a05621f6360a313c4a8042176ae120243c1944d8814891f8` |

`fn-wire-after-line-unstuffs-rendered-source-line` is a general theorem over
the receiver transition: under the carried article-body bound, applying the
actual receiver's `fn-wire-after-line` to `fn-wire-stuff-line source` retains
exactly `source`.  Its teeth include a literal dot-only source becoming two
dots on the wire and the bounded body-overflow close branch.

`tests/acl2/wire-tests.lisp` additionally proves one bounded full composition
through `fn-wire-drive`, the ACL2 transcription of the reader host loop.  The
rendered article has a literal leading-dot line, a dot-only line, internal
empty line and two trailing empty lines; its sole `:article` event has exactly
those seven source lines and ends back in command mode.  This is a theorem of
the actual receive path, not a Python formatter test.

The Python boundary checks also passed:

```
python3 -m unittest tests.test_feed       # Ran 10 tests, OK
python3 -m py_compile tools/feed_wire.py tools/run_owner.py
```

A narrow live ACL2 bridge witness called the host projection itself with a
`TAKETHIS` line followed by a dot-only source line.  It returned
`(:OK (... 13 10 46 46 13 10 46 13 10))`: the source dot was doubled and the
terminator appended before Python received the bytes.

## Scope still open

This packet does **not** claim a universal theorem that every successful raw
`fn-wire-render-block` byte vector, at every permitted size, is consumed by
`fn-wire-drive` into its original article.  The certified theorem is the
per-line inverse plus the non-degenerate bounded complete witness above.
The remaining stronger composition theorem needs a raw-byte/CRLF induction
and an output-length bound, then teeth for its hypotheses.  Until that lands,
the framing implementation and its bounded witness are certified, while a
whole-input round-trip proof is open.
