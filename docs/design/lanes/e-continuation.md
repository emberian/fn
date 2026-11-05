# fn2 layer E continuation (consumer wire, TLS/auth, web, peering, BP, CLI, packaging; present state at origin/dev a4bea27de, rewritten whole 2026-11-04)

Layer doc: `docs/e-surface.md`. Brief: `docs/design/briefs/FN2-LAYER-E-SURFACE.md`. Rulings the kinds code:
`REVIEW-ARGON-RESPONSE-20261031.md` (ack decided by the arm; append's outcome lookup before the write grant; v2
cursors accepted, v1 issued while fields fit; a wait's read starts at the cursor's position). In flight on
lane/consumer-socket (the consumer verbs over a real socket) and lane/m2-measure (the M2 cut count on H's
line); results are those lanes'.

## On dev (E, newest first)
- 9860d85a5 (H2): `fn2-cns` serves register, read, wait, ack, position and status: frame parameters decoded, the
  recorded (position, version) looked up in `fn2-consumer-cursor`, the frontier through `fn2-successor-published`,
  register stages `fn2-consumer-names-put` and `fn2-consumer-cursor-rebase`, ack per Argon ruling 1 (equal:
  accepted without a transaction; lower: `:behind`; above the frontier: `:beyond-frontier`), read and wait
  range-read `fn2-addr` from cpos+1 and park on `:wait-row`. K10
  (`fn2-k10-consumer-delivery-comes-from-committed-log`) and witnesses in `books/owed-consumer.lisp`; the
  full-verb turn test (register, wait, post, wake, read, ack, position, status) in `tests/sim-layer-e.lisp`.
- 2456161b6 (F6): `fn2-ctl` parses frames (`fn2-ctl-parse-frame-pool`), dispatches into `fn2-cns` through
  `fn2-machine-take-fn2-cns`, encodes and posts the 6-byte reply; turn tests through `fn2-cw-loop`.
- aac7a29e7 (F5): `fn2-ctl-owner-p` compares the peer's w0 with `fn2-control-owner-uid` (the profile's
  `:owner-uid`), not root; `fn2-cns-next-gen`/`-grant-one-gen` check the waiter generation on the edge.
- Earlier: E3/E3b (port.lisp, consumer-port, the codecs FNCT and fncu v1/v2), E4a/E4b (the peer model,
  `owed-peer.lisp`, six witnesses), E5a/E5c (`cns-edges.lisp`), E5d (`sim/check-consumer.lisp`, CONSUMER), E.P1a.

## What serves
No consumer verb serves on a socket; the six run through `fn2-turn` in `tests/sim-layer-e.lisp`. H's line at
132ac2c62 prints `M2 cuts 0/12 (sim-layer-e over the served machines not yet run)`: the nightly has no
`H_NIGHTLY_M2` command. Interim rows that are E's: COMPRESS (E2), XFNCATCHUP (E4).

## Owed, with the exact next step
1. The consumer over the `:local` listener on a socket (lane/consumer-socket) and the M2 count on H's line
   (lane/m2-measure: `H_NIGHTLY_M2` writes `OUT/m2.json` `{"passed": n, "total": 12, "source": ...}`).
2. `fn2-cns` and `fn2-ctl` to child form (both core form today); ctl's frame/reply/closing/draining phases repeat
   conn's carrier by hand until the form has a `:carrier` word.
3. Hand `defthm`s in `books/cns.lisp`: 9 (e.g. `fn2-ctl-parse-frame-pool-natp-0`); each is either about a
   declared operation or goes (MACHINE-FORM ruling).
4. `tests/consumer-codec-unit.lisp:18-20` reads fixtures at `../../tests/fixtures/...`, outside the tree since the
   promotion (49787612f); the path is `../tests/fixtures/...` or `fixtures/...` relative to the book.
5. E1 TLS, E2 credentials and grants (the Grant record is C's), E4 peering (needs A's `fn2-issue-connect`), BP,
   E6 operator verbs.

## Seams
- From A: the `:local` listener (uid/gid), `fn2-control-owner-uid`, the timer service (named, not defined).
- From B: the control connection rows (`fn2-b-ctl-rows`, `fn2-b-ctl-slot`).
- From C: `fn2-consumer-cursor`, `fn2-consumer-names`, `fn2-successor-published`, `fn2-successor-stream-member`.
- From D: the read rows (request S reads row 2X + S), the txn's `:consumer` mode.
