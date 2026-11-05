# fn2 layer D continuation (machines, scheduler over principals, NNTP; present state at origin/dev a4bea27de, rewritten whole 2026-11-04)

Layer doc: `docs/d-machines-nntp.md`. Brief: `docs/design/briefs/FN2-LAYER-D-MACHINES-NNTP.md`. The P.1-P.5 port
designs and the 35 asks of the form seat are in history (this file before this commit); every port they described
has landed. In flight on lane/article-octets (D6 3/n); results are that lane's.

## On dev (D, newest first)
- 132ac2c62: the peer bit comes from the profile's `:peering-interim` flag (`fn2-input-config`'s `peering`
  column, `fn2-conn-peering-p`), set only where peering is on and the family is not none; conn-unit's control:
  same family without peering answers TAKETHIS 502 and drains nothing. E4's grant replaces the flag.
- 21b661477 (H5, D5 3/n): CHECK (238/438), IHAVE (335 then 235/436/437, 435 on a known id) and TAKETHIS
  (239/436/439, the block drained through the feed path when no upload row is free) through the cursor's
  identity seek; MODE STREAM admitted; `sim/check-wire.lisp` learns TAKETHIS's immediate block.
- da003258a (H1): `fn2-conn` and `fn2-upload` on `defmachine-arms` in leaf books
  (`assembly-callbacks-d-conn.lisp`, `-d-upload.lisp`, helpers in `-d.lisp`); schemas and links in
  `conn-kind.lisp`, `upload-kind.lisp`; attached in `assembly-attach.lisp` and `owed-conn.lisp`.
- 0f568f89b (H3): RFC 3977 §4 wildmat (`fn2-wildmat-match-p`), LIST variants (ACTIVE ACTIVE.TIMES COUNTS
  NEWSGROUPS SUBSCRIPTIONS OVERVIEW.FMT HEADERS; 503 for DISTRIB.PATS and DISTRIBUTIONS), NEWGROUPS, NEWNEWS,
  HDR/XHDR over message-id, range or current article.
- 2456161b6 (F6): POST stages overview and group-address entries (`fn2-txn-stage-article`) so a posted article is
  visible to the cursor; the cursor's body comes from the overview row's stored tail.
- c985342f8 (D5 2/n): the txn's durable POST through B's S12 and C's `fn2-successor-emit`; 2314c1e90 POST in
  CAPABILITIES. Earlier: the cursor (D6 1/n eee0eb09e), D7 4/n-a (requests, grant source, principal id), D0, D2.

## What serves (H's line at 132ac2c62, both carriers, 0 disagreements)
All 26 served verbs are D's replies. Interim: XPAT and XFN-ZARTICLE (D6), STARTTLS (D7).

## What the served path does that its commit messages overstate
- ARTICLE/HEAD/BODY: headers are rebuilt from the overview row (`fn2-cursor-pool-headers`), the body is the
  overview row's stored tail, or `xlen` octets of `x` when the row has none (`fn2-cursor-put-x-loop`,
  `books/cursor.lisp:315`). `fn2-block-read` has no caller. lane/article-octets owns this.
- `*fn2-txn-groups-max*` is the literal 6 (`books/txn.lisp:43`).
- Kinds in core form (`defmachine-arms K` default mode): conn, upload, txn. Only the cursor is child form.

## Owed, with the exact next step
1. D6 3/n (lane/article-octets): ARTICLE/HEAD/BODY from the stored octets through `fn2-block-read` as an `:issue`
   with its completion; the fixture asserts posted octets with extra headers, dot-leading lines and several pages.
2. XPAT and XFN-ZARTICLE (the last two D6 rows).
3. The txn to `:children` once C's successor ops carry `:child` (c-continuation item 2) and B's posture does.
4. `*fn2-txn-groups-max*` from the profile, not a literal.
5. D7 5/n-6/n: timers and TLS admission over A's timer service (named, not defined) and STARTTLS (E1).
6. D26: `assembly-callbacks-d-conn` 336 s and `cursor` 249 s on bb2 (132ac2c62's certify).

## Seams
- From C: the successor ops, `fn2-identity-decide*`, `fn2-read-seek`; from B: `fn2-commit-admit-txn`, the posture,
  `fn2-block-read`; to E: the read rows (request S reads row 2X + S), `fn2-machine-take-fn2-cns`.
- Unit books: conn-answer-unit, conn-unit, upload-unit, cursor-unit (over the seeded store), txn-unit,
  request-unit, accounts-unit.
