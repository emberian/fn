# w10/nntp-tests: the last unowned red root, and a served POST that never replied

Branch `w10/nntp-tests`, worktree `build/lanes/w10-nntp-tests`, from dev
`1019c97`. Two jobs; both found a real defect rather than a stale pin.

## Per root

| root | verdict | evidence |
| --- | --- | --- |
| `tests/acl2/nntp-legacy-tests` | **CERTIFIED**, 81 assertions | laptop, ACL2 8.7, `build/acl2/certify-20260920T212727Z-14708` |
| `books/served` | **CERTIFIED** with this lane's fix | persvati `run-20260920T213058Z-5a53`, evidence `build/acl2/certify-20260920T213104Z-3494099` |
| `tests/acl2/served-tests` | **CERTIFIED**, 79 assertions | laptop, ACL2 8.7, `build/acl2/certify-20260920T213830Z-28697`, over the `books/served.cert` that run produced |
| `books/nntp-auth-invariants`, `books/ideal` | CERTIFIED (same run) | persvati `run-20260920T213058Z-5a53` |
| `books/owner-feed`, `books/owner`, `books/owner-invariants`, `books/owner-config`, `tests/acl2/owner-tests` | **NOT ATTEMPTED** -- every one failed at `(include-book …)`, cascading from `books/peer-feed-invariants` | persvati `run-20260920T213058Z-5a53` |
| `books/peer-feed-invariants` | **open at `fn-feed-selection-is-queued`** -- foreign to this lane, see the NOTE below | persvati `run-20260920T213058Z-5a53`, `books--peer-feed-invariants.certify.log:20330` |

## Job 1: XPAT joins, and then fn refuses the join

The failing assertion expected `221` with an empty list from
`XPAT subject 1-1 *T *t*` (gate `dev-909e055`, persvati
`~/fn-gates/dev-909e055/build/acl2/certify-20260920T185218Z-1964399/tests--acl2--nntp-legacy-tests.certify.log`).
Of the three candidate explanations — wrong code, wrong expectation, drifted
fixture — **the second is true of the assertion and the first is true of fn**,
and they are the same fact seen from two sides. The fixture did not drift.

`fn-nntp-xpat-join` (`books/nntp-responses.lisp:1524`) joins with one SP,
exactly as RFC 2980 §2.9 says and exactly as INN's `Glom` does. One line
later `fn-nntp-xpat-response` (`:1620`) parses the joined octets with
`fn-wildmat-parse`, which enforces RFC 3977 §4.1's `<wildmat-exact>`
(`fn-wildmat-exactp`, `books/wildmat.lisp:182`). SP is %x20 and is excluded.
So **every** XPAT whose pattern has more than one token gets `501`, and
`fn-nntp-xpat-join`'s multi-token branch can never produce a match.

Measured on both sides (`planning/evidence/inn-xpat-2026-09-20.md`):

- fn, `tools/acl2 --timeout 240` over a driver rebuilding the fixture from
  `books/nntp-effects`: reply `501 syntax error`; the joined pattern parses to
  `(:ERROR :SYNTAX)`; `(fn-wildmat-itemp 32)` is `NIL`; `*T*` alone gives
  `221` and the line; `*Q*` alone gives `221` and the empty block.
- **INN 2.7.4, its own compiled `libinn.a` on hbox**, driven with `CMDpat`'s
  two library calls and no daemon started:
  `Glom` → `[*T *t*]`, `uwildmat_simple("Test", "*T *t*")` = **false**, so INN
  answers **221 with an empty list**; and `uwildmat_simple("T st", "*T *t*")`
  = **true**. `CMDpat` performs no syntax check on the pattern at all.

The assertion is repaired to `501` and is a **sharper** witness of the join
than the empty block was: controls beside it show each token alone parses and
`*t*` alone matches `"Test"`, so two-pattern semantics would have rendered a
line. Four more assertions pin the cause directly.

**Open, OB-XPAT-SPACE.** fn cannot phrase-search a header, which is XPAT's
ordinary use. The cure is a pattern grammar for header text admitting SP, in
`books/wildmat.lisp`, **without** widening `<wildmat-exact>` where
`newsgroup-name = 1*wildmat-exact` reads it. Owner: whoever holds
`books/wildmat`; it re-opens `wildmat-parser-invariants`,
`wildmat-matcher-invariants` and `wildmat-utf8-invariants`, which is why this
lane recorded it instead of taking it. `specs/nntp-audit.md`'s §2.9 row is
walked back in the same commit, and `tests/test_reader.py`'s unrun XPAT socket
transcript carried the same wrong expectation and is corrected.

Second divergence, the other way: fn reads `,` as wildmat alternation and
matches `*T,*t*` against `"Test"`; INN's `uwildmat_simple` reads it as a
literal and does not. RFC 2980's "at least one pattern in wildmat" is on fn's
side, so this is recorded and not changed.

## Job 2: the served path was not answering POST at all

`ad29ab6`'s fix is **correct and confirmed**: the two-wrapper projection
assertion `:PASSED` on persvati `run-20260920T212324Z-5a6f`
(`build/acl2/certify-20260920T212331Z-3421997`, line 641). The book then ran
two events further and failed at `(take 4 *fn-t-served-240*)` — a *second*,
deeper failure that the first had been hiding, which is the "certify-book
stops at the first failure" rule paying for itself.

The cause is not in the test. `books/served.lisp:767` read

    (fn-nntp-post-outcome (fn-peer-session-base (fn-served-conn-session conn)) …)

while a served connection's session is `fn-auth-open-session`'s
(`books/served.lisp:846`, `:859`) — an auth session over a peer session over
the POST-composed reader session. `fn-nntp-post-outcome`
(`books/nntp-post.lisp:251`) answers an argument that is not
`fn-post-sessionp` with **no effects at all** rather than an error, so
**the served path emitted neither 240 nor 441**: a posting client got the 340
offer, sent its article, and was never told whether it was stored. The host
line is `host/reader-host.lisp:159`. `books/owner.lisp:596` already used the
full chain; this was the one call site the auth wiring left behind, and the
w9/server-polish handoff had predicted exactly it ("`fn-served-post-outcome`'s
`(fn-peer-session-base (fn-served-conn-session c))` gains an
`fn-auth-session-base` inside it").

Fixed by inserting `fn-auth-session-base`, in the definition and in the
`:rule-classes nil` restatement beside it. No theorem statement was weakened
and none was removed.

**NOTE for whoever owns `books/served`: the same wiring gap is still on the
transit path, latent.** `fn-served-transit-outcome` (`books/served.lisp:791`
after this lane's edit) hands `(fn-served-conn-session conn)` — an auth
session — to `fn-peer-transit-outcome`, which wants a peer session. It is not
observable today *only* because the reply octets do not read the session:
`fn-peer-single` (`books/peer-inbound.lisp:525`) reaches `fn-nntp-single`,
whose effects are `(list (fn-nntp-reply-effect (fn-nntp-crlf …)))` and ignore
the session argument (`books/nntp-session.lisp:88`), and `fn-peer-echo-reply`
ignores it outright. The moment any transit reply becomes state-dependent it
goes wrong silently, the way POST did. The edit is one accessor —
`(fn-auth-session-base (fn-served-conn-session conn))` — and this lane did not
take it because `books/owner-invariants.lisp:1184` and `:1195` reason over
that definition and re-opening a 1500-line invariants book for a change with
no observable effect is not this lane's trade.

**NOTE, foreign, and it blocks five roots: `books/peer-feed-invariants` is
open on dev `1019c97`.** The board's w6/peering-feed-4 line reads "the book
has no open form"; measured on persvati, `fn-feed-selection-is-queued` FAILS
after 150.5 s and 106,806,621 prover steps with a printed checkpoint (a real
proof failure, not a timeout). That theorem is not one of the eleven that
lane closed -- it dates from `1dd3374 w6/peering-feed`, the original lane --
so the board line and this measurement are about different forms and both can
be true. `books/peer-feed-invariants` is not in `books/served`'s dependency
path (it includes only `peer-feed`), so this is not this lane's doing; but
`books/owner-feed` includes it, and `books/owner`, `books/owner-invariants`,
`books/owner-config` and `tests/acl2/owner-tests` all failed at their
`include-book` behind it and were never attempted. **This lane's change to
`books/served.lisp` is therefore unverified against the owner chain**, which
is the one thing left open here: whoever unblocks `peer-feed-invariants`
should re-run `--affected-by books/served.lisp --closure` and confirm
`books/owner-invariants` (it reasons over `fn-served-post-outcome`'s
definition at `:1139`, `:1443`, `:1472` and `:1515`).

Also worth knowing: `tests/test_post.py:107` asserts the 240 over a real
socket and names `fn-served-post-outcome` in its docstring. It would have
caught this defect; `specs/nntp-audit.md` records that the Python suites
"did not run: they drive a live owner, which needs the certificates the
cascade above withholds". The same cascade hid the defect and delayed it.
