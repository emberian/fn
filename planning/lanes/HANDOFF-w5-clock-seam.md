# w5/clock-seam — the injection clock is per submission, not per connection

Branch `w5/clock-seam` from `dev` at `1c5b950`. Worktree
`build/lanes/w5-clock-seam`. Resolves the open defect recorded at the end of
`planning/lanes/HANDOFF-w5-owner-followups.md`: a connection could never post
a second time (`441 posting failed; the article was refused`), whatever the
article.

## The decision

`books/injection.lisp` derives a generated `Message-ID` from the clock
observation alone (`<wall.monotonic.fn@agent>`), and RFC 5537 §3.4 makes
`Injection-Date` the time of injection. The owner pinned **one** observation
per connection at accept and handed it to `fn-inj-decide`, so every submission
on a connection carried the identity of the first and the host's
duplicate-identity refusal fired on the second.

The seam: **two readings, with distinct jobs.**

- `observation` — pinned at accept, unchanged. It is the reader environment
  (`fn-nntp-env`: DATE, NEWGROUPS) so a reader's view of the server's calendar
  does not move under it.
- `injection` — supplied with **this** wire event. It is the only reading
  `fn-inj-decide` sees.

`fn-nntp-post-step (ps archive config observation injection wire-event)`. The
served connection is six fields (`fn-served-conn-injection`, index 5);
`fn-served-dispatch` passes it through and re-emits it. The owner rebuilds the
served connection on every read and puts `(fn-own-clock o)` — its current
observation, the one the host last reported through `(:observe obs)` — in that
field (`fn-own-read`, `fn-own-read-step`, `fn-own-outcome`, `fn-own-open`).
`tools/run_owner.py` takes a reading in `serve()` before each socket chunk.

**Not** at `fn-own-take-submission`, as the lane prompt proposed. The decision
— and therefore the identity and the 441 for a refused body — is made when the
article body arrives, inside `fn-nntp-post-step`; `fn-own-take-submission` only
moves an already-decided submission into flight. Taking the reading there would
mean queueing raw bodies and deferring every refusal past the reply. The
reading is taken at the one place the decision is made, which is what "per
submission" means here.

## Statements changed, and why

- `fn-own-read-is-served-step-on-pinned-prefix` and
  `fn-own-reader-sees-pinned-prefix-replay` (and their `-after-any-trace`
  forms) thread `(fn-own-clock o)` — `(fn-own-clock final)` in the trace forms
  — as the sixth argument of `fn-served-make-conn`. K1 constrains what a
  connection reads at its pin; the pin did not move and no conclusion changed.
- Every `fn-nntp-post-step` theorem in `books/nntp-post.lisp` gains the
  argument. `fn-post-refused-body-submits-nothing`'s hypothesis is now about
  the injection clock, which is the clock that refusal is a function of.
- `fn-served-open` takes the injection reading as its sixth argument;
  `fn-own-open-session-boundedp` mentions it.
- No keystone conclusion anywhere was weakened or removed.

## New keystones

- `fn-inj-generated-identity-separates-different-clock-readings`
  (`books/injection-invariants.lisp`, `:rule-classes nil`): if two
  observations generate the same identifier under one configuration, their
  wall readings are equal and their monotonic readings are equal. Fixed-width
  decimal at twenty digits has an exact left inverse and every
  `fn-clock-timep` value is below 10^20. Support: `fn-inj-rv` (the
  non-tail-recursive reverse the accumulator computes),
  `fn-inj-undigits-rev-inverts-digits-rev`, `fn-inj-append-cancels-at-equal-length`.
  `books/arithmetic/top.lisp` states nothing about `floor` or `mod`, so
  `ihs/quotient-remainder-lemmas` is included **locally**, after every other
  theorem in the book, and reaches no includer.
- `fn-post-distinct-injection-clocks-give-distinct-identities`
  (`books/nntp-post.lisp`, `:rule-classes nil`): two submissions on one
  connection — same session, same pinned archive, same configuration, same
  pinned observation — differing only in body and injection clock, neither
  supplying a `Message-ID`, receive distinct identities. Cited support:
  `fn-post-submission-is-the-decision-by-definition` (named as the definitional
  restatement it is) and `fn-inj-generated-identity-is-the-clock-identity`.
  `books/injection-invariants.lisp` is included **locally** here too, so an
  includer of `books/nntp-post.lisp` inherits none of its rules.

The prompt asked for "distinct bodies get distinct identities". That is false
as stated and the theorem does not claim it: a proto-article may supply its own
`Message-ID`, and two different bodies under **one** reading do share a
generated identifier. The hypothesis that the injection clocks differ is
exactly what the seam buys, and it is what the theorem carries.

## Teeth (`tests/acl2/nntp-post-tests.lisp`)

Four ground cases on one connection: the distinct-identity witness (two bodies,
two readings); the hypothesis dropped (two distinct bodies, **one** reading,
**same** generated Message-ID — the defect the seam removes); the retry rule
(same body, same reading, byte-identical octets); and the pinned reader
observation shown not to enter the identity.

## Evidence

- Local `ld` (`tools/acl2 --timeout 900`): `books/injection-invariants.lisp`
  clean, every form admitted including the new keystone;
  `books/nntp-post.lisp` clean, including
  `fn-post-distinct-injection-clocks-give-distinct-identities`. An `ld` is not
  a certification.
- ACL2, farm run `run-20260920T175602Z-51f8` on persvati
  (`--jobs 8 --remote-root /home/ember/fn-lanes/w5-clock-seam --closure`
  over injection-invariants, nntp-post, served, owner, owner-invariants and
  the four test books; cache: installed 159, kept 11, uncached 46).
  **Still running when this lane's budget ran out — NO VERDICT.** Harvest it
  with `python3 tools/farm.py wait persvati --remote-root
  /home/ember/fn-lanes/w5-clock-seam run-20260920T175602Z-51f8`. Nothing in
  this lane may be reported as certified until that run reports.
  Note before reading its verdict: `books/nntp-effects` is **open on dev** at
  `fn-nntp-hdr-labelled-line-is-block-text` (owner-followups' final board
  NOTE, 2598 s / 1.47e9 steps) and it is in this closure, so a failure there
  is pre-existing and cascades onto nntp-post, served and owner through no
  fault of this change.
- Python on persvati in that root: `tests.test_post tests.test_owner
  tests.test_reader` with `FN_ACL2=$HOME/fn-tools/acl2-8.7/saved_acl2`.
  **NOT RUN** — it needs the certificates the farm run had not produced. This
  is the first thing a successor runs, and
  `test_a_reader_pinned_before_a_post_keeps_its_view` is the case the whole
  lane exists for.
- `tests/test_post.py` was not edited. The design says the second post is a
  new article, not a retry: the two bodies differ, neither supplies a
  `Message-ID`, and the readings differ. If
  `test_a_reader_pinned_before_a_post_keeps_its_view` still fails, the seam is
  wrong, not the test.

## Open

1. `books/nntp-effects` has no verdict on `dev` (owner-followups' last
   finding: `fn-nntp-hdr-labelled-line-is-block-text` failed at 2598 s /
   1.47e9 steps). Untouched here and not diagnosed here.
2. Two submissions inside one millisecond on one connection still collide:
   the monotonic reading is in milliseconds and `fn-own-observe` accepts an
   equal reading. A durable post costs a barrier, so this is not reachable on
   the served path, but it is the remaining hypothesis of the keystone and is
   recorded rather than claimed away.
3. Owner-post open items 1, 2, 3, 5 and 6 stand unchanged.
