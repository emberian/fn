# w11/clock-seam — a clock the host contradicts is a clock the owner drops

Branch `w11/clock-seam` from `dev` at `5ae226f`, merged forward to `dev`
`38460cf` and then `e67b6cb`. Worktree `build/lanes/w11-clock-seam`.
Decision [D10-a](../decisions.md); proof target `PRF-033`.

## The seam's guarantee, in one sentence

A connection pins one clock observation at accept and that pin is the reader
environment — DATE and NEWGROUPS — which must not move under the session,
while every *decision* the node takes (the injection identity of each POST,
the stamp on each group-creation fact) is taken under the reading the host
supplied **with that event**, and the owner adopts a reading only when
`fn-own-observe` admits it as a later observation of the same clock.

## What was actually live, and what was not

`CHANGE root -> clock seam` named two defects. **The first was already fixed.**
`ac268de` ("a connection can never post twice") is 2026-09-20 02:31;
`w5/clock-seam` landed the per-submission injection clock in merge `7d8eff8`
after it, and its board line was never closed. Measured before touching
anything, on persvati at `dev` `5ae226f`, remote root
`/home/ember/fn-lanes/w11-clock-seam` after farm
`run-20260921T002506Z-3021` (`--closure books/owner`, 74 roots, exit 0):

```
test_clock_and_group_facts_go_through_the_owner ... ok
test_a_reader_pinned_before_a_post_keeps_its_view ... ok
Ran 2 tests in 7.289s   OK
```

Both named tests pass on dev. (`test_a_reader_pinned_before_a_post_keeps_its_view`
is in `tests/test_post.py`, not `tests/test_owner.py`.) No assertion was
edited in either file; neither file was edited at all.

**What was still live is one mechanism behind both symptoms**, and it is what
this lane fixes:

1. `host/owner-host.lisp` `fn-owner-observe` answered `:observed` or
   `:rejected` by comparing the owner before and after the event. The host
   was deciding, and because `fn-clock-later-observationp` is **non-strict**,
   an *admitted* reading equal to the one held moves nothing and was reported
   with the same word as a contradicted clock. That is the `2c985fe` symptom's
   mechanism, and it is a three-outcomes violation whether or not the test
   happens to be red on a given box.
2. `fn-own-observe` **kept** a contradicted reading. `books/injection.lisp`
   derives a generated Message-ID from the reading alone, so every POST after
   the first in that window minted the identity of the first, the durable path
   refused it as a duplicate, and the poster was told
   `441 posting failed; the article was refused`. An article verdict for a
   clock fault, and the exact shape of the defect `ac268de` reported.

## The decision (D10-a)

`fn-own-observe-outcome (o obs)` answers one of three distinct words and
`fn-own-observe` adopts accordingly:

| Outcome | When | The owner's clock afterwards |
| --- | --- | --- |
| `:observed` | a later observation of the same clock, **including one equal to the reading held** | the new reading |
| `:refused` | the monotonic counter went backwards, `has-wall` changed, or a widened bound moved the earliest admissible true time back | **none** |
| `:invalid` | no observation was supplied | unchanged |

The host reports that word. A refusal costs the owner its clock because
[`specs/time.md`](../../specs/time.md) already says a node that discovers its
clock was wrong is allowed to stop being sure; keeping the reading is the
opposite of that. With no clock the owner refuses to inject
(`fn-inj-decide`'s existing `:clock-unusable`, `441 posting failed; this
server has no usable clock reading`), refuses to create a group fact, and
answers DATE `503 no clock observation supplied` — three distinct answers,
none of them an article verdict. A clock-less owner is not a new state:
`fn-own-start` and `fn-own-reopen` both leave one and `fn-own-relation`
admits it, so **no new field, no new argument to the post step and no new
refusal reason were needed.**

Cost, stated: a POST or DECLARE-GROUP inside the one-event window is refused
with its own reason; a connection accepted in that window pins no observation
and answers DATE 503 for its session; and after a backwards correction the
node may re-mint a generated Message-ID from the lost interval, which the
durable path refuses as the duplicate it is. The rejected alternative — a
fourteenth owner field remembering the last reading minted under, which would
additionally separate two submissions inside one millisecond — is priced in
D10-a and recorded open.

## Theorems

- `fn-own-observe-refusal-names-a-contradiction` (`books/owner-invariants.lisp`,
  `:rule-classes nil`). KEYSTONE. On a related owner, `:refused` names one of
  the three backwards conditions; it is never merely a reading that did not
  move. The hypothesis "a clock is held" is **not** in the statement: with
  none the outcome is `:observed`, so that instance is vacuous rather than a
  tooth, and the micro-discipline says to delete it.
- `fn-post-without-a-clock-refuses-with-the-clock-line` (`books/nntp-post.lisp`).
  KEYSTONE. Awaiting an article, with a configuration that allows posting and
  an injection reading that is not an observation: no submission, and the
  effects are exactly the CLOCK line. Five hypotheses, five must-fail
  witnesses.
- `fn-own-observe-outcome-is-one-of-three` and
  `fn-own-observe-outcome-decides-the-clock-by-definition`, named for what
  they are, `:rule-classes nil`, cited by `:use`.

The subject question (AGENTS.md D6/D7): the host calls `fn-own-read`
(`host/owner-host.lisp` `fn-owner-chunk`), and
`fn-own-reader-sees-pinned-prefix-replay` is the existing theorem naming
`(fn-own-clock o)` as the sixth field — the injection reading — of the served
connection `fn-own-read-step` dispatches. The composition itself is carried by
evaluated witnesses rather than by another theorem chain, deliberately: see
below.

## Teeth (all evaluated by `tools/teeth_check.py`)

`tests/acl2/owner-tests.lisp`, **166 → 210 assertions**. The served-path block
runs `fn-own-read` — the function the host calls — on connection 4, which has
already taken one 240:

- a second POST after an admitted later reading is injected and its
  Message-ID **differs** from the first's;
- under the *first* post's reading, a different body gets the **same**
  Message-ID (the collision the per-submission seam removes, kept as the
  must-fail for that hypothesis);
- after a contradicted reading the owner has no clock, POST is still offered
  340, and the article gets
  `441 posting failed; this server has no usable clock reading` with an
  **empty queue** — asserted *not* equal to
  `441 posting failed; the article was refused` and not equal to the refused
  proto-article's line;
- `fn-own-declare-group` refuses, and a connection opened while the clock is
  gone answers DATE `503 no clock observation supplied`;
- the next reading is admitted and the connection posts again.

Plus, on the observation itself: the three words on concrete owners; the
equal-reading case asserted `:observed` with the owner unchanged (the case the
host used to spell as a refusal); three **separating** witnesses, one per
disjunct of the keystone's conclusion (monotonic alone, earliest-true alone
with the counter going forward, `has-wall` alone); and one must-fail for
`(fn-own-relation o)` on a hand-built owner whose clock field is not an
observation, where the conclusion evaluates to false.

`tests/acl2/nntp-post-tests.lisp` gains the reachable clock-line witness and
one must-fail per hypothesis of the new keystone.

The line that asserted a backwards reading leaves the owner **unchanged** is
gone. That line was pinning the defect.

`teeth_check.py --report` on both books: **no findings**. Corpus counts
(76 multi-hypothesis keystones, 15 named, 61 unchecked; 1
hypotheses-without-teeth, 20 keystone-without-witness, 8 no-subject, 37
predicate-never-anchored) are **identical to dev's**, so this lane adds
nothing to the unchecked number.

## Evidence

- Local `ld` through `tools/acl2` (one process at a time), every form
  admitted with no error: `books/owner.lisp`, `books/owner-invariants.lisp`,
  `books/nntp-post.lisp`, `tests/acl2/nntp-post-tests.lisp` and
  `tests/acl2/owner-tests.lisp` (210 `:PASSED`). An `ld` is not a
  certification.
- `make check`: green, `session_depth` 0 defects, ledger current
  (`tools/ledger.py --write`).
- Certification and the post-change live run: recorded in the section below.

## Open

1. **Two submissions inside one millisecond on one NODE still share a
   generated Message-ID.** `fn-clock-later-observationp` is non-strict and the
   identity is `<wall.monotonic.fn@agent>`, which is node-global rather than
   per-connection. Recorded under PRF-033 with its price; it needs two durable
   barriers inside one millisecond to reach.
2. A POST offered `340` by a clock-less owner is refused at the body. Answering
   `440` at the command instead would be a second reading of the same state and
   is not obviously better; not taken here, and not an RFC violation either way.
3. `books/nntp-effects` remains open at `FN-NNTP-HDR-LABELLED-LINE-IS-BLOCK-TEXT`
   (not this lane's, untouched here).
