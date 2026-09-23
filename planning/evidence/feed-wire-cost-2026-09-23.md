# Why the feed and wire books took 10 to 90 s, and the repair (lane COST-feed, 2026-09-23)

Branch `cost/feed` from `dev` 5c549e6c. The diagnosis was read from certify
logs that already existed. No slow form was rerun on the farm. The repairs
were found in `tools/proof_repl.py` sessions on the Mac, one session per book.
No theorem statement changed, no hypothesis was added, and nothing was
skipped. Every new lemma is `local`, so what each book exports is the same.

## The logs

Root's treewide run of `dev`'s head, `certify-20260923T003741Z-1790068` on
persvati (`/home/ember/fn-gates/dev-head/build/acl2/certify-20260923T003741Z-1790068/`),
has a log for all seven books. Their sources are byte-identical to `dev`
5c549e6c (sha256 compared). Four of the books are also in the seam run
`certify-20260923T000250Z-1473169`, and that run shows the same slow events.
Each log was parsed for every `Summary`: form, `Time:`, prover steps,
subgoals printed, the largest splitter note and the definitions in `Rules:`.
The worst passed walls in the brief (90 s for `peer-feed-invariants`, for
example) come from runs that shared a box. On the dev-head run the same
proofs take the times below, with the same step counts.

| book | certify-book time (dev head) | events over 1 s | share of the book in those events |
|---|---|---|---|
| peer-feed-invariants | 49.8 s | 7 (plus 11 between 0.5 and 1 s) | 91 % in 18 events |
| wire-outbound-invariants | 45.0 s | 1 | 96 % |
| feed-correspondence | 20.9 s | 2 | 91 % |
| feed-totality | 20.8 s | 3 | 98 % |
| owner-feed-port | 15.9 s | 3 | 94 % |
| transfer-journal-invariants | 11.0 s | 2 (plus 6 low-rate events at 0.7 to 0.9 s) | 88 % |
| tcpcl-invariants | 11.0 s | 4 | 77 % |

No slow event had a forcing round, and no subgoal name repeated. Every cost
is either a case split whose splitter note names the definitions that caused
it, or backchaining that `accumulated-persistence` shows to be useless.

## What each slow proof opened

**wire-outbound-invariants.**
`fn-wire-drive-of-host-rendered-article-preserves-source` took 43.2 s,
21.7 M steps and 744 subgoals. The splitter note at `Goal''` shows 105
subgoals from `if-intro` of `fn-wire-prefixp`, `nfix`, `not` and `posp`.
Each case then split again, 101 and 51 ways, on `fn-wire-prefixp`. The
three hypotheses `(not (fn-wire-prefixp *fn-wire-...-prefix* article))`
compare against constant prefixes, so the recursive definition unrolls
against the constant into a split over the article's first octets. The
proof never needs that. The same three hypotheses appear in the `:use`
instance of `fn-wire-render-feed-command-article-arm-unfolds`, so they
cancel propositionally.

**feed-correspondence.** `fn-feed-observe-records-reconstruct-live` took
17.3 s, 11.9 M steps and 1686 subgoals. At `Goal''` the goal splits 43 ways
over the reply codes. Each retry case then split about 226 ways on `nfix`
and `fix`, first inside `fn-feed-backoff-delay`, then `fn-feed-with-backoff`,
then `fn-feed-give-up`. The book enables `fn-feed-vocabulary` at the top,
and the hint closed the queue vocabulary but left `fn-feed-with-backoff`,
`fn-feed-backoff-delay` and `fn-feed-queue-requeue` open. Both sides of the
equation reach the same `fn-feed-with-backoff` of the same requeue and the
same delay, because replaying the `:feed-retry` record is `fn-feed-back-off`
with the same monotonic observation. Opening those functions only split on
their internal `nfix` tests. `fn-feed-replay-on-projection` took 1.6 s.
Its `:use` instance was proved with the projection, the recognizer and the
fold all open, although `fn-feedp-of-durable-projection` and idempotence
are what discharge it.

**feed-totality.** `fn-feed-live-port-step-refusal-preserves-work` (9.0 s,
805 subgoals, 96-way split) and `fn-feed-live-port-step-accepted-unfolds`
(8.2 s, 907 subgoals) are definition bridges over the port step's two-arm
`if`. `books/feed-events` leaves `fn-feed-live-records`, `-live-next`,
`-live-effects` and `fn-feed-records-portp` enabled. The hints enabled the
step and its accessors, and each bridge then opened the emitter over every
event kind and every reply code (`Rules:` lists 34 definitions).
`fn-feed-observe-records-are-driven` (3.0 s in the log, 1.8 s in the
session) is a real case analysis over reply codes and retry exhaustion
(104-way split). It is not changed.

**owner-feed-port.** `fn-own-feed-port-peer-records-true-listp` took 9.05 s
and 949 subgoals. `fn-own-feed-port-peer-ready-is-live-port-step` took
4.0 s and `-refusal-preserves-table` 1.8 s. It is the same emitter as in
feed-totality, opened under the owner wrapper (47 definitions). The two
bridges already closed `fn-feed-live-port-step`. Their conclusions and
hypotheses, though, name `fn-feed-live-records`, `-next` and `-effects`,
which were enabled and opened. The true-listp theorem needs one type fact,
that the port step's record field is a proper list, and none of the event
arms decides it.

**peer-feed-invariants.** Eighteen events took from 0.5 to 7.7 s. There are
four shapes:

- *A state predicate opened in a list induction.*
  `fn-feed-droppedp-of-state-of-set-state` (7.7 s, a 75-way split in the
  induction step) and `-of-append-one` (6.2 s, 60-way) opened
  `fn-feed-droppedp`, which is a member test over the drop-reason constant
  plus a `len`. The statements use it only as a predicate. The four
  `fn-feed-state-of-of-*-inflight`/`-settle` lemmas and the two in-flight
  count lemmas (0.5 to 1.15 s) opened `fn-feed-state-inflightp` the same
  way.
- *The recognizer re-derived on both sides.* `fn-feed-back-off-preserves-feedp`
  (3.5 s, 104-way split), `-give-up-` (0.95 s), `-lost-` (0.53 s),
  `fn-feed-apply-record-preserves-feedp` (2.8 s, 123-way split, with
  `fn-feedp` left open on purpose for its offer arm) and
  `fn-feed-back-off-does-not-lower-the-deadline` (0.98 s). Each opened
  `fn-feedp`, a record of twelve conjuncts, in the hypothesis and again on
  the rebuilt record, and opened `fn-feed-with-backoff` and
  `fn-feed-backoff-delay` (`nfix`/`fix` splits) under every arm. A
  transition moves one or two fields. What each proof needs is the queue
  conjuncts of the old record and what rebuilding the record asks of the
  new field.
- *The dispatcher over the same record internals.*
  `fn-feed-done-survives-a-driven-record` (7.7 s, 2105 subgoals: the three
  retry-code cases each split 817 ways on `fn-feed-backoff-delay`,
  `fn-feed-with-backoff` and `fn-feed-lost`),
  `fn-feed-not-dropped-survives-a-non-drop-record` (2.3 s) and the local
  `fn-feed-count-accepted-after-an-accepted-head` (7.1 s, 212-way split).
  The last one also opened `fn-feed-apply-record` and
  `fn-feed-record-drivenp`, although its proof is two `:use` instances.
  These proofs rightly keep the dispatcher open, since the content is one
  record. They do not need `fn-feedp` or the field updates open.
- *Peer preservation.* `fn-feed-back-off-preserves-peer` (0.65 s) opened
  the whole transition to read one field that `fn-feed-peer-of-with-*`
  already answers.

**transfer-journal-invariants.** `fn-tj-transition-preserves-statep` took
3.25 s and 760 k steps. `Rules:` names only `fn-tj-transition`. One
instrumented run (`accumulated-persistence`) showed that the time goes to
three exported rewrite rules of `transfer-invariants`:
`fn-transfer-add-chunk-nonadmissible-no-overwrite` (537 k frames),
`-exact-duplicate-no-overwrite` (340 k) and `-invalid-chunk-no-overwrite`
(340 k). Each backchained from the add-chunk result into
`fn-transfer-labelp`, `-max-label` and the `len` rules
(`fn-transfer-consp-has-positive-len` 1.19 M frames,
`fn-frame-len-{2,4,8}-conses` about 1 M each). None of those applications
was useful. The two keystones cited by `:use` are the whole proof.
Six local lemmas about `fn-tj-record-okp` took 0.7 to 0.9 s each at 45 to
65 k steps, which is 56 to 116 k steps per second. The profile of one of
them, `fn-tj-payload-is-octets`, shows `fn-tj-record-okp` opening into
`fn-frame-values-okp` (43 k frames, useless), then `fn-frame-field-okp`,
then `fn-frame-textp`, and then `fn-wildmat-decode-aux`,
`fn-wildmat-utf8-next` and `-utf8-4-tails` (UTF-8 validation, 30 k, 26 k
and 18 k frames, all useless). This happens because the book enables
`fn-frame-codec-vocabulary` and `fn-frame-record-vocabulary` at the top
(F3 of the 2026-09-22 review). `fn-tj-candidate-is-unverified-by-definition`
(1.9 s) opened the entry lookup, the completeness test and the reassembly
to read the constructor's first element.

**tcpcl-invariants.** 11.0 s in total (7.5 s in the session). The slow
events are `fn-tcl-final-ack-means-every-segment` (3.1 s, a 177-way split),
`-live-inbound-ends-in-exactly-one-outcome` (2.5 s),
`-step-emits-at-most-one-inbound-outcome` (1.6 s) and
`-drive-partition-independence` (1.3 s, an induction). They are the C2 and
C3 keystones over the whole message dispatch of `fn-tcl-step`. One probe was
made: close the handshake handlers behind a local lemma saying that they
emit no inbound outcome. It did not move the at-most-one theorem (1.18 s
against 1.13 s). The remaining cost is in `fn-tcl-recv-segment` under
`fn-tcl-messagep`, and a repair would need per-message-kind outcome lemmas.
Not done; the book is left unchanged.

## The repair

1. **wire-outbound-invariants.** The host-rendered article theorem's hint
   also disables `fn-wire-prefixp`.
2. **feed-correspondence.** The observe-records hint also closes
   `fn-feed-with-backoff`, `fn-feed-backoff-delay`, `fn-feed-queue-requeue`
   and `fn-feed-with-conn`. The replay-on-projection hint closes the
   projection, `fn-feedp` and `fn-feed-replay`.
3. **feed-totality.** The two port-step bridges enable the step and its
   accessors and close `fn-feed-live-records`, `-live-next`,
   `-live-effects`, `fn-feed-records-portp` and `fn-feedp`.
4. **owner-feed-port.** The two bridges close the same five. There are two
   new local lemmas: `fn-own-feed-records-portp-is-true-listp`
   (forward-chaining) and `fn-own-feed-port-step-records-true-listp` (the
   port step's record field is a proper list, proved over the two-arm `if`
   with the emitter closed). The true-listp theorem is then proved with
   `fn-feed-live-port-step` and `fn-feed-port-step-records` closed.
5. **peer-feed-invariants.** The droppedp propagation lemmas close
   `fn-feed-droppedp`, and the in-flight lemmas close
   `fn-feed-state-inflightp`. There are seven new local lemmas:
   `fn-feed-feedp-forward-backoff-until` and `fn-feed-feedp-forward-queue`
   (forward-chaining: the conjuncts of `fn-feedp` a transition reads),
   `fn-feed-feedp-of-with-queue` (the recognizer of the record with its
   queue replaced, stated as the queue conjuncts),
   `fn-feed-feedp-of-make-with-queue-and-attempt` (the same for the offer
   arm's `fn-feed-make`), `fn-feed-feedp-of-with-backoff` and
   `fn-feed-feedp-of-with-conn`, and `fn-feed-queue-of-with-fields`. With
   these, the preservation theorems, the deadline theorem, the peer
   preservation of back-off and lost, and the one-record keystones close
   `fn-feedp`, the three field updates and `fn-feed-backoff-delay`. The
   one-record keystones keep the dispatcher open. The local head-step lemma
   also closes `fn-feed-apply-record` and `fn-feed-record-drivenp`, since
   its two `:use` instances are the proof. `fn-feed-apply-record-preserves-feedp`
   no longer keeps `fn-feedp` open, and its comment says why.
6. **transfer-journal-invariants.** The top-of-book enable no longer opens
   `fn-frame-codec-vocabulary` or `fn-frame-record-vocabulary`. Every form
   of the book is admitted without them. The octet and fields lemma
   vocabularies stay: a load without them fails at
   `fn-tj-payload-is-octets`. `theory_check --table` still lists those two
   as codec theories at the top. They are rule sets, not definitions, but
   the check does not tell the two apart. The transition preservation hint
   closes the three no-overwrite rewrites. The candidate lemma closes the
   entry lookup, completeness, reassembly and field accessors.

## Session times (proof_repl, Mac, one session per book)

"Before" is the dev-head log. Two anchors were measured in the session
before any change, to check that the session and the log agree:
`fn-feed-droppedp-of-state-of-set-state` took 7.57 s against 7.69 s in the
log, and the whole of transfer-journal-invariants took 9.09 s against
11.0 s. "After" is the sum over every event of a fresh load of the edited
book. It includes the book's own `include-book`.

| book | before | after | largest event after |
|---|---|---|---|
| peer-feed-invariants | 49.8 s | 4.4 s | `include-book "peer-feed"` 0.84 s; largest proof 0.21 s |
| wire-outbound-invariants | 45.0 s | 1.7 s | `fn-wire-drive-of-successful-render-block-preserves-source` 0.80 s (unchanged, a ten-instance `:use`); the host theorem went from 43.2 s to 0.12 s |
| feed-correspondence | 20.9 s | 2.2 s | include 0.84 s; observe-records went from 17.3 s to 0.25 s, replay-on-projection from 1.6 s to under 0.1 s |
| feed-totality | 20.8 s | 2.8 s | `fn-feed-observe-records-are-driven` 1.84 s (unchanged); the two bridges went from 9.0 s and 8.2 s to under 0.1 s |
| owner-feed-port | 15.9 s | 1.4 s | include 1.22 s; records-true-listp went from 9.05 s to under 0.1 s |
| transfer-journal-invariants | 11.0 s | 1.3 s | include 0.68 s; the transition went from 3.25 s to 0.01 s, the candidate from 1.9 s to 0.01 s, the six codec lemmas from 0.7 to 0.9 s to 0.01 s |
| tcpcl-invariants | 11.0 s | 7.5 s (unchanged book, session speed) | final-ack 2.1 s, live-inbound 1.7 s, at-most-one 1.1 s |

The sessions for feed-correspondence, feed-totality and owner-feed-port
loaded `peer-feed-invariants` (and `owner-feed`) uncertified, because the
cache has no pair at the new digest. A session admission is not a
certificate.

## Certification

Not submitted. The farm refused the lane run before ACL2 started:
`farm.py submit persvati books/peer-feed-invariants
books/wire-outbound-invariants books/feed-correspondence books/feed-totality
books/owner-feed-port books/transfer-journal-invariants
tests/acl2/peer-feed-tests tests/acl2/wire-outbound-tests
tests/acl2/feed-correspondence-tests tests/acl2/feed-totality-tests
tests/acl2/owner-feed-port-tests tests/acl2/transfer-journal-tests --jobs 4
--timeout-seconds 1800 --remote-root /home/ember/fn-gates/cost-feed --acl2
/home/ember/fn-gates/toolchains/w25/acl2-literal --cache
/home/ember/fn-certcache` answered "no origin/toolchain-coherent certificate
set ... Re-run with --closure". Of the closure, 26 books have no pair in
`/home/ember/fn-certcache` at the digests of `dev` 5c549e6c: `frame-fields`,
`frame-invariants`, `frame-journal`, `frame-octets`, `identity`,
`identity-invariants`, `node`, `node-invariants`, `owner-feed`, `path`,
`peer-config`, `peer-feed`, `provenance`, `records`, `records-invariants`,
`records-shape`, `retention`, `scheduler`, `transfer`,
`transfer-invariants`, `transfer-journal`, `transfer-reservation`,
`transfer-union`, `wildmat`, `wire` and `wire-invariants`. A lane does not
use `--closure` (`planning/how-we-work.md`, "Certification cost"), so the
gate is root's treewide certification of `dev`'s head, and after it the
plain-roots submit above is this lane's whole run. Until then nothing in
this file is certified; it is session evidence only.

## What remains open

- tcpcl-invariants: the three C2 and C3 step theorems (1.1 to 2.1 s in the
  session) need per-message-kind outcome lemmas.
- feed-totality: `fn-feed-observe-records-are-driven` (1.8 s) is a real
  split over reply codes and retry exhaustion. Closing
  `fn-feed-retry-exhaustedp` alone fails.
- `books/feed-events` exports `fn-feed-live-records`, `-live-next`,
  `-live-effects`, `fn-feed-records-portp` and the record emitters
  enabled. Every includer that states a bridge over the port step opens
  them unless it closes them itself, which is what cost feed-totality and
  owner-feed-port 35 s between them. The structural repair is an export
  disable in feed-events, which recertifies the whole feed and owner
  cluster. That is for root to schedule.
- feed-correspondence, feed-totality and peer-feed-invariants still enable
  `fn-feed-vocabulary` / `fn-feed-invariants-vocabulary` at the top.
  `theory_check` flags them. Moving those enables into hints means
  rewriting every hint in the three books. It was not done here.
