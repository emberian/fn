# What was left on the chain, and the repairs (lane COST-rest, 2026-09-23)

Branch `cost/rest` from `dev` 5c549e6c. The diagnosis below comes from the
logs already on disk. The repairs were found in `tools/proof_repl.py`
sessions on the Mac, one per book. Each slow form got one instrumented run,
with `(accumulated-persistence t)`. The sessions included books below each
book that had no cached pair at these digests (`store-node`,
`store-node-invariants`, `hybrid-store`, ...) uncertified, from source. A
session admission is not a certificate. Certification is the last section.

Two sessions had to be started a second time. `snt` died when a form with an
unbalanced parenthesis reached the reader. `tco`'s server died with a
`BrokenPipeError` after its client was killed. Neither restart measured
anything a second time.

## The logs

| book | log (persvati) | book time |
|---|---|---|
| store-node-traces | `/home/ember/fn-gates/t1-seam/build/acl2/certify-20260923T000250Z-1473169/books--store-node-traces.certify.log` | 109.0 s |
| owner-invariants | same run, `books--owner-invariants.certify.log` | 46.1 s |
| anchor-invariants | `/home/ember/fn-gates/dev-head/build/acl2/certify-20260923T003741Z-1790068/books--anchor-invariants.certify.log` | 173.7 s |
| tcpcl-octets | same dev-head run, `books--tcpcl-octets.certify.log` | 153.8 s |
| tcpcl-session | same dev-head run, `books--tcpcl-session.certify.log` | 102.9 s |

In the manifest's 310 books, two other books over 20 s have no owner tonight:
`peer-feed-invariants` (48.9 s) and `identity-invariants` (20.4 s). They are
at the end of this file and were not changed.

## store-node-traces: `:use` instances carried into the cases that do not need them

| event | seam log | session, as on dev | after |
|---|---|---|---|
| `fn-snt-prepare-retention-preserves-relation` | 50.6 s, 38 544 678 steps, 12 subgoals | 60.4 s, 38 544 678 steps | 0.22 s |
| `fn-snt-record-directory-preserves-relation` | 34.2 s, 20 181 660 steps, 9110 subgoals (286-way split at `Goal''`) | 32.0 s, 20 182 028 steps | 0.49 s |
| `fn-snt-prepare-identity-preserves-relation` | 10.9 s, 10 772 447 steps, 115 subgoals | 13.1 s, 10 782 625 steps | 0.48 s |
| `fn-snt-prepare-preserves-relation` | 4.6 s, 3 928 114 steps, 19 subgoals | 4.9 s | 0.19 s |
| the book, every event | 109.0 s (82.2 s in the store lane's session) | | about 10 s, 1.5 s of it the `include-book` |

The session ran the original retention proof again: 38 544 678 steps, the
same count as the seam log, so the copy is the certified proof. The store
lane's instrumented run had not been able to reproduce it. Its accumulated
persistence:

- `(:definition fn-snt-relation)` expanded 116 016 times (11.1 M frames);
- `(:definition fn-snt-deferred-linkp)` 64 735 times (7.8 M);
- `(:definition fn-sn-prepare-retention)` 57 149 times (5.1 M);
- `fn-snt-relation-implies-structural-state`: 173 650 tries (5.3 M);
- `fn-snt-history-recoverable-under-record-bound`: 271 846 tries;
- no useful application at all for `fn-snt-extended-history-is-the-applied-event`
  (2.4 M frames), `fn-sn-new-success-requires-actual-matching-durable-node-completion`
  (1.3 M, and it opened `fn-sn-finish` 4962 times), `fn-replay-advance-okp`,
  `fn-snt-successful-replay-history-length` and
  `fn-snt-advance-at-current-is-identity`.

The step rate was 760 000 a second, so the time went to rewriting. There were
only 12 cases, and each cost about 3.2 M steps because each carried the whole
`:use` list. The largest item on it is `fn-snt-deferred-preparation-outcome`'s
instance, an implication over a `let*` of the replayed and applied nodes.
Only the staging case needs any of it. In every other case the transition
returns its argument, and the prover still rewrote the whole instance there,
under the relation's expansion.

Two things tried first failed, and they rule out the obvious causes:

- Withdrawing `fn-snt-relation-implies-structural-state`, the rule that
  backchains into the relation, made the proof slower: 45 202 427 steps.
- Closing the relation and expanding only its two occurrences failed after
  38.6 M steps. The expansions were not the cost.

The repair keeps the same instances and the same theory and changes where
they go. `:cases` splits the goal on the transition's own gate: the state
recognizer, the phase `:reserved`, the event kind, the applier's `consp`,
and `fn-sf-prepare-record` staging. The instances go only to `"Subgoal 1"`,
the case where the gate holds. In the other case the transition is the
identity on the state, and the goal closes by the relation's own expansion.
The same repair applies to the identity arm, to the article preparation
(`fn-sn-prepare`'s gate) and to the record-directory step. For that step the
case is `:record-attempted` with an `:ok` result, the only observation that
publishes. `fn-sn-io-preserves-state` stays on the whole goal, because the
fenced arm needs it. No new lemma was needed, and no statement changed.

## owner-invariants: the configuration theorem opened every transition at once, and was red on dev

`fn-own-snrt-step-keeps-configuration` took 35.3 s of the book's 46.1 s on
the seam run, with 19 122 subgoals. Its hint enabled `fn-snrt-step`,
`fn-snt-step` and seven transitions together. The splitter note at
`Subgoal 2` (734 ways) names `fn-replay-apply-retention-event`,
`fn-retain-matching-releasep`, `fn-sn-identity-context` and every transition.
The `Rules:` list opens 37 definitions, among them the three store-transaction
recognizers, `fn-sn-finish-identity` and `fn-replay-identity-step`. The
theorem says only that groups and capacity are unchanged.

On dev it was also red. The first incremental run of dev's head
(`certify-20260923T013826Z-2337665`) failed it after 52 067 steps. The cause
is 5c549e6c: `books/store-node`'s export disable now withdraws
`fn-sn-prepare-retention` and `fn-sn-prepare-identity`, and this hint did not
open them, so `(fn-sn-groups (fn-sn-prepare-retention s e))` was stuck.

The repair is the fact itself, one level at a time, each proved in the
minimal theory:

- `fn-own-sn-constructors-keep-configuration` (local). `fn-sn-update`,
  `-update-indexed`, `-update-accepted`, `-update-replayed`,
  `fn-sn-advance-identity-next` and `fn-sn-finish-identity` rebuild through
  `fn-sn-make-v2` with the old groups and capacity. It uses those six
  definitions and `fn-sn-groups/capacity-of-fn-sn-make-v2`, and nothing else.
  668 steps.
- `fn-own-sn-transitions-keep-configuration` (local). Each of the seven
  transitions, with its own definition and the lemma above, and no test
  opened. 6074 steps.
- The theorem itself: `fn-snrt-step`, `fn-snt-step`, the lemma above and the
  two resolution lemmas already exported
  (`fn-sn-refuse-reservation-preserves-configuration`,
  `fn-sn-known-abort-preserves-configuration`). 554 steps.

The book is 16.6 s in the session, 2.7 s of it the `include-book`. What
remains: `fn-own-step-records-prefix` 3.8 s (71 definitions),
`fn-own-durable-reply-names-a-durable-record` 2.2 s,
`fn-own-advanced-session-is-bounded` 1.7 s.

Every form of the owner cluster above it was admitted in its own session
against this branch: `owner-fault` (22 forms), `owner-config` (88),
`owner-prepare-correspondence` (26), `owner-agent` (41) and
`owner-tls-prefix` (13). Their test books were not loaded.

## anchor-invariants: the anchor tests opened in every goal

The book opens `fn-anchor-vocabulary` book-wide, and in this book that is the
whole anchor record. Every transition theorem therefore expanded
`fn-anchor-p` (ten field widths), `fn-anchor-verifiedp`,
`fn-anchor-signatures-okp` (the signed octets: `fn-anchor-le-bytes`, `floor`,
`mod`), `fn-anchor-one-nonce-p` and `fn-anchor-pinnedp`, although each
theorem only branches on them. The step rate across the book was 110 000 to
300 000 a second. The instrumented run of
`fn-anchor-node-accept-preserves-nodep` gave 7.4 s for 1 374 497 steps, and
its largest rune had only 0.4 M frames: `true-listp`, `fn-cbor-octet-listp`,
`binary-append` and 1228 useless openings of `fn-anchor-le-bytes`. Most of
the time is spent outside the rewriter. This lane did not find out where.

| event | dev-head log | session, as on dev | after |
|---|---|---|---|
| `fn-anchor-accept-list-latest-never-goes-back` | 85.4 s (induction, 314 subgoals, 49 definitions) | 83.5 s | under 0.5 s |
| `fn-anchor-node-accept-preserves-nodep` | 8.7 s | 7.2 s | under 0.5 s |
| `(verify-guards fn-anchor-node-accept-list)` | 9.3 s | 7.7 s | under 0.5 s |
| the three `-observed-is-` entry equalities | 6.5 to 7.5 s each | 6.9 to 8.3 s | under 0.5 s |
| every event after the order lemmas | 172 s | 119.5 s + 21.6 s | 0.8 s |

The repair is one local `in-theory` at the head of the transition section.
It closes the six tests (`fn-anchor-p`, `-verifiedp`, `-signatures-okp`,
`-window-okp`, `-one-nonce-p` and `-pinnedp`). It comes with one local
forward-chaining lemma, `fn-anchor-pinned-anchor-is-an-anchor` (the pin
test's first conjunct), which `fn-anchor-restore-refuses-image-it-cannot-outdate`
needs. `fn-anchor-verifiedp-observed-is-verifiedp` relates two of the tests,
so it opens them in its own hint. Closed there, the rewriter hit its call-depth
limit. The monotone keystone now goes through by its induction hint on the
lemmas above it, because nothing re-derives the acceptance inside each step.

## tcpcl-octets: `len` reopened on every `cdr`, and a need bound tried on every `len`

The book already said why `len` must stay closed for the fixed-layout
decoders (406 s for `fn-tcl-decode-term-yields-message` in September). It
closed it only after the XFER_SEGMENT block. The SESS_INIT and XFER_SEGMENT
blocks ran with `len` open: `fn-tcl-has-is-len-bound` turns each has-check
into a `len` bound, and `fn-tcl-consp-by-len` opened `len` on every `cdr` of
the layout. The splitter notes name only `fn-tcl-decode-segment`, `nfix` and
`not` (66 and 91 ways), but the `Rules:` lists carry `(:definition len)`,
`fn-cbor-octet-listp` and `fn-cbor-octetp`.

With `len` closed, the instrumented run of
`fn-tcl-decode-segment-append-error` (13.8 s) showed the rest.
`(:linear fn-tcl-decode-init-need-short)` had 34 465 tries and 4.8 M frames
and was never useful. Each try opened `fn-tcl-decode-init` (1165 openings,
4.8 M frames) to relieve its hypothesis. The book's later blocks withdraw
that rule for this reason. The XFER_SEGMENT block came before the withdrawal.

| block, in the session | before | after |
|---|---|---|
| XFER_SEGMENT (9 events) | 134.9 s: append-error 55.4, append-ok 35.5, need-short 13.6, outcomes 11.4, yields-message 8.1, canonical 6.2 | 1.1 s |
| SESS_INIT (9 events) | 20.3 s | 10.5 s (append-error 3.7 s, `verify-guards fn-tcl-decode-init` 2.0 s) |
| the whole book | 153.8 s (dev-head log) | 12.5 s |

The repair moves the two local `len` rules and `(disable len)` up to the
SESS_INIT block, and withdraws `(:linear fn-tcl-decode-init-need-short)` before
the XFER_SEGMENT block. Every other event of the book was admitted unchanged
under the moved theory.

## tcpcl-session: the field recognizers open in theorems that only carry them

| event | dev-head log | session, as on dev | after |
|---|---|---|---|
| `fn-tcl-touch-rx-preserves-cheapp` | 22.4 s (190-way split, 844 subgoals) | 19.3 s | 0.5 s |
| `fn-tcl-touch-rx-preserves-sessionp` | 9.1 s | 7.3 s | under 0.5 s |
| `fn-tcl-sessionp-is-cheap` | 8.1 s | 5.8 s | 0.04 s |
| `fn-tcl-sessionp-facts`, `fn-tcl-session-cheapp-facts` | 5.8 s, 7.0 s | 5.1 s, 5.1 s | under 0.5 s |
| `fn-tcl-next-preserves-cheapp` | 8.6 s | 8.1 s | 1.5 s |
| `fn-tcl-recv-contact-preserves-sessionp` / `-cheapp` | 4.7 s / 5.8 s | 3.7 s / 4.6 s | under 0.5 s |
| the book | 102.9 s | about 83 s | about 27 s |

Each of these theorems carries the session's conjuncts from one side to the
other. The splitter notes name `fn-tcl-inboundp`, `-outboundp`, `-paramsp`,
`-negotiatedp`, `-peer-initp` and `fn-cbor-octet-listp`. The repair is a
local theory, `fn-tcl-field-recognizers`, with those seven recognizers. It
is closed in the hints of those theorems. For `fn-tcl-next-preserves-cheapp`
the profile also showed `fn-tcl-session-cheapp-facts` with 164 280 tries.
That rule backchains into the recognizer the goal has already opened, and
`fn-tcl-outboundp-is-cheap` and `-inboundp-is-cheap` were never useful, so
those are closed in that hint too.

What remains: `fn-tcl-recv-segment-preserves-sessionp` (7.2 s) and `-cheapp`
(5.9 s). There `fn-tcl-messagep`, which the section enables, splits the
message into 2321 subgoals at 185 000 steps a second. The profile's frames
are small, so here too the time is not in rewriting. The repair would be a
fields lemma for an `:xfer-segment` message, with `fn-tcl-messagep` closed.
It was not written.

## Not changed

- `identity-invariants` (20.4 s). `fn-id-obligation-shape` takes 8.3 s,
  `-subject-is-not-an-obligation` 4.9 s and `-obligation-is-not-a-subject`
  2.0 s. None of them splits. They run at over 1 M steps a second through
  `fn-frame-split`, which the book enables, unrolled over the 16-octet
  label. `fn-frame-split-of-append` (frame-octets) already states the fact
  those three proofs need.
- `peer-feed-invariants` (48.9 s). No event is over 7.4 s. Four inductions
  (`fn-feed-droppedp-of-state-of-set-state` 7.4 s, `-of-append-one` 6.0 s)
  and three preservation lemmas of 2 to 7 s.
- `wire-outbound-invariants` (45.0 s on the dev-head log, and not in the
  310-book manifest). `fn-wire-drive-of-host-rendered-article-preserves-source`
  is 43.2 s: a four-instance `:use`, 1479 subgoals, 503 000 steps a second.
  That is the store-node-traces shape, but this lane did not try it.

## Files changed

`books/store-node-traces.lisp`, `books/owner-invariants.lisp`,
`books/anchor-invariants.lisp`, `books/tcpcl-octets.lisp`,
`books/tcpcl-session.lisp`, and the ledger that `tools/ledger.py --write`
regenerates. No theorem statement changed and none was removed. Nothing is
skipped, and no rule class of an exported theorem changed. Every new event
is local.
