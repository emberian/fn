# Why the NNTP cluster's slow books were slow, and the repairs (lane COST-nntp, 2026-09-23)

Branch `cost/nntp` from `dev` 1554e2cd. I read the diagnosis from existing
certify logs. The repairs were tried in `tools/proof_repl.py` sessions on the
Mac against the cached closure. When a closure book had no cached pair at
this branch's digests, the session included it uncertified from source.
That is sound for timing and says nothing about certification. The farm
run named at the end is the certification.

## The logs

| log (persvati) | what it is |
|---|---|
| `/home/ember/fn-gates/t1-seam/build/acl2/certify-20260923T000250Z-1473169/books--{nntp-effects,policy,feed-connection-invariants,nntp-invariants,nntp-post,nntp-auth}.certify.log` | the 310-book run (manifest `planning/evidence/manifests/certify-20260923T000250Z-1473169.json`) |
| `/home/ember/fn-gates/dev-head/build/acl2/the treewide run of dev's head that root stopped after 345 books (no manifest was written)/books--{nntp-effects,policy,feed-connection-invariants,nntp-invariants}.certify.log` | the stopped treewide run of `dev`'s head; the same events within 10% (nntp-effects 106.1 s, policy 98.6 s, feed-connection-invariants 93.6 s, nntp-invariants 69.7 s) |

The other books in the brief took under 3 s each in the 310-book run:
`nntp-newnews` 0.6 s, `nntp-responses` 1.3 s, `served` 2.3 s and
`served-tls-prefix` 1.6 s. I left them alone.

## Book totals

| book | 310-book run (persvati) | session after (Mac, sum of every event) |
|---|---|---|
| `books/nntp-effects` | 106.8 s | 7.4 s |
| `books/policy` | 87.7 s | 4.4 s |
| `books/feed-connection-invariants` | 83.7 s | 3.5 s |
| `books/nntp-invariants` | 75.0 s | 5.6 s |
| `books/nntp-post` | 7.4 s (13 s in root's worst wall) | 1.8 s |
| `books/nntp-auth` (not changed) | 13.9 s | 12.7 s |

In the 310-book run the listed events add up to the certify time within
0.1 s in each book. The session totals include the book's own
`include-book` events.

## Cause classes, one per slow event

All but one of the slow events belong to the class the brief names. ACL2
rewrites inside out. So when a recognizer, a renderer or a lookup is left
enabled, it is expanded before the lemma that states the one fact the
proof needs can match. When the goal dispatches on arms, every `if` in
the expansion then becomes a case. The one exception is `policy`, whose
time went outside the counted prover steps. It still has the same
repair.

### `books/nntp-effects`

| event | before (seam) | after (session) | what was open, and why |
|---|---|---|---|
| `fn-nntp-date-octets-length` | 46.1 s, 25 835 615 steps, 6 subgoals | 0.01 s, 3 745 steps | The hint enabled `fn-nntp-pad2`/`-pad4`. Their arguments opened first: `fn-nntp-digit-octet`'s ten-way table over `fn-nntp-mod`/`-div`, which open to `floor`/`mod` (if-intro `floor`, `fn-nntp-digit-octet`, `-div`, `-mod`, `nfix`). A padded field's length does not depend on its number. |
| `fn-nntp-listgroup-initial-is-a-status-line` | 12.5 s, 6 190 462 steps, 133 subgoals | 0.09 s | `fn-nntp-decimal-field`, `-decimal`, `-decimal-rev` and `fn-nntp-group-summary` were open. The summary counts were rendered digit by digit, but the status line needs only the first four octets. |
| `fn-nntp-group-initial-is-a-status-line` | 8.8 s, 4 448 724 steps, 145 subgoals | 0.07 s | the same |
| `fn-nntp-listgroup-initial-is-response-text` | 7.6 s, 3 292 704 steps, 92 subgoals | 0.01 s | the same. `fn-nntp-decimal-field-is-response-text` was proved 400 lines earlier, and it could not match an opened field. |
| `fn-nntp-group-initial-is-response-text` | 7.3 s, 3 051 001 steps, 92 subgoals | 0.03 s | the same |
| `fn-nntp-effects-xpat-range` | 4.8 s, 677 240 steps | 0.02 s, 13 626 steps | A rewrite rule with an open recursive recognizer as its hypothesis (see below) |
| `fn-nntp-effects-listgroup-command` | 3.3 s, 1 478 165 steps, 33 subgoals | 0.08 s | `fn-nntp-projectionp`, and under it `fn-statep`, the whole node state. The book enabled `fn-statep`, `fn-articlep` and `fn-pendingp` book-wide at line 25. The only use of the hypothesis is to discharge `fn-nntp-effects-listgroup-result`'s identical hypothesis. |
| `fn-nntp-effects-group-result`, `-listgroup-result` | 1.1 s, 1.1 s | 0.05 s, 0.06 s | the same, `fn-statep` |

For `xpat-range`, one instrumented session run with
`(accumulated-persistence t)` named the cost. Of 675 368 steps, 498 824
frames sat under two useless tries of
`fn-nntp-xpat-with-a-total-filter-is-the-hdr-block` (books/nntp-legacy). Its
hypothesis `fn-nntp-xpat-selects-everythingp` is a recursive recognizer
over the article list. Relieving it opened `fn-nntp-hdr-content`,
`fn-nov-scrub`, `fn-article-parse-lines` and the message-id grammar, and
this proof never uses the rule.

Repair (all in `books/nntp-effects.lisp`, no statement changed):

1. **The `fn-statep`/`fn-articlep`/`fn-pendingp` enable is removed from
   the top of the book.** The whole book still loads without it, 165
   forms, so no proof here needed the node state open.
2. **`fn-nntp-decimal-field` is closed** by a `local` disable after its
   shape lemmas (`-is-a-digit-run`, `-is-nonempty`, `-is-bounded`,
   `-is-octets`, `-is-true-listp`, `-is-response-text`,
   `-first-is-digit`). Those lemmas are the facts a response proof needs.
   Three later hints already disabled the field by hand.
3. The initial-line hints close `fn-nntp-group-summary`. The LISTGROUP
   response-text hint closes `fn-nntp-group-initial`, so the GROUP lemma
   just above it does the work.
4. Two local shape lemmas, `fn-nntp-pad2-length` (2) and
   `fn-nntp-pad4-length` (4). The DATE length hint now keeps `pad2`/`pad4`
   closed, as the DATE status-line and response-text hints already did.
5. The `xpat-range` hint disables the legacy total-filter rule, with a
   comment giving the reason.

### `books/policy`

| event | before (seam) | after (session) |
|---|---|---|
| `fn-pol-current-is-stmt-or-nil` | 49.1 s, **336 946** steps, `Goal'` then Q.E.D. | 0.00 s, 1 330 steps |
| `(defun fn-pol-current)` guard | 18.4 s, **126 262** steps, `Goal'` then Q.E.D. | 0.03 s, 14 390 steps |
| `(defun fn-pol-candidatep)` guard | 9.0 s, 726 992 steps, 19 subgoals | 0.00 s, 183 steps |
| `(defun fn-pol-authorized-set)` guard | 5.5 s, 497 841 steps, 57 subgoals | 0.00 s, 25 steps |

The first two are not a case explosion. Each proof is `Goal'` and then
Q.E.D. Their `Rules:` lists are short: `fn-pol-latest-is-stmt`,
`-candidates-are-lace` and the `fn-lace-p` type prescription. But 126 262
steps took 18 s, about 50 times this machine's usual rate, so the time
went outside the counted rewrites. I ran experiments on the guard
conjecture of `fn-pol-current`, sent as a `thm`, one at a time:

| hint on the guard conjecture | time | steps |
|---|---|---|
| none (as in the book) | 19.8 s | 126 273 |
| `(disable (:executable-counterpart tau-system))` | 20.3 s | 126 262 |
| `(disable fn-lace-p)` | 20.1 s | 126 077 |
| `(disable fn-pol-stmt-p-shape)`, the only forward-chaining rule on `fn-stmt-p` | 6.7 s | 81 896 |
| `(disable fn-pol-candidates)` | 0.03 s | 14 356 |
| `(disable fn-pol-candidatep)` | 0.03 s | 14 401 |

Cause: `fn-pol-candidatep` was open, and so was the book-wide codec
(line 37 enables the record and CBOR vocabularies, and `theory_check.py
--table` lists `policy` as a codec opener). The rewriter unfolded the
candidates recursion one step and opened the test at `(car lace)`: the
statement recognizer, the signature check `fn-prin-verifiedp` and the
policy decoder. Forward chaining through `fn-pol-stmt-p-shape` on the
new `fn-stmt-p` terms accounts for two thirds of the time. I did not
attribute the other third to a rule. The goal needed only
`fn-pol-candidates-are-lace`, and that lemma's own hint already
disables `fn-pol-candidatep`. The two guard proofs of 9.0 s and 5.5 s
have a related cause. `fn-pol-statement-policy` was open, and the CBOR
item decoder was run to learn that a decoded policy is a list.

Repair (`books/policy.lisp`):

1. A `local` disable of `fn-pol-candidatep` right after
   `fn-pol-candidate-listp`, with a comment.
2. A local shape lemma, `fn-pol-statement-policy-is-true-list`, proved
   from the existing `fn-pol-statement-policy-is-policy` with the
   decoder closed. After it comes a `local` disable of
   `fn-pol-statement-policy`.
3. `fn-pol-authorized-set-is-true-list` used to get the policy's shape
   by opening the decoder. It now `:use`s
   `fn-pol-statement-policy-is-policy`, so its hint changed (a `:use`
   was added) but its statement did not.

### `books/feed-connection-invariants`

| event | before (seam) | after (session) |
|---|---|---|
| `fn-fc-step-preserves-state` | 41.5 s, 11 977 705 steps, 7 702 subgoals, deepest `Subgoal 1.109.108.38.7.5`, 103 at `Subgoal 2'` | 0.01 s, 922 steps |
| `fn-fc-from-line-preserves-state` (local) | 13.8 s, 3 765 858 steps, 1 411 subgoals | 0.02 s, 12 171 steps |
| `fn-fc-table-remove-preserves-table` | 12.8 s, 3 683 132 steps, 537 subgoals under induction, 146 at `Subgoal *1/2'` | 0.02 s, 2 586 steps |
| `fn-fc-with-input-phase-is-state` (local) | 10.8 s, 3 648 011 steps, 3 298 subgoals | 0.55 s, 672 132 steps |
| `fn-fc-table-removed-name-absent` (local) | 2.0 s, 511 115 steps | 0.01 s, 1 980 steps |

`books/feed-connection` exports every definition enabled. Each of these
proofs therefore opened `fn-fc-statep` and, under it, `fn-fwi-statep`,
`fn-wire-octet-listp`, `fn-wire-octetp` and `fn-fap-tokenp` on every arm.
The splitter's if-intro lists name exactly those. The step theorem also
opened `fn-fc-from-line` and `fn-fc-with-input-phase` before this book's
own local lemmas about them could match. The T9c lane found the same
cause in `fn-fc-table-lookup-is-state` and `-put-preserves-table` and
fixed those two (`planning/evidence/feed-tls-teeth-2026-09-22.md`). The
84 s that remained was the same cause in five more proofs.

Repair (hints and two local shape lemmas, in the book only):

- In the five hints, the state recognizers are closed with the same list
  the put and lookup proofs use.
- `fn-fc-from-line-preserves-state` also keeps `fn-fc-with-input-phase`
  closed, so `fn-fc-with-input-phase-is-state` does that work.
- `fn-fc-step-preserves-state` keeps the line handler, the phase update,
  the result record and the fwi accessors closed. Each arm then closes by
  a lemma. For that it needs two local lemmas:
  - `fn-fc-statep-input-and-phase`: a state's input is an
    `fn-fwi-statep` and its phase is an `fn-fc-phasep`;
  - `fn-fc-next-state-of-result`.

### `books/nntp-invariants`

| event | before (seam) | after (session) |
|---|---|---|
| `fn-nntp-next-or-last-preserves-consistent-session` | 61.8 s, 17 547 222 steps, 4 991 subgoals, 624 at `Goal''` | 0.01 s, 9 225 steps |
| `fn-nntp-number-retrieval-preserves-consistent-session` | 5.0 s, 1 827 027 steps, 2 528 subgoals, 343 at `Subgoal 2'` | 0.02 s, 9 653 steps |

Both hints `:use` `fn-nntp-article-response-preserves-consistent-session`,
and the vocabulary opened at the top of the book leaves
`fn-nntp-session-consistentp`, `fn-nntp-sessionp` and
`fn-nntp-cursor-validp` open. So every `:use` instance, and the goal
itself, expanded the session recognizer. The splitter's if-intro list is
`fn-nntp-cursor-validp`, `-session-consistentp`, `-sessionp`, `len` and
`posp`. The arm needs to know only two things about a selected group:
that it is a string, and that it is one of the archive's groups.

I reran the original NEXT/LAST form once in the session by mistake: 53.1 s,
the same 17 547 222 steps. It serves as the Mac baseline.

Repair: two local shape lemmas, placed before the number retrieval:

- `fn-nntp-consistent-session-group-is-a-group`: a consistent session's
  selected group is a member of `fn-state-groups`;
- `fn-nntp-consistent-session-group-is-a-string`.

Both hints now close the session recognizers, the session accessors,
`fn-nntp-single` and `fn-nntp-result-session`. The NEXT/LAST hint no
longer enables `fn-article-nonempty-true-list-is-consp`, which it
needed only to answer the `true-listp` inside the opened session
recognizer. The comment at the top of the book that pointed to that
enable now says so.

### `books/nntp-post` (added by root: 13 s worst wall)

| event | before (seam) | after (session) |
|---|---|---|
| `fn-post-submission-is-an-injected-article` | 3.4 s, 1 664 857 steps, 161 at `Goal` | 0.27 s, 200 634 steps |
| `fn-post-submission-is-the-decision-by-definition` | 1.8 s, 1 084 912 steps, 76 at `Goal` | 0.27 s, 200 247 steps |
| `fn-post-refused-body-submits-nothing` | 1.0 s, 635 648 steps, 60 at `Goal` | 0.01 s, 2 290 steps |

The splitter names `fn-post-sessionp`, `fn-nntp-sessionp` and `posp`. The
step's first test is `(fn-post-sessionp ps)`, and it opened into the
reader session recognizer. The three hints now also disable
`fn-post-sessionp`, as the clock and disallowed-posting theorems in the
same book already did.

### `books/nntp-auth` (not changed)

The 13.9 s is spread across eight theorems of 0.4 to 1.8 s each. Each is a
dispatch over the whole `fn-auth-step`, with 155 to 318 cases at `Goal`,
and each hint already closes the peer step and the tokenizer. The
definitions opened in them are the step's own arms: `fn-auth-command`,
`-authinfo`, `-bind-principal-peer`, `-principal-match` and
`-with-base`. That is the proof's subject, not a recognizer or codec
left open. In the session the book totals 12.7 s, of which 1.9 s is
`include-book "peer-inbound"` with `replay` and `hybrid-store` included
uncertified from source. Getting it under 10 s would need per-arm lemmas
for `fn-auth-step` (config, peer and consistency per arm), with the
dispatch theorems restated as a `:cases` over them. That is a proof
restructure, not a closed theory, so it is left open here.

## Not verified

- These are live-session loads, not certificates. The farm run below
  certifies the five changed books and their test books.
- In the sessions, `nntp-effects` included `nntp-invariants` from
  source, and `nntp-post` included `nntp-effects` and `nntp-invariants`
  from source. Their changed bytes had no cached pair.
- Dependents above these books (`nntp-auth`, `served`, the host images
  and others) were not loaded. Every change is local to its book except
  one: removing `nntp-effects`' book-wide enable of `fn-statep` is also
  local, so no includer sees a different theory. No exported rule was
  added. `fn-pol-statement-policy-is-true-list` is `local`.
- In `policy`, the third of the 49 s that the forward-chaining
  experiment did not explain was not attributed to a rule. The repair
  removes all of it.
