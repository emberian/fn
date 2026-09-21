# Handoff: w11/owner-config (the last red root in the owner cluster)

Branch `w11/owner-config` from `dev` at `2e99538`. Worktree
`/Users/ember/dev/fn/build/lanes/w11-owner-config`. Takes both packets
[`HANDOFF-w11-snt-guards.md`](HANDOFF-w11-snt-guards.md) §4 left open: the
cross-cluster one (`fn-own-relation` has no identifier bound) and the local
one (the second keystone plus a test book the tree did not have).

## 1. The question that had to be answered before any edit

`fn-ocfg-open-pins-the-live-configuration` needs *freshness of `next-id` in
the pin table*. The board CHANGE asked first whether the bound behind it is
true of the reachable states and merely unstated, or whether connection-id
allocation is defective. **It is true and was merely unstated**, checked by
enumerating every site that builds a connection list or writes the `next-id`
field rather than by eye:

| site | `books/owner.lisp` | conns | next-id | keeps the bound |
| --- | --- | --- | --- | --- |
| `fn-own-open` | `:650` | `(cons conn conns)` at `id = (fn-own-next-id o)` | `(1+ (nfix id))` | yes: the new connection is at the old bound and the bound moves one above it |
| `fn-own-open-peer` | `:697` | the same | the same | yes |
| `fn-own-read`, `fn-own-read-step`, `fn-own-advance`, `fn-own-outcome` | `:751`, `:789`, `:831` | `fn-own-replace-conn` at `(fn-own-conn-id conn)`, or `fn-own-remove-conn` | unchanged | yes: no identifier moves |
| `fn-own-close` | `:849` | `fn-own-remove-conn` | unchanged | yes |
| `fn-own-start` | `:517`, `:532` | `nil` | `0` | yes, vacuously |
| `fn-own-reopen` | `:918` | `nil` | carried | yes, vacuously |
| every other `fn-own-make` | 25 sites | `(fn-own-conns o)` | `(fn-own-next-id o)` | yes, both passed through together |

So no allocation defect, and nothing about allocation changed. What changed
is that the relation now **states** the bound.

## 2. What `books/owner-invariants` gained

`fn-own-ids-below-next-p` (`:164`), one recursive predicate --- every open
connection's identifier is a natural strictly below `fn-own-next-id` --- and
one conjunct of `fn-own-relation` placed immediately after the existing
`(natp (fn-own-next-id o))`, so that conjunct discharges the predicate's
`(natp next-id)` guard at the one call site. The relation gets strictly
stronger, so nothing that HYPOTHESISES it changes.

Four list lemmas beside the existing `fn-own-replace-conn-okp` /
`fn-own-remove-conn-okp` pair (`-monotone` and `fn-own-find-conn-id-below-next`
are `:rule-classes nil`, the replace/remove ones are rewrite rules, and
`fn-own-ids-below-next-p-of-open` is the cons-at-`next-id` rule the two open
arms need). Two exported theorems: `fn-own-relation-has-no-connection-at-next-id`
(what `books/owner-config` spends) and `fn-own-advance-finds-only-what-it-had`
(`:rule-classes nil`).

**Which arms did work.** Measured, not guessed: `ld` of the book with
`:ld-error-action :continue` after the conjunct alone reported **five**
failures, `fn-own-read-`, `fn-own-read-step-`, `fn-own-advance-`,
`fn-own-outcome-` and `fn-own-step-preserves-relation`, and the last two were
the cascade of the first three. `fn-own-open-preserves-relation` and
`fn-own-open-peer-preserves-relation` closed on the new rewrite rule with no
hint at all, and the other thirteen `-preserves-relation` theorems needed
nothing. The cure for the three was one `:instance` each, in the shape their
`fn-own-find-conn-okp` instance already had.

## 3. What `books/owner-config` gained, and why neither statement is weaker

Each keystone gains the hypothesis `(fn-ocfg-statep oc)`. That is the
book's own carried state relation, not an ad-hoc precondition; both theorems
were FALSE without it and were left unproved by the previous lane rather
than weakened.

* **`fn-ocfg-open-pins-the-live-configuration`.** A pin at the identifier
  about to be allocated would have to be the pin of an OPEN CONNECTION there
  (`fn-ocfg-pins-pin-conns-only`), and §1's bound says there is none, so
  `fn-ocfg-pin-add` --- which never overwrites --- installs the live
  configuration. 4077 prover steps, citing
  `FN-OWN-RELATION-HAS-NO-CONNECTION-AT-NEXT-ID`.
* **`fn-ocfg-advance-observes-the-live-configuration`.** `fn-ocfg-pin-set`
  replaces and never adds, so it needs a pin at `id` in the PRE-state table;
  `fn-ocfg-conns-pinnedp` gives it, carried back over the advance by
  `fn-own-advance-finds-only-what-it-had`. 937 prover steps, citing
  `FN-OCFG-PIN-FIND-OF-PIN-SET-SAME`. The hypothesis cannot be moved to the
  pre-state: `fn-own-advance` DROPS a connection whose re-pinned session
  leaves `fn-own-conn-boundedp`, and then `fn-ocfg-advance` leaves the table
  alone and the old pin stands.

**The trap both local bridge lemmas sprang**, worth the next lane's minute:
each is a `defthm` whose conclusion is a recognizer call, so by default it is
a REWRITE rule that turns that call into `T` --- which destroys the very
hypothesis its own `:use` adds, before the exported bridge can contradict it.
Measured: keystone 1 failed at `Subgoal 5''` with the pin in its hypotheses
and the connection term *gone*, and the `Rules` list named the local lemma
and not the bridge. Both are `:rule-classes nil` now.

`fn-ocfg-open-pins-the-live-configuration` also loses its `let` wrapper and
spells the same term out. The theorem is unchanged; the `let` hid the
hypothesis stack from every reader of the source, `tools/teeth_check.py`
among them (`hypotheses_of` sees `let` and reports none).

The prose at `fn-ocfg-pin-add` now names both hypothesis stacks, replacing
the sentence w11/snt-guards withdrew.

## 4. `tests/acl2/owner-config-tests`, and what the teeth checker said

New Makefile root beside `tests/acl2/owner-tests`. The scenario holds **two
configurations at once** --- generation 1 serving `fn.letters` and `fn.test`,
generation 2 serving those and `fn.dtn` --- and two connections pinned one to
each, so no assertion can hold of an empty value and the open/advance
witnesses have something to separate.

| keystone | witness | tooth per hypothesis |
| --- | --- | --- |
| `fn-ocfg-open-pins-the-live-configuration` | the SECOND open: the table already holds the other configuration, so a pin of anything at all would not satisfy the conclusion | `fn-ocfg-statep`: a stale pin at the identifier about to be allocated, after which the new connection serves generation 1 under a generation-2 owner --- the wrong value is a whole configuration, not an absence. "The open installed a connection there": an owner at its connection bound, where `fn-ocfg-statep` HOLDS and only this hypothesis fails |
| `fn-ocfg-advance-observes-the-live-configuration` | connection 0 at generation 1 before and generation 2 after, so a silent no-op FAILS the assertion | `fn-ocfg-statep`: an open connection with no pin, after which the advanced connection serves NOTHING where the live configuration serves three groups. "The advance kept a connection there": an identifier no connection holds, at a state the recognizer accepts |
| `fn-ocfg-pin-is-stable-without-advance` | an event list that is not inert --- it opens a connection and observes a clock, and the third connection is pinned afterwards --- over which the pin it must not move does not move | no pin at the identifier, which one `(:open)` then gives one; and a list that DOES re-pin it, `((:advance 0))`, which moves the pin from generation 1 to generation 2 |
| `fn-ocfg-list-active-lists-the-pinned-served-table` | one hypothesis, so the negative assertion is the case; the positive witness is that the same command on two connections of one owner answers two different group lists | --- |

`python3 tools/teeth_check.py --evaluate tests/acl2/owner-config-tests.lisp`:
**214 probes, prefix ok, exit 0, 214 values**, and `--report` has **no
finding** against the book. Spot-checked in `build/teeth/values.json`: the
stale witness pins `(1 ...)` where the live configuration is `(2 ...)`, and
the two served tables really are the two-group and three-group lists. The
tree counter went from 73 multi-hypothesis keystones with 12 named to **76
with 15** --- three added, three toothed, unchecked unchanged at 61.

## 5. PRF-028 takes the owner side, with its subject gap stated

`planning/proof-events.json` gives PRF-028 the four `fn-ocfg-` keystones
above. **Every one carries a `pending_subject`**, because
`grep -rn fn-ocfg host/ tools/` has zero hits: no host line calls any
`fn-ocfg-` function, `fn-ocfg-served-port-answers-list-active-at-the-pin` is
false today, and the served port still answers LIST ACTIVE from the
allocation domain (`fn-nntp-dispatch`, `books/nntp-responses.lisp:225`,
`:308`, `:319`). That is the R5 wire seam, recorded at the end of
`books/owner-config.lisp` and in `specs/reconfiguration.md` §8 --- and it is
the next global step for this book, not this packet.

## 6. Per-root certification

Box chosen by measurement, not habit, and by FREE MEMORY and not load:
persvati load 5.19 with **55 G available**, hbox load 2.38 with **10 G
available** (112 of 123 G held by the HOL co-tenant). Load said hbox;
memory said persvati, and memory is what kills a box, so persvati.
`--jobs 4` (another lane was on it), `--remote-root
/home/ember/fn-lanes/w11-owner-config`, `--affected-by
books/owner-invariants.lisp --closure` --- one wide run rather than many,
because the conjunct is in `books/owner-invariants`.

persvati **`run-20260921T001423Z-0f98`**, evidence
`build/acl2/certify-20260921T001432Z-904323/manifest.json`; ACL2 8.7 /
SBCL 2.6.8 at `/home/ember/fn-tools/acl2-8.7/saved_acl2`, sha256
`c8a7a804d9cc80e2025a8ab0e1d9325f2a0c4a027a5dcdcb2c1093e9cd5c8163`,
`ACL2_CUSTOMIZATION=NONE`, `ACL2_BOOK_HASH_ALISTP=NIL`, `timeout_seconds`
1800, the tree at this lane's `a74707c`. 275 roots selected before the cache
filter; **74 books attempted, 74 certified, 0 failed**, 231.2 s wall. Box
cache on submit: installed 69, kept 89, uncached 118, foreign_local 0; all
74 pairs published back. `local_source_audit` findings: none (`defaxiom`,
`defttag`, `include-raw`, `set-raw-mode`, `skip-proofs`).

| root | verdict | evidence |
| --- | --- | --- |
| `books/owner-config` | **certified**, 1.004 s | `run-...-0f98`, `books--owner-config.certify.log`: zero `ACL2 Error`, 29 `Q.E.D.` This was the run's only failure in `run-20260920T234122Z-7687`; it is the last red root the owner cluster had |
| `tests/acl2/owner-config-tests` | **certified**, 1.015 s | `tests--acl2--owner-config-tests.certify.log`: **75 of 75 `:PASSED`**, zero `ACL2 Error`. New root |
| `books/owner-invariants` | **certified**, 8.112 s | 111 `Q.E.D.`, zero `ACL2 Error`; the new conjunct and its five theorems |
| `tests/acl2/owner-tests` | **certified**, 1.155 s | **166 of 166 `:PASSED`**, unchanged: the stronger relation killed no owner witness. Its hand-built counterexamples all carry a `next-id` above their connection identifiers, so each still fails the relation for the reason it was written for |
| `books/owner` | **certified**, 1.344 s | `run-...-0f98` |
| `books/served`, `books/config-stream` | **certified**, 1.474 s / 0.847 s | `run-...-0f98` |
| the other 68 attempted roots | **certified** | `manifest.json` `book_results`, all `passed` |
| `make check` | green | laptop, before each commit; `session_depth` 0 defects, ledger current |

`dev` moved to `5ae226f` (w11/tcpcl-theory) while this ran. Its books ---
`books/tcpcl-invariants`, `books/tcpcl-session`, `tests/acl2/tcpcl-tests` ---
are in NO root of this closure (`grep -c tcpcl` over the 74 is zero), so the
run above still speaks for the merged tree's owner cluster. The merge's three
conflicts were `planning/deputies/BOARD.md` (both sections kept) and the two
generated ledger files (regenerated, not hand-resolved).

## 7. Ledger over the lane (`dev` `2e99538` to this branch)

| quantity | before | after |
| --- | --- | --- |
| `defthm`/`defthmd` | 5507 | 5516 |
| `defun` | 3926 | 3927 (`fn-own-ids-below-next-p`) |
| certification roots | 274 | 275 (`tests/acl2/owner-config-tests`) |
| `assert-event` checks | 5310 | 5385 |
| theorems flagged SUSPECT | 46 | 46 |
| export-hygiene warnings | 72 | 72 |
| enabled-projection warnings | 26 | 26 |
| multi-hypothesis keystones / named in a test book | 73 / 12 | 76 / 15 |

Two theorems are added to an export theory (`fn-own-invariants-vocabulary`
gains the new predicate and its three rewrite rules; the bridge and
`fn-own-advance-finds-only-what-it-had` stay out of it, the first
deliberately --- `books/owner-config` spends it --- and the second because a
`:rule-classes nil` theorem has no rune to withdraw).

## 8. What was NOT done

* **The wire.** No host line calls any `fn-ocfg-` function
  (`grep -rn fn-ocfg host/ tools/`: zero hits), so
  `fn-ocfg-served-port-answers-list-active-at-the-pin` is still false and
  still recorded rather than stated, and all four PRF-028 owner-side events
  carry a `pending_subject`. **This is the next global step for this book**:
  one served-table argument on `fn-served-conn`, `fn-served-dispatch` and
  `fn-nntp-dispatch`, owned jointly by the owner and NNTP clusters.
* **`fn-ocfg-statep` is not proved preserved by `fn-ocfg-step`.** The two
  keystones hypothesise it and the test book EVALUATES it true at every
  state of its scenario --- after each open, after the configuration moves,
  after the advance --- but there is no `fn-ocfg-step-preserves-statep`.
  Until there is, "under `fn-ocfg-statep`" is a hypothesis about a
  recognizer, not about a reachable state. That is the next packet in this
  book, and it is smaller than it looks: `fn-ocfg-open` and `fn-ocfg-close`
  move the table exactly as the owner moves the connection list.
* **Recovery.** `fn-own-reopen` still replays the article history only, so
  the owner cannot state the recovered generation (`books/owner-config.lisp`,
  the OPEN note at the end). Unchanged by this packet.
* No `skip-proofs`, no `defaxiom`, no trust tag, no statement weakened, no
  keystone removed.
* `tools/proof_profile.py` was not run: the slowest form in this packet is
  `prove: 0.01`, 4108 prover steps, and the rule is to profile a SLOW form.
  The whole book certifies in 1.004 s.
