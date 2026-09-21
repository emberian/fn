# `fn-cpc-validp` accepted a prefix that is not a journal (2026-09-21)

Lane `w11/checkpoint-validator`. ACL2 8.7, laptop, `tools/certify_books.py`
with `ACL2_BOOK_HASH_ALISTP=NIL` (set by the tool).

## The question

`tests/acl2/checkpoint-codec-tests.lisp:204` asserted

    (not (fn-cpc-validp *cpc-value* *cpc-groups* 10
                        (list *cpc-r0-bad-generation*)))

and `tools/teeth_check.py --evaluate` reported the body NIL
(`planning/evidence/teeth-audit-2026-09-20.md:38`); the wildmat lane hit the
same root as the single foreign failure of a 151-root run. Two readings were
open: the validator is wrong, or the witness is not actually bad-generation.

## The measurement

One `ld` run against the FIXED book, with the OLD body re-defined in the same
world under a scratch name so both verdicts come from one world. Driver:
`tests/acl2/cpv-driver.lsp` (untracked scratch; its text is below).

    1 gen/txid of the witness      1 / 0
    2 fn-sf-record-listp bad       NIL
    3 fn-checkpoint-capture bad    (:ERROR :HISTORY)
    4 replay(bad) EQUAL replay(ok) T
    5 OLD fn-cpc-validp on bad     T
    6 NEW fn-cpc-validp on bad     NIL
    7 NEW fn-cpc-validp on sound   T
    8 capture-value(bad) = *val*   NIL

Line 1 settles the second reading: `*cpc-r0-bad-generation*` is `*cpc-r0*`
with the generation it consumed moved off its txid, which is exactly what
`fn-sf-record-listp` forbids (`books/store-files.lisp:233`), and line 2 is
that recognizer refusing it. **The witness was right.** Line 5 is the defect:
the validator answered T on a prefix the model's own capture refuses as
`:history` (line 3).

Line 4 is why no amount of replay could have caught it.
`fn-replay-apply-record` (`books/replay.lisp:263`) passes
`(fn-record-generation record)` into `fn-node-prepare`,
`fn-node-pending-matchesp` and `fn-node-complete` and never compares it with
`(fn-record-txid record)`, so replay of the corrupt prefix returns a result
EQUAL to replay of the sound prefix. A validator that compares only replay
results is blind to this corruption by construction.

Line 8 is the tooth: with the clause dropped, `fn-cpc-valid-is-capture-value`
would be FALSE on this witness, because the capture of the prefix is the
refusal and not the checkpoint offered.

## The fix

`books/checkpoint-codec.lisp`: `fn-cpc-validp` carries
`(fn-sf-record-listp prefix 0 0 (fn-checkpoint-frontier checkpoint))` as a
clause, placed after the configuration equalities and before the replay, in
the clause order `fn-checkpoint-capture` uses. Validation is now the third
member of the family that tests this condition, beside capture's `:history`
(`books/checkpoint.lisp:163`) and restore's `:suffix`
(`books/checkpoint.lisp:222`).

- `fn-cpc-valid-is-capture-value` loses its second hypothesis, which is now
  a clause of its first: one hypothesis, `fn-cpc-validp`.
- `fn-cpc-valid-refuses-generation-mismatch` (new, `:rule-classes nil`):
  a prefix with any member whose generation is not its txid is refused, for
  every checkpoint and configuration offered with it. `:rule-classes nil`
  because as a rewrite it would be a free-variable rule concluding NIL on a
  recognizer call.
- One local guard fact, `fn-cpc-checkpointp-frontier-is-natural`, and one
  local `:rule-classes nil` induction, `fn-cpc-journal-generation-matches`.

Teeth in `tests/acl2/checkpoint-codec-tests.lisp`, all concrete values:
the witness (both hypotheses hold, validation refuses); membership dropped
(the same mismatching record, not a member of the prefix offered, validation
accepts); mismatch dropped (`*cpc-r0*`, a member whose generation is its
txid, validation accepts); and the clause's own tooth, line 8 above.

## Certification

| root | result | evidence |
| --- | --- | --- |
| `books/checkpoint-codec` | passed | `build/acl2/certify-20260921T014816Z-65096` |
| `tests/acl2/checkpoint-codec-tests` | passed | `build/acl2/certify-20260921T015342Z-73133` |
| `books/checkpoint-publish` | passed | `build/acl2/certify-20260921T015044Z-68937` |
| `tests/acl2/checkpoint-publish-tests` | passed | same run |
| `tests/acl2/checkpoint-tests` | passed | same run |

Those five runs predate the second `git merge dev` (to `186ed0b`), which
changed `books/store-node-invariants` and so invalidated every certificate in
that closure, including the checkpoint books'. The authoritative post-merge
evidence is the whole-tree run below, which re-certified all of them.

`certify-book` stops at the first failure, so before this lane the ~45 events
of the test book after line 204 had never been attempted. They are attempted
now and they pass; the tail the deputy brief warns about was empty here.

## The whole tree, post-merge

hbox `run-20260921T020141Z-c3c3`, every Makefile root, `--jobs 8`, remote
root `/tank/fn/lanes/w11-checkpoint-validator`, tree = `dev` `186ed0b` plus
this lane's fix (commit `6ad5a80`). Manifest:
`/tank/fn/lanes/w11-checkpoint-validator/build/acl2/certify-20260921T020148Z-1425543/manifest.json`.

**274 of 276 roots passed.** The two failures are `books/bp-node` and
`tests/acl2/bp-node-tests` (`ACL2 Error`, no certificate on disk), both owned
by `w11/bp-node`. All six checkpoint roots passed. 273 pairs were published
to `~/.cache/fn-certs` and hbox's `/tank/fn/certcache` has them too.

One book of the 277 read is outside the root closure and so is certified by
nothing: `tests/acl2/store-node-resolution-traces-tests.lisp`, which is not
in `ACL2_BOOKS` and which no book includes. It is ABSENT from `book_results`
rather than failed. It arrived in `8209f27`.

## PRF-008, in the same cluster

`teeth_check --report` also flagged PRF-008: all three of its events were
named in no test book. They are named now, and each has the one hypothesis
it has (`fn-checkpoint-admissible-splitp`) shown necessary on a concrete
value, in `tests/acl2/checkpoint-tests.lisp`
(`build/acl2/certify-20260921T021458Z-14379`):

- `fn-checkpoint-admissible-capture-is-exact`: the capture on the admissible
  split is asserted equal to the exact `fn-checkpoint-make` the theorem
  names, not merely `:ok`.
- `fn-checkpoint-admissible-capture-value-is-valid`: `fn-checkpointp` of
  that value, already asserted.
- Tooth for both: a prefix whose record binds generation 1 against txid 0 --
  the same corruption this lane fixed in the codec -- makes the split
  inadmissible, the capture not that `fn-checkpoint-make`, and its value not
  a checkpoint at all.
- `fn-checkpoint-plus-suffix-equals-full-replay`: the restore/full-replay
  equality on the admissible split, already asserted. Tooth: with
  `*cp-stale-txid*` as the suffix the split is inadmissible and the two
  sides genuinely disagree -- restore refuses the frontier reuse as
  `:suffix` while full replay of the appended history answers `:ok`. That is
  the divergence the hypothesis rules out, and it is a safety-relevant one.

Corpus `keystone-without-witness` 22 -> 21; no finding of any class remains
in this cluster.

`tools/teeth_check.py --evaluate --report tests/acl2/checkpoint-codec-tests.lisp`

- before (`planning/evidence/teeth-audit-2026-09-20.md`): one `assertion-false`
  at line 204, one `book-does-not-run` refusal at that same form (so the
  assertions after it were inert, not weak), one `predicate-never-anchored`
  and one `recogniser-never-true` for `fn-cpc-result-okp` at line 117.
- after: 274 probes, `prefix ok`, exit 0, all 274 evaluated; 78 assert-events,
  78 witnesses, **0 findings**. `fn-cpc-result-okp` is anchored positively on
  the accepted decode at line 118, which closed the two line-117 findings.

## What this does not say

`fn-cpc-validp` has no caller in `host/`, `tools/` or any other book. The
served restore path is `host/checkpoint-host.lisp` -> `fn-checkpoint-restore`,
which tests `fn-sf-record-listp` on its suffix and was never exposed to this
bug. These keystones are the codec cluster's statement of what validation
means; they do not yet cover the host's path, and no requirement should cite
them as if they did.

## Driver text

    (set-prover-step-limit 2000000)
    (include-book "../../books/checkpoint-codec")
    (set-guard-checking :none)
    (defun cpv-old-validp (checkpoint groups capacity prefix)
      (declare (xargs :guard t :verify-guards nil))
      (and (fn-checkpointp checkpoint)
           (equal groups (fn-checkpoint-groups checkpoint))
           (equal capacity (fn-checkpoint-capacity checkpoint))
           (let ((answer (fn-replay groups capacity prefix)))
             (and (fn-replay-okp answer)
                  (equal (fn-replay-result-sequence answer)
                         (fn-checkpoint-sequence checkpoint))
                  (equal (fn-replay-result-node answer)
                         (fn-checkpoint-node checkpoint))))))
    (defconst *g* '("fn.letters" "fn.test"))
    (defconst *r0* (fn-record-make 0 0 0 "<cp0@example.invalid>" '(65 13 10)
                      '("fn.letters") "cp-pin-0" "cp-content-0" "cp-release-0" 2))
    (defconst *rb* (fn-record-make 0 0 1 "<cp0@example.invalid>" '(65 13 10)
                      '("fn.letters") "cp-pin-0" "cp-content-0" "cp-release-0" 2))
    (defconst *pfx* (list *r0*))
    (defconst *bad* (list *rb*))
    (defconst *val* (fn-checkpoint-capture-value
                     (fn-checkpoint-capture *g* 10 *pfx* 3)))

run from `tests/acl2/` (the driver must run in the book's directory) as
`../../tools/acl2 --timeout 240 < cpv-driver.lsp`, followed by the eight
`cw` probes printed above.
