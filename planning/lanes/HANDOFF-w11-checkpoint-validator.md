# w11/checkpoint-validator — the validator was wrong, not the witness

Branch `w11/checkpoint-validator`, from `dev` and merged with `dev` `186ed0b`.
One commit. Evidence for every number here:
[`planning/evidence/checkpoint-validator-2026-09-21.md`](../evidence/checkpoint-validator-2026-09-21.md).

## The verdict

`tests/acl2/checkpoint-codec-tests.lisp:204` was the one failing root of the
2026-09-21 persvati gate (`~/fn-gates/dev-e4fb8bc`, evidence
`build/acl2/certify-20260921T010456Z-1412435`, 272 of 275) that no lane
owned. Two readings were open and exactly one is true:

**The validator was wrong.** `*cpc-r0-bad-generation*` is a genuine
non-journal record — `fn-record-make 0 0 1 …`, so generation 1 against txid
0, which is precisely the equality `fn-sf-record-listp` requires
(`books/store-files.lisp:233`). `fn-sf-record-listp` refuses it and
`fn-checkpoint-capture` answers `(:error :history)`. `fn-cpc-validp`
answered **T**. A validator whose job is to refuse malformed durable state
accepted a prefix that the model's own capture refuses, and the two owners of
"is this prefix a journal" disagreed about the same bytes.

The comment above the assertion — that "replay refuses that record, so
validation fails with it and the hypothesis is not separately droppable on an
executable witness" — was the false part. It is droppable, and this is the
witness that drops it.

## Why replay could never have caught it

`fn-replay-apply-record` (`books/replay.lisp:263`) passes
`(fn-record-generation record)` into `fn-node-prepare`,
`fn-node-pending-matchesp` and `fn-node-complete` and never compares it with
`(fn-record-txid record)`. Measured in one `ld`:

    (equal (fn-replay groups capacity bad-prefix)
           (fn-replay groups capacity sound-prefix))   ==>  T

So a validator that compares only replay results is blind to a corrupt
generation binding **by construction**. This is a fact about `fn-replay`, not
about this witness, and anyone else who plans to check durable state by
comparing replay results should read it as such.

## The fix

`books/checkpoint-codec.lisp`. `fn-cpc-validp` carries
`(fn-sf-record-listp prefix 0 0 (fn-checkpoint-frontier checkpoint))`, placed
after the configuration equalities and before the replay, in the clause order
`fn-checkpoint-capture` uses. Validation is now the third member of the
family that tests this condition, beside capture's `:history`
(`books/checkpoint.lisp:163`) and restore's `:suffix`
(`books/checkpoint.lisp:222`).

- `fn-cpc-valid-is-capture-value` loses its second hypothesis, which is now a
  clause of its first. One hypothesis: `fn-cpc-validp`. Nothing is weakened —
  the content is the same implication with a stronger subject, and a host that
  calls the validator now gets the binding with no side condition to discharge.
- `fn-cpc-valid-refuses-generation-mismatch` is new: any member of the prefix
  whose generation is not its txid refuses validation, for every checkpoint
  and configuration offered with it. `:rule-classes nil` **on purpose** — as a
  rewrite it would be a free-variable rule (`record` occurs only in the
  hypotheses) concluding `nil` on a recognizer call, which is the shape the
  deputy brief names as a trap.
- Two local supports: `fn-cpc-checkpointp-frontier-is-natural` (the guard
  obligation the new clause adds) and `fn-cpc-journal-generation-matches`
  (`:rule-classes nil`, the induction over the record list).

Teeth in the test book, all concrete values, none a general negated
`must-fail`: the witness with both hypotheses holding and validation
refusing; membership dropped (the same mismatching record, not a member of
the prefix offered — validation accepts); mismatch dropped (`*cpc-r0*`, a
member whose generation is its txid — validation accepts); and the clause's
own tooth, that `fn-checkpoint-capture-value` of the corrupt prefix is not
the checkpoint, which is what would make `fn-cpc-valid-is-capture-value`
false if the clause were removed.

One more finding in the same book, from `teeth_check --report`:
`fn-cpc-result-okp` was asserted false once and true nowhere in the corpus,
so a constantly-false definition satisfied every claim about it. It is
anchored positively now on the accepted decode (line 118).

## What ran

| root | result | evidence |
| --- | --- | --- |
| `books/checkpoint-codec` | passed | `build/acl2/certify-20260921T014816Z-65096` |
| `tests/acl2/checkpoint-codec-tests` | passed | `build/acl2/certify-20260921T015342Z-73133` |
| `books/checkpoint-publish` | passed | `build/acl2/certify-20260921T015044Z-68937` |
| `tests/acl2/checkpoint-publish-tests` | passed | same run |
| `tests/acl2/checkpoint-tests` | passed | same run |

`python3 tools/certify_books.py --affected-by books/checkpoint-codec.lisp
--dry-run` names exactly four roots, and all four are above, so no other
root's verdict can move because of this lane. Those five runs predate the
second `git merge dev` (`186ed0b`), which changed `books/store-node-invariants`
and invalidated every certificate in that closure; the authoritative
post-merge evidence is the whole-tree run below.

**The whole tree, post-merge.** hbox `run-20260921T020141Z-c3c3`, every
Makefile root, `--jobs 8`, remote root
`/tank/fn/lanes/w11-checkpoint-validator`, manifest
`.../build/acl2/certify-20260921T020148Z-1425543/manifest.json`. **274 of
276 roots passed, and the only two failures are `books/bp-node` and
`tests/acl2/bp-node-tests`** — the pair `w11/bp-node` owns. So on this
lane's tree the answer to "does the whole tree certify but for the
bundle-node pair" is yes. 273 pairs published to `~/.cache/fn-certs` and to
hbox's `/tank/fn/certcache`.

One book of the 277 read is certified by nothing:
`tests/acl2/store-node-resolution-traces-tests.lisp` is not in `ACL2_BOOKS`
and no book includes it, so it is the single book outside the root closure
that `planning/ledger.md` counts. It arrived in `8209f27`. Posted as a NOTE;
this lane does not own the call.

**PRF-008, same cluster.** `teeth_check` also flagged that all three PRF-008
events were named in no test book. They are named now in
`tests/acl2/checkpoint-tests.lisp`
(`build/acl2/certify-20260921T021458Z-14379`), each with its one hypothesis
(`fn-checkpoint-admissible-splitp`) shown necessary on a concrete value: the
exact-capture equality and `fn-checkpointp` of its value, both broken by a
bad-generation prefix (the same corruption this lane fixed in the codec);
and the restore/full-replay equality, broken by `*cp-stale-txid*` as the
suffix, where restore refuses the frontier reuse as `:suffix` while full
replay of the appended history answers `:ok`. Corpus
`keystone-without-witness` 22 → 21; no teeth finding of any class remains in
this cluster.

`certify-book` stops at the first failure, so before this lane the events of
the test book after line 204 had never been attempted; they are attempted now
and they pass. The tail the brief warns about was empty here.

`tools/teeth_check.py --evaluate --report tests/acl2/checkpoint-codec-tests.lisp`
after: 274 probes, `prefix ok`, exit 0, all evaluated; 78 assert-events, 78
witnesses, **0 findings**. Ledger for the cluster: `books/checkpoint-codec`
105 → 108 `defthm`s, `tests/acl2/checkpoint-codec-tests` 68 → 78
`assert-event`s; tree totals 5638 → 5641 and 5634 → 5644. `make check` green.

## Registry

`PRF-037` (claimed on the board before it was written; `PRF-035` is
`w11/one-owner`'s claim and is not in the file yet, `PRF-036` is
`w11/bytestore-k2`'s and is). Status `certified`, requirement `STO-006`,
depends on `PRF-008`. Both events carry a `pending_subject` note.

## What is still open, and it is the honest part

**`fn-cpc-validp` has no host caller.** Nothing in `host/`, `tools/` or any
other book calls it; the served restore path is `host/checkpoint-host.lisp` →
`fn-checkpoint-restore`, which tests `fn-sf-record-listp` on its suffix and
was therefore never exposed to this bug. By the first assurance rule these
keystones are properties of a sibling API. They are worth having — the codec
cluster's statement of what validation means, and the defect was real — but
no requirement should cite them as covering the served path until either the
host calls `fn-cpc-validp` or a named theorem equates it to what
`fn-checkpoint-restore` admits. That is the cross-cluster step this lane
could not take alone; it belongs to whoever owns `host/checkpoint-host.lisp`.

The natural shape of that theorem, for whoever takes it: with
`checkpoint = fn-cpc-result-value (fn-cpc-frame-decode …)` and the same
prefix, `fn-cpc-validp` holds exactly when `fn-checkpoint-restore` on the
empty suffix returns `:ok` at the checkpoint's own frontier. Both sides now
test the journal-interval condition, which is what made them incomparable
before this lane.
