# PKT-855: the reclaim's note (correctness-remainder-9, 2026-09-29)

N2 of planning/evidence/proto-determinism-2026-09-27.md: `store reclaim`
rewrites history; a holder of the pre-reclaim log could not tell why its fold
differs. PKT-857 recorded the instant (a configuration row). What was missing
was a durable statement of WHAT the reclaim decided over WHICH history.

## Decision: a configuration delta in the instant's record, not a log event

The shape correctness-remainder-5 sketched (an `fn-e` log event, code 2, as
the rewritten history's last record) touches every store-event dispatch:
`fn-cpe-eventp` appears in 251 places across 51 files, and no fold ignores
an unknown kind (it falls to the article path and is refused). The
configuration history already holds the instant, survives the drop that
unlinks the covered segments, and travels with a copy of the store. A new
configuration delta kind costs `books/config.lisp` (kind, code, apply,
reason) and nothing else.

`(:reclaim-note TEXT "" 0 ())`, code 28, is published in the same record as
the instant (`fn-rcn-deltas`), so no process death separates them. The value
keeps the latest note as the limits row `("retention-reclaim-note" "" TEXT 0)`.
The history keeps every note.

TEXT = `at=CODE history=N reclaimed=K freed=F msgids=HEX` (`fn-rcn-text`).

## Check

`store reclaim --recorded` computes its decision, then `fn-rcn-check`
answers one of three things:
- `:checked` when the note at the recorded instant is this decision's note;
- `:reclaim-note-mismatch`, refused by name before any rewrite;
- `:unchecked` when nothing is reclaimed or the note is of an earlier instant.

Keystones: `fn-rcn-recorded-note-reads-back`, `fn-rcn-recorded-note-checks`
(PRF-1025).

## Open

- The live owner pass (`fnn-owner-reclaim-pass`, books/owner-reclaim-instant)
  records its instant without a note; its rerun is `:unchecked`. It should
  publish the note after its decision and before the install
  (online-reclaim's path). Until then a live instant within the same second
  as an earlier offline reclaim's would compare against that stale note (the
  prefix matches by instant code only).
- The fold does not APPLY the note. A holder of the old log re-derives the
  rewrite with `--recorded`; "state = fold(old log ++ note)" is not a
  theorem.
