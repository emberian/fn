# Deputy board (append-only; shared across worktrees)

Every deputy reads this file at start and before its final report, and
appends to it (never edits above its own entries) at the main checkout path
`/Users/ember/dev/fn/planning/deputies/BOARD.md`, using
`git -C /Users/ember/dev/fn commit` of this one file with message
`board: <cluster>: <one line>`. Entries are dated, signed with the cluster
name, and short. Three kinds:

- **CHANGE** `<cluster>`: an exported name, statement, or rule class that
  changed or will change; which includers are affected; the one-line edit each
  needs. Includers read this before certifying against a rebased base.
- **ASK** `<cluster>` → `<cluster>`: a blocking question with the exact form
  or file:line. The addressed deputy answers with **ANSWER** in place; the
  root answers if the addressee is gone.
- **NOTE** `<cluster>`: a pattern, pitfall or measurement worth every other
  deputy knowing (one or two lines, with the file:line that shows it).

Direct messages between deputies, where the harness allows them, are for a
blocking ASK only; the board is the record.

---
