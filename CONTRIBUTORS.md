# Contributors' guide

`CONTRIBUTING.md` has the commands. This page is the design in brief, and
how to read a claim. Each line names the file that says it at length.

## The design

- ACL2 decides; native Common Lisp does the I/O. Identities, limits,
  framing, groups, charges and every reply are ACL2 functions in `books/`;
  `host/` reads sockets and disks and calls them
  (`docs/architecture.md`).
- fn says yes only after the disk confirms. Every answer is accepted,
  refused or uncertain, and they are never mixed up
  (`specs/lifecycle.md`, `specs/failures.md`).
- An article's bytes, its Message-ID and a node's article number are
  different things (`specs/objects.md`, `docs/glossary.md`).
- Work is bounded per step; a step that runs out of its quantum yields
  and resumes. What is bounded, and by which theorem, is
  `docs/resource-contract.md`.
- The store representation being built now is
  `planning/design-store-representation-2026-10-01.md`.

## Where truth lives

| question | file |
| --- | --- |
| what is decided | `planning/decisions.md` |
| what fn must do | `planning/requirements.json`, then `specs/` |
| what is to be proved | `planning/proofs.json`, `docs/proofs.md` |
| what is true now | `planning/now.md`, `planning/current.md` (generated) |
| what is broken | `planning/repair/STATUS.md` (generated from `planning/repair/items/`) |
| which examples must work | `tests/scenarios/catalog.json` |
| how to test each kind of thing | `docs/testing.md` |

A dated plan or record describes its own date, not today.

## Reading a claim

A claim names its coordinate: the source commit, whether the books were
admitted or certified, whether a process or a built image ran, and on
which node. None of these implies the others (`AGENTS.md`, "What makes a
claim").

A theorem counts only when its subject is the function the server
actually calls, or is bridged to it by name (`tools/reach_check.py`
checks this). A key theorem ships with a witness that its hypotheses
can hold and one showing it fails without them. No `skip-proofs`,
`defaxiom` or trust tag counts as done (`docs/proofs.md`).

Unfinished work is listed, not hidden: `planning/now.md` and the repair
ledger name what is still open.
