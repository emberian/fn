# Fiber convergence-release: v0.6, one gate over every root

What this strand of v0 has proved, what it has only tested, the pessimistic
numbers with the scope they cover, and what is open. Every number here is
cited to the file it came from; nothing is retyped from memory. Written by
the w9/release lane against `dev` at `52eb0db`.


## What is proved

- **The gate machinery itself.** `tools/certs.py` will not cache a pair except
  against a passed manifest, keyed on the whole include closure, so a cached
  certificate cannot outlive the book text it was made from
  (`planning/requirements.json` HST-004 note).
- **The ledger is generated.** `planning/proofs.json` event arrays come from
  `tools/ledger.py` over `planning/proof-events.json`; a cited name must exist,
  must not be flagged by the suspect detector, and must live in a book a
  Makefile root reaches (`docs/proofs.md`, "Registry states").
- **21 of the 56 registry requirements are `implemented`** with keystones and
  evidence paths; 26 proof targets are registered, 16 `in-progress` and 10
  `planned`, and none is `certified`. Counts from `planning/requirements.json`
  and `planning/proofs.json` at `52eb0db`.

## What is tested and not proved

- One command now reproduces the whole verdict: `tools/verdict.py <commit>
  --host persvati` ships the commit, runs the box gate (`make certify`, the
  Python suite, `tools/gate_publish.sh`), then the deploy gate, the two-node
  gate, the INN lab on hbox and the scale gate with `--reuse`, under a lock
  held on every host it touches. Its run against `52eb0db` is
  `planning/evidence/verdict-52eb0db-2026-09-20.md`.
- Two boxes run fn as a service from `packaging/`:
  `planning/evidence/live-52eb0db-2026-09-20.md`.

## Open, with the evidence that says so

- **No proof target is `certified`.** Sixteen are `in-progress`, which the
  registry's own description defines as "not fully certified".
- **The v0.6 gate condition is not met**: it asks that every requirement be
  `implemented`/`validated` with keystones or `deferred` with a reason, and 35
  are still `specified`.
- **The suite is not green.** The Python failures and errors counted in the
  verdict record are the current number; the two named in
  `planning/deputies/BOARD.md` that will not clear by retrying are the
  second-post 441 (w5/owner-followups, diagnosed: one pinned observation per
  connection means one durable post per connection) and the reader-pin case
  that depends on it.
- **The include-hygiene backlog is open.** `tools/ledger.py`'s host lint found
  47 names that resolve only because a bridge happens to `ld` another file
  first, across eight host files; `host/owner-host.lisp` is the worst with 16.
  Nothing in the tree records that load order except
  `host/native/build.lisp`. `planning/deputies/BOARD.md`, w5/host-lint.
- **Identity and authority (D01, OBJ-003, OBJ-007) are unwritten.**
  `books/crypto-seam` and `books/statement` certify but are an abstract seam;
  AGENTS.md forbids reading an abstract model as a signature claim.

## Pessimistic numbers, each with its scope

- **One full `make certify` of this tree**: 221 Makefile roots. The
  `bdd59d2` gate completed 213 of 216 roots in 709.8 s at 12 jobs on persvati;
  the current tree's number is in `planning/evidence/verdict-52eb0db-2026-09-20.md`.
  Scope: persvati, that job count, with the box's cache warm -- a cold box is
  a different measurement entirely.
- **The single most expensive book**: `books/nntp-effects` at 2598.79 s and
  1,473,740,297 prover steps, and it fails at the end of that
  (`planning/deputies/BOARD.md`, w5/owner-followups FINAL note). Scope: one
  invocation at `--timeout-seconds 5400` with the box co-tenant.
- **A certificate set is not relocatable.** Certificates record absolute
  full-book-names, so 217 pairs scavenged across directories made the native
  build refuse; all of a set must come from one directory
  (`planning/deputies/BOARD.md`, w8/tcpcl-native). Scope: every future attempt
  to warm a tree from more than one gate.

## Rules this record follows

- A keystone is cited only where a root that reaches it certified in a farm
  gate whose manifest is named above. A theorem admitted in a lane worktree
  and never gated is listed as open, not as proved.
- A pessimistic number carries its scope in the same sentence, and the scope
  names the host, the load and the shape of the input.
- A passing test is not a proof and a certificate is not an audit. Where the
  two disagree about a claim, the disagreement is written down rather than
  resolved in favour of the greener one.
