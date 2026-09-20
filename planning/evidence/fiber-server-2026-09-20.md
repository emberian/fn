# Fiber server: v0.1, the owner certifies and runs

What this strand of v0 has proved, what it has only tested, the pessimistic
numbers with the scope they cover, and what is open. Every number here is
cited to the file it came from; nothing is retyped from memory. Written by
the w9/release lane against `dev` at `52eb0db`.


## What is proved

- **The served step is the function the host calls.** `fn-served-step-partition-independence`
  and `fn-served-step-preserves-connp` are about the one function the reader
  host drives per socket; w4/served-path removed the `:program-mode`
  `fn-reader-chunk` and the host's duplicate reply framing, which is what
  closed the wire `pending_subject` note. Cited at
  `planning/requirements.json` HST-001 note.
- **Effects are bounded and typed.** `fn-nntp-step-effects-well-formed`,
  `fn-nntp-closed-step-has-no-effects` and the served effect-typing keystones
  (`planning/requirements.json` HST-002 note).
- **Cursor transitions and error semantics** (NNT-002), **framing independent
  of socket chunk boundaries** (NNT-003) and **views reflect complete
  committed membership** (NNT-006) are `implemented` with keystones in
  `planning/requirements.json`.
- **Three outcomes stay distinct at the entry point.** The deploy gate drove
  accepted 0, refused 1, uncertain 3 from `tools/run_store.py`, the exit codes
  the assurance rules are about: `planning/evidence/deploy-cce4b11-2026-09-20.md`
  rows 11 to 13.

## What is tested and not proved

- One commit ran as a service on persvati, was SIGKILLed from inside an open
  POST, and reread byte-for-byte through a fresh server after recovery:
  `planning/evidence/deploy-cce4b11-2026-09-20.md` rows 23 to 28 (32 steps,
  1 failed, 2 not exercised).
- The read-back after a durable POST works at the owner level: a poster's own
  GROUP sees its own article immediately after its 240
  (`planning/deputies/BOARD.md`, w5/owner-followups, the DIAGNOSED note).

## Open, with the evidence that says so

- **A connection can post exactly once.** Driven directly against the owner on
  persvati: A on conn1 gives 240, B on conn1 gives `441 posting failed; the
  article was refused`, C on conn2 gives 240, D on conn1 gives 441. The cause
  is the single clock observation each connection pins at accept, so the
  injected identity repeats. `planning/deputies/BOARD.md`, w5/owner-followups
  final note. `tests/test_post.py::test_a_reader_pinned_before_a_post_keeps_its_view`
  is left FAILING rather than edited to pass.
- **CAPABILITIES omits POST while POST answers 340.** RFC 3977 section 5.2.2
  requires the capability exactly when posting is permitted. Recorded as a
  live counterexample against NNT-001 in `planning/requirements.json`, found
  at `planning/evidence/deploy-cce4b11-2026-09-20.md` row 20.
- **No concurrent reader on the reader path.** `tools/run_reader.py` serves one
  connection at a time (`listener.listen(1)`), so the v0.1 gate condition -- a
  second reader live across another connection's POST -- cannot be exercised
  there at all; the owner is the only concurrent server and its certification
  is the open item below. `planning/deputies/BOARD.md`, w5-deploy-gate note.
- **`books/nntp-effects` has a real failing form**, not a timeout:
  `FN-NNTP-HDR-LABELLED-LINE-IS-BLOCK-TEXT` at `books/nntp-effects.lisp:971`
  fails after 2598.79 s and 1,473,740,297 prover steps
  (`planning/deputies/BOARD.md`, w5/owner-followups FINAL note). 2598 s for one
  book is a cluster-level cost finding independent of the verdict.

## Pessimistic numbers, each with its scope

- **Slowest single post, 1024-octet bodies**: 6.239 s at a 4096-article store,
  31.0% of the 20.0 s prompt deadline that call was racing; median 3.927 s.
  Scope: persvati, that load window, two groups per article, one writer,
  incompressible bodies. `planning/evidence/scale-0e9a421-2026-09-20.md`.
- **Slowest single post, 32768-octet bodies**: 0.462 s at 512 articles, 1.9% of
  a 20.4 s deadline; median 0.276 s. Same scope.

## Rules this record follows

- A keystone is cited only where a root that reaches it certified in a farm
  gate whose manifest is named above. A theorem admitted in a lane worktree
  and never gated is listed as open, not as proved.
- A pessimistic number carries its scope in the same sentence, and the scope
  names the host, the load and the shape of the input.
- A passing test is not a proof and a certificate is not an audit. Where the
  two disagree about a claim, the disagreement is written down rather than
  resolved in favour of the greener one.
