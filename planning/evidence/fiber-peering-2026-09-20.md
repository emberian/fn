# Fiber peering: v0.2, two nodes that converge

What this strand of v0 has proved, what it has only tested, the pessimistic
numbers with the scope they cover, and what is open. Every number here is
cited to the file it came from; nothing is retyped from memory. Written by
the w9/release lane against `dev` at `52eb0db`.


## What is proved

Landed with w6/peering-inbound (`planning/deputies/BOARD.md`, 2026-09-20):

- **K1, transit is the POST path**: `fn-peer-transfer-is-the-post-path` and
  `fn-peer-transfer-stages-only-scope-groups` in `books/peer-inbound-invariants.lisp`.
  This is the subject-rule theorem for the whole fiber: it says the transit
  entry point reduces to one `fn-node-prepare`, the same acceptance POST uses.
- **K2, loop freedom**: `fn-peer-loop-is-refused`, over the RFC 5537 3.6 Path
  test `fn-path-names-p` in the new `books/path.lisp`.
- **K3, duplicate suppression**: `fn-peer-history-is-refused-at-offer`,
  `fn-peer-history-is-refused-at-transfer`, `fn-peer-history-grows-under-transfer`,
  with `fn-peer-history-hasp` = articles union bindings.
- **Peer records are configuration, not a file**: `books/config.lisp` gained
  `:set-peer` (code 9) and `:remove-peer` (code 10); `*fn-cfg-delta-kinds*` has
  ten members. `books/peer-config.lisp` holds the opaque six-field
  `fn-cfg-peerp` and `fn-cfg-peer-deltas-change-only-peers`.
- **Transit is refused on a reader connection**: `books/nntp.lisp` answers
  IHAVE/CHECK/TAKETHIS with `502 transit is not permitted on this connection`
  (RFC 3977 3.2.1; it was 500 as an unknown keyword).

## What is tested and not proved

- Two fn nodes on one host exchanged articles both ways and converged:
  `planning/evidence/twonode-dfd8758-2026-09-20.md`, 63 steps, 0 failed, 5 not
  exercised.
- Against a real INN 2.7.4 built from a pinned tarball
  (sha256 `80fc7e80...b051d3b`), IHAVE into INN, the duplicate and the Path
  loop, and what innfeed sends to fn sent by hand:
  `planning/evidence/inn-lab-f4e8272-2026-09-20.md`, 75 steps, 0 failed, 2 not
  exercised, on hbox.

## Open, with the evidence that says so

- **The outbound half of K2, K4 restart, the general tail-entry lemma, RFC 5537
  3.6 step 2** (there is no certified RFC 5322 date reader) and
  **`verify-guards` of the decision functions** are recorded open in
  `specs/peering.md` status and in the w6/peering-inbound board note.
- **`fn-cfg-peer-rows` / `fn-cfg-peer-of-rows` round trip is OPEN in general**;
  only ground witnesses are proved (same note).
- **The owner does not yet carry the transit port.** The exact forms are the
  PROPOSAL in the w6/peering-inbound board entry, owned by w5/owner-post; until
  it lands, transit is reachable through `fn-served-open-peer` and not through
  the process an operator starts.
- **The two live nodes are peers on paper only.** Both bind `127.0.0.1`
  because `fn run` refuses any other listener host, so the peer records written
  by the live deployment name addresses neither node can reach.
  `planning/evidence/live-52eb0db-2026-09-20.md`.

## Pessimistic numbers, each with its scope

- The INN lab's certificate row is the honest one to quote: `matched=53
  mismatched=97 absent=10` against `/tank/fn/gates/dev-9321344`
  (`planning/evidence/inn-lab-f4e8272-2026-09-20.md`). More than half the books
  in that run were included without a certificate that hashed to the revision
  under test. Scope: that run, that gate neighbour, on hbox.

## Rules this record follows

- A keystone is cited only where a root that reaches it certified in a farm
  gate whose manifest is named above. A theorem admitted in a lane worktree
  and never gated is listed as open, not as proved.
- A pessimistic number carries its scope in the same sentence, and the scope
  names the host, the load and the shape of the input.
- A passing test is not a proof and a certificate is not an audit. Where the
  two disagree about a claim, the disagreement is written down rather than
  resolved in favour of the greener one.
