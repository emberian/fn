# Fiber substrate-transport: v0.4, TCPCLv4 and the statement carrier

What this strand of v0 has proved, what it has only tested, the pessimistic
numbers with the scope they cover, and what is open. Every number here is
cited to the file it came from; nothing is retyped from memory. Written by
the w9/release lane against `dev` at `52eb0db`.


## What is proved

- **`books/stx-carrier` is certified** on persvati, run `run-20260920T052853Z-b82b`
  (`build/acl2/certify-20260920T052855Z-*/books--stx-carrier.certify.log`, zero
  failures). It holds the detached encoding, the base64 layer, the field value
  and the payload-by-kind projection (`planning/deputies/BOARD.md`,
  w7/substrate-s1 final note).
- **TCPCLv4 session records, octets and the session machine** are in
  `books/tcpcl-records`, `books/tcpcl-octets`, `books/tcpcl-session`,
  `books/tcpcl-invariants` with `tests/acl2/tcpcl-tests`; the farm run
  `run-20260920T051453Z-c9a2` certified all three tcpcl books inside a 60-of-63
  closure (`planning/deputies/BOARD.md`, w8/tcpcl-native).
- **No protocol value in the native TCPCL host is computed by Lisp.**
  `host/tcpcl-host.lisp` is sixteen wrappers over `books/tcpcl-session`, each
  returning a flat `(session events unconsumed)` triple; `host/native/tcpcl.lisp`
  opens no socket of its own (same note). This is the one-owner rule holding.

## What is tested and not proved

- Nothing. `planning/evidence/tcpcl-9cbf301-2026-09-20.md` says so as its
  headline: **the native image did not build and none of the five lab
  scenarios ran**, because `books/served`, `books/nntp-post` and
  `books/nntp-effects` each exceeded the runner's 1800 s cap with five other
  lanes on the box.

## Open, with the evidence that says so

- **`books/stx-verify` is open at one form**, `fn-stx-decimal-octets-are-printable`
  (`books--stx-verify.certify.log:1754`); `books/stx-invariants` and
  `tests/acl2/stx-tests` cascade off it, and `tests/test_stx.py` has not run for
  want of the `stx-invariants` certificate.
- **Two theorems were removed and recorded open, never weakened**:
  `fn-stx-authored-source-is-octet-list` and `fn-stx-payload-for-is-octet-list`
  do not follow from `fn-article-syntax-p`, because the projection walks
  `fn-article-field-raw-lines` and `books/article.lisp` constrains those to
  `true-listp` only.
- **PRF-019 and PRF-020 have their events generated but are not `certified`.**
  PRF-020's subject rule is unmet: `fn-stx-transit-verdict-is-fn-stx-verdict`
  names `fn-peer-transfer` and needs K1's transit path.
- **SUB-001 to SUB-006 stay `specified`.** Their notes say "no book exists at
  this revision"; `books/stx-carrier` and `books/stx-verify` now exist, so the
  notes are stale for SUB-001 and SUB-002 in that one respect and the status
  still cannot move while `stx-verify` is open.
- **Two one-line hooks are owed by other clusters**: the HDR
  `:FN-VERIFIED` token at `books/nntp-responses.lisp:1322`/`:1341`, and the
  `FN-Statement` line in `fn-inj-prefix` (`books/injection.lisp`). Neither book
  was edited by the substrate lane.
- **The served TCPCL path revalidates the whole session per chunk (D3).**
  `fn-tcl-drive`'s guard is `fn-tcl-sessionp`, and `fn-tcl-inboundp` inside it
  runs `fn-tcl-octet-listsp` and `fn-tcl-lists-len` over every octet staged so
  far. This is the assurance rule "no whole-state revalidation on a served
  path" being broken, recorded in `planning/deputies/BOARD.md`, w8/tcpcl-native.
- **A certificate set is not relocatable and must never be mixed across
  directories.** Scavenging 217 certificates from every gate whose book *text*
  matched made ACL2 include each book from the directory its own certificate
  named, and the build refused. Same note; this is why the image needs its own
  `--closure` run.

## Pessimistic numbers, each with its scope

- **`fn-tcl-complete` emits XFER_ACK before the `:bundle-received` whose data
  the ack promises.** Acting on the event list in order would put an
  acknowledgement on the wire ahead of durability, so `fnn-tcl-act` buffers
  every outbound octet for the length of one event list and releases it after
  the barrier. A barrier that does not complete is uncertain: the buffer is
  dropped, the ack is never written, exit 3. Scope: the native host only; a
  second host will need the same rule (`planning/deputies/BOARD.md`,
  w8/tcpcl-native).

## Rules this record follows

- A keystone is cited only where a root that reaches it certified in a farm
  gate whose manifest is named above. A theorem admitted in a lane worktree
  and never gated is listed as open, not as proved.
- A pessimistic number carries its scope in the same sentence, and the scope
  names the host, the load and the shape of the input.
- A passing test is not a proof and a certificate is not an audit. Where the
  two disagree about a claim, the disagreement is written down rather than
  resolved in favour of the greener one.
