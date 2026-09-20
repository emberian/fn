# Handoff: w4/served-path (packets P0 and P1)

Branch `w4/served-path`, worktree `build/lanes/w4-served-path`, from `dev`
`ca66782`. Design: [`specs/node-functionality.md`](../../specs/node-functionality.md)
sections 2.2, 3 and 5, packets P0 and P1;
[`DESIGN-composition-summary.md`](DESIGN-composition-summary.md).

## The gap this closes

`fn-reader-chunk` (`host/reader-host.lisp`) was `:program` mode and consumed at
most one wire event, handing an unconsumed suffix back to a `while pending:`
loop in `tools/run_reader.py:serve_client`. Together they computed
`fn-wire-drive` followed by `fn-nntp-step` per event, and no theorem said so.
That is the wire `pending_subject` note. The loop is now one logic-mode,
guard-`t`-verified function and the host calls it once per socket read.

## What is in the tree

`books/served.lisp` (new Makefile root, after `tests/acl2/nntp-teeth-tests`).
The connection record is (wire framing state, NNTP session, pinned archive),
opaque after its record lemmas. `fn-served-step` is one socket read:
`fn-wire-drive` over the chunk, `fn-served-nntp-run` (a fold of `fn-nntp-step`
over the framed events, accumulating effects in order), and the close effect on
the open-to-closed transition edge only. `fn-served-run` folds reads.
`fn-served-reply-octets` and `fn-served-closingp` are the two projections the
host may take of an effect list; they used to be `fn-reader-effect-octets` and
`fn-reader-close-effectsp` in `:program`-mode host Lisp, which made the host a
second owner of the reply framing. `fn-served-open` owns the greeting.

Keystones, each lifted from a named lemma whose statement is unchanged:

- `fn-served-step-preserves-connp` — from `fn-wire-drive-preserves-statep`
  (`books/wire-invariants.lisp:563`) and
  `fn-nntp-finite-trace-preserves-consistent-session`
  (`books/nntp-invariants.lisp:822`), reached through the bridge
  `fn-served-nntp-run-session-is-nntp-run-session` (superseded: the w4/post composition replaced the run-and-bridge shape by the byte fold, whose preservation theorem is `fn-served-step-preserves-connp` directly and whose partition independence is the hypothesis-free `fn-served-feed-of-append`; the bridge lemma no longer exists on dev).
- `fn-served-step-effects-are-typed`, `fn-served-run-effects-are-typed` — from
  `fn-nntp-step-effects-well-formed` (`books/nntp-effects.lisp:846`).
  `fn-nntp-effectsp` **is** the refusal enumeration: every effect of a served
  read is `(:reply octets)` with `fn-nntp-replyp`, or `(:close)`, and nothing
  else. `fn-served-typed-effect-is-reply-or-close-by-definition` reads that off
  `fn-nntp-effectp`; it is `:rule-classes nil` and is not a registry event.
- `fn-served-step-partition-independence` — from
  `fn-wire-drive-partition-independence` (`books/wire-invariants.lisp:580`)
  plus `fn-served-nntp-run-of-append`. Unconditional in the close effect
  because the effect sits on the transition edge: a read of an already-closed
  wire is a no-op.
- `fn-served-run-is-the-concatenated-step` — a list of reads is one read of the
  concatenation, for every partition. Hypotheses: `fn-served-connp` and
  `fn-served-chunk-listp`.
- `fn-served-reply-stream-is-partition-independent` — the byte-level corollary
  the host needs: two partitions of the same octets give the same reply bytes.
- `fn-served-step-nntp-steps-is-bounded` — the number of dispatcher steps one
  read performs is at most the read's length, from
  `fn-wire-next-strictly-consumes` (`books/wire-invariants.lisp:311`).

`books/ideal.lisp` (new root) is a **skeleton**: the `fn-ideal-*` state record
with the field order of section 1.1, the port dispatcher with `fn-served-step`
as the reader port, and a stub per other port returning the state with a
`(:todo <port>)` effect. `fn-ideal-statep` is the shape plus the served path's
share of the invariant and says in the book which clauses of section 1.1 it is
missing and which book each needs. The five robustness theorems of section 3
are written there as commented statements marked OPEN, none proved.

`tests/acl2/served-tests.lisp` (new root): guard-world audit
(`fn-served-step` is `:common-lisp-compliant` with guard `T`), the reader's own
transcript as a reachable non-degenerate witness, the two required cuts (cut A
inside the GROUP argument; cut B after the 211 is earned and inside the next
command, so the first chunk's reply is a strict non-empty prefix), the
bytewise partition, and the work figure (3 dispatcher steps for 30 octets
against a bound of 30).

Host: `host/reader-host.lisp` keeps one opaque global `fn-reader-conn` and the
pinned snapshot; `fn-reader-chunk` is one call to `fn-served-step`.
`tools/run_reader.py:serve_client` is one `reader.chunk` per `recv`.
`Acl2Reader.chunk` still returns three values so that
`tests/test_reader_partitions.py` and `tests/bench/measure.py` are unchanged;
the third is now always `[]` because a served read consumes the whole chunk.
`tests/test_served_differential.py` is new: the same octets through
`fn-served-run` inside ACL2 and through `serve_client` over a socketpair, with
byte equality asserted for seven partitions.

`docs/prefixes.md` registers `fn-served-`, `fn-ideal-`, `fn-dtn-` and
`fn-sys-` (P0); the last two are marked as having no book yet.

## What is open, recorded not weakened

- **Cost of one `fn-nntp-step`.** The book bounds the number of dispatcher
  steps per read by the read's length and records the missing closed form, with
  the shape of the theorem, at the end of `books/served.lisp`. The worst
  commands are `LISTGROUP` over a range and `LIST ACTIVE` with a wildmat; the
  instrumented twin is packet P3 / M6. No book claims that bound today.
- **No tooth for `fn-wire-octet-listp octets`.** `fn-wire-drive` re-checks
  `fn-wire-statep` every turn and refuses a non-octet by closing the framing,
  so no violating value was found: both probes recorded in
  `tests/acl2/served-tests.lisp` hold rather than fail. The hypothesis cannot
  be deleted, because `fn-wire-drive-preserves-statep` carries it. The
  obligation is either to strengthen that lemma or to produce a separating
  chunk.
- **No tooth here for `fn-served-connp` on the effect-typing theorem.** It is
  inherited from `fn-nntp-step-effects-well-formed`, and the teeth for that
  hypothesis belong in `tests/acl2/nntp-teeth-tests.lisp`, where the keystone
  is. The forged connection does not separate it (an unusable archive still
  answers a well-formed 411 or 503); that is measured in the test book rather
  than asserted.
- **`fn-ideal-*` is a skeleton.** No theorem in the tree may cite a stub
  branch, and `fn-ideal-statep` must not be quoted as "the F_node invariant"
  until the clauses listed in the book exist. Packet P0's real content (the
  relay, store and configuration clauses, the projection theorems of section
  1.3, the every-port witness trace) is not done.

## For the next lane

- **w4/post** owns the POST branch of `fn-nntp-step` and article-mode framing.
  `fn-served-step` needs no change for it: an `(:article ...)` event comes out
  of `fn-wire-drive` and is dispatched like any other. The exact interface
  change is posted as a CHANGE on `planning/deputies/BOARD.md`.
- **P2 (guard closure)** can now name a real subject: `fn-served-step` is
  guard-`t` verified and its closure walk is the next step, together with the
  `ledger.py --check` rule of section 3.1.
- **M7 (connection isolation)** needs `fn-ideal-conn-find`/`-put` to carry ids
  and the w2 owner keystones; the dispatcher already keys connections by id.

## Certification and test evidence

Merged `dev` (convergence fixes) at `b7b8c11`; conflicts were BOARD.md
(unioned) and `planning/ledger.{json,md}` (regenerated). `make certs-install`
installs only 26 of 210 books on this tree, so the closure was certified
**in place, one root at a time**, `FN_ACL2_TIMEOUT_SECONDS=1800`, ACL2 8.7 /
SBCL 2.6.8 on this laptop, `ACL2_BOOK_HASH_ALISTP=NIL`. All thirteen roots
pass, each with an evidence directory under `build/acl2/`:

    books/wire  books/wire-invariants  books/wildmat  books/nntp-syntax
    books/nntp-session  books/nntp-projection  books/nntp-responses
    books/nntp  books/nntp-invariants  books/nntp-effects
    books/served               certify-20260919T221440Z-46133
    books/ideal                certify-20260919T221527Z-48280
    tests/acl2/served-tests    certify-20260919T221528Z-48327

`books/ideal` failed once and was fixed, not worked around: `fn-ideal-make-result`
had a formal named `state`, which ACL2 reserves. The formal is `node` now.

`tests/acl2/served-tests` certifying means every `assert-event` in it passed
under real ACL2: the guard-world audit (`fn-served-step` is
`:common-lisp-compliant` with guard `T`), the transcript witness, both
required cuts, the bytewise partition, the forged-connection teeth, and the
3-dispatcher-steps-for-30-octets work figure.

The Python suites are `unittest`, not pytest:

    python3 -m unittest tests.test_reader tests.test_reader_partitions \
                        tests.test_served_differential -v

**Ran 24 tests in 78.6 s, OK.** `tests/test_reader.py` and
`tests/test_reader_partitions.py` are byte-identical to their pre-lane
versions and pass unchanged, including the every-two-piece-cut matrices. The
seven new differential tests compare the socket's bytes to `fn-served-run`
evaluated inside ACL2 over the same octets and agree on every partition.

## Composed with w4/post (2026-09-19, integration lane)

The "fn-served-step needs no change for POST" prediction above was wrong by
one fact: the wire must be switched into article mode *between* framing the
POST line and framing the byte after it, and `fn-wire-drive` frames the whole
read before the dispatcher sees anything. `books/served.lisp` is therefore a
byte fold now (`fn-served-feed` over `fn-wire-feed-byte`, dispatcher per
framed event, `fn-wire-begin-article` on the `:begin-article` effect). Every
keystone named above keeps its statement; `fn-served-nntp-run` and its bridge
to `fn-nntp-run-session` are gone (the fold is over bytes, not events), and
partition independence is now `fn-served-feed-of-append`, structural, with no
wire lemma. `fn-served-step-effects-are-typed` concludes `fn-served-effectsp`
(adds `:submit`). `fn-served-open` takes the posting configuration and the
clock observation. Details and open items in
[`HANDOFF-w4-post.md`](HANDOFF-w4-post.md).
