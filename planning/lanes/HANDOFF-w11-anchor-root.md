# Handoff: `w11/anchor-root`

Lane worktree `build/lanes/w11-anchor-root` on `w11/anchor-root`, branched from
`dev` `d763e1c`. Executes §3 step 0 of
[HANDOFF-w11-one-owner](HANDOFF-w11-one-owner.md), and corrects that document's
central factual claim while doing it.

## 0. The correction, first, because it changes the size of the defect

`HANDOFF-w11-one-owner.md` §3, `specs/anchor.md`'s trust section and
`BOARD.md`'s NOTE all say:

> Every captured vector in `tests/vectors/` is single-nonce, so this has never
> been observed; it is a property of the servers, not of fn.

**That is false.** `tests/vectors/roughtime-int08h-2026-09-19-later2.json` has
a `PATH` **one node deep** and `INDX` **1**, and its `ROOT` is not the leaf
digest of its nonce. Measured:

    $ python3 - <<'EOF'
    ... decode_message(response_hex)[b"PATH"] ...
    EOF
    roughtime-int08h-2026-09-19.json         PATH 0 octets  INDX 0  root==leaf True
    roughtime-int08h-2026-09-19-later1.json  PATH 0 octets  INDX 0  root==leaf True
    roughtime-int08h-2026-09-19-later2.json  PATH 64 octets INDX 1  root==leaf False

So int08h batches, and the divergence was **live in fn's own test suite on
every run**: `tests/test_anchor.py::test_restoring_with_a_fresh_anchor_succeeds`
recorded LATER2 as a durable freshness anchor while every anchor keystone
described a different signed message from the one `anchor_verdict` had
verified. It was never a hypothetical about servers fn does not query. It was
one in three of fn's own vectors.

This also changes the *cost* of the fix, which the design could not have
weighed: declining to use what the model cannot describe is not a corner
case, it is a third of the anchors this node obtains. §2 is what that cost bought and what
it forced.

## 1. What changed

**The root is a field.** `fn-anchor` has a tenth field, `root` (64 octets),
and `fn-anchor-root` is the generated accessor, not
`(fn-anchor-leaf-digest (fn-anchor-nonce a))`. So `fn-anchor-srep-octets` and
`fn-anchor-signed-octets` are the octets the host ran Ed25519 over, for a
response of any batch size. Both FNAN kinds gain a tenth `:blob`,
`fn-anchor-host-fields` takes ten, `Anchor.fields()` returns ten.

**An unfoldable tree is `:uncertain`, not `:refused`.**
`fn-anchor-one-nonce-p a` is `(equal (fn-anchor-root a)
(fn-anchor-leaf-digest (fn-anchor-nonce a)))`, and it is a **branch** of
`fn-anchor-node-accept`, `fn-anchor-node-advance` and `fn-anchor-restore`,
answering `:uncertain :unmodelled-tree`.

The design said "a conjunct of `fn-anchor-verifiedp`, so a batched response is
REFUSED". Taking it literally would have made fn say `refused: unverified` —
a false statement about a response whose two signatures verify — and it would
have put a third of int08h's answers under a word that means "this server is
lying". `specs/anchor.md`'s own rule settles it: "a refusal would claim
knowledge it does not have". fn does not know a batched response is bad; it
knows it cannot state the binding. That is the same condition as an
unreachable server, and it gets the same outcome and the same exit code 3.
`fn-anchor-verifiedp` therefore means exactly what it meant on `dev` —
signatures and window — and the new condition sits beside it.

**One hypothesis per A-CRYPTO seam, and the window is ACL2's.** The host now
supplies two values, not one:

| argument | is | seam |
| --- | --- | --- |
| `verdict` | `fn-anchor-signatures-okp` | `fn-anchor-sig-verify` (Ed25519) |
| `one-nonce` | `fn-anchor-one-nonce-p` | `fn-anchor-leaf-digest` (SHA-512) |

and `fn-anchor-verifiedp-observed` applies `fn-anchor-window-okp` **inside**
the entry the host calls. `tools/roughtime.py`'s `mint <= midpoint <= maxt`
was, as `HANDOFF-w11-one-owner.md` §5 item 2 says, half the discharge of the
host-entry hypothesis with `anchor_verdict` supplying the other half from a
different file. It is now a preflight whose value nothing in the logic depends
on. That item is closed without touching `parse_response`'s ordering, so the
blocking dependency §3 step 4 names did not have to be paid.

## 2. Every theorem that mentions the root, `fn-anchor-verifiedp` or the signed octets

Enumerated before editing; verdict for each. "Covered scope" is the change
that matters, not the text.

| theorem | book | verdict |
| --- | --- | --- |
| `fn-anchor-signed-octets-determine-the-root` | anchor | **KEYSTONE, strictly stronger.** Text unchanged; `fn-anchor-root` is now the field, so it covers a response of any batch size instead of the empty-`PATH` case only. Proof is simpler (append cancellation over the field, no digest length needed) |
| `fn-anchor-one-nonce-signed-octets-determine-the-leaf-digest` | anchor | **new, and a COROLLARY, not a registry event.** The sentence the keystone used to state unconditionally, now carrying `fn-anchor-one-nonce-p` as the hypothesis that was always doing the work |
| `fn-anchor-srep-octets-are-octets` | anchor | **hypothesis added**, `(fn-anchor-p a)`. Not a weakening of a live claim: the root's width is now the record's to state rather than the total constrained digest's, which is exactly why `fn-anchor-dele-octets-are-octets` already carried that hypothesis. Both callers are guarded by `fn-anchor-p` |
| `fn-anchor-srep-octets-length` | anchor | same, `:rule-classes nil` |
| `fn-anchor-signed-octets-are-octets` | anchor | same |
| `fn-anchor-srep-octets-guard` | anchor | statement unchanged; the root conjunct now comes from the record shape instead of `fn-anchor-leaf-digest-length` |
| `fn-anchor-root-of-fn-anchor` | anchor | **new**, generated: the tenth accessor-of-constructor |
| `fn-anchor-of-accessors`, `fn-anchor-injective`, `fn-anchor-shapep-of-fn-anchor`, the three forward facts | anchor | regenerated over ten fields |
| `fn-anchor-verifiedp-observed-is-verifiedp` | invariants | **new KEYSTONE.** The Ed25519 half of the host hypothesis, discharged once for all three entries |
| `fn-anchor-node-accept-observed-is-node-accept` | invariants | **hypothesis split and made dischargeable.** Was one hypothesis, `(equal (and verdict t) (fn-anchor-verifiedp a))`, which no host could discharge: `anchor_verdict` computed neither the window nor the tree shape. Now two, one per seam, and `tools/run_store.py` computes exactly those two |
| `fn-anchor-node-advance-observed-is-node-advance` | invariants | same |
| `fn-anchor-restore-observed-is-restore` | invariants | same |
| `fn-anchor-unverified-is-refused` | invariants | **unchanged**, and deliberately: `fn-anchor-verifiedp` means what it meant on `dev`. Reachable — a bad signature or a bad window — and witnessed |
| `fn-anchor-accepted-anchor-is-strictly-newer` | invariants | **KEYSTONE, unchanged.** The `:accepted` set is smaller (no batched anchors) but not empty; the reachable non-degenerate witness is `*anchor-node-held*` accepting `*anchor-live*` |
| `fn-anchor-accept-list-latest-never-goes-back` | invariants | KEYSTONE, unchanged |
| `fn-anchor-incarnation-advances-only-under-a-newer-anchor` | invariants | KEYSTONE, unchanged |
| `fn-anchor-restore-refuses-image-it-cannot-outdate` | invariants | **KEYSTONE, text unchanged, second conjunct narrower.** Its first conjunct (never `:accepted`) is unchanged. Its `:possibly-stale` half is under `fn-anchor-acceptablep`, which gained `fn-anchor-one-nonce-p`, so a batched presented anchor now yields `:uncertain :unmodelled-tree` and no staleness verdict at all. That is correct: fn cannot say a batched response fails to outdate the image, because it cannot say what the response covers. Both branches are reachable and witnessed |
| `fn-anchor-accepted-restore-outdates-the-image` | invariants | **strictly stronger**: `fn-anchor-acceptablep` is in the conclusion |
| `fn-anchor-accepted-restore-opens-a-new-incarnation` | invariants | unchanged |
| `fn-anchor-restore-without-an-anchor-is-uncertain` | invariants | unchanged |
| `fn-anchor-absent-anchor-is-uncertain` | invariants | unchanged |
| `fn-anchor-fork-admits-neither-image` | invariants | **KEYSTONE, unchanged text, strictly stronger discrimination.** `fn-anchor-image-referenced` equality is over ten-field records, so two images whose anchors differ only in their root are now a fork rather than `:same` |
| `fn-anchor-admitted-pair-agrees-on-its-anchor` | invariants | same, complement |
| `fn-anchor-accepted-anchor-covers-one-nonce` | invariants | **new, definitional, NOT a registry event.** Unfolds `fn-anchor-node-accept`. Present because it is the contract in one line at the decision that writes durable state |
| `fn-anchor-accepted-restore-anchor-covers-one-nonce` | invariants | same, for restore |
| `fn-anchor-unmodelled-tree-is-uncertain` | invariants | **new, definitional.** D13 at the new branch: neither refused nor accepted |
| `fn-anchor-restore-under-an-unmodelled-tree-is-uncertain` | invariants | same, for restore |
| `fn-anchor-node-accept-preserves-nodep`, `-outcomep`, `fn-anchor-node-advance-preserves-nodep`, `fn-anchor-restore-outcomep`, `fn-anchor-accepted-node-holds-the-anchor`, `fn-anchor-unaccepted-leaves-the-node-alone`, `fn-anchor-advance-increments-by-one` | invariants | unchanged; the new branch preserves each |
| `fn-anchor-decode-of-encode` | anchor-record | **KEYSTONE, unchanged text, covers the tenth field** |
| `fn-anchor-record-anchor-is-an-anchor`, `fn-anchor-spec-for-is-spec-list`, the two frame guard lemmas | anchor-record | unchanged |

**No theorem survives only because the new branch made its case unreachable.**
The two candidates were `fn-anchor-unverified-is-refused` (still reached by a
bad signature: `*anchor-out-of-window*` and the `nil` verdict witnesses) and
the `:possibly-stale` half of the restore keystone (still reached by
`*anchor-older*` against `*anchor-image-old*`). Nothing is marked
`unreachable-in-composition`, because nothing needed to be.

## 3. Is a batched response refused?

It is **not accepted**, which is the question that mattered, and it is
reported `:uncertain :unmodelled-tree` rather than `:refused`, for the reason
in §1. At the CLI:

    $ python3 tools/run_store.py --store <s> anchor \
        --anchor-vector tests/vectors/roughtime-int08h-2026-09-19-later2.json
    anchor uncertain: unmodelled-tree                     # exit 3
    $ python3 tools/run_store.py --store <s> recover \
        --anchor-vector tests/vectors/roughtime-int08h-2026-09-19-later2.json
    ... anchor=uncertain [unmodelled-tree] ...            # exit 3

Both are asserted in `tests/test_anchor.py::StoreAnchorCommands::test_a_batched_anchor_is_uncertain_at_both_commands`,
against the real capture. **This is a behaviour regression against a real
server, taken deliberately**: fn can no longer use roughly one in three of
int08h's answers, and the operator retries. D22 records the trade.

## 4. What the keystones cover, before and after

| | before | after |
| --- | --- | --- |
| `fn-anchor-signed-octets` | `(radius, midpoint, leafdigest(nonce))` — the message of a one-nonce response, and of no other | the message the host verified, for any response |
| `fn-anchor-signed-octets-determine-the-root` | empty-`PATH` responses | every response |
| the three host-entry equalities | hypothesis `(equal (and verdict t) (fn-anchor-verifiedp a))`, which the host did not compute: `anchor_verdict` was two Ed25519 checks, the window came from `roughtime.py:258`, and for a batched response the two sides were about different messages | two hypotheses, one per seam, both computed by `anchor_verdict` and `Anchor.one_nonce` in one file; the window is inside the entry |
| the acceptance and restore keystones | applied to whatever the host recorded, silently including batched responses they did not describe | applied to exactly what the node accepts, and the node accepts only what they describe |

## 5. SHA-512: not reached, and what stays trusted

Not reached, deliberately: the brief's third step was conditional on budget
and the previous lane's judgement — do not state the fold over a constrained
digest without attaching a realiser — is endorsed and unchanged. There is
still **no SHA-512 in the tree**.

What stays trusted, recorded with file and line in the tree's trust boundary
(`docs/architecture.md` § Trust boundary) and in `specs/anchor.md`'s trust
section, per AGENTS.md's rule on trusted facilities:

- **`tools/roughtime.py:124` (`_leaf`)**, SHA-512 of `0x00 || nonce`. "The
  host's `_leaf` is `fn-anchor-leaf-digest`" is a named correspondence, not a
  proved one, exactly as "the host's Ed25519 is `fn-anchor-sig-verify`" is. It
  is the reading under which `Anchor.one_nonce` discharges
  `fn-anchor-one-nonce-p`.
- **`tools/roughtime.py:128,132` (`_node`, `merkle_root`)**, the fold: sibling
  order, index bit order, depth bound, `INDX`-fits-`PATH`. Still unowned — but
  **no longer load-bearing for anything fn accepts**. A response that needs
  them is uncertain, so `merkle_root` is load-bearing only where it returns
  `_leaf(nonce)` and folds nothing. The trusted surface went from a tree walk
  of arbitrary depth to one hash of 33 octets.

No `A-*` assumption was invented. There is still no theorem that could take
one as a hypothesis, which is why the previous lane declined and why this one
does too.

## 6. A defect on `dev`, fixed in passing

`planning/decisions.md` on `dev` `d763e1c` **contains committed merge conflict
markers**: `<<<<<<< HEAD` at line 382, `=======` at 478, `>>>>>>> dev` at 685
(the last line of the file). The HEAD side is D14-c; the dev side is D19, D20
and D10-a. Every decision after D14-b was inside a conflict hunk, so
`tools/next_id.py` and every reader saw a broken file. Resolved here by
keeping both sides — the HEAD side's sentence "**Taken 2026-09-20 as D14-c
below**" plus D14-c, then D19, D20, D10-a — and dropping the dev side's
duplicated fragment "one.". A repository-wide sweep for `^<<<<<<< ` and
`^>>>>>>> ` finds nothing else.

## 7. The operational trap: the hazard is real, its predicted cause is not

The brief predicted: `host/store-host.lisp` now includes
`books/frame-trailer`, so every ACL2-backed CLI invocation loads it; a stale
`.cert` is an `include-book` ERROR where an absent one is only a warning; and
`tools/certs.py install` leaves pairs it has no cache entry for, so `peer add`
or any CLI call may fail with "ACL2 bridge call marker did not precede its
prompt".

**Refuted as stated, for the `certs.py` half.** `tools/certs.py` is content
addressed: `content_hash` is SHA-256 of the file, and a cached pair is used
only when the book, the certificate and *every book in the closure the key is
computed from* still hash to what the recording run produced
(`tools/certs.py:14-18`). A cache keyed on content cannot hand you a stale
certificate for that content. What it can do is leave one **absent**, which
it reports as `uncached:` — and absent is a warning, not an error. Measured
here: the install reported `install: 279 books`, named the whole anchor
cluster among its `uncached:` lines, and **did** have a cache entry for
`books/frame-trailer`, which it installed. The first `Acl2Store()` of this
lane, in `tests/test_anchor.py`, then loaded `host/store-host.lisp` and ran
23 tests. No bridge marker failure, at any point in the lane.

**Confirmed in its mechanism, with a different cause.** A stale `.cert` *is*
an `include-book` error, and the way a lane gets one is not `certs.py` — it
is editing a `.lisp` after certifying it in the worktree, which is the
ordinary lane loop. This lane produced that state twice, and
`tools/certify_books.py` caught both: it records `source_digests_sha256` at
the start and `source_digests_sha256_after` at the end and reports "ACL2 did
not produce complete clean certification evidence" when they differ, even
though every book passed. Runs `certify-20260921T023518Z-48220` and
`certify-20260921T024149Z-57352` are that, with `book_results` all `passed`
and `book_failures` empty; `certify-20260921T025008Z-65381` is the clean one.
**So the rule to put in a lane prompt is not "recertify because `certs.py`
lies" — it is "certify last, and treat a `source_digests` mismatch as the
runner telling you your `.cert` files are now stale."**

## 8. Cost, measured, and the one form worth profiling

`books/anchor-invariants` got **slower**, and the number is the extra branch.
Same laptop (macOS arm64, ACL2 8.7 / SBCL 2.6.8), `tools/certify_books.py`,
one sample each:

| tree state | book wall | `fn-anchor-accept-list-latest-never-goes-back` |
| --- | --- | --- |
| root on the record, one-nonce as a conjunct of `fn-anchor-verifiedp`, no new branch (`certify-20260921T022345Z-30908`) | 168.3 s | 94.3 s |
| the shipped shape, `:uncertain :unmodelled-tree` as its own branch (`certify-20260921T025008Z-65381`) | 367.4 s | 175.9 s |

The whole cluster is 382 s and every book passes, so nothing is blocked; but
one extra branch in three transitions doubled the list induction, which is
half the cluster's wall time on its own. Prior committed manifests put this
book at 98 to 212 s, all of them on the Linux boxes, so they are not a
baseline for these two.

**Not profiled, and that is the honest gap.** `tools/proof_profile.py`
requires `--host hbox` or `--host persvati` and a mirrored remote root, which
this lane did not have; no hint was added blind in its place, and no proof
was restructured. The next lane in this cluster should run

    python3 tools/proof_profile.py books/anchor-invariants \
        fn-anchor-accept-list-latest-never-goes-back --host hbox

before touching it. The likely cure, stated so it can be refuted: the
induction opens `fn-anchor-node-accept` at every step and so re-derives six
branches, when all it needs are two lemmas already proved above it —
`fn-anchor-accepted-anchor-is-strictly-newer` and
`fn-anchor-unaccepted-leaves-the-node-alone` — plus
`fn-anchor-node-accept-preserves-nodep` and transitivity. That is a proof
restructuring, not a hint, which is why it was not attempted at the end of a
lane.

## 9. Registry

- **D22** (`planning/decisions.md`), claimed on the board: the root on the
  record, the uncertain outcome, the seam split, and the three rejected
  alternatives. **It was claimed as D21 and renumbered on the merge**:
  `w11/node-index` took D21 for the served statement index and reached `dev`
  first. `tools/next_id.py` was run and the board CLAIM was posted, and the
  collision happened anyway, because both claims were written before either
  branch merged. That is the fifth and sixth lane on one number this wave;
  the CLAIM line catches it at merge, not at allocation.
- **FLR-004**'s note (`planning/requirements.json`) rewritten: the paragraph
  describing this defect as open is replaced by what closed it and what did
  not.
- **No new proof target.** The anchor cluster still has **no curated events in
  `planning/proof-events.json`**, so none of its keystones appear in
  `proofs.json`, and `PRF-017` is still `planned` with an empty `events`
  array. That was true before this lane and is the single largest remaining
  gap in this cluster; see §10.

## 10. The next global step

**Curate the anchor cluster's events into `PRF-017`.** Six keystones now
certify and none of them is cited anywhere a reader of `proofs.json` would
look: `fn-anchor-accepted-anchor-is-strictly-newer`,
`fn-anchor-accept-list-latest-never-goes-back`,
`fn-anchor-incarnation-advances-only-under-a-newer-anchor`,
`fn-anchor-restore-refuses-image-it-cannot-outdate`,
`fn-anchor-fork-admits-neither-image`,
`fn-anchor-verifiedp-observed-is-verifiedp`, plus
`fn-anchor-signed-octets-determine-the-root` and `fn-anchor-decode-of-encode`.
`PRF-017`'s statement is "different events cannot silently share an
origin/incarnation/sequence identity"; the incarnation-advance half is now
evidenced and the counter-allocation half is not, so the honest move is
`in-progress` with a note naming the half that is open — not `certified`. That
is one lane's careful hour and it is the difference between "the tree has this
evidence" and "a reader can find it".

Then, in order: `books/sha512.lisp`, which does not exist yet (§3 steps 1 to
3 of `HANDOFF-w11-one-owner.md`) and is now a **feature** — it is what lets
fn use a batched Roughtime response at all — and then `parse_response`'s
ordering, which the window fix here no longer blocks on.
