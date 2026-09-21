# Handoff: `w11/one-owner`

Lane worktree `build/lanes/w11-one-owner` on `w11/one-owner`, branched from
`dev` `e4fb8bc` and merged with `dev` `3a2640c` mid-lane. Three items from
AGENTS.md's assurance rule *One owner per decision, and it is ACL2*, taken
from the twin sweep in `planning/lanes/HANDOFF-w11-harness-health.md`, which
is on branch `w11/harness-health` (commit `98ca6ca`) and not yet on `dev`;
read it with `git show w11/harness-health:planning/lanes/HANDOFF-w11-harness-health.md`
until it merges.

| item | outcome |
| --- | --- |
| 1. `fn peer add` with defaults is refused | **already fixed on `dev` by `w11/twonode-feed` (`17b68b0`) while this lane was running.** This lane's own mechanism was withdrawn on the merge; what it kept is the regression test at both surfaces |
| 2. the frame integrity trailer has three host copies | **closed.** `books/frame-trailer.lisp`, `fn-frame-trailer`, four keystones, 25 teeth, both books certified, three host copies deleted. A **fourth** copy found and reported |
| 3. the Roughtime Merkle fold | **designed, not implemented**, per the brief's instruction not to half-implement it. A worse defect than the fold was found underneath it and is recorded |

## 1. `fn peer add`: fixed on `dev` before this lane merged, and by a better fix

Reproduced first, on a scratch store at `dev` `e4fb8bc`:

    $ python3 tools/run_store.py --store <tmp> peer add upstream \
        --nntp news.example.invalid:119 --inbound-groups 'fn.*' \
        --source-address 192.0.2.1
    store: refused peer add: peer-record          # exit 1

This lane's first commit (`1a1f739`) fixed it by defaulting the argument to
`None` and resolving it from a new `(fn-store-cfg-peer-constants)` through
`Acl2Store.peer_constants`, which is what the brief asked for. **On merging
`dev` that turned out to be the second fix of the same defect.**
`w11/twonode-feed` `17b68b0` had already made the default `0` and taught
`fn-store-cfg-peer-record` (`host/store-node-host.lisp:203-213`) to supply
`*fn-record-max-payload*` for it.

Theirs is the better fix and it is the one on `dev`: the *default* is a
decision, and under theirs ACL2 owns the default as well as the ceiling,
where under mine Python still chose "the largest the model permits". So the
whole of this lane's mechanism was withdrawn on the merge —
`fn-store-cfg-peer-constants`, `Acl2Store.peer_constants`, the
`DEFAULT_PEER_*` constants, `PEER_INBOUND_MAX_HELP` and the second argument
to `peer_arguments` — and `tools/run_store.py`, `bin/fn` and
`host/store-node-host.lisp` are byte-identical to `dev`. Adding machinery
that does what the tree already does is the twin one layer out.

**What this lane keeps is the test neither fix shipped**, at both surfaces
and typing no number:

- `tests/test_store_config.py::StoreConfigTests::test_peer_add_with_no_size_options_is_accepted`
  — `peer add` with no size options is accepted; the ceiling is then **read
  back out of the record ACL2 admitted** (`peer list`'s `max-octets=`), and
  the same peer at `ceiling + 1` is still exit 1 with `peer-record`, while
  at `ceiling` exactly it is accepted. So the test shows the default works,
  the bound still bites, and it is the bound that bites — and a later change
  to `*fn-record-max-payload*` does not need this file edited.
- `tests/test_fn_cli.py::FnCliTests::test_peer_add_with_no_size_options_is_accepted`
  — the same at the `bin/fn` surface, asserting the `accepted peer add`
  outcome line.

Live evidence after the merge is in §5.

Still open one layer out, and not taken here: `tools/live_service.py:210`
renders `1048576` into a stub peer record it prints for an operator to copy.
`w11/harness-health` has `32768` there on its branch, which is a typed
literal; when that lane merges the durable spelling is `0`, which is now the
word for "the model's ceiling".

## 2. The frame integrity trailer: one owner, `fn-frame-trailer`

`books/crypto-attach.lisp` has attached `fn-sha256` to `fn-frame-digest`
since `w9/digest`, so the model could already compute the trailer and
nothing used it. Three hosts each ran their own SHA-256 over the protected
prefix, and each checked its trailer only against its own.

**The owner.** `books/frame-trailer.lisp`, new, a leaf book:

    (defun fn-frame-trailer (octets)
      (declare (xargs :guard t :verify-guards nil))
      (if (not (fn-cbor-octet-listp octets)) :bad (fn-frame-digest octets)))
    (verify-guards fn-frame-trailer)

`:bad` rather than a digest for an out-of-domain argument, because
`fn-sha256` fixes its argument: without the guard a host bug would come back
as a plausible 32 octets.

**A book and not a `fn-store-` host wrapper**, which is what the brief named.
The owner's ACL2 session loads `host/owner-host.lisp` and never
`host/store-host.lisp`, so a host wrapper would have had to be written
twice. A book is included by both, and it is what lets the function be guard
verified and its keystones proved. `docs/prefixes.md` gains `frame-trailer`
on both `fn-frame-` rows.

**The three host lines, which is the subject question AGENTS.md asks.**

| host | before | after | called from |
| --- | --- | --- | --- |
| `tools/frame_bridge.py` | `hashlib.sha256` at `:153` and `:160` | `FrameSession.trailer` | `seal`, `digest_of` — and through them `store_frame`, `store_unframe`, the journal record codecs, `inbound_frame`, `inbound_unframe` |
| `host/native/io.lisp` | `fnn-sha256` at `:757` and `:762` | `fnn-trailer` | `fnn-seal`, `fnn-digest-of` — and through them `fnn-frame`, `fnn-unframe` |
| `tools/run_owner.py` | `hashlib.sha256` at `:337` and `:348` | `Acl2Owner.trailer` | `feed_frames`, `feed_replay_frame` (the FNFD feed trailer) |

`tools/frame_bridge.py` and `tools/run_owner.py` no longer import `hashlib`
at all. `fnn-sha256` stays for its two host-only callers that are not twins:
a log line's JSON body digest (`io.lisp:862`) and the `sha256` CLI verb
(`io.lisp:1841`).

**The keystones**, all in `books/frame-trailer.lisp`, cited under `PRF-035`
and generated into its `events` array by `tools/ledger.py`:

- `fn-frame-protected-plus-trailer-is-seal` — prefix from ACL2, trailer from
  ACL2, concatenation by the host, and the result **is** `fn-frame-seal`.
  The statement it supersedes,
  `fn-frame-store-encode-is-protected-plus-digest`, holds for a `digest` it
  cannot name, so it left the host trusted for exactly the thing at issue.
- `fn-frame-decode-of-host-framing` — the decode direction, with the trailer
  re-derived over the frame's own `fn-frame-protected-prefix`, answers
  `fn-frame-ok` of what went in. That composition is `digest_of`.
- `fn-frame-store-protected-plus-trailer-is-seal` and
  `fn-frame-store-decode-of-host-framing` — the store instance the bridge
  executes.

**Teeth**, `tests/acl2/frame-trailer-tests.lisp`, 25 `assert-event` checks.
Two FIPS 180-4 vectors; the exact store protected prefix and its trailer;
the `:bad` arm with a non-degenerate neighbour; a witness per keystone; and
one violating value per hypothesis **clause**, because `fn-frame-inputp` is
one named predicate but is stronger than keystone 1 needs. The book says so:
a magic whose third octet is 300 breaks the shape clause keystone 1 needs, a
`max-payload` of 2 breaks the bound clause only keystone 2 needs, and a
non-octet record breaks the store instance.

This test book also closes a tooth `tests/acl2/frame-tests.lisp:286-295`
records as impossible — "`fn-frame-digest` is constrained (A-CRYPTO), so no
ground term evaluates it and no `assert-event` separates the host decoder
from the specification decoder on a concrete input". Under the attachment it
does, and §5 of `planning/evidence/frame-trailer-one-owner-2026-09-21.md`
has the separating pair.

**A fourth copy, found and not taken.** `tools/run_feed.py:179,184,190`
(`FeedBridge.record`, `.decode`, `.apply_frame`) is the same FNFD trailer
again, in the feed's client half. Neither `planning/lanes/HANDOFF-w9-digest.md` nor
`HANDOFF-w11-harness-health.md` names it — the latter names only
`TRAILER_BYTES = 32` in that file, the slice constant, not the digest.
`w11/harness-health` **deletes `tools/run_feed.py` entirely** on its branch
(its `Journal`, `Session` and `TRAILER_BYTES` move to `tools/feed_wire.py`;
`FeedBridge` goes away). Editing it here would be a modify/delete conflict
for a file that is about to stop existing. **Whoever lands
`w11/harness-health` should confirm those three lines left with the file**,
and if any part of `FeedBridge` survives the move, point it at
`fn-frame-trailer`.

**Cost, measured and not hidden.** The trailer is a bridge call now, so the
decimal-octet marshalling is on the frame path. Laptop, warm session, one
sample each: 0.001 s at 32 octets, 0.008 s at 4 KiB, 0.051 s at 32 KiB,
0.497 s at 256 KiB, 1.710 s at 1 MiB. Every store, workflow and receipt
record is under the 65538-octet frame payload cap. The one path that can
reach 4 MiB is `FrameSession.inbound_frame`, a staged BP bundle, and that
seal is now marshalling-dominated. It is the by-reference follow-up
`planning/lanes/HANDOFF-w9-digest.md` already names ("a payload handle the store already
holds"), recorded rather than optimised, per the recorded direction to
retire the Python host.

## 3. The Roughtime Merkle fold: the design, and the worse thing under it

**Answer to the brief's first question: this tree has no SHA-512.**
`books/sha256.lisp` is the only hash in logic; `grep -rn sha512` over
`books/` finds three comments and no code. Roughtime's fold is SHA-512.

**What is actually there.** `fn-anchor-leaf-digest` (`books/anchor.lisp:170`)
is an `encapsulate` whose *witness* is local and returns 64 zeros; the
function itself is exported and constrained to "64 octets" and nothing more.
There is no node digest, no path fold, no `fn-anchor-in-treep`. So
`tools/roughtime.py:124,128,132` is the only thing in the tree that decides
whether a response covers this client's nonce, and the tag order, sibling
order, index bit order, depth bound and `INDX`-fits-`PATH` check are all
unowned.

**And a worse defect underneath it, found while reading for this item.**

1. `fn-anchor-root a` **is** `(fn-anchor-leaf-digest (fn-anchor-nonce a))`
   (`books/anchor.lisp:259`). The model is hard-wired to the one-nonce tree:
   empty `PATH`, `INDX` 0. The nine fields the durable record carries
   (`Anchor.fields`, `tools/roughtime.py:211`) **do not include the root**.
2. The host is not so restricted. `tools/roughtime.py:137` admits a `PATH`
   up to 32 nodes deep, and `anchor_verdict` (`tools/run_store.py:1964`)
   asks ACL2 to rebuild the signed octets from **the root on the wire**,
   not from `fn-anchor-root`.
3. The theorem that makes the host's call the model's function is
   `fn-anchor-node-accept-observed-is-node-accept`
   (`books/anchor-invariants.lisp:261`), whose hypothesis is
   `(equal (and verdict t) (fn-anchor-verifiedp a))`. `fn-anchor-verifiedp`
   (`books/anchor.lisp:426`) is two `fn-anchor-sig-verify` calls **over
   `fn-anchor-signed-octets a`**, which is built from `fn-anchor-root`, plus
   `mint <= midpoint <= maxt`.

So for a **batched** Roughtime response the host computes a verdict about
one message and the theorem's hypothesis is about another, and nothing
anywhere notices: `anchor_verdict` compares ACL2's reconstruction against
the wire SREP and they agree, because it fed ACL2 the wire root. The anchor
keystones simply stop applying to the run, silently. Every captured vector
in `tests/vectors/` is single-nonce, so this has never been observed; it is
a property of the servers, not of fn.

A second half of the same hypothesis is also split: the host's `verdict` is
`anchor_verdict`'s two Ed25519 checks **only**. The `mint <= midpoint <=
maxt` conjunct of `fn-anchor-verifiedp` is discharged by
`tools/roughtime.py:258`, a literal copy of `books/anchor.lisp:435-436`, in
a different function in a different file. That is harness item 3, and it is
load-bearing: it is not a redundant check, it is half the discharge of a
named hypothesis.

Recorded in `specs/anchor.md`'s trust section and in `FLR-004`'s note.

### The design, in the order it should be taken

**Step 0 (cheap, do first, no SHA-512 needed): put the root on the record.**
Add a tenth field `root` to `fn-anchor`, make `fn-anchor-root` the accessor
rather than the derivation, and add
`(equal (fn-anchor-root a) (fn-anchor-leaf-digest (fn-anchor-nonce a)))`
as a conjunct of a new `fn-anchor-one-nonce-p`. Then either require
`fn-anchor-one-nonce-p` in `fn-anchor-verifiedp` — which makes the current
host *refuse* batched responses instead of mis-modelling them, fail-closed
and honest — or leave it out and carry it as a stated hypothesis. Either
way the model stops asserting something about the signed octets that the run
did not compute. This is a records change in one cluster and its
recertification; it needs no new cryptography and it removes the silent
divergence. **Take this before anything else.**

**Step 1: `books/sha512.lisp`.** A mechanical sibling of
`books/sha256.lisp` (508 lines): 64-bit words, 80 rounds, the SHA-512 `K`
and `H0` tables, rotations 28/34/39 and 14/18/41, `ssig` shifts 1/8/7 and
19/61/6, a 128-bit length field and a 1024-octet block. Same shape
throughout — `fn-sha512-w64`, `-pad`, `-words16`, `-schedule`, `-rounds`,
`-compress`, `-blocks`, `-fix-octets`, `-of-octets` — and the same two
exported facts (`fn-sha512-shape`, the coercion identity). FIPS 180-4 has
the vectors; `tests/acl2/sha256-tests.lisp` has the pattern, including the
padding boundaries, which for SHA-512 are 111, 112, 127, 128, 129, 239, 240.
Budget it as its own packet; it is a day's careful transcription and it is
the only part of this that is genuinely new code.

**Step 2: the fold, stated over the digest, attached the way
`books/crypto-attach.lisp` attaches the others.**

    (defun fn-anchor-leaf-preimage (nonce) (cons 0 nonce))
    (defun fn-anchor-node-preimage (l r) (cons 1 (append l r)))
    (defun fn-anchor-merkle-fold (value path index step) ...)   ; bounded by (len path)
    (defun fn-anchor-merkle-root (nonce path index) ...)
    (defun fn-anchor-in-treep (nonce path index root) ...)

`fn-anchor-leaf-digest` becomes
`(fn-anchor-digest (fn-anchor-leaf-preimage nonce))` over one constrained
64-octet `fn-anchor-digest`, and a second book attaches `fn-sha512` to it,
discharging exactly the two shape constraints as `crypto-attach.lisp` does
for `fn-frame-digest` — and saying, as that book does, that collision
resistance is A-CRYPTO and is not a consequence of the attachment. **Do not
state the fold over a constrained digest and stop there.** Without a
realiser the fold cannot run, so `parse_response` would still be the thing
that decides, and the twin would have moved into ACL2 without leaving
Python. The attachment is what makes this a fix.

**Step 3: `fn-anchor-verifiedp` gains
`(fn-anchor-in-treep (fn-anchor-nonce a) (fn-anchor-path a) (fn-anchor-index a) (fn-anchor-root a))`**,
with `path` and `index` two more record fields, and
`tools/roughtime.py`'s `_leaf`, `_node` and `merkle_root` are deleted. The
depth bound (`MAX_PATH_NODES`) and the `INDX`-fits-`PATH` check move into
`fn-anchor-in-treep` as refusals, not as host preflight.

**Step 4: the ordering fix, which blocks step 3.** `parse_response` accepts
or refuses before any bridge call, so the window check and the signature
preimages cannot move until it is restructured to return *unchecked* fields
with `anchor_verdict` as the sole gate — harness item 2. Deleting
`tools/roughtime.py:258` before that lands removes the only check on that
path.

**If the honest answer is "not yet".** Then steps 1–3 do not happen and the
fold is a trusted facility, which is what `specs/anchor.md` now says in
terms: the fold is named, its file and lines are named, what it decides is
named, and the one-nonce divergence is named. That is a record, not an
assumption: an `A-*` in `books/assumptions.lisp` would need a theorem that
takes it as a hypothesis, and there is no such theorem because there is no
fold in the logic to hypothesise about. Writing one would be the "prose
assumption" AGENTS.md forbids.

## 4. The twin table, audited

The sweep's *Real twins with an owner, not taken here* table is **twelve
rows, not eleven**, across the six owners the brief names. Every row is
accurate on `dev` `3a2640c`; four line numbers have drifted. Nothing in it
was fixed here.

| # | sweep says | on `dev` today | owner |
| --- | --- | --- | --- |
| 1 | `run_store.py:51,1829` `max_payload_bytes` 32768 | `:51` and `:1882` | store |
| 2 | `run_store.py:81` `CONFIG_RECORD_BYTES` 65538 | **`:94`** | store |
| 3 | `run_store.py:36,70` 65538 in `MAX_RECOVERY_RECORD_BYTES` | `:36`, `:70` | store |
| 4 | `run_store.py:90` `ANCHOR_RECORD_BYTES = 1024 + 42` | **`:103`** | store / time-anchor |
| 5 | `scheduler.py:41,42` `MAX_TEXT`, `MAX_DECISION_RECORD` | `:41`, `:42` | scheduler |
| 6 | `feed_wire.py:36` `TRAILER_BYTES = 32` | **`run_feed.py:51`** — `feed_wire.py` does not exist on `dev`; the move is `w11/harness-health`'s, unmerged | owner/feed |
| 7 | `run_bp_receive.py:22,23,162,235`, `run_bp_ingress.py:26`, `media.py:54` | all present | bp |
| 8 | `auth_secret.py:37,38,39` 16/32/64 | present | substrate |
| 9 | `crypto_host.py:17,18` 32/64 | present | time-anchor |
| 10 | `roughtime.py:48-51` nonce/root/sig/key octets | present | time-anchor |
| 11 | `roughtime.py:45,46` the two context strings | present; **checked** by `tests/test_anchor.py` | time-anchor |
| 12 | `roughtime.py:66-79` the tag-count/offset header | `:66-78` | time-anchor |

Row 11 is the likeliest source of the "eleven": it is a twin whose
divergence is already a test failure, so it is the one a count might
reasonably have excluded.

## 5. The six that need an ACL2 function that does not exist, by what a wrong value costs

The brief asks for a priority, not a list. Ordered by the **cost of the
value being wrong**, which is not the same as the size of the fix.

1. **The Roughtime Merkle fold** (`roughtime.py:124,128,132`, time-anchor).
   The only one of the six where a wrong value makes the node believe a
   falsehood **about the outside world**: a response that does not cover
   this node's nonce accepted as a freshness anchor, which is the single
   thing the anchor exists to prevent, and which then licenses an
   incarnation advance (`OBJ-006`) and a restore. Its cost is compounded by
   §3's divergence, which is live today and needs no wrong value at all —
   only a server that batches. **Step 0 of §3 is the highest-value hour in
   this whole list and needs no SHA-512.**
2. **The delegation validity window** (`roughtime.py:258`, time-anchor).
   Promoted from the sweep's "only ordering blocks it": it is not a
   redundant check. It is half the discharge of
   `fn-anchor-node-accept-observed-is-node-accept`'s single hypothesis, and
   `anchor_verdict` supplies the other half from a different file. If the
   copy and `books/anchor.lisp:435-436` ever disagree, every anchor keystone
   stops describing the run, silently and with no test failing.
3. **The signature preimages inside `parse_response`**
   (`roughtime.py:237,247`, time-anchor). ACL2 *does* own these octets and
   `anchor_verdict` *does* re-check its reconstruction against the wire, so
   a divergence here faults rather than accepts — fail-safe. It ranks third
   not for its own cost but because it is the **blocking dependency** of (1)
   and (2): neither can land until `parse_response` returns unchecked
   fields with `anchor_verdict` the sole gate.
4. **`checkpoint.py:46` `SELECTION_BOUND = 4096`** (checkpoint). On the
   recovery path, which is where fn's durability claims live, and invented
   host-side: `books/checkpoint-codec.lisp` has `*fn-cpc-tag-octets*` and no
   selection-frame maximum. It is a *bound*, so it fails closed — the cost
   of a wrong value is a store that cannot select a checkpoint it published
   and recovers to old authority, not a bad acceptance. One `defconst` and
   one bridge read would close it; it is the cheapest real fix on this list.
5. **9P2000 framing** (`fn9p.py:134-404`). The largest body of unowned
   protocol code here, 270 lines, but its blast radius is a **read
   projection**: a wrong value corrupts a view, never the durable store.
   The sweep's own disposition is right — an adapter for a foreign protocol
   is honestly a registry entry accepting it as an unowned wire format, not
   a book to write.
6. **The media manifest** (`media.py:54,122,194,266,353`). Lab staging,
   outside the store, outside every durability and freshness claim. A wrong
   value costs a re-stage. Either `books/media.lisp` or, better, a registry
   entry saying media staging is outside the model.

## 6. What ran

Full record: `planning/evidence/frame-trailer-one-owner-2026-09-21.md`.

- `tools/certify_books.py books/frame-trailer tests/acl2/frame-trailer-tests`
  **on the merged tree** — both passed, 1.754 s and 2.508 s, evidence
  `build/acl2/certify-20260921T015922Z-80937`. (Before the merge: 1.137 s
  and 2.818 s in two runs.) 25 `assert-event` checks; the tree's total moved
  5459 → 5484. ACL2 8.7, SBCL 2.6.8, laptop.
- `Acl2Owner(max_conns=4)` comes up in 4.0 s with the new
  `host/owner-host.lisp` include and `Acl2Owner.trailer` equals
  `hashlib.sha256` at 0, 3 and 1024 octets — so the owner session, which
  never loads `host/store-host.lisp`, resolves `fn-frame-trailer`.
- `tests.test_workflow_journal` + `tests.test_receipt_journal` +
  `tests.test_checkpoint` — 38 tests, OK, 487.2 s. These are the suites that
  drive `seal` and `digest_of` through the journal and checkpoint record
  paths.
- The trailer equals `hashlib.sha256` at 32, 4096, 32768, 262144 and
  1048576 octets through the live bridge; a transaction record written by
  the changed code has `sha256(raw[:-32]) == raw[-32:]` on disk; a store
  written by the previous code still opens.
- `make check` and `python3 tools/ledger.py --write` before each commit.

**One operational finding, paid for once.** Right after the merge and
before the recertification, this lane's own `peer add` test failed with
`store: ACL2 bridge call marker did not precede its prompt`, and passed
after `certify_books.py`. `host/store-host.lisp` includes
`books/frame-trailer` now, so **every ACL2-backed CLI invocation loads it**,
and a *stale* certificate is an `include-book` error where *no* certificate
is only a warning; `tools/certs.py install` replaces the pairs it has and
leaves the ones it does not. So a merge that changes anything in that
closure can leave a stale pair that breaks the CLI rather than only a proof.
Not reproduced deliberately, so that is the likely cause and not a measured
one — but recertify (or delete the stale `.cert`) after a merge either way.

**Not exercised.** The native image was not rebuilt or run; `fnn-trailer`
rests on the precedent of `fnn-subject-id`, which has called an
attached-digest ACL2 function through the same `fnn-core` path since
`w9/digest`. That is a precedent, not a run. `feed_frames` and `feed_replay_frame`
were not driven end to end, only the `trailer` call they make: the feed
tests that exist drive `tools/run_feed.py`, which this lane did not change. No
farm run: the only certified files this lane added are a leaf book and its
test book, and no existing book includes either.
