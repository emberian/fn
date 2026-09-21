# Handoff: w11/tcpcl-theory — the served-path guard, landed with the theory that survives it

Branch `w11/tcpcl-theory`, worktree `build/lanes/w11-tcpcl-theory`, from `dev`
at `19f3302`. Boxes: hbox `/tank/fn/lanes/w11-tcpcl-theory`, ACL2
`/tank/fn/acl2-8.7/saved_acl2`, cache `/tank/fn/certcache`, everything under
`swarm-build`; persvati `/home/ember/fn-lanes/w11-tcpcl-theory`, ACL2
`$HOME/fn-tools/acl2-8.7/saved_acl2`, cache `~/fn-certcache`. Both measured
before use (`uptime`, `free -g`): hbox load 2.22 with 21 G available,
persvati load 2.89 with 63 G. Every ACL2 run below is on hbox with **no
prover step limit** and a wall-clock cap of `FN_ACL2_TIMEOUT_SECONDS=1800`;
§9.2 is why there is no step limit anywhere in this record.

This is the packet [HANDOFF-w9-dtn-e2e](HANDOFF-w9-dtn-e2e.md) §7 specified:
the O(n²/chunk) served-path guard fix and the `books/tcpcl-invariants` theory
work, in that order, certified together before either merged.

## 1. The result in one table

Per root, `certify-book`'s own `Time:` line, hbox, `--jobs 4`:

| root | dev `19f3302` | +theory (`164f964`) | +guard (`9784cdc`) |
| --- | --- | --- | --- |
| `books/tcpcl-session` | 25.259 s | 25.59 s | **62.76 s** |
| `books/tcpcl-invariants` | **609.687 s** | **6.61 s** | **7.25 s** |
| `tests/acl2/tcpcl-tests` | 0.312 s | 0.46 s | **0.46 s** |

Evidence: dev is w9/dtn-e2e's `certify-20260920T230902Z-1283742`
(`/tank/fn/lanes/w9-dtn-e2e-fix`), and it is a baseline for *exactly* these
bytes — its manifest's `source_digests_sha256` for all eight books in the
closure equal this worktree's at `19f3302`, so it was not re-run. +theory is
`certify-20260920T233326Z-1303168`; +guard is
`certify-20260921T000317Z-1324995`, the branch head with dev merged in. The
same packet was certified three times before it as it grew — 65.30 / 7.40 /
0.48 s at `certify-20260920T233937Z-1307933` (before §5's teeth), 64.27 /
7.31 / 0.47 s at `certify-20260920T234831Z-1314032` (with them), 64.33 /
7.35 / 0.47 s at `certify-20260920T235524Z-1317872` (`540dd78`) — and the
four differ by under two seconds on the session book and under a tenth on
the other two, which is the noise on this box. All in
`/tank/fn/lanes/w11-tcpcl-theory`, all `ACL2 certification passed`, zero
`ACL2 Error` in every log, 70.849 s wall for the three roots at `--jobs 4`.

The 39.7 s `books/tcpcl-session` gains is the cheap recognizer family proving
itself once, at certification, against a walk of the staged prefix removed
from every socket chunk of every transfer.

## 2. Where the invariants book's 609 s actually was

Not where the previous lane's profile pointed, because that profile was taken
on the *cheap-guard* configuration, where C1 was 2386 s of forward chaining.
On dev the per-form breakdown of the baseline log says it plainly: **five
forms below `(local (in-theory (enable fn-tcl-sessionp)))` are 585.52 s of
609.53 s**, and `fn-tcl-drive-is-a-result`, above that line, is another
10.60 s from the open transitions. (The first commit's message rounds these
together as "596.12 s across six forms"; this is the exact split.)

| form | dev | after |
| --- | --- | --- |
| `fn-tcl-live-inbound-ends-in-exactly-one-outcome` | 230.01 s | 1.62 s |
| `fn-tcl-step-emits-at-most-one-inbound-outcome` | 160.97 s | 1.09 s |
| `fn-tcl-tick-fails-a-live-inbound-only-when-closing` | 134.12 s | 0.21 s |
| `fn-tcl-input-error-never-completes-a-transfer` | 44.42 s | 0.03 s |
| `fn-tcl-tcp-close-never-completes-a-transfer` | 16.00 s | 0.01 s |
| `fn-tcl-drive-is-a-result` | 10.60 s | 0.08 s |
| `fn-tcl-drive-partition-independence` (C1) | 0.42 s | 0.05 s |
| whole book, 58 forms | 609.53 s | 6.54 s |

Every one of those `Time:` lines has `prove` ≈ total and `other` ≈ 0, so by
§9.1 this was the rewriter, and the cure was still a theory change: the
recognizer was **open** for the first five, each of which carried its eleven
sub-recognizers into its clause — the same fan `books/deftransition.lisp`
exists for and that C2 measured as 1082 subgoals. (The last two rows are the
transitions, not the recognizer: they sit above that line and pay for
`fn-tcl-step` being open.) What the five need about a field arrives by
forward chaining instead;
`fn-tcl-retained-transfer-is-bounded-by-definition` now closes on
`FN-TCL-SESSIONP-FORWARD-INBOUND` and `FN-TCL-INBOUNDP-FORWARD-FIELDS` in 233
prover steps.

## 3. A third diagnostic, worth the same as the other two

**A subgoal `:in-theory` hint is evaluated against the book's CURRENT theory,
not against its parent goal's.** So

```lisp
:hints (("Goal"        :in-theory (e/d (fn-tcl-drive) (fn-tcl-step ...)))
        ("Subgoal *1/3" :in-theory (enable fn-tcl-drive-is-a-result)))
```

does not mean "the Goal's theory plus that rule"; it means "the book's
ambient theory plus that rule", and C1's Goal hint — the one that closes
`fn-tcl-step` for the fold — was silently undone under every subgoal it named.
This is documented, not inferred: ACL2 8.7's `:doc hints` says under
`:in-theory` that "an `:in-theory` hint will always be evaluated relative to
the current ACL2 logical world, not relative to the theory of a previous
goal", and its example is structurally C1's --
`(("Goal" :in-theory (disable f)) ("Subgoal 3" :in-theory (enable g)))` --
with the note that "the `disable` of `f` on behalf of the hint at Goal will
be lost at Subgoal 3" (`/tank/fn/acl2-8.7/doc.lisp:54271`). It is also
measured here: with nothing else changed, closing the four transitions at the
top of the book took C1 from 0.42 s to 0.05 s, and it is why w9's profile saw
`FN-TCL-STEP` at 481,747 frames inside a theorem whose Goal hint disables
`fn-tcl-step`. The general rule: **a Goal-level `e/d` only holds under a
subgoal that names no `:in-theory` of its own; to hold everywhere, close it in
the book.** It is written down as `docs/proof-style.md` §9.3, beside w9's §9.1
and §9.2.

`grep -rn '("Subgoal[^"]*"[^)]*:in-theory' books/ tests/acl2/ host/` finds two
other sites in the tree, both unmeasured and both certifying today:
`books/peer-inbound.lisp:1125`, whose `("Subgoal *1/1" :in-theory (enable
fn-peer-session-consistentp fn-peer-sessionp ...))` gets back the `Goal`
hint's `(:d fn-node-statep)`, `(:d fn-cfgp)` and
`fn-peer-command-preserves-consistent-session`; and
`books/article-public-bound.lisp:99`, whose two sibling subgoal hints spell
the whole `e/d` and whose `*1/1` does not. Cost, not correctness; one `Time:`
line each settles it.

## 4. Every configuration tried, with what it cost

No step limit anywhere; the cap is wall clock.

| # | Configuration | Cap | Result |
| --- | --- | --- | --- |
| baseline | dev `19f3302`, unmodified | 3600 s | 609.53 s, green (w9's run, digest-matched to this tree) |
| T1 | the four transitions closed book-wide and opened at the eight forms that need them; `(local (in-theory (enable fn-tcl-sessionp)))` above C3 removed | 900 s `ld` probe | **6.54 s, 58 of 58 forms, zero errors** |
| T1 | the same, as a real `certify-book` over three roots | 1800 s | **green**: 25.59 / 6.61 / 0.46 s |
| T2 | T1 + the guard change of `a913425^` restored verbatim, `fn-tcl-session-cheapp` and `fn-tcl-cheap-rules` closed in the invariants book | 900 s `ld` probe | C1 fails at `Subgoal *1/2'4'`, **which is `fn-tcl-drive-is-a-result`**; the other 58 forms all close, 7.25 s |
| T3 | T2 + `("Subgoal *1/2" … :in-theory (enable fn-tcl-drive-is-a-result))` | 900 s `ld` probe | C1 fails at `Subgoal *1/4''`, same rule, one case further on |
| T4 | T3 + the same hint at `Subgoal *1/4` | 900 s `ld` probe | **7.27 s, 59 of 59 forms, zero errors, no unused hints** |
| T4 | the same, as a real `certify-book` over three roots | 1800 s | **green**: 65.30 / 7.40 / 0.48 s |
| T4+teeth | T4 + the separating witnesses of §5 | 1800 s | **green**: 64.27 / 7.31 / 0.47 s (`certify-20260920T234831Z-1314032`) |
| head | the branch head `540dd78` | 1800 s | **green**: 64.33 / 7.35 / 0.47 s (`certify-20260920T235524Z-1317872`) |
| merged | the branch head with dev `2e99538` merged in | 1800 s | **green**: 62.76 / 7.25 / 0.46 s (`certify-20260921T000317Z-1324995`) |

The T2/T3 failure is the packet in miniature and is recorded rather than
patched over: while `fn-tcl-drive`'s totality test was the literal
`(fn-tcl-sessionp s)` of C1's own hypothesis, the need case was decided by
assumption at no cost; with the test naming `fn-tcl-session-cheapp` the two
sides of the equality no longer open to the same term, and the leftover goal
is exactly the shape lemma its three sibling subgoals already cite.

None of the previous lane's configurations were repeated.

## 5. The teeth the cheap recognizer needed

`fn-tcl-sessionp-is-cheap` is the load-bearing new theorem, and nothing in
the tree showed it was not an identity — if the two recognizers were the
same predicate, the guard would still be walking the staged octets and the
bridge would be `X ⊆ X`. `tests/acl2/tcpcl-tests.lisp` now carries one
separating witness per dropped conjunct, each the live-transfer session of
`*t-b-mid*` with its inbound record rebuilt through `fn-tcl-next`:
`*t-b-nonoctet*` stages `'((300))` with the carried sum still agreeing, so
only `fn-tcl-octet-listsp` separates them; `*t-b-wrong-sum*` stages
`'((1 2 3))` with a carried sum of 0, so only the length equation does. Both
satisfy `fn-tcl-session-cheapp` and neither satisfies `fn-tcl-sessionp`, and
each assertion is accompanied by the check that the *other* conjunct still
holds, so the separation is by more than the weakest clause. Four further
assertions anchor the guard on sessions the golden exchange actually reaches.
The test book had never run under this change at all: it sat unattempted
behind the invariants failure through all three of the previous lane's
configurations.

## 6. What did not change

No keystone statement moved. C1 to C4 are the same theorems with the same
hypotheses; the diff in `books/tcpcl-invariants.lisp` is three `in-theory`
events (the two of commit 1 and `fn-tcl-cheap-rules` in commit 2), nine
`:hints` lists edited and one subgoal hint added. Eight of the nine are
commit 1's — `fn-tcl-recv-segment-final-ack-means-every-segment`,
`fn-tcl-inbound-is-created-only-by-start`,
`fn-tcl-step-emits-at-most-one-inbound-outcome`,
`fn-tcl-live-inbound-ends-in-exactly-one-outcome`,
`fn-tcl-settle-of-broken-stream`, `fn-tcl-ending-refuses-new-transfers`,
`fn-tcl-refused-transfer-sends-no-more-segments`,
`fn-tcl-step-keeps-local` — and the ninth is C1's `Subgoal *1/2`, in
commit 2. (Commit 1's own message says "nine hint lists" for a commit that
edited eight; this list is the exact one.)
`tools/ledger.py --write` after commit 1 changed nothing at all — no proof
event added, removed or renamed — and after commit 2 it adds exactly the
cheap family's 42 `defthm` and 2 `defun` in `books/tcpcl-session.lisp`.
`make check` exits 0 at both commits. No `skip-proofs`, no `defaxiom`, no
trust tag; nothing weakened.

`books/tcpcl-session.lisp` is the reverted change restored **verbatim** from
`a913425^`, not rewritten: `fn-tcl-session-cheapp` guards the nine executable
entry points and `fn-tcl-drive`'s totality `mbe`, `fn-tcl-sessionp-is-cheap`
bridges, 24 `-preserves-cheapp` lemmas and `fn-tcl-initial-session-is-cheap`
carry it, and `fn-tcl-cheap-rules` names the whole family so an includer can
close all of it at once.

## 7. The transfer cost, measured two ways

**The mechanism, measured directly, and this is the number to quote.** Both
recognizers asked the same question about the same session record, on hbox,
`books/tcpcl-session` certified, guard checking on, under `time$`:

| staged segments | `fn-tcl-sessionp` | `fn-tcl-session-cheapp` |
| --- | --- | --- |
| 1 | 0.75 µs/call (0.15 s / 200,000) | **0.70 µs/call** (0.14 s / 200,000) |
| 1,000 | 15 µs/call (0.03 s / 2,000) | **0.70 µs/call** (0.14 s / 200,000) |
| 20,000 | 250 µs/call (0.50 s / 2,000) | **0.70 µs/call** (0.14 s / 200,000) |

The specification recognizer is linear in the staged list — 20× the segments
for 16.7× the cost — and the cheap one does not move at all, to three
significant figures, across four orders of magnitude of staged data. At
20,000 staged segments the guard the host used to pay per socket chunk cost
**about 360× the one it pays now**, and since the staged list grows with the
transfer, that per-chunk cost is exactly the O(n²/chunk) w8 found. The driver
is a dozen forms over the certified book: three `defconst` sessions the
machine accepts — six `assert-event`s confirm that both recognizers hold of
all three, so each traverses to completion and returns T and neither is
timed on an early exit — and two counting loops. It is scratch, not tree
code, and is reproduced in
`planning/evidence/tcpcl-theory-w11-2026-09-20.md`.

**`tools/tcpcl_lab.py --scenario profile`, and a caveat about it.** Its
verdict is `ok` — below the 8× bar that a quadratic guard would blow through
at about 16× — but its *ratio* is not a reproducible number at these sizes.
Run today on hbox against the image w9/dtn-e2e built (`/tank/fn/lanes/
w9-dtn-e2e/build/fn-host-dtn`, a cheap-guard image, though not from bytes
identical to this branch's): 64 KiB **0.232 s**, 256 KiB **0.124 s**, ratio
**0.53**, both transfers intact, `ok: true`. w9's own run of the same
scenario against the same image reported 0.115 s, 0.212 s and ratio 1.84.
The large transfer being *faster* than the small one says what is really
being timed: two process starts of a 262 MB image, with the second warm. The
scenario separates 16× from ~1×, which is what it was built for; it does not
measure the guard, and a lane should not quote its ratio as though it did.

**Not measured here: an image built from this branch.** It needs the DTN
closure certified on a box. persvati `run-20260920T234237Z-8081`
(`/home/ember/fn-lanes/w11-tcpcl-theory`, `--jobs 4`, 1800 s cap) certified
seven of its nine roots in the first two minutes — `store-observed-traces`,
`bp-ingress`, `bp-receipt`, `bp-receipt-records`, `bp-workflow-records`,
`tcpcl-session`, `bp-bundle` — and then spent the rest of its budget on
`books/bp-bundle-invariants`, which was **cut at 1800.3 s** at
`fn-bpb-decode-block-is-canonical-by-construction`, `Subgoal
51.18.18.19.12.8.10`; `books/bp-node` then failed with "no certificate" and
the run exited 1. Its ACL2 child was at 99.9% CPU throughout, so it was
computing and not queued behind another lane's slot. That book is not this
lane's and the finding is on the board for the BP cluster, with the profile
to run on it. hbox was the wrong box for this closure: it lacked 23 of its
60 books where persvati lacked 9. Nothing above
depends on it: the direct measurement is of the certified book itself, and
the lab run is of a cheap-guard image. The remaining claim it would settle is
end-to-end throughput on this exact tree, which no number in this record
asserts.

## 8. The merge

**dev is at `7f6df89` and carries this packet**, fast-forwarded from the
lane branch, so dev's three tcpcl files are byte-for-byte the tree that
`certify-20260921T000317Z-1324995` certified (the two commits after that run
touch only `planning/`).

`w11/snt-guards` landed on dev (`2e99538`) while this lane was measuring, so
dev was merged in here first, rather than the other way round. Three conflicts, all
in shared registries and none in a book: `planning/deputies/BOARD.md`, where
both lanes appended a dated section and both are kept in merge order with no
line of either edited, and `planning/ledger.json`/`.md`, regenerated with
`tools/ledger.py --write` over the merged tree because that is the only way
those two are ever written.

Against the merged dev the ledger delta is exactly this lane and nothing
else: `defthm` 5507 → 5549 and `defun` 3926 → 3928 (the cheap family),
"functions left at the default with an explicit guard" 1787 → 1789, and
`assert-event` checks 5310 → 5323 (the separating witnesses of §5). The
other lane's rows are untouched.

The tcpcl closure does not intersect that work — `books/tcpcl-session`
includes `cbor`, `clock`, `defrecord`, `deftransition`, `tcpcl-records` and
`tcpcl-octets`, none of which dev touched — so the certificates stayed
content-valid across the merge; the three roots were re-run against the
merged tree anyway.

## 9. Open, in the order I would take them

1. **The outbound suffix is still walked per chunk.** Unchanged from
   `specs/tcpcl.md` §6: `fn-tcl-outboundp` is a conjunct of
   `fn-tcl-session-cheapp` and two of its conjuncts measure `remaining`, so a
   *send* of n octets is still O(n²/chunk). The obligation is written out
   there; it needs guard-total `fn-tcl-take`/`fn-tcl-drop` or a carried
   `(len remaining)`. The `profile` scenario above measures a send, so it is
   the measurement that will move when this closes.
2. **`books/tcpcl-invariants` still enables the vocabulary wholesale**
   (line 32). Four transitions and two recognizers are now closed by name
   above it, which is the fix for what was measured; the honest version is to
   drop the wholesale enable and name what each form opens. That is a
   separate, larger edit over 58 forms and this lane did not attempt it.
3. **`fn-tcl-cheap-rules` is exported ENABLED** by `books/tcpcl-session`, as
   `docs/proof-style.md` §9.1 prescribes (the theory exists so an includer can
   close it in one line, which `books/tcpcl-invariants` does). Today the only
   other includers are `host/tcpcl-host.lisp`, `tests/acl2/tcpcl-tests` and
   the two build lists, none of which reasons in `fn-tcl-sessionp`. The next
   book that includes `books/tcpcl-session` *and* enables its vocabulary must
   close `fn-tcl-cheap-rules` in the same breath, or it inherits the
   doubled forward-chaining family that cost w9/dtn-e2e five hours.
4. The three BP packets of HANDOFF-w9-dtn-e2e §2 are untouched and still in
   that order.
