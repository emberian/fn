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
| `books/tcpcl-session` | 25.259 s | 25.59 s | **64.27 s** |
| `books/tcpcl-invariants` | **609.687 s** | **6.61 s** | **7.31 s** |
| `tests/acl2/tcpcl-tests` | 0.312 s | 0.46 s | **0.47 s** |

Evidence: dev is w9/dtn-e2e's `certify-20260920T230902Z-1283742`
(`/tank/fn/lanes/w9-dtn-e2e-fix`), and it is a baseline for *exactly* these
bytes — its manifest's `source_digests_sha256` for all eight books in the
closure equal this worktree's at `19f3302`, so it was not re-run. +theory is
`certify-20260920T233326Z-1303168`; +guard is
`certify-20260920T234831Z-1314032` (the branch head, including the teeth of
§5; the same tree without them was `certify-20260920T233937Z-1307933` at
65.30 / 7.40 / 0.48 s). All in `/tank/fn/lanes/w11-tcpcl-theory`, all
`ACL2 certification passed`, zero `ACL2 Error` in every log, 72.453 s wall
for the three roots at `--jobs 4`.

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
recognizer was **open**, and each of the six carried its eleven
sub-recognizers into its clause — the same fan `books/deftransition.lisp`
exists for and that C2 measured as 1082 subgoals. What the six need about a
field arrives by forward chaining instead;
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
Measured: with nothing else changed, closing the four transitions at the top
of the book took C1 from 0.42 s to 0.05 s, and it is why the profile saw
`FN-TCL-STEP` at 481,747 frames in a theorem whose Goal hint disables
`fn-tcl-step`. The general rule: **a Goal-level `e/d` only holds under a
subgoal that names no `:in-theory` of its own; to hold everywhere, close it in
the book.**

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
| T4+teeth | T4 + the four separating witnesses of §5, branch head | 1800 s | **green**: 64.27 / 7.31 / 0.47 s (`certify-20260920T234831Z-1314032`) |

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
hypotheses; the diff in `books/tcpcl-invariants.lisp` is two `in-theory`
events, nine `:hints` lists and one added subgoal hint.
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

## 7. The transfer cost

PROFILE-PLACEHOLDER

## 8. Open, in the order I would take them

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
