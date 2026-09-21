# Handoff: w11/tcpcl-outbound — the send-side guard, and the decision behind it

Branch `w11/tcpcl-outbound`, worktree `build/lanes/w11-tcpcl-outbound`, from
`dev` at `38460cf`, with `dev` at `e67b6cb` merged in before landing. Box:
hbox only, `/tank/fn/lanes/w11-tcpcl-outbound`, ACL2
`/tank/fn/acl2-8.7/saved_acl2`, cache `/tank/fn/certcache`, everything under
`swarm-build`, **no prover step limit**, `FN_ACL2_TIMEOUT_SECONDS=1800`,
`--jobs 4` throughout so that every figure compares with the previous lane's.
hbox was measured before use by `AnonPages` and the RSS sum, not by `free`:
load 0.18, `AnonPages` 0.77 G, `MemFree` 27.9 G.

This is the packet `planning/lanes/HANDOFF-w11-tcpcl-theory.md` §9.1 named:
the last O(n²/chunk) served-path guard, on the sending side.

## 1. The decision (D20, and it was written as D19)

`specs/tcpcl.md` §6 named two candidate cures and left the choice open.
**Taken: guard-total `fn-tcl-take` and `fn-tcl-drop`.** Guard `(natp n)`, the
`fn-wire-ag-car` `mbe` pattern of `books/wire.lisp`, logical definitions
unchanged — `(car x)` and `(cdr x)` of an atom are already `nil`, so both
functions always had a value past the end of the list and the `mbe` only
gives the raw-Lisp code a definition there. That was the whole obstacle:
their `(fn-tcl-has octets k)` guard was the only thing that needed
`fn-tcl-outboundp`'s length equation.

**Rejected: a `remaining`-length scalar carried in the outbound record.** It
does not discharge the obligation. `(fn-tcl-has remaining k)` is a statement
about the list, so a carried `rem-len` relieves it only through
`(equal rem-len (len remaining))`, and checking *that* costs the walk, so it
cannot live in the cheap recognizer either — the carried length would have to
be combined with guard-total take and drop anyway. It is also strictly more
change for nothing: the record widens from seven fields to eight, every
`fn-tcl-make-outbound` call site and `books/tcpcl-records` move with it, and
the new field is state that can disagree with reality. A third shape was
considered and rejected with it: letting `fn-tcl-pump` test
`(fn-tcl-has remaining k)` itself is only O(chunk), but it buys the guard
with a branch the composed machine cannot reach, which the assurance rules
forbid as evidence. Full entry in `planning/decisions.md`.

**The id collided.** This was D19 until `w11/wildmat-xpat` landed its own D19
on dev at `e67b6cb` while this lane was measuring — the second such collision
in two days. Allocating by "highest in the file plus one" is what collides;
the board claim says so.

## 2. What changed

- `books/tcpcl-octets.lisp`: `fn-tcl-take` and `fn-tcl-drop` guard-total.
  `fn-tcl-has` is unchanged and is still every decoder's own branch test.
- `books/tcpcl-session.lisp`: `fn-tcl-outbound-cheapp` split off
  `fn-tcl-outboundp` exactly as `fn-tcl-inbound-cheapp` was split off
  `fn-tcl-inboundp` — the two conjuncts that measure the suffix dropped, the
  ordering `(<= sent-len total)` they implied carried explicitly because
  `fn-tcl-pump` needs it to know its chunk is a natural,
  `fn-tcl-outboundp-is-cheap` the only link. `fn-tcl-session-cheapp` carries
  the cheap one; `fn-tcl-outbound-cheapp-forward-fields` joins the
  forward-chaining family; both new names join `fn-tcl-cheap-rules` and
  `fn-tcl-session-vocabulary`, so an includer still closes the whole family
  in one line.
- `tests/acl2/tcpcl-tests.lisp`: the teeth of §4.
- `specs/tcpcl.md` §3 and §6, `planning/decisions.md`,
  `planning/evidence/tcpcl-outbound-w11-2026-09-20.md`.
- **`books/tcpcl-invariants.lisp` is untouched.** `git diff` over it is
  empty: C1 to C4 are the same theorems with the same hypotheses, and no hint
  in that book needed an edit.

## 3. Certification: all four roots together, with a control

`certify-book`'s own `Time:` line, hbox, `--jobs 4`. The control is the same
command on the same box the same night in a copy of this tree with the three
changed files replaced by `dev`'s bytes and their certificates removed. It
exists because this lane is the first to change `books/tcpcl-octets` and no
hbox figure for that book existed.

| root | dev bytes (control) | +D20 | previous lane, dev |
| --- | --- | --- | --- |
| `books/tcpcl-octets` | 101.258 s | **108.625 s** | not measured on hbox |
| `books/tcpcl-session` | 64.842 s | **64.584 s** | 62.76 s |
| `books/tcpcl-invariants` | 7.862 s | **7.257 s** | 7.25 s |
| `tests/acl2/tcpcl-tests` | 0.352 s | **0.333 s** | 0.46 s |
| wall, eight books at `--jobs 4` | 174.689 s | **181.273 s** | — |

Both runs `status passed`, `book_failures {}`, zero `ACL2 Error` in every
log. Control
`/tank/fn/lanes/w11-tcpcl-outbound-base/build/acl2/certify-20260921T004818Z-1354736`
(`--no-publish`, so it seeded nothing). The run in the table is
`build/acl2/certify-20260921T005957Z-1365818` (farm run
`run-20260921T005953Z-6393`, exit 0), taken on the merged branch head, and it
is the one whose `source_digests_sha256` match this tree. An earlier
identical-shaped run — `certify-20260921T004345Z-1351598`, **101.740 /
62.542 / 6.974 / 0.323 s**, 172.038 s wall — was superseded when the D19 → D20
renumber changed comment bytes in three of the four books. Both are kept
because together they say what this box's noise is: `books/tcpcl-octets`
reads 101.258 s (dev bytes), 101.740 s and 108.625 s on the same box within
twenty minutes, a spread of 7.4 s on 101 s.

**Making take and drop guard-total costs `books/tcpcl-octets` nothing** —
the change is well inside that spread, and the two lower readings are one
from each side of it — and the cheap outbound recognizer costs
`books/tcpcl-session` nothing (64.584 s against the control's 64.842 s).

## 4. The teeth

`fn-tcl-outboundp-is-cheap` is the new load-bearing theorem and nothing in
the tree showed it was not an identity. `tests/acl2/tcpcl-tests.lisp` now
carries one separating witness per dropped conjunct, each the mid-transfer
session `*t-a-mid*` — A has sent 3 of 5 octets and holds `(40 50)` unsent —
with its outbound record rebuilt through `fn-tcl-next`, and each accompanied
by the check that the *other* conjunct still holds, so the separation is by
more than the recognizers' weakest clause:

- `*t-a-nonoctet*` holds two non-octets unsent, so `3 + 2 = 5` still holds
  and only `fn-cbor-octet-listp` separates them;
- `*t-a-wrong-len*` holds one octet where two are unsent, so the suffix is
  octets and only the length equation separates them.

Both satisfy `fn-tcl-session-cheapp`; neither satisfies `fn-tcl-sessionp`.
Five further assertions anchor `fn-tcl-outbound-cheapp` on the sending
sessions the golden exchange actually reaches, and four check that the
relaxed take and drop answer past the end of a list with the value the
logical definition always had — `(fn-tcl-take 3 '(1 2))` is `'(1 2 nil)` and
`(fn-tcl-drop 3 '(1 2))` is `nil`, which are calls the old guard forbade.

## 5. The guard, measured directly, and this is the number to quote

Both recognizers asked the same question about the same session record,
`books/tcpcl-session` certified, guard checking on, under `time$`, **200,000
calls at every size** so that no cell rests on a 0.01 s reading. Seven of
seven `assert-event`s `:PASSED` in each tree, so both recognizers return T on
all three sessions and neither is timed on an early exit; zero `ACL2 Error`
in both logs. The driver is reproduced in
`planning/evidence/tcpcl-outbound-w11-2026-09-20.md` §2; logs in
`build/probe/`.

| unsent octets | `fn-tcl-sessionp` | `fn-tcl-session-cheapp` **before** | `fn-tcl-session-cheapp` **after** |
| --- | --- | --- | --- |
| 1 | 0.80 µs | 0.75 µs | **0.75 µs** |
| 1,000 | 3.80 µs | 3.90 µs | **0.75 µs** |
| 20,000 | 62.0 µs | 62.85 µs | **0.75 µs** |

**The old cheap guard was not cheap on a send**: 62.85 µs against the
specification recognizer's 62.9 µs at 20,000 unsent octets, indistinguishable
because `fn-tcl-outboundp` sat inside it verbatim and both walked the suffix
the same two times. **It was linear**: net of the ~0.7 µs the session's own
fields cost, 20× the octets for 19.8× the cost, and the host paid it once per
socket chunk. **After D20 it does not move at all** across four orders of
magnitude — 83× cheaper than the specification recognizer at 20,000 octets,
84× cheaper than what the same guard cost the day before.

The unit is one octet of unsent data. The receive-side table counts staged
*segments*, so its 360× and this 83× are different ratios and should not be
compared.

## 6. The lab gate: NOT RUN, and the blocker is one book in another cluster

`tools/tcpcl_lab.py --scenario profile` times a send, so with this packet it
would for the first time be a gate on what changed. It needs a native image
and **`books/bp-node` does not certify on dev**, so no image exists to run it
against, for this lane or any other. `w10/dtn-3` landed at `dbf1aa7` and says
so: the book is open at exactly one guard conjecture, `fn-bpp-fragmentp`'s
guard on the primary's flags, because `books/bp-primary` ships its accessors
with their `:definition` runes enabled. It is the only root between that tree
and `tools/build_native_host.sh`. `books/bp-bundle-invariants`, the blocker
when `w11/tcpcl-theory` looked at this last night, now certifies — with two
forms removed and recorded open — so the blocker moved one book down, not
away.

This lane confirmed the shape of the gap rather than taking the BP cluster's
work: after publishing `/tank/fn/lanes/w10-dtn-3`'s pairs into hbox's cache
(850 → 859 entries) and installing, this tree holds 42 of that image's 60
books. **Not run** is the status; not passed, not failed. When it runs, only
its verdict and its `intact` flags carry weight — the previous lane measured
its *ratio* at 1.84 one day and 0.53 the next, because it times two process
starts of a 262 MB image.

## 7. Open, in the order I would take them

1. **The lab gate, the moment `books/bp-node` certifies.** One command:
   `FN_NATIVE_BUILD=host/native/build-dtn.lisp
   FN_NATIVE_IMAGE=build/fn-host-dtn sh tools/build_native_host.sh`, then
   `python3 tools/tcpcl_lab.py --image build/fn-host-dtn --scenario profile`.
   It is the first end-to-end number this packet would move.
2. **`books/tcpcl-invariants` still enables the vocabulary wholesale**
   (line 32), unchanged from the previous lane's §9.2. Four transitions and
   both whole-state recognizers are closed by name above it; the honest
   version is to drop the wholesale enable and name what each of the 58 forms
   opens. Neither lane attempted it.
3. **A third recognizer would now cost a third forward-chaining family.**
   `fn-tcl-cheap-rules` has grown by two names and still closes the whole
   family in one line, which is what `docs/proof-style.md` §9.1 exists for.
   Any book that includes `books/tcpcl-session` *and* enables its vocabulary
   must close `fn-tcl-cheap-rules` in the same breath;
   `books/tcpcl-invariants` is still the only such book.
4. **Decision ids need an allocator, not a convention.** Two collisions in
   two days, both from "highest in the file plus one" read against a dev that
   moved. A `tools/` one-liner that takes the next id and writes the board
   claim in one step would end it; that is a tooling-cluster packet.
