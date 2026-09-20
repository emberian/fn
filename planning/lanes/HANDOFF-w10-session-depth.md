# w10/session-depth: the fourth instance, the check that finds the fifth, and the fix that ends the class

Branch `w10/session-depth`, worktree `build/lanes/w10-session-depth`, from dev
`99a348c`. One defect class: the served command chain is four session records
deep and every base accessor reads `car`, so a call that stops one level short
is answered with a plausible value rather than an error.

    auth --fn-auth-session-base--> peer --fn-peer-session-base--> post
         --fn-post-session-base--> reader

## 1. The live one: `fn-served-transit-outcome`

`books/served.lisp` handed `fn-peer-transit-outcome` the whole auth session;
it wants the peer session. Fixed to `(fn-auth-session-base
(fn-served-conn-session conn))`, with a `:rule-classes nil` restatement
`fn-served-transit-outcome-effects-by-definition` beside it, so the depth of
the call is a statement in the book and not only a line of code.

**The teeth, and the honest limit.** No assertion over
`fn-served-transit-outcome`'s VALUE can separate the two depths today,
because the transit reply does not read its session at all (`fn-peer-single`
reaches `fn-nntp-single`, whose effects are the reply alone, and
`fn-peer-echo-reply` ignores it outright). That is precisely why the miss was
invisible. So `tests/acl2/served-tests.lisp` observes the SESSION the outcome
is computed from: the two candidate sessions are different values of which
exactly one is an `fn-peer-sessionp`; the served path's effects are those of
`fn-peer-transit-outcome` over the peer session; the result record's session
— what a state-dependent reply would read — is that peer session and not the
auth session above it. Beside them is a **negative control that is also an
alarm**: it pins that today the two depths give the same octets, so when a
transit reply becomes session-dependent that assertion fails and its failure
is the notice that every call site must be re-read. That is the honest
witness; the thing that would actually have CAUGHT this is §2.

## 2. The sweep: `tools/session_depth.py`

A standalone tool, wired into `make check`, not a rule in `tools/ledger.py`.
Why: it needs an s-expression parse and a fixpoint over the whole book set,
which the ledger's name- and line-oriented reader does not do; and it must be
runnable alone in a lane. It reuses the ledger's `Reader`, so there is one
s-expression reader in the tree, not two. `make check` already has three such
tools and the precedent (`transcribe_check.py`) for "a defect fails, drift is
counted".

It infers the session level of every formal from the calls each definition
makes — no hand-maintained table of callees — seeded by the naming rule
`fn-<tag>-session-<field>` / `fn-<tag>-sessionp` that `docs/prefixes.md`
pins, plus the constructors, which build a `list` and so cannot be inferred.
Levels travel through `let`/`let*`. Three categories: **DEPTH** (a base
accessor applied at the wrong level), **ARGUMENT** (an expression at a known
level passed to a formal at another) — both fail — and **CHAIN** (a walk
spelled by hand outside the named projections), counted, failed under
`--strict`.

**On dev `99a348c`: 300 files, 112 typed formals, 17 defects, 30
hand-spelled walks, 0 conflicting formals.** The full hit list:

| where | kind | what |
| --- | --- | --- |
| `books/served.lisp:810` | ARGUMENT | **the live one**, fixed here |
| `books/owner-config.lisp:248`, `:252` | DEPTH | **`fn-ocfg-group-pinned-by-readerp` read the PEER NAME where it meant the reader's selected group**, fixed here |
| `books/owner-config.lisp:412` | DEPTH | `fn-ocfg-list-active` answered LIST ACTIVE from the same wrong reach, fixed here |
| `books/owner-config.lisp:502` | DEPTH | the theorem restating that definition, fixed with it |
| `books/owner-invariants.lisp:1329`, `:1333`, `:1342`, `:1346`, `:1349`, `:1422`, `:1427`, `:1431`, `:1536`, `:1546` | DEPTH | `fn-peer-session-base` of a connection that holds an auth session, in `:use` instances — **foreign, see §5** |
| `books/owner-invariants.lisp:1414` | ARGUMENT | `fn-peer-with-base` applied to the auth session — **foreign** |
| `tests/acl2/served-tests.lisp:231` | ARGUMENT | the deliberate forged witness; now carries `; session-depth-ok:` with its reason |

`books/owner-config.lisp:248` is the one worth reading twice. A connection's
session is an auth session; `fn-post-session-base` of it is the PEER session,
whose field 1 is the peer name. So `fn-nntp-session-group` returned the peer
name, the condition was false of every reader, and **design §2.3's
admissibility rule — never retire a group a reader is standing in — did not
hold for any reader.** Nothing failed: a peer name is not a group name, so
the guard simply never fired.

**What the check cannot see**, stated in the tool and worth repeating: a
session that round-trips through `fn-post-make-result` /
`fn-post-result-session`, because that result record is shared by all three
wrappers and therefore carries no level (a design smell in its own right — it
is the untyped seam that lets the levels blur); a session stored in and read
back out of any other record field; a formal whose level no call constrains;
and anything built by a macro other than the three projections. It also says
nothing about whether a level is the RIGHT one for the protocol, only that
the caller and the callee agree.

`tests/test_session_depth.py` (15 cases) runs the checker over each of the
four historical misses reduced to its shape — `fn-own-conn-boundedp`'s POST
test on the whole session, `fn-served-post-outcome`'s short reach, the
test-side copy of it, and the transit one — and over the corrected
spellings, the `let*` propagation, the shadowed binding, the waiver
mechanism and the drift category.

## 3. The deeper fix: both, and why in this order

**Named projections, as MACROS.** `fn-peer-reader-session`
(`books/peer-inbound.lisp`), `fn-auth-post-session` and
`fn-auth-reader-session` (`books/nntp-auth.lisp`). A macro expands to exactly
the term its call sites already spell, so naming the walk costs no theorem,
no rule, no export entry and no re-proof — and that is the whole argument
for it: a *function* would have been a new definition to admit, guard-verify,
enable, disable and export in eight books, which is why the same fix would
otherwise have gone in one book at a time and left the rest spelling walks.
Adding a wrapper is now one edit per book. They live in the book that owns
the outer wrapper, with that book's registered prefix, not in `books/served`
under `fn-served-`: `books/nntp-auth.lisp` spells two of these walks itself
and is below `served`, `owner`, `owner-config` and `owner-invariants`, so it
is the lowest home that all of them can see.

**Distinguishable refusal, taken for the POST outcome only.**
`fn-nntp-post-outcome` answered a non-`fn-post-sessionp` argument with NO
EFFECTS. That is not accepted, refused or uncertain; it is a fourth thing
that reads as success, and it is why the POST miss cost a day. It now
answers `403 internal fault; the posting session is malformed` (RFC 3977
§3.2.1), and `fn-post-outcome-separates-a-malformed-session` states that the
fourth outcome differs from all three others whatever the store reported.
No theorem statement was weakened, removed or restated to accommodate it;
`fn-post-outcome-240-only-for-a-durable-observation` keeps its
`fn-post-sessionp` hypothesis, and the teeth now include the violating value
that shows the hypothesis is necessary.

**Blast radius, measured.** Source: `books/nntp-post.lisp` (one branch, one
`defconst`, one new `:rule-classes nil` theorem) and
`tests/acl2/nntp-post-tests.lisp` (15 new assertions, 47 total). Proof: none
— `books/nntp-post` and `tests/acl2/nntp-post-tests` both certified on the
laptop first try. Certificates: `books/nntp-post` is low, so every book above
it re-certifies; that set is the same one the macro edits already touch.
Behaviour: only on a path that was already defective.

**Not taken, and it is the next step.** `fn-peer-transit-outcome` has the
same benign answer and worse: it does not test `fn-peer-sessionp` at all, so
a wrong-level session produces a *correct-looking* reply. Giving it the same
403 treatment is the same shape of edit in `books/peer-inbound.lisp` plus its
test book, and it would turn the transit teeth above from a negative control
into a real separation. Owner: whoever holds `books/peer-inbound`.

## 4. Certification

| root | verdict | evidence |
| --- | --- | --- |
| `books/nntp-post` | **CERTIFIED** | laptop, ACL2 8.7, `build/acl2/certify-20260920T215621Z-50486` |
| `tests/acl2/nntp-post-tests` | **CERTIFIED**, 47 assertions | laptop, ACL2 8.7, `build/acl2/certify-20260920T215750Z-51499` |
| `tools/session_depth.py` | 15 unit cases pass | `python3 -m unittest tests.test_session_depth` |
| `make check` | green | includes the new check |
| 66 of 80 roots | **CERTIFIED** | persvati `run-20260920T220225Z-6d2d`, `--affected-by books/nntp-post.lisp --closure --jobs 4`, evidence `build/acl2/certify-20260920T220232Z-3813815` |
| `books/provenance-codec` | **FAILED**, the one genuine failure | same run, `books--provenance-codec.certify.log:2658` |
| `books/peer-inbound`, `books/nntp-auth`, `books/served`, `tests/acl2/served-tests`, `books/owner`, `books/owner-config` and seven more | NOT ATTEMPTED, cascades of it | see §5 |

**The teeth DID run.** `certify-book` cannot reach `books/served`, but `ld`
can: a driver that `ld`s `provenance-codec`, `peer-inbound`, `nntp-auth`,
`served` and `served-tests` in order, under `:ld-error-action :continue`,
admits every definition, closes `fn-served-transit-outcome`'s two theorems
**Q.E.D.** (the restatement in 0.18 s and 91,383 steps), and runs
`tests/acl2/served-tests.lisp` with **95 of 95 assertions `:PASSED`**,
including all sixteen this lane added. It is an admission in a world
contaminated by the technique — `nntp-auth`'s `(include-book "peer-inbound")`
re-processes the uncertified source and its `deftheory fn-peer-vocabulary`
collides with the earlier `ld`, so peer-inbound's export theory never runs
and eight served theorems fail on theory grounds, none of them this lane's.
Evidence §4b has the driver, the quotes and the caveat in full.

Every number and log line above, and the sweep's before/after output, is in
[`planning/evidence/session-depth-2026-09-20.md`](../evidence/session-depth-2026-09-20.md).

**What is known about the uncertified edits without ACL2.** The three
projections are macros, so a conversion must leave the logical term
identical. Expanding them in the new sources and diffing the whole form list
against dev `99a348c` (evidence §3) gives: `books/owner.lisp` **0 changed
forms**; `books/peer-inbound.lisp` and `books/nntp-auth.lisp` only the macro
definitions added; `books/served.lisp` exactly one changed form,
`fn-served-transit-outcome`, plus its new restatement; the two test books
**0 removed**. So the entire semantic surface of this lane is six forms, two
new `:rule-classes nil` theorems, one `defconst` and 35 assertions — and of
those, the `books/nntp-post` ones are certified. That is a statement about
macro expansion, not a proof.

## 5. What cannot be verified here, and why

**`books/provenance-codec` is open at dev HEAD and it gates everything above
`books/nntp-post`.** `books/peer-inbound` includes it
(`books/peer-inbound.lisp:45`), so `books/peer-inbound`, `books/nntp-auth`,
`books/served`, `tests/acl2/served-tests`, `books/owner`,
`books/owner-config` and `books/owner-invariants` all fail at their
`include-book` and are never attempted. Measured here: laptop
`build/acl2/certify-20260920T215904Z-52240`, `books/peer-inbound` at
`ACL2 Error in ( INCLUDE-BOOK "provenance-codec" ...): There is no
certificate`. The diagnosis is w10/owner-relation's board NOTE
(`fn-prov-rebuild-of-its-own-fields`, `books/provenance-codec.lisp:477`,
the `(:match . x)` hole); it is not this lane's book and was not touched.

So: **this lane's changes to `books/served.lisp`,
`tests/acl2/served-tests.lisp`, `books/peer-inbound.lisp`,
`books/nntp-auth.lisp`, `books/owner.lisp` and `books/owner-config.lisp` are
NOT certified.** What is known about them is that the macro conversions
expand to the byte-identical terms they replace (a macro expansion, not a
proof claim), and that the two substantive edits — the transit depth and the
four `owner-config` depths — change terms in books that cannot be read today.
Whoever unblocks `books/provenance-codec` should re-run
`--affected-by books/nntp-post.lisp --closure` and confirm `books/served`,
`tests/acl2/served-tests` and `books/owner-config`.

**`books/owner-invariants` is not touched.** Its eleven wrong-depth sites are
real and three of the four forms it is open at are exactly these: its `:use`
instances name `(fn-peer-session-base (fn-own-conn-session conn))` where the
statement reaches `(fn-peer-session-base (fn-auth-session-base ...))`, so
they name terms the goal does not contain. w10/owner-relation's board CHANGE
says that lane is repairing `fn-own-advanced-session-is-bounded`'s hint block
and nothing else. The other sites are recorded in the tool's `OPEN_DEFECTS`
with the owner and the fix; **an entry that stops matching FAILS the check**,
so whoever repairs a site deletes its line in the same commit.

## 6. For the next lane

- Finish `books/owner-invariants`: `fn-auth-session-base` for the depth-1
  reaches (`:1329`, `:1333`, `:1342`, `:1346`, `:1349`, `:1422`, `:1427`,
  `:1431`, `:1536`, `:1546`), `fn-auth-post-session` /
  `fn-auth-reader-session` for the walks, and at `:1414` an
  `fn-auth-with-base` around the `fn-peer-with-base` so the rebuild keeps the
  login. Then delete the `OPEN_DEFECTS` entries.
- Give `fn-peer-transit-outcome` the 403 treatment (§3).
- `fn-post-make-result` / `fn-post-result-session` is one result record
  shared by three wrapper levels. It is the reason the check has a blind
  spot and part of the reason the levels blur at all. Three typed result
  records, or one carrying its level, would close it.
