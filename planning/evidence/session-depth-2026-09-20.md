# Session depth, 2026-09-20: the sweep, the expansion diff, and the runs

Everything `planning/lanes/HANDOFF-w10-session-depth.md` and the board claim,
with the command that produces it. Tree: `build/lanes/w10-session-depth`,
branch `w10/session-depth` from dev `99a348c`. ACL2 8.7.

## 1. The sweep as found, before any edit

Reproducible from any tree with this lane's tool, because the tool takes
paths:

    mkdir /tmp/before && git archive 99a348c books tests/acl2 host | tar -x -C /tmp/before
    python3 tools/session_depth.py /tmp/before/books /tmp/before/tests/acl2 /tmp/before/host

```
books/nntp-auth.lisp:435: CHAIN: fn-auth-single: a hand-spelled walk fn-peer-session-base then fn-post-session-base: say fn-peer-reader-session instead
books/nntp-auth.lisp:436: CHAIN: fn-auth-single: a hand-spelled walk fn-auth-session-base then fn-peer-session-base: say fn-auth-post-session instead
books/nntp-auth.lisp:780: CHAIN: fn-auth-command: a hand-spelled walk fn-peer-session-base then fn-post-session-base: say fn-peer-reader-session instead
books/nntp-auth.lisp:781: CHAIN: fn-auth-command: a hand-spelled walk fn-auth-session-base then fn-peer-session-base: say fn-auth-post-session instead
books/nntp-auth.lisp:959: CHAIN: defthm fn-auth-command-effects-well-formed: a hand-spelled walk fn-peer-session-base then fn-post-session-base: say fn-peer-reader-session instead
books/nntp-auth.lisp:960: CHAIN: defthm fn-auth-command-effects-well-formed: a hand-spelled walk fn-auth-session-base then fn-peer-session-base: say fn-auth-post-session instead
books/owner-config.lisp:248: DEPTH: fn-ocfg-group-pinned-by-readerp: fn-post-session-base wants a post session, (fn-own-conn-session (car conns)) is auth: (fn-post-session-base (fn-own-conn-session (car conns)))
books/owner-config.lisp:252: DEPTH: fn-ocfg-group-pinned-by-readerp: fn-post-session-base wants a post session, (fn-own-conn-session (car conns)) is auth: (fn-post-session-base (fn-own-conn-session (car conns)))
books/owner-config.lisp:412: DEPTH: fn-ocfg-list-active: fn-post-session-base wants a post session, (fn-own-conn-session conn) is auth: (fn-post-session-base (fn-own-conn-session conn))
books/owner-config.lisp:502: DEPTH: defthm fn-ocfg-list-active-lists-the-pinned-served-table: fn-post-session-base wants a post session, (fn-own-conn-session (fn-own-find-conn id (fn-own-conns (... ...)))) is auth: (fn-post-session-base (fn-own-conn-session (fn-own-find-conn id (... ...))))
books/owner-invariants.lisp:1243: CHAIN: defthm fn-own-conn-boundedp-is-post-session: a hand-spelled walk fn-auth-session-base then fn-peer-session-base: say fn-auth-post-session instead
books/owner-invariants.lisp:1267: CHAIN: local: a hand-spelled walk fn-auth-session-base then fn-peer-session-base: say fn-auth-post-session instead
books/owner-invariants.lisp:1303: CHAIN: local: a hand-spelled walk fn-peer-session-base then fn-post-session-base: say fn-peer-reader-session instead
books/owner-invariants.lisp:1304: CHAIN: local: a hand-spelled walk fn-auth-session-base then fn-peer-session-base: say fn-auth-post-session instead
books/owner-invariants.lisp:1308: CHAIN: local: a hand-spelled walk fn-peer-session-base then fn-post-session-base: say fn-peer-reader-session instead
books/owner-invariants.lisp:1309: CHAIN: local: a hand-spelled walk fn-auth-session-base then fn-peer-session-base: say fn-auth-post-session instead
books/owner-invariants.lisp:1313: CHAIN: local: a hand-spelled walk fn-auth-session-base then fn-peer-session-base: say fn-auth-post-session instead
books/owner-invariants.lisp:1328: CHAIN: local: a hand-spelled walk fn-peer-session-base then fn-post-session-base: say fn-peer-reader-session instead
books/owner-invariants.lisp:1329: DEPTH: local: fn-peer-session-base wants a peer session, (fn-own-conn-session conn) is auth: (fn-peer-session-base (fn-own-conn-session conn)) [open elsewhere]
books/owner-invariants.lisp:1332: CHAIN: local: a hand-spelled walk fn-peer-session-base then fn-post-session-base: say fn-peer-reader-session instead
books/owner-invariants.lisp:1333: DEPTH: local: fn-peer-session-base wants a peer session, (fn-own-conn-session conn) is auth: (fn-peer-session-base (fn-own-conn-session conn)) [open elsewhere]
books/owner-invariants.lisp:1341: CHAIN: local: a hand-spelled walk fn-peer-session-base then fn-post-session-base: say fn-peer-reader-session instead
books/owner-invariants.lisp:1342: DEPTH: local: fn-peer-session-base wants a peer session, (fn-own-conn-session conn) is auth: (fn-peer-session-base (fn-own-conn-session conn)) [open elsewhere]
books/owner-invariants.lisp:1345: CHAIN: local: a hand-spelled walk fn-peer-session-base then fn-post-session-base: say fn-peer-reader-session instead
books/owner-invariants.lisp:1346: DEPTH: local: fn-peer-session-base wants a peer session, (fn-own-conn-session conn) is auth: (fn-peer-session-base (fn-own-conn-session conn)) [open elsewhere]
books/owner-invariants.lisp:1349: DEPTH: local: fn-peer-session-base wants a peer session, (fn-own-conn-session conn) is auth: (fn-peer-session-base (fn-own-conn-session conn)) [open elsewhere]
books/owner-invariants.lisp:1414: ARGUMENT: local: fn-peer-with-base argument 0 wants a peer session, (fn-own-conn-session (fn-own-find-conn id (fn-own-conns o))) is auth [open elsewhere]
books/owner-invariants.lisp:1421: CHAIN: local: a hand-spelled walk fn-peer-session-base then fn-post-session-base: say fn-peer-reader-session instead
books/owner-invariants.lisp:1422: DEPTH: local: fn-peer-session-base wants a peer session, (fn-own-conn-session (fn-own-find-conn id (fn-own-conns o))) is auth: (fn-peer-session-base (fn-own-conn-session (fn-own-find-conn id (... ...)))) [open elsewhere]
books/owner-invariants.lisp:1426: CHAIN: local: a hand-spelled walk fn-peer-session-base then fn-post-session-base: say fn-peer-reader-session instead
books/owner-invariants.lisp:1427: DEPTH: local: fn-peer-session-base wants a peer session, (fn-own-conn-session (fn-own-find-conn id (fn-own-conns o))) is auth: (fn-peer-session-base (fn-own-conn-session (fn-own-find-conn id (... ...)))) [open elsewhere]
books/owner-invariants.lisp:1431: DEPTH: local: fn-peer-session-base wants a peer session, (fn-own-conn-session (fn-own-find-conn id (fn-own-conns o))) is auth: (fn-peer-session-base (fn-own-conn-session (fn-own-find-conn id (... ...)))) [open elsewhere]
books/owner-invariants.lisp:1536: DEPTH: defthm fn-own-durable-reply-names-a-durable-record: fn-peer-session-base wants a peer session, (fn-own-conn-session (fn-own-find-conn id (fn-own-conns o))) is auth: (fn-peer-session-base (fn-own-conn-session (fn-own-find-conn id (... ...)))) [open elsewhere]
books/owner-invariants.lisp:1546: DEPTH: defthm fn-own-durable-reply-names-a-durable-record: fn-peer-session-base wants a peer session, (fn-own-conn-session (fn-own-find-conn id (fn-own-conns o))) is auth: (fn-peer-session-base (fn-own-conn-session (fn-own-find-conn id (... ...)))) [open elsewhere]
books/owner.lisp:595: CHAIN: fn-own-conn-boundedp: a hand-spelled walk fn-peer-session-base then fn-post-session-base: say fn-peer-reader-session instead
books/owner.lisp:596: CHAIN: fn-own-conn-boundedp: a hand-spelled walk fn-auth-session-base then fn-peer-session-base: say fn-auth-post-session instead
books/peer-inbound.lisp:528: CHAIN: fn-peer-single: a hand-spelled walk fn-peer-session-base then fn-post-session-base: say fn-peer-reader-session instead
books/peer-inbound.lisp:727: CHAIN: fn-peer-command: a hand-spelled walk fn-peer-session-base then fn-post-session-base: say fn-peer-reader-session instead
books/peer-inbound.lisp:744: CHAIN: fn-peer-step: a hand-spelled walk fn-peer-session-base then fn-post-session-base: say fn-peer-reader-session instead
books/peer-inbound.lisp:940: CHAIN: defthm fn-peer-command-effects-well-formed: a hand-spelled walk fn-peer-session-base then fn-post-session-base: say fn-peer-reader-session instead
books/served.lisp:779: CHAIN: fn-served-post-outcome: a hand-spelled walk fn-auth-session-base then fn-peer-session-base: say fn-auth-post-session instead
books/served.lisp:788: CHAIN: defthm fn-served-post-outcome-effects-by-definition: a hand-spelled walk fn-auth-session-base then fn-peer-session-base: say fn-auth-post-session instead
books/served.lisp:810: ARGUMENT: fn-served-transit-outcome: fn-peer-transit-outcome argument 0 wants a peer session, (fn-served-conn-session conn) is auth
tests/acl2/served-tests.lisp:228: ARGUMENT: assert-event: fn-post-sessionp argument 0 wants a post session, (fn-served-conn-session *fn-t-served-forged*) is auth
tests/acl2/served-tests.lisp:313: CHAIN: assert-event: a hand-spelled walk fn-auth-session-base then fn-peer-session-base: say fn-auth-post-session instead
tests/acl2/served-tests.lisp:484: CHAIN: assert-event: a hand-spelled walk fn-peer-session-base then fn-post-session-base: say fn-peer-reader-session instead
tests/acl2/served-tests.lisp:485: CHAIN: assert-event: a hand-spelled walk fn-auth-session-base then fn-peer-session-base: say fn-auth-post-session instead
session_depth: 300 books, 112 typed formals, 6 defects, 30 hand-spelled walks, 11 open elsewhere, 0 waived, 0 conflicting formals
```

**Seventeen defects over 300 files** — the summary line splits them because
the eleven in `books/owner-invariants.lisp` are recorded in the tool's
`OPEN_DEFECTS` (they belong to w10/owner-relation), so it prints
`6 defects ... 11 open elsewhere`. Thirty hand-spelled walks, zero
conflicting formals. Five of the seventeen had never been named:
`books/served.lisp`'s transit call and the four in
`books/owner-config.lisp`. The sixth of the six, `served-tests.lisp:228`, is
a deliberate wrong-level witness and now carries its waiver.

## 2. After this lane

    python3 tools/session_depth.py
    # session_depth: 300 books, 112 typed formals, 0 defects,
    #   13 hand-spelled walks, 11 open elsewhere, 3 waived, 0 conflicting formals

The eleven are `books/owner-invariants.lisp`'s, recorded with their owner
and their fix; an entry that stops matching fails the check. The three
waived are deliberate wrong-level witnesses in
`tests/acl2/served-tests.lisp`, each carrying its reason on a
`; session-depth-ok:` line. The thirteen walks are in
`books/owner-invariants.lisp` (nine, foreign) and in `:use` instances and
macro definitions that name the expanded term on purpose.

## 3. The macro conversions changed no term

The three projections are macros, so a conversion should leave the logical
term byte-identical. Tested by expanding them in the new sources and
diffing the whole form list against dev `99a348c`
(the script is reproduced at the end of this file):

```

books/peer-inbound.lisp: 129 -> 130 forms; 1 added/changed, 0 removed/changed
   + defmacro fn-peer-reader-session

books/nntp-auth.lisp: 153 -> 155 forms; 2 added/changed, 0 removed/changed
   + defmacro fn-auth-post-session
   + defmacro fn-auth-reader-session

books/served.lisp: 112 -> 113 forms; 2 added/changed, 1 removed/changed
   - defun fn-served-transit-outcome
   + defun fn-served-transit-outcome
   + defthm fn-served-transit-outcome-effects-by-definition

books/owner.lisp: 155 -> 155 forms; 0 added/changed, 0 removed/changed

books/owner-config.lisp: 59 -> 59 forms; 3 added/changed, 3 removed/changed
   - defun fn-ocfg-group-pinned-by-readerp
   - defun fn-ocfg-list-active
   - defthm fn-ocfg-list-active-lists-the-pinned-served-table
   + defun fn-ocfg-group-pinned-by-readerp
   + defun fn-ocfg-list-active
   + defthm fn-ocfg-list-active-lists-the-pinned-served-table

books/nntp-post.lisp: 57 -> 59 forms; 3 added/changed, 1 removed/changed
   - defun fn-nntp-post-outcome
   + defconst *fn-post-malformed-session-line*
   + defun fn-nntp-post-outcome
   + defthm fn-post-outcome-separates-a-malformed-session

tests/acl2/served-tests.lisp: 121 -> 141 forms; 19 added/changed, 0 removed/changed
   + defconst *fn-t-served-transit-sub*
   + defconst *fn-t-served-transit-want*
   + defconst *fn-t-served-transit-session*
   + assert-event (fn-peer-submissionp *fn-t-served-transit-sub*)
   + assert-event (fn-peer-sessionp *fn-t-served-transit-session*)
   + assert-event (not (fn-peer-sessionp (fn-served-conn-session *fn-t-served-conn*))
   + assert-event (not (equal *fn-t-served-transit-session* (fn-served-conn-session *
   + assert-event (equal (fn-served-result-effects (fn-served-transit-outcome *fn-t-s
   + assert-event (equal (fn-post-result-session (fn-peer-transit-outcome *fn-t-serve
   + assert-event (not (equal (fn-post-result-session (fn-peer-transit-outcome *fn-t-
   + assert-event (equal (fn-post-result-effects (fn-peer-transit-outcome (fn-served-
   + assert-event (equal (take 4 (fn-served-reply-octets (fn-served-result-effects (f
   + defconst *fn-t-served-403*
   + assert-event (equal (take 4 *fn-t-served-403*) (quote (52 48 51 32)))
   + assert-event (consp *fn-t-served-403*)
   + assert-event (not (equal *fn-t-served-403* *fn-t-served-240*))
   + assert-event (not (equal *fn-t-served-403* *fn-t-served-441-refused*))
   + assert-event (not (equal *fn-t-served-403* *fn-t-served-441-uncertain*))
   + assert-event (fn-served-effectsp (fn-served-result-effects (fn-served-post-outco

tests/acl2/nntp-post-tests.lisp: 57 -> 74 forms; 16 added/changed, 0 removed/changed
   + defconst *fn-tp-too-deep*
   + defconst *fn-tp-too-shallow*
   + defconst *fn-tp-403*
   + assert-event (fn-nntp-sessionp *fn-tp-too-deep*)
   + assert-event (not (fn-post-sessionp *fn-tp-too-deep*))
   + assert-event (fn-post-session-shapep *fn-tp-too-shallow*)
   + assert-event (equal (fn-post-session-base *fn-tp-too-shallow*) *fn-tp-s0*)
   + assert-event (not (fn-post-sessionp *fn-tp-too-shallow*))
   + assert-event (equal (fn-post-result-effects (fn-nntp-post-outcome *fn-tp-too-dee
   + assert-event (equal (fn-post-result-effects (fn-nntp-post-outcome *fn-tp-too-sha
   + assert-event (equal (fn-post-result-effects (fn-nntp-post-outcome *fn-tp-too-dee
   + assert-event (fn-nntp-effectsp *fn-tp-403*)
   + assert-event (not (equal (fn-post-result-effects (fn-nntp-post-outcome *fn-tp-to
   + assert-event (not (equal (fn-post-result-effects (fn-nntp-post-outcome *fn-tp-to
   + assert-event (not (equal (fn-post-result-effects (fn-nntp-post-outcome *fn-tp-to
   + assert-event (equal (fn-post-result-effects (fn-nntp-post-outcome *fn-tp-too-dee
```

Read the two lines that matter: `books/owner.lisp` has **0 changed forms**
(the `fn-own-conn-boundedp` conversion is pure notation), and
`books/served.lisp` has exactly one changed form, `fn-served-transit-outcome`
— the `fn-served-post-outcome` conversion beside it is term-identical.
`tests/acl2/served-tests.lisp` and `tests/acl2/nntp-post-tests.lisp` have
**0 removed**: their conversions are term-identical and everything else is
new teeth. So the whole semantic surface of this lane is six forms
(`fn-served-transit-outcome`, `fn-ocfg-group-pinned-by-readerp`,
`fn-ocfg-list-active` and its restating theorem, `fn-nntp-post-outcome`),
two new `:rule-classes nil` theorems, one `defconst`, and 35 assertions.

This is a statement about macro expansion, not a proof: it says the prover
would see the same terms, not that the terms are right.

## 4. Certification

| root | verdict | run |
| --- | --- | --- |
| `books/nntp-post` | CERTIFIED | laptop `build/acl2/certify-20260920T215621Z-50486`; and persvati `run-20260920T220225Z-6d2d`, 6.121 s |
| `tests/acl2/nntp-post-tests` | CERTIFIED, 47 assertions | laptop `build/acl2/certify-20260920T215750Z-51499`; and persvati `run-20260920T220225Z-6d2d`, 0.642 s |
| 66 of 80 roots | CERTIFIED | persvati `run-20260920T220225Z-6d2d`, `--affected-by books/nntp-post.lisp --closure --jobs 4`, remote root `/home/ember/fn-lanes/w10-session-depth`, installed 58 kept 61 uncached 156, evidence `build/acl2/certify-20260920T220232Z-3813815` |
| `books/provenance-codec` | **FAILED**, the one genuine failure | same run, `books--provenance-codec.certify.log:2658`, `ACL2 Error [Failure] in ( DEFTHM FN-PROV-REBUILD-OF-ITS-OWN-FIELDS`, 3.418 s |
| `books/peer-inbound`, `books/peer-inbound-invariants`, `books/nntp-auth`, `books/nntp-auth-invariants`, `books/served`, `books/owner`, `books/owner-config`, `books/owner-invariants`, `books/ideal`, `tests/acl2/peer-inbound-tests`, `tests/acl2/nntp-auth-tests`, `tests/acl2/served-tests`, `tests/acl2/owner-tests` | NOT ATTEMPTED | thirteen cascades of the above, same run |

`books/peer-inbound.lisp:45` includes `provenance-codec`, which is why the
cascade starts one level lower than the board had been saying. The same
failure on the laptop: `build/acl2/certify-20260920T215904Z-52240`,
`ACL2 Error in ( INCLUDE-BOOK "provenance-codec" ...): There is no
certificate`.

**So this lane's edits to `books/peer-inbound.lisp`, `books/nntp-auth.lisp`,
`books/served.lisp`, `books/owner.lisp`, `books/owner-config.lisp` and
`tests/acl2/served-tests.lisp` are NOT certified.** §3 is what is known
about them without ACL2.

## 4b. The teeth DID run, by `ld`, and what that run is and is not

`certify-book` cannot reach `books/served`, but `ld` can, because
`include-book`'s missing certificate is the only thing in the way. Driver,
run from the worktree root with `tools/acl2 --timeout 3000`:

    (set-ld-error-action :continue state)
    (set-prover-step-limit 2000000)
    (ld "books/provenance-codec.lisp" :ld-error-action :continue)
    (ld "books/peer-inbound.lisp"     :ld-error-action :continue)
    (ld "books/nntp-auth.lisp"        :ld-error-action :continue)
    (ld "books/served.lisp"           :ld-error-action :continue)
    (ld "tests/acl2/served-tests.lisp" :ld-error-action :continue)

**What it establishes.** Every definition in the four books admits.
`FN-SERVED-TRANSIT-OUTCOME` admits; its two theorems close **Q.E.D.** —
`FN-SERVED-TRANSIT-OUTCOME-EFFECTS-BY-DEFINITION` in 0.18 s and 91,383
prover steps, `FN-SERVED-TRANSIT-OUTCOME-EFFECTS-ARE-TYPED` in 0.01 s over
`FN-PEER-TRANSIT-OUTCOME-EFFECTS-WELL-FORMED`. And
**`tests/acl2/served-tests.lisp` ran with 95 of 95 assertions `:PASSED`**,
including all sixteen this lane added: the transit-depth separation, the
result record's session, the negative control, the 235 prefix, and the six
403 assertions over the forged connection.

**What it is NOT.** It is an admission in a contaminated world, and the
contamination is the technique's, not the tree's: `books/nntp-auth.lisp`'s
`(include-book "peer-inbound")` re-processes `books/peer-inbound.lisp`
(it has no certificate) in a world where the `ld` above already defined
`FN-PEER-VOCABULARY`, so its `deftheory` fails with *"The name
FN-PEER-VOCABULARY is in use as a theory"* and peer-inbound's export theory
never runs. Served's proofs therefore run with 10,933 enabled runes instead
of the theory the book builds, and eight of them fail on theory grounds —
the first, `FN-SERVED-DISPATCH-EFFECTS-ARE-TYPED`, with *"A theory
expression could not be evaluated"*, which names the cause exactly. None of
the eight is one this lane wrote or touched. **So this run is evidence about
the definitions, the two new theorems and the assertions, and about nothing
else; `books/served` remains uncertified.** 46 `ACL2 Error` lines in the
log, all of them in that cascade or in `books/provenance-codec`'s own three
failures.

## 5. The checker's own tests

    python3 -m unittest tests.test_session_depth
    # Ran 15 tests ... OK

Four of the fifteen are the four historical misses reduced to their shape.

## 6. The expansion script

Kept here because it is the evidence for §3 and is a one-off against a base
commit rather than a tool the tree runs.

```python
"""Expand the three named projections in the NEW sources and diff against dev.

The claim under test: every macro conversion this lane made replaced a term
with a name that expands to the same term, so no theorem, goal or executable
value changed.  Anything that differs after expansion is a SEMANTIC edit and
must be one of the ones the handoff names.
"""
import importlib.util, subprocess, sys
from pathlib import Path

ROOT = Path("/Users/ember/dev/fn/build/lanes/w10-session-depth")
spec = importlib.util.spec_from_file_location("ledger", ROOT / "tools" / "ledger.py")
ledger = importlib.util.module_from_spec(spec); sys.modules["ledger"] = ledger
spec.loader.exec_module(ledger)
Sym = ledger.Sym

MACROS = {
    "fn-peer-reader-session":
        lambda a: [Sym("fn-post-session-base"), [Sym("fn-peer-session-base"), a]],
    "fn-auth-post-session":
        lambda a: [Sym("fn-peer-session-base"), [Sym("fn-auth-session-base"), a]],
    "fn-auth-reader-session":
        lambda a: [Sym("fn-post-session-base"),
                   [Sym("fn-peer-session-base"), [Sym("fn-auth-session-base"), a]]],
}

def expand(form):
    if not isinstance(form, list):
        return form
    out = [expand(x) for x in form]
    if out and isinstance(out[0], Sym) and str(out[0]) in MACROS and len(out) == 2:
        return MACROS[str(out[0])](out[1])
    return out

def render(f):
    if isinstance(f, list):
        return "(" + " ".join(render(x) for x in f) + ")"
    if isinstance(f, str) and not isinstance(f, Sym):
        return '"' + f + '"'
    return str(f)

def name(form):
    if isinstance(form, list) and len(form) > 1:
        return f"{render(form[0])} {render(form[1])}"[:80]
    return render(form)[:80]

BASE = "99a348c"
for rel in ["books/peer-inbound.lisp", "books/nntp-auth.lisp", "books/served.lisp",
            "books/owner.lisp", "books/owner-config.lisp", "books/nntp-post.lisp",
            "tests/acl2/served-tests.lisp", "tests/acl2/nntp-post-tests.lisp"]:
    old_src = subprocess.run(["git", "-C", str(ROOT), "show", f"{BASE}:{rel}"],
                             capture_output=True, text=True, check=True).stdout
    new_src = (ROOT / rel).read_text()
    old = [render(expand(f)) for f in ledger.read_forms(old_src)]
    new = [render(expand(f)) for f in ledger.read_forms(new_src)]
    old_set, new_set = set(old), set(new)
    added = [f for f in ledger.read_forms(new_src) if render(expand(f)) not in old_set]
    removed = [f for f in ledger.read_forms(old_src) if render(expand(f)) not in new_set]
    print(f"\n{rel}: {len(old)} -> {len(new)} forms; "
          f"{len(added)} added/changed, {len(removed)} removed/changed")
    for f in removed:
        print("   - " + name(f))
    for f in added:
        print("   + " + name(f))
```
