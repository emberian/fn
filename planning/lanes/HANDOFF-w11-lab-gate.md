# w11-lab-gate handoff

Branch `w11/lab-gate`, worktree `build/lanes/w11-lab-gate`, from `dev`
`cbede52`, with `dev` `b51108b` merged at `123ced9`.

The lane exists because of one incident. `receive_bpa_request` gained a
required keyword-only `bundle` on 2026-09-19 (`4ec3541`); the callers in
`tools/` were updated, two in `tests/` were not; both integration labs were
dead for a day and every `make check` was green for all of it, because
nothing in the tree ran a lab — and the one test that would have failed had a
skip keyed on a failure message and reported a SKIP.

Four things, in the order the brief asked for them.

## 1. `make labs`

`tools/labs.py`, plus `make labs` (tier `local`) and `make labs-quick` (tier
`quick`). Eleven rows: seven labs and four harness dry runs, printed in
separate sections so a dry run can never be read as a lab result. Three
outcomes, distinct all the way to the exit code the way D13 asks everywhere
else — `passed`, `failed`, `not-runnable` — and the exit code is 1 only when
a lab actually failed. A not-runnable row always says what is missing and how
to get it. Two teeth in the runner itself: a lab that exits 0 and leaves no
evidence file is a **failure**, because that is the shape the four-node
record took while the lab could not start; and `--require <name>` turns a
named lab's absence into a failure, which is how a box that is supposed to be
able to run one says so.

The tier table and the costs are in `tests/README.md`. Not wired into `make
check`: `check` is seconds and runs before every commit, the quick tier is
about two and a half minutes and the box tier is hours, and a gate nobody can
afford to run is a gate nobody runs.

**What it reports today, on this laptop** (`python3 tools/labs.py --tier all`,
the full run is `build/labs/<stamp>/` with `report.json` beside it):

| row | outcome here | detail |
| --- | --- | --- |
| `four-node` | **passed**, 73.0 s | 22 of 22; evidence in the run directory |
| `tcpcl` | not-runnable | no native image at `build/fn-host`; `sh tools/build_native_host.sh` builds one and needs a certified tree |
| `ltp` | not-runnable here | no pinned ION at `/tank/fn/ltp`. **It passed on hbox**, see §2 |
| `deploy` | not-runnable | needs a farm box: pass `--host` |
| `twonode` | not-runnable | needs a farm box: pass `--host` |
| `inn` | not-runnable | needs `--host` naming a box with the pinned INN |
| `scale` | not-runnable | needs a farm box: pass `--host` |
| `deploy-dry` | passed, 27.9 s | 34 steps, 0 failed |
| `twonode-dry` | passed, 18.2 s | 84 and 81 steps, 0 failed |
| `scale-dry` | passed, 15.5 s | 28 steps, 0 failed |
| `inn-dry` | **was RED on dev**, now passes | 18 tests, 80 steps, 0 failed |

`make labs-quick` on this laptop: **5 passed, 0 failed, 0 not-runnable**, 177 s
in all. A failing row also carries a **diagnosis** when its output matches one
of four causes that are not in the lab at all: a stale certificate (below), a
book included uncertified, a run directory too deep for a unix socket, and an
absent `FN_ACL2`. A lane that meets one of those should not spend an
afternoon in the lab, and the row says so.

**A third dead harness, found by writing the runner.** `tests/test_inn_lab.py`
errored in `setUpClass` on `dev` with `IndexError: list index out of range` at
`tools/inn_lab.py:826`. Real `nnrpd -D` writes `run/nnrpd-<port>.pid` and the
lab reads that file — a change made on 2026-09-20 because killing the shell
child it forked from had left a stray reader daemon on the box — and
`tests/inn_lab_fake` was never updated, so the lab parsed an empty pid and
indexed `[0]` into an empty list. Two defects, both fixed: the fake writes the
pid file real nnrpd writes, and the lab records a gap ("nnrpd came up and
wrote no pid file, so this run cannot stop exactly the reader it started")
instead of dying. That second half is a defect of the **real** lab, not only
of its dry run. `tests.test_inn_lab` now runs 18 tests, 80 steps, 0 failed.

**A fifth thing nothing ran: the four-node lab cannot start in a gate tree.**
`run_lab` called `git rev-parse HEAD` unguarded for its evidence header, and a
gate tree is a `git archive` extract with no repository, so it raised before
the lab did anything — all eight four-node reds of one gate had that single
cause. There is a `lab_revision()` now: `--revision`, else
`FN_GATE_REVISION`, else the rev-parse, and **it refuses rather than writing
"unknown"**, because an evidence file that cannot name what it is evidence
about is worse than no run. `tools/labs.py` passes `--revision` explicitly.
Verified in all four cases, including the refusal against a directory with no
`.git`.

**A fourth fake was missing.** The twonode dry run had never exercised the
TCPCLv4 phase at all: with no fake image build and no fake lab, the phase
always took the "no image" branch. Now that a failed build is a failed step
(§4) that branch had to become honest, so `tests/tcpcl_lab_fake` was added --
a `build_native_host.sh` that writes a stub and a `tcpcl_lab.py` that prints
the seven rows and a summary -- and both dry-run classes overlay it. 74 and 71
steps became 84 and 81. `FN_FAKE_TCPCL_DROP` names scenarios to leave out, so
the gate's "the lab produced no result for this scenario" path can be driven
on purpose.

## 2. The LTP lab: fixed, and it runs

`tests/ltp/run_fn_ltp_lab.py` passed on hbox.
`tests/evidence/2026-09-21-ltp-lab.md` and `.json`: request ADU 474 octets
crossing the LTP link byte-identically, receiver outcome `accepted`, receipt
regenerated, the staged copy deleted only after the durable receipt, 1 record
/ 1 article / 1 pin and the exact article bytes on the receiving store. ION
4.2.1-a.1 at `/tank/fn/ltp` exactly as `tests/ltp/pin.json` records, two nodes
over LTP/UDP on loopback, started and stopped by the lab's own scripts; both
were down when the run ended and `killm` was not used.

The repair goes through `encode_primary`, not through a default argument, and
what that costs is written into the lab's own `not_demonstrated` list and the
evidence file. ION's `bp_receive()` destroys the bundle inside the SDR
transaction it commits before it returns, so the block cannot be handed over.
What `BpDelivery` reports is the source EID and the creation timestamp, which
is exactly `fn-bpp-primary-identity-value` (`books/bp-primary.lisp`): source,
creation time, sequence. `IonStagingInbox.bundle` re-encodes those three
observed fields through ACL2's `fn-bpi-host-bundle-prefix`; every field it
supplies rather than observes — destination, report-to, flags, CRC type — is
one the identity projection provably ignores. **The identity fn staged under
came from ION's report of the bundle's fields, not from the octets that
crossed the link, and a transport that misreported those three fields would
be believed.** Closing that needs the block captured inside `fn_ltp_stage.c`
before `bp_receive()` returns.

`tools/bundle_bridge.encode_primary` gained the `ipn` endpoint form (the
laboratory registers only `ipn`; the previous caller, the mock BPA, is
`dtn`-scheme and is unaffected). `ipn_eid` is the exact inverse of the `ipn`
branch of the existing `_eid_text`. Before the hbox run, the seam was
round-tripped through ACL2 on the laptop: an `ipn`-sourced block encodes to 37
octets, `fn-bpi-host-bundle-report` reads back `ipn:1.1`, creation, sequence
and `live`, the same three fields under a different destination give the same
identity key, and a different sequence parts.

Two smaller limits, both recorded: `fn_ltp_stage.c`'s `/` → `_` substitution
is not invertible, so `observed_fields` refuses a non-`ipn` source rather than
guessing; and `--lifetime` is ION's TTL in seconds while RFC 9171 4.2.8's
field is milliseconds, written down in one named constant as a conversion
between two programs' argument units.

**One trap, paid for here:** never pipe `tests/ltp/start_node.sh` into
anything. The ION daemons it forks inherit the pipe and hold it open, so
`| tail` never sees EOF and the driving script wedges forever. The first hbox
attempt sat for seventeen minutes that way with node1 up and node2 never
started. Redirect to a file instead.

## 3. The caller-signature lint

`tools/harness_check.py`, one line in `make check`, about a second, no ACL2.
Three lints in one tool because they are one question asked of three corpora.

**`signatures`** binds every resolvable Python call in `tools/`, `tests/` and
`bin/` against the definition it names, the way CPython would at the call:
missing required parameters, unexpected keywords, too many positionals, a
parameter given twice. It resolves a call only when it can do so exactly — an
imported module attribute, an imported function, a constructor, or
`self.<method>` inside a class all of whose bases are in the corpus — and
counts what it declined rather than guessing. On this tree: **22719 calls,
3195 resolved, 19 undecidable (`f(*rest)`, `f(**rest)`), 0 findings**. It
gates.

Its hit list, which is the point: with the `bundle` argument removed again
from the LTP lab it reports, in one line,
`tests/ltp/run_fn_ltp_lab.py:109 receive_bpa_request: missing 1 required
argument: 'bundle'` and `defined at tools/run_bp_receive.py:113`. That is the
exact break, at the exact line, naming the exact definition. Every other
caller of `receive_bpa_request` in the tree — nine of them, in `tools/media.py`,
`tests/campaign/`, `tests/bp-dtn7/`, and five test files — was already correct.
`tests/test_harness_check.py` holds that case as a fixture so it stays caught.

**`acl2-arity`** asks the same question of two corpora no certification
reads: the 25 `ld`ed files under `host/`, and **ACL2 forms spelled inside
Python string literals**. The second is the sharper target and it found a
fourth dead harness. `d484e9a` gave `fn-served-open` a seventh formal and
updated both Lisp callers; `tests/test_served_differential.py:57` spells that
call as text, so all seven of its tests raised `FN-SERVED-OPEN takes 7
arguments ... given 6` instead of comparing bytes, and the bridge host and
`books/served` went a day with no divergence check running. The repair is
one argument, `(fn-auth-open-config)`, exactly as `host/reader-host.lisp:137`
passes it: **`python3 -m unittest tests.test_served_differential` is 7 of 7 in
2.4 s** where before it was 7 errors. Credit where it is due — the same
repair landed on `dev` from another lane while this one was measuring, and
the merge keeps dev's comment with a sentence naming the lint added to it.
What this lane contributes is the check that catches the next one.

918 applications over 25 host files and 371 readable Python strings, 262
undecided, **3 findings left**: `fn-sched-pos` at
`tests/test_teeth_check.py:58` and `:60` and `fn-feed-observe` at `:280`, all
synthetic fixtures for the teeth checker rather than calls anything makes.
They are another lane's fixtures and this lint does not gate, so they are
reported rather than edited. Two kinds of prose are skipped, each after it produced findings on the real
tree: a docstring (four of the first eight), and a sentence that merely
*mentions* a form — `"... the authenticated principal's allowance
(fn-auth-postingp, RFC 3977 section 6.3.1.1). The feed was never reached."`
parses, so a string counts only when every top-level item in it is a form,
which prose never is (two more, on dev's `tools/v0_matrix.py`, found by the
merge). A form holding a `{}` or a `%s` is not decided at all, because a
`" ".join(...)` in that slot stands for any number of arguments.

Are the two the same check? **The same question, a different mechanism, and
the answer decided the scope.** A book's arity is ACL2's own business —
`certify-book` refuses a wrong one — so books need no lint, and what let
`books/owner` stay unreadable was a *stale certificate being reported*, which
content-keyed certificates (`docs/proofs.md`) are the fix for. A host file is
`ld`ed and never certified, so nothing reads it until a bridge starts up,
which is the Python gap in Lisp. `tools/host_check.py` answers it dynamically
and only when `FN_ACL2` names an ACL2; this is the always-on static half. A
first version of this lint ran over `books/` too and produced 31 findings, all
of them artefacts of reading Lisp with a lint-grade reader (`#c(1 2)` read as
two tokens, `fn-defrecord-export`'s `:also` name lists read as applications).
That is itself the argument: a second reader of the books is a second opinion
waiting to go wrong, and it was dropped rather than papered over.

**`waivers`** is §4's lint; see below.

## 4. The waiver sweep

**32 skip sites under `tests/`, exactly as the brief said**, plus 35
harness-recorded skips under `tools/` and four non-unittest sites. Triage:

| class | tests/ | tools/ | what it is |
| --- | --- | --- | --- |
| environmental and honest | 28 | 4 | no ACL2, no openssl, not darwin, no `DTN7_REPO`, no python3.12, no `cryptography`, no native image, not a git repository. All say what is missing. **Left alone.** |
| capability probe | 0 | 9 | a surface this tree has not built, recorded with the observed reply. Left alone; one now carries a `waiver-ok:` declaration. |
| **waiver for a known defect** | **4** | **14** | the dangerous kind. Named below. |
| operator election / other | 0 | 8 | `--skip-previous`, `--nntplib-python none`, `transcribe_check`'s declared exemptions, `session_depth`'s reason-required waivers. Left alone. |

### The dangerous ones, individually

1. **`tests/test_fn_cli.py:157` — the one true named-text waiver, and it was
   stale.** `if "books/owner" in str(unavailable): self.skipTest(...)`, for
   the `fn-served-open` / `fn-served-make-conn` arity break. **The break is
   repaired** — `books/owner` certifies and `harness_check --lint acl2-arity`
   finds no disagreement in any `ld`ed host file — so the waiver had outlived
   its defect. **Removed**, not re-pointed.
   **And it was hiding something.** With it gone, `start_service` fails, in
   two different ways on two consecutive runs: once with no `LISTENING` line
   inside the harness's 300 s deadline, once, 11.6 s in, with `owner: ACL2
   bridge call marker did not precede its prompt / refused run the owner did
   not serve`. Started by hand outside the test the same service listens in
   20 s, so this is not a service that cannot start. **The second symptom
   has a known cause that is not the lab's**: `include-book` treats a STALE
   certificate as an ERROR where an absent one is only a warning, so the
   bridge dies before anything runs, and that is worth trying first
   (`python3 tools/certs.py install`, or certify the closure).
   `tools/labs.py` prints exactly that advice on any row whose output carries
   the string. **Claimed as `OB-FN-RUN-OWNER`
   and it is not this lane's**: the owner is whoever owns `tools/run_owner.py`
   and the `Acl2Store` call/prompt protocol. `tests/test_fn_cli.py` is
   honestly red until it is answered.
2. **`tests/test_stx.py:59`** — `if signed.returncode != 0: raise
   unittest.SkipTest(...)` on the *subject of the class*, so any defect in
   `tools/stx.py sign` turned the whole statement-carrier suite green by
   absence. **Now an `AssertionError`.** The only honest skip there is the one
   on the class, which is ACL2 being absent.
3. **`tests/test_owner.py:310` and `:353`** — the reason said "openssl is not
   available" and the predicate was `self_signed()` returning `None` on *any*
   non-zero exit: an openssl too old for `-addext`, a full disk, a broken
   `req`. **The predicate is now `shutil.which("openssl") is None`**, which is
   what the reason claims, and an openssl that is present and refuses raises
   with its stderr.
4. **`tools/deploy_gate.py:874`, `tools/twonode_gate.py:902`,
   `tools/inn_lab.py:1001` — "the server did not restart after recovery".**
   The worst of the set. A node that cannot come back after `recover` is a
   durability defect of the first order, and each was recorded as a
   not-exercised step. **The structural repair is in `deploy_gate.py`, which
   the other three subclass**: `not_exercised()` builds a step with `rc=None`
   and `Step.failed` cannot see one, so the gate printed `failed=0` and
   exited 0. There is now a second recorder, `did_not_complete()` /
   `Gate.broke()`, which records `rc=1` against `expect=0`. An absence is
   still an absence; a symptom is now a failure, and the row carries the
   symptom (`start_server` records why it did not reach LISTENING).
5. Converted with it, same reasoning, each named in a comment at the site:
   `deploy_gate.py:764` (the read-only reader did not reach LISTENING on a
   tree this gate deployed), `twonode_gate.py:940` (the native image build ran
   and failed) and `:965` (the lab ran and produced no row),
   `scale_gate.py:359` (an adopted series file that is there and unparseable),
   `:383` (the profile pass printed no JSON), `:415` (neither entry point
   served the store this gate built), `inn_lab.py:894` (nnrpd did not start)
   and `:1008` (innd never started, so the control scenario has no control).
6. **`tools/inn_lab.py:640`** (the peer record probe) is a capability, not a
   defect, and now says so with a `waiver-ok:` declaration naming
   `specs/peering.md` section 1.2 and the `(:set-peer record)` delta.
7. **Left as findings, with their reasons**, because they are cross-process
   and a static reader cannot see them: `tools/twonode_gate.py:233` and
   `tools/inn_lab.py:316` set `out["ok"] = True` when an `IHAVE`/offer draws
   `500`/`501`/`502`. `inn_lab` discharges that honestly — its skip at `:946`
   quotes both observed replies verbatim — and `twonode_gate`'s three at
   `:660`/`:663`/`:666` say only "peering: not available on this tree", with
   the observed reply one call away in the gap at `:652`. Folding that reply
   into the step's own reason is a small, worthwhile follow-up.
   `tools/live_service.py:522` drops a host from the rest of a run on a failed
   ship with a printed line and no record in the evidence file; same class,
   not converted here because `live_service` has no `Step` ledger to put it in.

### The new-waiver check

`harness_check --lint waivers` flags a skip whose predicate reads a **failure**
— a substring of an exception, a non-zero return code, an NNTP response code —
rather than a dependency, following one hop of intra-function assignment. A
flagged site may declare itself with a `# waiver-ok: <reason>` comment, in the
shape `tools/session_depth.py` already uses, and a waiver with no reason is
not a waiver; the reason must name a registry identifier, an expiry, an owner,
or a capability this tree has not built. **Every accepted declaration is
printed on every run**, so they cannot pile up unseen. On this tree after the
sweep: 33 skip sites, 32 environmental, 1 waiver, 1 declared, **0 findings**.
It gates.

## Evidence

- `tests/evidence/2026-09-21-ltp-lab.md` and `.json` — the hbox LTP run.
- `build/labs/<stamp>/report.json` and the per-lab `output.txt` — what
  `tools/labs.py` reported, per lab, with its reason.
- `python3 tools/harness_check.py` — 0 findings on all three lints; the
  counts above are its own.
- `python3 -m unittest tests.test_harness_check` — the lints' teeth: the
  historical `bundle` break as a fixture, a keyword typo, a `**kwargs` callee
  that must not be flagged, a failure-keyed skip, an environmental skip that
  must not be flagged, and a declared waiver that must not be flagged.
- `make check` green at each commit, including after the `dev` merge.
- On hbox: the lane tree is mirrored at `/tank/fn/lanes/w11-lab-gate` (tracked
  files only) with its ION run under `/tank/fn/ltp/run/fnlab-20260921T015951Z`
  and the start/stop/lab logs beside the mirror in `ltp-20260921T015951Z/`.
  Both ION nodes were stopped and verified gone; nothing this lane started is
  still running there. The mirror can be removed when the lane lands.

## Two notes for other lanes

**`tools/run_feed.py` is untouched by this lane.** `w11/one-owner` asked this
lane to confirm the deletion of it, and the disappearance of the fourth frame
integrity trailer with it. There is no such deletion here and no
modify/delete conflict against this branch: `git status` is fourteen modified
files and seven new ones and that file is in neither list, and
`git log -- tools/run_feed.py` on `w11/lab-gate` is dev's history unchanged.
All three trailer computations are still present in this tree --
`tools/run_feed.py:179`, `:184` and `:190`, each
`hashlib.sha256(...).digest()`, with `import hashlib` at `:39`. Whoever does
delete it, or moves any of it into `tools/feed_wire.py`, carries the
`fn-frame-trailer` ownership across; this lane cannot confirm a deletion it
is not making.

**Certificate staleness is not detected in advance, on purpose.** Pairs are
content-keyed and `tools/certs.py install` copies them out of the cache with
their original timestamps, so a file date says nothing: an mtime proxy called
62 of 62 books under the four-node lab's host files stale, in a worktree whose
lab then ran green. It was written, measured, and removed. What is left is
`DIAGNOSES` on the failing row.

## Open, and named

1. **`OB-FN-RUN-OWNER`** (claimed on the board): `tests/test_fn_cli.py`'s two
   service tests are red, in two distinct ways on two consecutive runs, and
   the service starts fine by hand in 20 s. Owner: `tools/run_owner.py` and
   the `Acl2Store` call/prompt protocol. Do not re-waive it.
2. **Nothing runs `make labs` automatically.** This lane built the target and
   deliberately did not wire the slow set into `make check`. The next step is
   a place that does run it — the wave's landing gate is the obvious one, with
   `--tier quick` before a merge and `--tier box --host <box> --require
   deploy,twonode` once per wave.
3. **The box tier has never been exercised through `tools/labs.py`.** Its
   preconditions and argument shapes were checked by hand and by the four dry
   runs; the first real `--tier box` run should be watched.
4. **`signatures` resolves 14% of call sites.** The rest are stdlib and bound
   methods. Resolving method calls on locally constructed objects would raise
   it a lot and needs a small type inference; worth doing only if something
   breaks that this misses.
5. **Three `acl2-arity` findings remain** and are another lane's:
   `fn-sched-pos` at `tests/test_teeth_check.py:58` and `:60` and
   `fn-feed-observe` at `:280`, synthetic fixtures for the teeth checker
   spelled with the wrong arity. Nothing evaluates them, so they are not a
   defect; spelling them correctly would let `acl2-arity` gate as the other
   two lints do.
6. **The gates' response-code waivers** (item 7 above) are the last
   failure-keyed verdicts, and they are cross-process. The cheap improvement
   is to put the observed reply into each skipped step's own reason, the way
   `inn_lab.py:946` already does.
