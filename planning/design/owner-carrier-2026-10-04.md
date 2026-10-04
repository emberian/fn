# OWNER CARRIER decision file, 2026-10-04 (lane/carrier, Fable; wave 3 packet 4)

For the advisory consultation (`planning/design/README.md`; Codex/Astra is out until 10-08, so the
other model is Kimi, section 9). Paths are relative to the lane worktree
`/Users/ember/dev/fn/build/lanes/carrier` (base origin/dev `d4e53323c`).

The question the brief sets (FN-SWARMPLAN-20261004 section 4 wave 3 row 4, section 6 D40 row):
which of the two carriers is the successor -- dev's `fn-ost-*` stobj book plus `thread.py`, or
`lane/stage-5b-carrier@fa32ac06f`'s rewritten books -- or whether the answer is the sf-statep idiom
change (`sf-statep-idiom-2026-10-03.md` option 1: unconditional store-file steps with shape
guards); what the owned invariant IS as a carried stobj field given ACL2 8.7's refusal (D40's
finding); which of the 338 owed writers get a preservation theorem, which are deleted, which stay
`proof-owed`; the migration order and what the RAW-DISPATCH lane lands first.

**The lean, in one line: the idiom change is the successor; the stobj is not on the critical
path; dev's book and `thread.py` are kept as the eventual physical carrier; stage-5b's `xf.py`
branch is retired as an input. Sections 3 to 7 say why and what the first slice is.**

## 0. Coordinates and measurements (nothing here is new; it is what the decision rests on)

**The exposure.** COST-GATE (handoff `planning/handoff-2026-10-03/cost-gate.md`, image set
`45e05c7fd`, guards on, tmpfs, 2 KiB POSTs): `fn-owner-io` is called twice per POST and costs 92 ms
and 11.8 MB per call at N=1000 articles, fitted exponent 1.0; 99.9 % of it is the executable
counterpart evaluating the entry guard `fn-sn-statep` of the live Store: `fn-sf-record-listp` 63 ms,
the success keyset 24 ms, `fn-node-statep` 3.5 ms. Extrapolated: about 9 s and 1.2 GB per call at
100k, 18 s per POST. Every other entry guard on the POST path is flat (O(article), 1.3 to 3.3 ms).

**What dev does about it today (POST-GUARD-OFF, `812082a53`; D40 "source implementation status").**
Nine owner entries are declared `:raw-with (:carried fn-owner-served-carried :assuming
A-OWNER-INVARIANT-CARRIED)` in `host/interfaces.lisp` (`fn-owner-io`, `-take`, `-control-submit`,
`-prepare-retention`, `-prepare-identity`, `-prepare-consumer`, `-prepare-topic`, `-known-abort`,
`-refuse-reservation`; `planning/interfaces.json` `raw_dispatched` lists 15 names, the other six are
`fn-hist$p-*`/`fn-hroot-*` over an abstract-stobj correspondence and are not this packet's). The raw
definition runs; the counterpart's guard walk is skipped; the justification is the carried relation
`fn-owner-retain-statep` (`books/owner-retain-transitions.lisp`):

```lisp
(defun fn-owner-retain-statep (state)            ; proof-only, never executed on a served path
  (and (boundp-global 'fn-owner state)
       (fn-lgoc-invariantp (fn-owner-ocfg state))
       (fn-prc-carryp (fn-owner-retain-carry state))))
```

established at the recovery install under A-RECOVERED-OPEN, preserved by thirteen writers
(`host/owner-retain-host.lisp`, the pilot's three prepares), concluding each entry guard
(`fn-owner-retain-statep-implies-entry-guard`). The carried state is the whole ACL2 `state`, so
`def-carried`'s completeness counts every host-called entry that returns `state` as a writer: 338
are owed by name under the `:incomplete (A-OWNER-INVARIANT-CARRIED (...))` escape in
`host/owner-served-carried.lisp:94`; 25 `PGO-OWED-*` ledger items (`slice: carrier`) sum 332 of
them. A-OWNER-INVARIANT-CARRIED is "a temporary native dispatch trust marker" (specs/failures.md):
nothing proves the skipped guard holds at the call.

**Why the guard cannot be narrowed in place (the stage-5b finding, confirmed by reading).** The
whole chain under `fn-owner-io` carries `fn-sn-statep` only because of two `mbe` layers:

```
fn-owner-io (host/owner-host.lisp:1680)        :guard (and (boundp-global 'fn-owner state)
                                                            (fn-sn-statep (fn-sbud-oc-store (fn-owner-ocfg state))))
  fn-olr-ocfg-reserve / -order (owner-log-route.lisp:60,70)   :guard (fn-sn-statep (fn-own-store (fn-ocfg-owner oc)))
    fn-rcon-ocfg-io (records-concrete-owner.lisp:33)          :guard (fn-sn-statep (fn-own-store (fn-ocfg-owner oc)))
      fn-rcon-own-store-io (:25)                              :guard (fn-sn-statep (fn-own-store o))
        fn-rcon-sn-io (records-concrete.lisp:404)             :guard (fn-sn-statep s)
          body: (if (mbe :logic (fn-sn-statep s) :exec t) (fn-sn-update s (fn-rcon-sn-file-step ...) node) s)
          fn-rcon-sn-file-step (:380)                         :guard (fn-sf-statep files)
            fn-sf-start-frontier, -frontier-file-result, -frontier-replace-result, -frontier-dir-result,
            -record-file-result, -record-link-result, (fn-rcon-)-record-dir-result, -recovery-barrier
              (store-files.lisp:686-830, 1135)                :guard (fn-sf-statep s)
              body: (if (and (mbe :logic (fn-sf-statep s) :exec t) (equal (fn-sf-phase s) PHASE)) STEP s)
```

An `mbe`'s obligation is `guard => (logic = exec)`, so each step's guard must imply `fn-sf-statep`,
each caller's guard must imply the callee's, and the whole-log walk is forced up to the host entry,
where the counterpart evaluates it once per call. Every accessor and constructor on this path
(`fn-sf-phase`, `-frontier`, `-barriers`, `-record-candidate`, `-frontier-candidate`,
`-records-field`, `fn-sf-remake`, `fn-sf-make-fields`, `fn-sfr-snoc`, `fn-sf-record-pair`,
`fn-sn-update`, `fn-sn-files`, `fn-own-make`, `fn-own-refresh`, `fn-ocfg-with-owner`) has guard `t`.
The only arithmetic is `(< (fn-sf-frontier s) *fn-sf-max-uint*)`, `(1+ (fn-sf-frontier s))` and
`(1+ (fn-sf-barriers s))`. So, with the `mbe` conjunct gone, the honest guard of the eight io steps
is O(1): the two counters are naturals.

**The idiom census** (the sf-statep file asked "find every instance"): 54 sites of
`(mbe :logic (R s) :exec t)` across 19 files and six recognizers:

| recognizer | sites | files |
|---|---|---|
| `fn-sn-statep` | 27 | store-node.lisp (9), owner-commit-carried (3), owner-prepare-deferred-carried (3), identity-retain-carried (2), store-node-resolution (2), catalog-commit, config-physical-replay, node, owner-prepare-carried, post-identity-index, post-prepare-catalog, post-retain-carried, records-concrete, replay-identity-index, replay, store-observed, store-prepare-correspondence (1 each) |
| `fn-sf-statep` | 17 | store-files.lisp (15), records-concrete (1), host/owner-served-carried (1, in a comment) |
| `fn-node-statep` | 4 | |
| `fn-retain-statep` | 3 | |
| `fn-cnode-statep` | 2 | |
| `fn-exchange-statep` | 1 | |

Only three theorems in the tree USE the identity off the invariant (`(not (fn-sn-statep ...))`
or `(not (fn-sf-statep ...))` in a statement): `fn-si-prepare-off-state-is-identity` (local,
store-intern.lisp:958, about `fn-sn-prepare`), `fn-hma-finish-outside-the-state-is-a-stutter`
(local, held-message-id-answer.lisp:99, about finish) and store-observed.lisp:217 (recovery). None
is on the io path. The step family's own theorems are all `(implies (fn-sf-statep s) ...)`
(`fn-sf-start-frontier-preserves-state` and 2 more in store-files.lisp; the record-dir case in
store-files-invariants.lisp:722); `fn-sn-io-cannot-acknowledge` is unconditional and holds by
frame on both arms. Fan-in of the eight steps: 34 to 37 books each (overlapping), 31 books mention
`fn-sn-file-step`; `fn-sn-io` is mentioned in 12 further books (productive-contract 32,
store-node-traces 28, topic-history-store-invariants 27, config-store-steps 24, ...).

**A trap for "shape guards".** `fn-sf-shapep` (store-files.lisp:77) is NOT O(1): it contains
`(fn-sfr-canonp (nth 4 x))` and `(fn-sl-canonp (nth 7 x))`, and `fn-sl-canonp h` is
`(equal (fn-sl-of (fn-sl-list h)) h)`, which rebuilds the snoc-list twice (O(N), allocating).
A guard is chosen by reading what the body needs, never by a predicate's name.

**The two carriers, as they are.**

| | dev: `books/owner-carrier.lisp` + `tools/owner_carrier/` | `lane/stage-5b-carrier@fa32ac06f` |
|---|---|---|
| stobj | `fn-owner-st` (`fn-ost-ocfg`, `fn-ost-installedp`, `fn-ost-carry`), accessors renamed `fn-ost-*`; 60 lines; "becomes authoritative only at the atomic caller-threading migration" | same three fields; accessors keep the OLD names (`fn-owner-ocfg`, `fn-owner-install-ocfg`, ...) so tier-A hints survive |
| rewriter | `thread.py` (303 lines): refuses rather than guesses (unknown binding/output syntax, non-literal state, direct global write, `case`/`stobj-let`/`er` tails, guard hints); preserves theorem events untouched; writes only a NEW output directory; input hashes bound to a loaded-world snapshot (`world.lisp` `fn-ocw-snapshot`: the closure of every function whose body or guard reaches the four owner globals); 9 tests pass | `xf.py` (369 lines): classifier R/O/M; rewrites formals, stobjs, guards, bindings, call sites AND theorem events; mis-rewrites `(:instance THM (var term))` hint pairs; `sigs2.txt` dumped from an image world 1,058 commits behind dev; scratch paths hard-coded in `run.py`/`hand.py` |
| state | no migration run; two codex branches (`codex/owner-carrier-current-20261003`, `-refusal-20261003`) carry tests and a native ABI probe, nothing more | 8 books admitted from source on hbox; `owner-connection-callbacks`, the refinement book, `owner-host` in the image world and the tests never admitted; does not build |
| the writer set it would make exact | 277 touchers, 104 writers (69 `:program`, 35 compliant); 41 host-called writers (23 `:program`); 151 host-called touchers -- stage-5b's dump, stale but indicative | same dump |

Two structural facts about ANY global-to-stobj move, which neither tool changes: (1) it is atomic
-- every reader of `'fn-owner` must switch in one commit or the owner has two authorities
(both tools' authors say so: "one held batch, not rebased"; "authoritative only at the atomic
migration"); (2) it does not shrink the proof debt, it makes the writer list exact: 104 writers of
which 69 are `:program` and can carry no theorem until converted. Raw dispatch over the carried
relation stays a trust marker until every one is proved.

**ACL2 8.7's refusal, exactly** (`~/tools/acl2-fn/acl2-8.7/other-events.lisp`): `chk-defstobj-attachments`
(line 20938) refuses a `defstobj` "because the stobj recognizer ~x1 would depend on the function~s ~&2,
which ha~s attachments. See :DOC stobj-attachment-restrictions"; `chk-defabsstobj-attachments` (24504)
refuses a `defabsstobj` with an attached ancestor of "the correlation or recognizer function" (or of the
creator and exports when there is no `:corr-fn`). `fn-digest` is attached
(`books/crypto-attach.lisp:75`, `(defattach fn-digest fn-blake3-stobj)`); `fn-lgoc-invariantp` reaches it
through `fn-cst-relation` (the node compared to the replay of every event) and the records' digests. So
neither a field `(:type (satisfies fn-lgoc-invariantp))` nor an abstract stobj whose `:logic`
recognizer is the invariant is admissible, and the same holds for `fn-sn-statep` as the Store's
recognizer whenever the Store becomes a stobj.

## 1. The rule today and why it came up

AGENTS.md: "No whole-state revalidation on a served path: carry the invariant in state and prove it
preserved." D40: the host may call the raw definition when the skipped guard conjuncts are carried
conjuncts, established, preserved by every writer, and concluded from the relation. POST-GUARD-OFF
applied D40 with the preservation half waived under a named escape, because the honest writer set
could not be computed over `state` (every state-returning entry) and the carrier move that would make
it computable does not build. The design question (Astra's, 10-03): is the better long-run design the
idiom change (1), or is raw dispatch over the carrier (2) sufficient?

## 2. The options

**(A) Raw dispatch over a stobj carrier** (stage-5b's plan, tiers B/C after the move). Cost: the atomic
move (277 touchers; 10 to 15 lane-days, in progress since 10-02, not building), then program-to-logic
for 69 writers, then 104 preservation theorems, then the escape is retired. Until the last theorem the
trust marker stays. The guard `fn-sn-statep` remains on every function in the chain; it is skipped,
not removed; a developer or test that evaluates it still pays O(N).

**(B) The idiom change, per served chain.** Delete the `mbe` conjunct from the kernel steps a chain
reaches; give each step the O(1) guard its body needs; the chain's guards weaken to that; the host
entry's guard loses `fn-sn-statep`; the counterpart evaluates an O(1) guard; nothing is raw-dispatched
for cost. The `-is-` twin equalities (`fn-rcon-sn-io-is-sn-io`, `fn-rcon-ocfg-io-is-ocfg-step`,
`fn-rcon-sn-file-step-is-sn-file-step`) stay UNCONDITIONAL because the abstract and the concrete side
share the same kernel steps and both lose the `mbe` together; the preservation theorems keep their
`(implies (fn-sf-statep s) ...)` statements; what changes logically is only the step's value OFF the
invariant (no longer the identity), which three local lemmas use, none on the io path. Cost: for
`fn-owner-io`, five books and one host guard (section 7); for the rest of the owner's entries, the
remaining 9 `fn-sf` and 27 `fn-sn` sites, chain by chain. Fan-in certification: `store-files`' closure
(most of the tree), once per slice, on the farm.

**(C) The Store as a stobj with an attachment-free recognizer** (`fn-sn-statep` as the stobj's
recognizer would be free in every guard: a stobj formal's recognizer is never evaluated). This is the
representation stage (D41, ST2 to ST5), not this wave; section 4 names what it needs.

## 3. The lean: (B), with (A)'s book and tool kept for the owner's eventual physical form

1. (B) is literally ember's answer ("we can just not have that guard"): the whole-state check leaves
   the guard instead of being skipped under a marker. After S4 (the rows deleted) there is nothing
   for A-OWNER-INVARIANT-CARRIED to cover on the converted chains and the 338 owed writers stop
   being a DISPATCH-soundness debt (section 5 says what they become). Between S1 and S4 the
   converted entry's row still skips its (now O(1)) conjunct under the same marker: the debt is
   unchanged until S4 (section 9, G2b and G6c).
2. (B) is incremental per served entry; (A) is atomic by nature, which is why two attempts and ~12
   lane-days have produced no landed migration.
3. (B) is strictly safer at runtime. Under (A) a violated invariant makes raw execution unfaithful
   (callees' guards assumed, safety-0 code on a value they were not verified for). Under (B) the
   shape guard IS checked; a violated semantic invariant yields a faithful computation of the logical
   function on an off-invariant state: a wrong answer at worst, never undefined behaviour. The
   invariant is proof-time under both; (B) does not pretend otherwise.
4. The idiom "IS the whole-state revalidation AGENTS.md forbids, pushed down a layer"
   (sf-statep-idiom-2026-10-03.md). (A) hides it behind a dispatch table; (B) removes it.
5. (A)'s real value, an exact writer set, is available without the stobj: the installer closure
   (section 5), which dev's `world.lisp` already computes.
6. The stobj is still the right physical form for the owner's state once its representation is
   decided (D41 stage "owner": pages, the resource vector). When that stage comes, dev's
   `books/owner-carrier.lisp` and `thread.py` are the tool: the refusing rewriter with
   snapshot-bound inputs is the better engineering, and the migration is run ONCE on then-current
   dev, never rebased. `lane/stage-5b-carrier` is retired as an input: its classifier is subsumed
   by `thread.py`'s signature flags, its dump is stale, its hint rewriting is wrong.

What (B) does NOT claim: it does not make any served entry O(1) whose BODY walks the store (e.g. a
prepare whose logical spec replays the history: `fn-sf-prepare-record` calls
`fn-sf-history-recoverablep`; the concrete prepare the host calls goes through the live node, which
is why COST-GATE measured it flat, but each chain is read before it is converted). Those are
representation items for the ST-stages and are named, not hidden, when found.

## 4. What the owned invariant IS as a carried field: the exact workaround

The invariant is NOT a stobj type, and cannot be (section 0, ACL2 8.7). The workaround both
carriers already use, and the one `def-carried` exists for (section 9 lists the alternatives):

- the carrier's fields are untyped (`:initially nil`), its recognizer (`fn-owner-stp`) is structural
  and attachment-free;
- the semantic relation is a plain `:logic` predicate over the carrier, never executed on a served
  path (`fn-owner-retain-statep` over `state` today; `fn-ost-retainp (fn-owner-st)` :=
  `(and (fn-ost-installedp st) (fn-lgoc-invariantp (fn-ost-ocfg st)) (fn-prc-carryp (fn-ost-carry st)))`
  when the stobj lands);
- it is carried by theorem through `def-carried`: `:established` at the recovery install
  (`:ok :recovering`, `:produced` by the two recover functions under A-RECOVERED-OPEN, `:witness`
  the empty history's open), `NAME-FN-carries` per writer, `:concludes` bridges to each entry guard's
  carried heads;
- completeness is over the EXACT writer set: `stobjs-out` once the stobj exists, the installer
  closure before it (section 5).

For the Store itself (option C, the ST-stages): its stobj recognizer must be attachment-free, so
`fn-sn-statep` splits as the index already does under D21 (`fn-sn-indexedp` is "deliberately NOT
here"): shape and structure in the recognizer, digest agreement and replay agreement
(`fn-cstp-carriedp`, `fn-ocl-relation`) carried by theorem. Record it in `specs/owner.md` now so
ST2/ST3 do not rediscover the refusal.

## 5. The 338 owed writers: criterion, then disposition

They are owed by the conservative criterion "host-called and returns `state`". The exact criterion:
F is a writer iff F's closure (bodies and guards, `:logic` and `:program`, through attachments)
reaches `put-global`/`f-put-global` of `'fn-owner` or `'fn-owner-retain-carry`, or a `put-global`
with a non-literal key, or one of the installers (`fn-owner-install-ocfg`, `fn-owner-install-open-ocfg`,
`fn-owner-retain-carry-put`). Raw Lisp cannot reach the globals except through a dispatched entry
(`tools/raw_dispatch_rule.py`; a grep of `host/native/*.lisp` finds no `fn-owner-install-ocfg` or
`'fn-owner` put). `tools/owner_carrier/world.lisp` (`fn-ocw-direct`, `fn-ocw-close`,
`fn-ocw-snapshot`) computes exactly this closure in the loaded world; it needs two extensions (a
non-literal key and an attached function in the closure count as writers).

| class | count at the stale dump | disposition |
|---|---|---|
| host-called, returns state, NOT in the installer closure | about 297 of 338 | **deleted** from the owed list; their `PGO-OWED-*` rows closed `refuted: not a writer of the owner's globals (installer closure)`; no theorem: a function that cannot write the globals preserves the relation by the stobj/closure discipline, which the generator checks, not a per-function proof |
| host-called writer, `:common-lisp-compliant` | 18 (13 already proved + the pilot's 3; the rest: `fn-owner-finish`, `-finish-identity`, `-finish-submission`, `-open`, `-reconfigure-unstage`, `-set-auth-config`, `-orcp-swap`, `-recover-from-store-open`, ...) | **preservation theorem** `(implies (fn-owner-retain-statep state) (fn-owner-retain-statep RET))` by the tier-A pattern (`host/owner-retain-host.lisp`: the configured-owner keystone from `books/owner-host-relation.lisp`'s COVERAGE table plus the frame lemmas) |
| host-called writer, `:program` | 23 | **proof-owed** by name, one item per file as today, until program-to-logic (each a slice: `fn-owner-finish-submission`, `-outcome`, `-transit-outcome`, `-exposure-open`, `-posting-configure`, `-install-profile`, `-reconfigure-complete`, `-recover-from-store-open`, `-tls-established`, the feed and account arms) |

Regenerate the three lists at landing from `fn-ocw-snapshot` in the image world (the dump above is
from `89c779f78`); the numbers in this file are the shape of the answer, not its value.

`def-carried` then retires the `:incomplete` escape for this row: completeness is declared by
closure (`:writers (:closure (fn-owner-install-ocfg fn-owner-install-open-ocfg fn-owner-retain-carry-put))`,
name to be fixed with the generator's owner), a `:program` writer is refused BY NAME (no silent
waiver), and A-OWNER-INVARIANT-CARRIED is deleted from specs/failures.md. Under (B) this ledger is
CLAIM coverage -- "the keystones' hypothesis holds at every served call" -- and no execution rests
on it.

## 6. Migration order, and what the RAW-DISPATCH lane lands first

| step | what | files | who |
|---|---|---|---|
| S1 (this lane, now) | `fn-owner-io` off the whole-state guard: the eight io steps unconditional with `:guard (fn-sf-countersp s)`; `fn-sn-io`, `fn-sn-file-step`, `fn-rcon-sn-io`, `fn-rcon-sn-file-step`, `fn-rcon-sf-record-dir-result`, `fn-rcon-own-store-io`, `fn-rcon-ocfg-io`, `fn-olr-ocfg-reserve/-order` guards weakened to it; `fn-owner-io`'s guard loses `fn-sn-statep`; the served row's `:concludes` gains the bridge for the new head | `books/store-files.lisp`, `books/store-node.lisp`, `books/records-concrete.lisp`, `books/records-concrete-owner.lisp`, `books/owner-log-route.lisp`, `host/owner-host.lisp` (one guard), `host/owner-served-carried.lisp` (one `:concludes` line), a teeth book | carrier |
| S2 | the take/prepare/refuse/known-abort chains (`fn-sn-prepare`, `-refuse-reservation`, `-known-abort`; `fn-sf-refuse-reservation`, `-prepare-record`, `-prepublish-abort`, `-abort-completion`; the `fn-sn-statep` sites in the `*-carried` books) | same shape, per chain | carrier |
| S3 | the finish and recovery chains (`fn-sn-finish`, `fn-sf-core-completion`, `-emit-success`, `:replaying`/`:recovering`) | same | carrier |
| S4 | delete the nine owner `:raw-with` rows, A-OWNER-INVARIANT-CARRIED, the `:incomplete` escape; `RAW_OWNER_ENTRIES` 7 -> 0 in `tests/test_native_owner.py`; the trap stays for the `fn-hist$p` rows | `host/interfaces.lisp`, `specs/failures.md`, `host/owner-served-carried.lisp`, the test | carrier, after RAW-DISPATCH's exit, announced |
| S5 | `def-carried` completeness by closure; the owed-writer disposition of section 5 | `books/def-carried.lisp`, `tools/owner_carrier/world.lisp`, the ledger | carrier (generator owner consulted) |
| S6 (ST-owner, later) | the stobj move with `thread.py` over dev's book, once, on then-current dev | `tools/owner_carrier/`, `books/owner-carrier.lisp`, the host | whoever owns the owner's representation stage |

**Collision rule with RAW-DISPATCH** (the D40 trap and the `:raw-with` rows, now): S1 does not touch
`host/interfaces.lisp`, `books/definterface.lisp`, `books/def-carried.lisp` or
`tests/test_native_owner.py`. After S1, `fn-owner-io`'s row is still LEGAL by D40's checker (its guard
keeps one carried conjunct, `fn-sf-countersp` over the owner's store, concluded by the row's new bridge)
and is a no-op (it skips an O(1) check); the trap has nothing to trap for that entry and everything it
had for the eight others. RAW-DISPATCH lands its trap and row edits first; S4 removes the rows after
its exit. The one file both lanes may touch in S1 is `host/owner-served-carried.lisp` (`:concludes`,
one line): announced before the push.

**Composition lane**: S1 moves `store-files`/`store-node` bytes near the root of the image closure.
Their recipe pins a sha; the integrator merges S1 after their next push; the farm run for S1's closure
is one run (`farm.py submit hbox --affected-by books/store-files`), not per book.

## 7. The first slice, statement-first

The entry: `fn-owner-io` (POST's io, the measured exposure). "Moved onto the carrier" means: its guard
no longer walks the store; the carried relation (the `def-carried` row) still concludes its guard;
its preservation theorem is unchanged and still proved.

**Props** (each with its ATLAS fields: satisfiable, teeth, premise-inhabited):

- P1 (new definition) `fn-sf-countersp s := (and (natp (fn-sf-frontier s)) (natp (fn-sf-barriers s)))`,
  guard `t`, O(1). P1a `fn-sf-statep-implies-countersp`. Satisfiable: `(fn-sf-initial-state)`;
  non-vacuous: `(fn-sf-make :ready 0 nil 'junk nil nil nil 5)` satisfies it and fails `fn-sf-statep`.
- P2 (changed definitions) the eight io steps with `(declare (xargs :guard (fn-sf-countersp s)))` and
  the `mbe` conjunct deleted; `fn-sn-io`, `fn-rcon-sn-io` likewise (`:guard (fn-sf-countersp (fn-sn-files s))`);
  `fn-sn-file-step`, `fn-rcon-sn-file-step`, `fn-rcon-sf-record-dir-result`, `fn-rcon-own-store-io`,
  `fn-rcon-ocfg-io`, `fn-olr-ocfg-reserve`, `fn-olr-ocfg-order` guards weakened to the same head over
  their store; `fn-owner-io`: `:guard (and (boundp-global 'fn-owner state) (fn-sf-countersp (fn-sn-files (fn-sbud-oc-store (fn-owner-ocfg state)))))`.
- P3 (existing statements, unchanged, re-proved): `fn-sf-<step>-preserves-state` (8),
  `fn-sn-io-preserves-state`, `fn-sn-io-cannot-acknowledge`, `fn-rcon-sn-io-is-sn-io`,
  `fn-rcon-sn-file-step-is-sn-file-step`, `fn-rcon-ocfg-io-is-ocfg-step`,
  `fn-olr-ocfg-reserve-is-the-file-route-by-definition`, `fn-lgoc-log-reserve/-order/-rcon-io-preserves-invariant`,
  `fn-owner-io-preserves-retain-state` (the Prop the brief names; `host/owner-retain-host.lisp:214`),
  `fn-owner-io-refuses-an-unsafe-observation` (its teeth, :229).
- P4 (new bridge) `fn-owner-retain-statep-implies-io-guard`:
  `(implies (fn-owner-retain-statep state) (fn-sf-countersp (fn-sn-files (fn-sbud-oc-store (fn-owner-ocfg state)))))`,
  from `fn-owner-retain-statep-implies-entry-guard`, `fn-sn-statep`, `fn-sf-statep-implies-countersp`;
  added to the served row's `:concludes` so D40's checker still accepts the (now no-op) row.

**Teeth** (`tests/acl2/store-files-counters-tests.lisp`): T1 the identity off the invariant is gone
and observable: on a `countersp`-but-not-`statep` state in phase `:ready`, `fn-sf-start-frontier`
answers phase `:frontier-staged` (before: the identity); T2 world facts: the guards of
`fn-sf-start-frontier`, `fn-sn-io`, `fn-rcon-sn-io` mention none of `fn-sf-statep`, `fn-sn-statep`,
`fn-sf-record-listp`, `fn-sf-success-listp` (`all-fnnames` of `(guard F nil (w state))`); T3 the
preservation theorems under `fn-sf-statep` hold on the existing fixtures (`store-node-tests.lisp`,
`store-files-teeth-tests.lisp` unchanged and green).

**Measurement protocol** (REPL, laptop pool): a store of N records built with `fn-sf-make`/`fn-sn-make-v6`
from records satisfying `fn-sf-record-listp` (sequence i, txid i, generation i) and successes
`((i . i) ...)`, node `fn-sf-replay-node` once; `(fn-sn-statep s)` asserted T (the fixture is a state;
COST-GATE's lesson); `time$` of the OLD guard `(fn-sn-statep s)` and the NEW guard
`(fn-sf-countersp (fn-sn-files s))`, ten evaluations each, N = 1,000 and 10,000. The native POST
figure: before = COST-GATE's image-set numbers (4/8/30 ms per POST at N = 30/200/1000 guards on;
the raw-dispatched dev build is the current baseline); after = the integrator's next batch image
(`tools/cost_gate.py` window or `tests.test_native_owner` served-POST timing), run id in the lanedump.

**Gate**: `tools/remote_check.sh auto --target check-lane`; `tools/farm.py submit hbox --affected-by
books/store-files` and `green_check --strict` for the closure; the REPL admission of every changed book
form by form; a theorem that does not go through is a `proof-owed` item naming it, filed in the same push.

## 8. What would change the lean

- If the fan-in certification shows the identity off the invariant is load-bearing in a KEYSTONE
  (not a local lemma) -- e.g. a crash-model cut theorem stated without `fn-sf-statep` -- restate it
  under the hypothesis; if that weakens the keystone's claim, stop, record it here, escalate.
- If the trap lane needs a raw-dispatched OWNER entry as its test subject after S4, keep one row by
  agreement (the `fn-hist$p` rows should suffice).
- If a served chain's BODY is O(N) (section 3's caveat), (B) fixes nothing there; it becomes an
  ST-stage item, named in this file.
- If the generator's owner refuses completeness-by-closure as unsound (an ACL2 route to a global
  this file missed), the escape stays for exactly the named route and section 5's deletions do not
  happen; the dispatch soundness argument of section 3 is unaffected (nothing is skipped).

## 9. Advisory consultation (completed 2026-10-04, carrier2)

Two reviews, both on the same prompt (this file as it stood at `b7195275e`, the pasted
definitions, and the S1 diff and teeth book; no tools, no web, an empty directory; the prompt is
78 KB). **grok-4.7** (`grok --prompt-file ... --tools "" --no-subagents --disable-web-search`)
and **Kimi K2.7** (`kimi -p ... --agent-file reviewer.md --skills-dir <empty>`; it finished this
time, inside the 50-minute cap) each returned numbered findings. Below, each finding with the
answer and the witness for that answer.
(F = finding; G = grok, K = Kimi.)

| # | finding | verdict | answer and witness |
|---|---|---|---|
| G1a | S1 must delete `fn-sn-io`'s and `fn-rcon-sn-io`'s own `mbe` too, or their guards cannot weaken | AGREE (it was the plan, P2) | done in `a10f9c6c7`: both bodies are now the unconditional `fn-sn-update`; `verify-guards fn-sn-io` / `fn-rcon-sn-io` take no hints |
| G1b, K2 | `fn-rcon-sf-record-dir-result`'s `:use fn-sf-statep-implies-shapep` hint suggests the body needs shape (O(N)) | REFUTED | `fn-rcon-sf-record-pair` is `:guard t` (records-concrete.lisp:172), as are `fn-sfr-snoc`, `fn-sf-make-fields`, `fn-sf-records-field`, `fn-sf-successes-field`; the hint was decoration and is deleted; the function now has guard `fn-sf-countersp` with no hints, and it verifies (certify run in the lanedump) |
| G1c | accessors are `:verify-guards nil` | REFUTED | they are verified before the steps (store-files #22-#33); the REPL admitted every step's `verify-guards` (#165-#194) |
| G2 | `fn-sf-countersp` is not preserved: the frontier directory result installs the candidate as the frontier; the reserve composite's chained guard needs a preservation lemma | AGREE (the lemma was missing) | added `fn-sf-io-steps-keep-countersp` (every io step but the directory result keeps the guard; REPL #195), `fn-sn-file-step-keeps-countersp`, `fn-sn-io-keeps-countersp`, `fn-rcon-ocfg-io-keeps-the-store-counters`; the reserve chain is start, file, replace (each keeps it), then dir (needs it only on entry). An off-invariant `:log-reserve` can leave a junk frontier; the NEXT call's guard is then false |
| G2b | while the `:raw-with` row stands, that next call runs raw and `<`/`1+` on a non-number is a Lisp error, not "a wrong answer"; section 3.3 overclaims for S1-S3 | AGREE, scoped | section 3.3's safety claim holds after S4, not before; between S1 and S4 the skip rests on the carried relation exactly as today (it implies the new head through `fn-owner-retain-statep-implies-io-guard`). Section 3.1 is corrected above |
| G3 | the twins stay unconditional only if the deletion is lockstep; the predecessor's diff was not (`fn-rcon-sf-record-dir-result` kept its `mbe`) | AGREE | lockstep in `a10f9c6c7`: `fn-rcon-sf-record-dir-result`, `fn-rcon-sn-io` lose the `mbe` with their kernel twins; the unconditional `-is-` theorems are re-proved unchanged in the certify run |
| K3 | an abstract wrapper on the `:io` path (`fn-snt-step`, `fn-snrt-step`, `fn-own-store-step`) may carry its own `fn-sn-statep` `mbe` and break `fn-rcon-ocfg-io-is-ocfg-step` | REFUTED by reading | store-node-traces.lisp:608 (`fn-snt-step`), store-node-resolution.lisp:593 (`fn-snrt-step`), owner.lisp:2143 (`fn-own-store-step`), owner.lisp:3154, owner-config.lisp:689: their `mbe`s are only over `car`/`cadr` of the event, never `fn-sn-statep`; the theorem's re-proof is in the certify run |
| G4, K4 | the installer-closure criterion misses writer routes: `makunbound-global` (falsifies `boundp-global 'fn-owner`); a quoted form evaluated by `trans-eval`, `magic-ev-fncall`, `ev-fncall`, `ld` (`fn-ocw-callees` stops at `fquotep`); raw code through `return-last`/`progn!` under a ttag; attachments; the snapshot is an unproved `:program` tool | AGREE | section 5's criterion becomes conservative (section 5a below): every such route makes a function a writer, and a function whose closure reaches an unknown body (no `unnormalized-body`, not a known primitive) is a writer. The deletions happen only for functions the scanner proves free of every route |
| G4b | `unnormalized-body` holds `f-put-global`; `put-global` is the macro, so `world.lisp` misses direct puts | REFUTED | in the REPL (ACL2 8.7), `(getpropc 'f-put-global 'macro-body)` is `(cons 'put-global ...)`, and `put-global` has formals `(key value state-state)`: `put-global` is the function, `f-put-global` the macro. The same session shows `makunbound-global` is a function `(x state-state)`, which is the route G4/K4 name |
| G4c | `world.lisp` counts readers (`get-global`, `boundp-global1`) as hits | AGREE, by design | it computes the TOUCHER closure `thread.py` needs; the writer census is a separate scan (section 5a) |
| G5, K5 | the 8.7 reading is right, but "the exact workaround" is not the only one: an attachment-free reference digest with an equality theorem; a `:corr-fn` absstobj whose exports may call `fn-digest`; removing the attachment | AGREE | section 4 now reads "the workaround both carriers use"; the alternatives are recorded for ST2/ST3 (a typed Store field over a reference digest is the one worth costing there). G5's note that the pasted `fn-sn-statep` does not show the `fn-digest` ancestry is right for the paste. The ancestry goes through `fn-node-statep`'s replay/record digests; the ST2 packet must exhibit it with `(all-fnnames ...)` before relying on it |
| G6a | the census of off-invariant identity lemmas looked only for literal `(not (fn-sf-statep ...))` hypotheses | AGREE | the fan-in certification is the check: a theorem that relied on the identity under any other negated hypothesis fails to re-prove. A failure is a `proof-owed` item or a restatement, recorded in the lanedump |
| G6b, K6d | T2 reads only the guard's head; `fn-sf-countersp` could hide a walk; T2 omits the owner layers and `fn-owner-io` | AGREE | the teeth book now checks `fn-sf-countersp`'s own body (only `natp` and the two accessors), T2 covers `fn-rcon-own-store-io`, `fn-rcon-ocfg-io`, `fn-olr-ocfg-reserve/-order`, and T2 has its own teeth (it must flag `fn-sf-core-completion`, still on the whole-log guard). `fn-owner-io`'s guard is checked by a `make-event` in host/owner-retain-host.lisp, at image build |
| G6c | section 3.1 says the 338 stop being a dispatch debt when (B) lands, but S1 keeps the row | AGREE | corrected in section 3.1: unchanged until S4 |
| G6d | the 92 ms was the guards-on counterpart; the raw-dispatched image already skips it, so S1 changes nothing a served POST on the raw image pays | AGREE | the before/after measurement is therefore the COUNTERPART arm (`FN_NATIVE_DISPATCH_COUNTERPART=1`, measure_post.py), where S1 must make `fn-owner-io` flat, plus the guard costs in the REPL. S1's payoff is that S4 can delete the row with no cost regression |
| K6a | `fn-sf-statep-implies-countersp` needs uint32 implies natp | AGREE, no change | it proves with `fn-sf-statep fn-sf-countersp` enabled (REPL, store-files #163) |
| K6b | why keep a no-op raw row rather than drop it in S1 | AGREE it is asserted, answered | RAW-DISPATCH owns `host/interfaces.lisp` until its exit; two lanes editing the rows is the collision section 6 avoids. S4 deletes it |
| K6c | nothing pins the census snapshot to a build | AGREE | the census is filed as evidence with the image set's sha and the world's source sha (section 5a) |

### 5a. The writer criterion, as amended by section 9

F is a writer of the owner's globals iff F's closure (bodies, guards and attachments, `:logic`
and `:program`) reaches any of these:
(1) `put-global` or `makunbound-global` with key `'fn-owner` or `'fn-owner-retain-carry`, or
with a non-literal key;
(2) an evaluator over a form or a function symbol computed at run time: `trans-eval` and its
variants, `ev`/`ev-fncall`/`ev-fncall-w`, `magic-ev-fncall`, `ld`/`ld-fn`. `apply$` and `ev$`
are excluded by rule, because they run only badged functions, which cannot take `state`;
(3) `return-last` whose first argument is not one of ACL2's built-in keys (raw code under a
ttag);
(4) a function with no `unnormalized-body` that is neither a primitive nor constrained without
an attachment.

The installers are writers by (1). The scan is conservative: each route counts as a write,
whatever it does at run time. `with-live-state` and redefinition after the snapshot are excluded
by rule. The image build refuses redefinition (`ld-redefinition-action` nil), and `with-live-state`
in a host file is a ttag'd raw form, which (3) catches. Raw Lisp modules reach the globals only
through dispatched entries (`tools/raw_dispatch_rule.py`). The census is run in an image world,
filed with the image set's sha (`evidence_store.py put`), and is the evidence for each deletion.

## DECISION

**Status: AGREED (carrier2, 2026-10-04), with the amendments of section 9.** The two reviews
(grok-4.7 and Kimi K2.7, both completed) attack the slice's execution, not the lean. Every
AGREE finding is folded into S1's commit or into section 5a. The REFUTED findings each carry
their witness in the table above. No finding asks for option (A) or (C).

The design: (B) the sf-statep idiom change, per served chain, `fn-owner-io` first (S1, landed on
`lane/carrier2`, in lockstep on both sides of every twin). The stobj carrier is the eventual
physical form (dev's `books/owner-carrier.lisp` + `tools/owner_carrier/thread.py`, run once on
then-current dev). `lane/stage-5b-carrier@fa32ac06f` is retired as an input. The invariant is
never a stobj type (section 4; the alternatives section 9 lists are recorded for ST2/ST3). The
338 owed writers are reclassified by the conservative closure of section 5a; a deletion needs
the filed census, and until S4 the escape stays for every name the census does not clear.
RAW-DISPATCH lands first, and S1 leaves `host/interfaces.lisp` untouched (section 6). Between
S1 and S4 the dispatch debt is unchanged (section 3.1, corrected).

Open, marked:
(q1) the generator owner's view of completeness-by-closure (S5).
(q2) `fn-sn-shapep`/`fn-sf-shapep` O(N), left to the ST-stages.
(q3) the native counterpart-arm POST "after" figure needs the integrator's batch image.
(q4) the exact owed-writer counts need the section 5a census in a current image world.
