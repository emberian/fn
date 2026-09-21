# Handoff: w10/owner-relation (the session seam, and what was behind it)

Branch `w10/owner-relation` from `dev` at `99a348c`, merged `dev` at
`9396a86` and `5dbd745`. Worktree
`/Users/ember/dev/fn/build/lanes/w10-owner-relation`. Spec:
[`specs/peering.md`](../../specs/peering.md) §3 and §4 for the feed half;
[`docs/proof-style.md`](../../docs/proof-style.md) for the export and hint
rules this lane leans on.

The lane was launched to close the `:open-peer` arm of
`fn-own-step-preserves-relation`. That arm was already closed on current
`dev`; the report naming it was taken before the `w10/auth-served` merge.
What was actually there is below, and it is five defects, not one.

## 1. What the checkpoint was

`1019c97` merged `w10/auth-served` into `dev` over `w6/peering-inbound-2`.
The two branches had each repaired the same defect at a different depth:
inbound-2 read the served session as a PEER session over a POST session,
auth-served as an AUTH session over a peer session over a POST session.
The merge took auth-served's STATEMENTS and kept inbound-2's HINTS and
CITATIONS, form by form, and `certify-book` stops at the first failure, so
only the first was ever reported. Four sites in
`books/owner-invariants.lisp`:

| site | what was wrong | repair |
| --- | --- | --- |
| `fn-own-advanced-session-is-bounded` (`:1288`) | three `:use` instances (`fn-peer-sessionp-forward-fields`, `fn-nntp-set-cursor-sessionp`, `fn-peer-sessionp-of-fn-peer-with-base`) reached `(fn-peer-session-base (fn-own-conn-session conn))` where the statement reaches through `fn-auth-session-base` first. The hypotheses were FALSE, not absent, so the goal read `(not (fn-post-session-shapep ...))` at `Subgoal 572.108.80` rather than naming a missing fact | every instance reaches the full depth |
| `fn-own-advance-repins-the-connection` | cited `fn-own-conn-boundedp-is-peer-session`, a name with no `defthm`; and its `fn-own-find-conn-of-replace-conn-same` instance rebuilt the connection with `fn-peer-with-base` alone where `fn-own-advance` (`books/owner.lisp:700`) wraps `fn-auth-with-base` around it | cites `-is-post-session` and `-is-auth-session`; the instance is `fn-own-advance`'s own session |
| `fn-own-durable-reply-names-a-durable-record` | the same dead name; and `ps` one wrapper short of what `fn-served-post-outcome` (`books/served.lisp`) hands `fn-nntp-post-outcome` | cites `-is-post-session`; every `ps` is `(fn-peer-session-base (fn-auth-session-base ...))` |
| `fn-own-invariants-vocabulary` | named the dead name. **A `deftheory` over a name with no rule is a hard error**, so `include-book "owner-invariants"` failed and `tests/acl2/owner-tests` was INERT | cites `-is-post-session` |

One lemma is new and `local`: **`fn-own-auth-base-of-fn-auth-with-base`**.
`books/nntp-auth.lisp` exports no accessor-of-update lemma for its own
`fn-auth-with-base` and withdraws the definition rune at export, where
`books/peer-inbound.lisp:1169` exports
`fn-peer-session-base-of-fn-peer-with-base` for the wrapper below it.
Without it nothing reduces the rebuilt session's base and the group
conjunct of `fn-own-conn-boundedp` cannot be decided. **Cross-cluster
proposal 1** below.

**No statement changed anywhere in this lane.**

## 2. The blocker nobody had seen: `books/provenance-codec`

The owner chain could not certify at `dev` HEAD for a reason outside the
owner cluster. persvati `run-20260920T214627Z-5441` (`dev` `99a348c`,
`--closure` over this lane's three roots) has exactly ONE genuine proof
failure and seven "no certificate" cascades of it:

    books/provenance-codec  (fn-prov-rebuild-of-its-own-fields)
      -> books/peer-inbound -> books/nntp-auth -> books/served
         -> books/owner -> books/owner-invariants, books/owner-config,
            tests/acl2/owner-tests

The provenance lane certified that book (`run-20260920T200514Z-39c0`)
*before* `w10/dtn-3`'s `fn-defrecord` change (`ab8816e`, merged at
`fed697f`) reached `dev`; the four `-of-its-accessors` facts the proof
`:use`s are that change's. Two `local` lemmas close it, no statement
changed:

* **`fn-prov-a-non-mismatch-diagnostic-is-the-match`.** `fn-prov-diagnosticp`
  is a disjunction and `books/provenance.lisp:80` states it
  forward-chaining. A disjunctive forward-chained conclusion lands in the
  context as one `or` the prover does not split on, so the "not a
  `:mismatch`" direction has to be instantiated by hand; the mismatch
  direction already has its own directed rule
  (`fn-prov-mismatch-diagnostic-shape`).
* **`fn-prov-transit-rebuilds-at-its-kind`.** The rebuild writes the kind
  and the diagnostic back as the LITERALS the case split is on (`:ihave`,
  `'(:match)`) where `fn-prov-transit-of-its-accessors` is stated over
  `(fn-prov-transit-kind x)` and `(fn-prov-transit-diagnostic x)`, so the
  `:use`d instance never matched. With both as variables it is the same
  fact in the shape the goal has.

### What happened to this repair at the merge

`dev` landed `w10/dtn-3` while this lane ran, and that lane found the
DEEPER cause of the same failure: the four `-of-its-accessors` facts are
now GENERATED by `fn-defrecord` and generated ENABLED, so each `:use`
hypothesis was rewritten to `(equal p p)` by its own rule before the goal
could spend it, and its `e/d` disables all four. That subsumes both local
lemmas above, which are **dropped**; `books/provenance-codec` takes dev's
version at every hunk. Keep the diagnosis on this page anyway: the
`:match` arm and the literal-versus-accessor mismatch are real and are
what a reader of `Subgoal 107.6''` will see first. Re-verified on the
merged tree: `ld`, zero `ACL2 Error`.

## 3. `books/owner-config` has never been admitted

Not a merge residue: the defect is in `7f59156`, the commit that created
the book. Four accessors were `(car x)`, `(car (cdr x))`, ... under
`:guard t`, which owes `(implies (not (consp x)) (equal x nil))` --- false
at `x = 3`. So the book's guard conjectures, its record lemmas and its
eight theorems have never run. **Repaired here** with the tree's own
idiom, `(mbe :logic (car x) :exec (fn-ag-car x))` (`books/owner.lisp:93`
for the same pattern); the `:logic` bodies are unchanged so every
statement keeps its meaning. That takes the book from 76 `ACL2 Error` to
31, and what remains is two named defects, both recorded OPEN:

* **`fn-ocfg-statep` (`:guard t`) calls `fn-own-relation`, whose guards
  are not verified.** Adding `(declare (xargs :guard t))` to
  `fn-own-conn-okp`, `fn-own-conns-okp`, `fn-own-view-okp` and
  `fn-own-ledger-durablep` verifies all four (measured), and then
  `fn-own-relation` stops at `fn-snt-relation`
  (`books/store-node-traces.lisp:159`), which is not guard-verified and
  whose body calls `fn-node-complete`, guarded by `fn-node-statep`.
  **Cross-cluster proposal 2.** The four guard declarations are NOT in
  this lane's commits: they make `books/owner-invariants` red on their
  own, and they buy nothing until the store side lands.
* **`fn-ocfg-reconfig-record`** owes
  `(acl2-numberp (fn-cfg-generation (fn-ocfg-config oc)))`. An `nfix`
  changes the term that `fn-ocfg-statep`'s staged clause compares against
  (`(+ 1 (fn-cfg-generation ...))`), so it is a packet with a rewrite, not
  a one-line edit. Everything else in the book's 31 errors cascades from
  these two.

## 4. `tests/acl2/owner-tests` was inert, and three field changes behind

Because of §1's `deftheory`, none of its **166** `assert-event` forms had
ever executed. Once the book admits they expose three arity drifts, none
of them the test's own idea:

* `fn-own-open` gained `acfg` (w10/auth-served): three sites passed one
  argument. They pass `nil`, which `fn-auth-open-session` maps to
  `(fn-auth-open-config)` --- requires nothing, offers nothing --- so each
  assertion keeps the meaning it had before authentication existed.
* `fn-own-make` gained `feeds` as its thirteenth field (w10/owner-feed):
  eight sites passed twelve arguments. They pass a thirteenth `nil`, the
  empty feed table `fn-own-start` builds.
* `fn-served-open` gained `injection` then `acfg`: three sites passed six
  of seven.

No assertion was weakened, added or removed. **166 of 166 pass**,
including `w10/kernel-freedom`'s owner-specific counterexample, which was
written and unrun for exactly this reason. *(kernel-freedom: your
`fn-own-ledger-durablep` assertions execute and pass.)*

## 5. `tests/test_feed.py`: four never-run defects, all host-side

The three ACL2 cases skipped themselves for want of `books/peer-feed.cert`
until foreign certificates appeared in the main checkout, so nothing here
had ever run. `FAULT timed out` was four defects in a row and **none is in
`books/peer-feed` or in the model**:

1. `FakePeer` created the store DIRECTORY and never wrote `store.json`;
   the fake reader pins its article list at accept
   (`tests/deploy_gate_fake/tools/run_reader.py` `serve`), so the
   connection thread died of `FileNotFoundError` before the `201` greeting
   and the client blocked until `--timeout`.
2. `Acl2Feed.tick` and `.observe` marshalled `(mv-nth i (fn-feed-tick-step
   ...))`; both book functions return `(mv state effects)` and ACL2 8.7
   refuses that spelling at the top level ("signature mismatch").
   `mv-list` is the reader-side spelling of the same value.
3. Both then ASSIGNED the new feed state before reading the command out of
   the effects. The form is re-evaluated per read, so the third read ran
   against the already-offered feed, selected nothing, and returned an
   EMPTY command; the driver sent zero bytes and waited for a reply to
   nothing. That is what the timeout was.
4. The test article's `Path:` named the peer's own path-identity, so the
   fake peer refused every offer 437 as a loop (RFC 5537 §3.5) while every
   assertion expects 235/239.

All four repaired; **4 of 4 pass**, 9.7 s.

### The proposal about `tools/run_feed.py`, with the evidence

**Retire it in favour of the owner's driver**, and rewrite
`tests/test_feed.py` against `tools/run_owner.py`'s `Feed` class. Not done
here, because it is the feed cluster's call and this lane was told to
propose rather than act. The evidence is defects 2 and 3: `run_feed.py` is
a SECOND driver for a decision the owner already owns, and it has drifted
from `books/peer-feed` three times --- the Python three-digit split
`w10/owner-feed` deleted, the `mv` signature, the read-after-assign ---
each time invisibly, because nothing ran it. `tools/run_owner.py` has none
of these: it drives the feed through `fn-own-tick-peer` and
`fn-own-feed-reply`, which return `(effects . owner)` conses, so the `mv`
marshalling does not arise, and it holds the store lock, which
`run_feed.py` does not. What would be lost is the ability to feed one peer
with no owner process; what would be gained is one owner per decision
(AGENTS.md) and a test that exercises the live path.

## 6. Per-root certification

Box measured first (`ssh persvati uptime`, `ssh hbox uptime`): persvati
load 4.5 with 57 G available, hbox load 3.7 but 113 of 123 G used, so
persvati. `--jobs 4`, `--remote-root /home/ember/fn-lanes/w10-owner-relation`.

persvati `run-20260920T222128Z-eedc`, 73 roots attempted, **72 certified,
1 failed**, evidence fetched to
`build/acl2/certify-20260920T222132Z-3999996/manifest.json` (ACL2 8.7 /
SBCL, `ACL2_CUSTOMIZATION=NONE`, `ACL2_BOOK_HASH_ALISTP=NIL`, the tree at
this lane's `57ba93f`).

| root | verdict | evidence |
| --- | --- | --- |
| `books/owner-invariants` | **certified** | `run-...-eedc`; `books--owner-invariants.certify.log`. Every event runs, `deftheory fn-own-invariants-vocabulary` included |
| `tests/acl2/owner-tests` | **certified**, 166 of 166 `assert-event` | `run-...-eedc`. Had never been admitted before this lane |
| `books/owner-config` | **OPEN** at `fn-ocfg-statep` | `run-...-eedc`, `books--owner-config.certify.log:969`: "The body for FN-OCFG-STATEP calls the function FN-OWN-RELATION, the guards of which have not yet been verified." `certify-book` stops there, so the second defect (`fn-ocfg-reconfig-record`, §3) is unattempted on the box and was measured locally |
| `books/provenance-codec` | **certified** (was the gate) | `run-...-eedc` |
| `books/peer-inbound`, `books/nntp-auth`, `books/served`, `books/owner` | **certified** | `run-...-eedc`; all four were "no certificate" cascades of `provenance-codec` in `run-20260920T214627Z-5441` |
| `tests/test_feed.py` | **4 of 4 ok**, 9.7 s | laptop, `python3 -m unittest tests.test_feed -v` |
| `make check` | green | laptop, before each commit |

The export-theory line of §1's last row (`fn-own-conn-boundedp-is-auth-session`
withdrawn) landed AFTER that run, so `books/owner-invariants` and
`tests/acl2/owner-tests` were re-`ld`ed locally (zero `ACL2 Error`,
166 of 166) and re-submitted as persvati `run-20260920T222651Z-97fc`.
**That run confirms the same verdicts on the final tree**: 73 roots, 72
certified, `books/owner-config` the one failure, `books/owner-invariants`
and `tests/acl2/owner-tests` (166 of 166 `:PASSED`) certified. Evidence
`build/acl2/certify-20260920T222654Z-4053945/manifest.json`, ACL2
`/home/ember/fn-tools/acl2-8.7/saved_acl2`, sha256
`c8a7a804d9cc80e2025a8ab0e1d9325f2a0c4a027a5dcdcb2c1093e9cd5c8163`.
`books/owner-invariants` itself certifies in 7.6 s (prove 6.3 s).

**Final, on the merged tree** (dev `1b2b2ab` merged in, which brought
`w10/dtn-3` and `w10/session-depth`): persvati
`run-20260920T224103Z-7c59`, evidence
`build/acl2/certify-20260920T224106Z-4192084/manifest.json`. **73 roots,
72 certified**, the same single failure `books/owner-config` at
`fn-ocfg-statep`; `tests/acl2/owner-tests` certified with 166 of 166
`:PASSED`. That is the run the per-root table above should be read
against.

Ledger over the lane (`tools/ledger.py --write`, `dev` `5dbd745` to this
branch): theorems 5548 -> 5551 (the three new `local` lemmas), suspects
45 -> 45, export-hygiene warnings 72 -> 72, enabled-projection warnings
26 -> 26, `assert-event` count 5275 -> 5275 (no assertion added or
removed; 166 of them now execute).

**On the box cache.** The first submit found `installed 36, kept 68,
uncached 171`; the second, after the first had seeded persvati's cache,
found `installed 78, kept 28, uncached 169`. Seeding works. It is still
169 uncached because no box has ever held a `dev`-HEAD closure (§7).

## 7. The finding that explains the disagreement between lanes

**No box holds a dev-HEAD certificate closure, and the main checkout's
certificates are foreign.** persvati `/home/ember/fn-lanes/dev-w6pf4` ---
the w6 feed lane's run root, whose 250 `.cert`/`.port` pairs are the ones
sitting in `/Users/ember/dev/fn` --- has `books/defrecord.lisp` at
`30a413f1` where `dev` has `ec4252ef`. `/home/ember/fn-lanes/w10-kernel-freedom`
has that same old `defrecord` AND `books/served.lisp` at `3f8f3f57` where
`dev` has `81b84d3d`. So "72 of 75 roots, `books/owner` certified" and
"open at `fn-own-advanced-session-is-bounded`" are statements about two
different trees, neither of them `dev`. In the main checkout those foreign
pairs do not fail: ACL2 loads every book UNCERTIFIED with a page of
warnings, which is why nothing noticed, and it is also what un-skipped
`tests/test_feed.py` (§5).

**What to do about it:** `python3 tools/certs.py install` in the main
checkout removes nothing that is foreign-but-unusable, because the pairs'
origin (`/home/ember/fn-lanes/dev-w6pf4`) does not exist locally and
`install` therefore accepts them. The pairs are content-keyed but the
CONTENT they were made from is not `dev`'s. Either `certs.py install`
should verify the installed pair against the book's own closure hash after
installing, or the main checkout should hold no certificates at all.
Posted on the board.

## 7b. What the merge with `w10/session-depth` cost, and what it bought

`tools/session_depth.py` recorded two `OPEN_DEFECTS` entries against
`books/owner-invariants.lisp` naming exactly the repair of §1. They are
**deleted here**, as that file's own rule requires of whoever fixes the
site. What remains in that book is 23 hand-spelled walks, which the tool
reports as `CHAIN` and which are correct at depth; converting them to
`fn-auth-post-session` and `fn-auth-reader-session` is a follow-up and was
not taken, because it is 23 multi-line `:use` terms and the lint does not
fail on it (non-`--strict`). `make check` is green.

The same lane changed `fn-nntp-post-outcome` to answer a malformed session
with **403, the fourth outcome**, where it used to answer with no effects.
That killed one witness in `tests/acl2/owner-tests.lisp`, and repairing
the witness removed a hypothesis:

* the assertion was the teeth for
  `fn-own-durable-reply-names-a-durable-record`'s
  `(fn-own-find-conn id (fn-own-conns o))` --- an absent connection at
  which the equality hypothesis STILL held, because `fn-own-outcome`
  answers an unknown connection `nil` and the served side answered `nil`
  too;
* measured after the merge (`with-guard-checking :none`, printed): the
  owner still answers `nil`, the served side is now the 403 reply. They
  differ, so **no connection-free state can satisfy the equality**;
* a hypothesis with no violating value is unnecessary
  (`docs/proof-style.md` §5), so it is **deleted from the theorem**, which
  is then strictly stronger, and the assertion records the separation that
  makes it so. Not weakened, not waived; the book and the test book were
  both re-run.

## 8. JOB 3: what `fn-feed-replay-is-the-live-feed-modulo-inflight` needs

Not started, as instructed. `specs/peering.md:800` states it over a
hypothetical ideal machine (`fn-ideal-feed`, `fn-ideal-feed-journal`), and
§4's status row says the missing half is "a live machine that emits its
own journal". **That machine now exists and it is the owner**, so the
statement should be re-aimed at `fn-own-run` before anyone tries to prove
it. Concretely:

1. **The emitter side already exists**, one function per arm:
   `fn-own-feed-durable-records` (`books/owner.lisp:1025`),
   `fn-own-tick-peer-records` (`:1057`), `fn-own-tick-records` (`:1061`),
   `fn-own-feed-reply-records` (`:1099`). What does NOT exist is the fold
   that says a TRACE emits a journal: `fn-own-feed-journal (o events)`,
   the append of each step's records along `fn-own-run`. One definition.
2. **The replay side already exists**: `fn-own-feed-recover`
   (`books/owner.lisp:1132`) is `fn-feed-replay` on the peer's entries and
   nothing else, and `fn-feed-replay-is-the-fold`,
   `-preserves-feedp` and `-preserves-peer` are proved in
   `books/peer-feed-invariants`.
3. **The statement to prove**, in owner vocabulary and with no ideal
   machine:

   ```lisp
   (defthm fn-own-feed-replay-is-the-live-feed-modulo-inflight
     (implies (and (fn-own-relation o)
                   (fn-own-feed-tablep (fn-own-feeds o))
                   (fn-feed-journal-imagep
                    (fn-own-feed-journal o events) records))   ; a crash image
              (equal (fn-feed-settle
                      (fn-own-feed-entry-feed
                       (fn-own-feed-entry-of
                        peer (fn-own-feeds (fn-own-feed-recover
                                            (fn-own-reopen o ...) peer records)))))
                     (fn-feed-settle
                      (fn-own-feed-entry-feed
                       (fn-own-feed-entry-of peer (fn-own-feeds
                                                   (fn-own-run o events))))))))
   ```

   `fn-feed-settle` (the in-flight-to-`:queued` normaliser) does not exist
   yet either; `fn-own-feed-restart-all` is the live half of it and
   `fn-feed-replay`'s own fence is the replayed half, so `fn-feed-settle`
   should be DEFINED as what `fn-feed-restart` does to one entry, and the
   equation proved by induction on `events` with a one-step lemma per arm.
4. **The obligation that makes it non-vacuous**: `fn-feed-journal-imagep`
   must admit a torn tail (the host appends the record BEFORE the bytes it
   authorises, `tools/run_owner.py`), and the teeth must include a trace
   whose crash image drops the last record while the peer already has the
   article --- otherwise the theorem is about complete journals only and
   says nothing about a crash.
5. **Cost**: one definition (`fn-own-feed-journal`), one definition
   (`fn-feed-settle`), five one-step arm lemmas, the induction, and the
   teeth. It belongs in the feed cluster, not here: every lemma it needs
   below the owner is in `books/peer-feed-invariants`.

## 9. Cross-cluster proposals

1. **`books/nntp-auth.lisp`: export
   `fn-auth-session-base-of-fn-auth-with-base`.** One `defthm`, beside
   `fn-peer-session-base-of-fn-peer-with-base`
   (`books/peer-inbound.lisp:1169`), proved by enabling
   `(:d fn-auth-with-base)`. This lane carries it `local` in
   `books/owner-invariants.lisp`; every other includer of the auth session
   will want it. Owner: the auth/served cluster.
2. **`books/store-node-traces.lisp`: guard-verify `fn-snt-relation`.**
   It is what stops `fn-own-relation`, which is what stops
   `fn-ocfg-statep`, which is what stops `books/owner-config` (§3). Its
   body calls `fn-node-complete`, guarded by `fn-node-statep`, so the
   packet is "carry `fn-sn-statep` into the guard, or make the `:exec`
   path `mbe`-guarded the way `books/acceptance.lisp` does". Owner: the
   store/kernel cluster.
3. **`books/owner-config.lisp`: `fn-ocfg-reconfig-record`'s generation**
   (§3, second bullet). Owner: whoever takes the owner-config root next;
   it is small but it needs a rewrite to keep `fn-ocfg-statep`'s staged
   clause true.
4. **`tools/certs.py install` should re-verify the installed pair**
   against the book's own closure hash, or the main checkout should hold
   no certificates (§7). Owner: the tooling cluster.
5. **Retire `tools/run_feed.py`** (§5). Owner: the feed cluster.

## 10. What was NOT done

* `books/owner-config` is not certified and its two remaining defects are
  recorded open above, not weakened.
* No `skip-proofs`, no `defaxiom`, no trust tag, no statement weakened.
* The four guard declarations in §3's first bullet were measured and then
  REVERTED, because they leave `books/owner-invariants` red until the
  store side lands.
* JOB 3 was not started.
