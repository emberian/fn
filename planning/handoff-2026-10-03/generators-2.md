# Lane generators-2 (Fable deputy), 2026-10-03

Worktree build/lanes/generators-2, branch lane/generators-2 from origin/dev 4aa332295.
Scope: (1) def-carried-view, (2) the teeth generator, (3) the keyset mbe macro,
(4) consolidation (paged-catalog onto def-representation, dead code, slow books).

## Interface sketch (sent to the coordinator first; siblings DEF-ENTRY, DEF-COMMAND,
## DEF-HOLDER call (2) from their own expansions; STAGE-5B and SERVED-CATALOG-LIVE use (1))

### (2) The teeth generator: `defteeth` and its program-mode core

What exists: books/defkeystone.lisp (defthm + teeth from one form; 7 uses) mirrored by
tools/ledger.py defkeystone_expansion, tools/keystone_emit.py (registry half), and
tools/teeth_check.py. The registry has 3,860 keystone events; the other 3,850 keystones
have hand teeth found by a comment convention ("; fn-name" then assert-events), a floor,
not a check. The generator makes the schema the macro for EVERY keystone, including one
admitted elsewhere, and makes a missing tooth a refusal.

    (defteeth NAME                        ; NAME an admitted theorem in this world
      :witness ((VAR VAL) ...)            ; REQUIRED: full antecedent + conclusion, under guards
      [:hyps (L1 ... Ln)]                 ; labels; default h1..hn over the LITERAL statement
      :breaks ((Li ((VAR VAL) ...) [:corrupt "why"]) ...)   ; REQUIRED, one per hypothesis
      :mutations ((L TERM ((VAR VAL) ...)) ...) | (:none "why")  ; REQUIRED (stub refused)
      [:corrupt ((L ((VAR VAL) ...)) ...)]
      [:visits ((VISIT-TERM BOUND-TERM :attains ((VAR VAL) ...) | :none "why") ...)]
      [:hints HINTS])                     ; the must-fail re-proofs' hints (default: NAME's own)

    (fn-teeth-events NAME SPEC WRLD)      ; :program; the events above, for a sibling macro
    (fn-teeth-refusal NAME SPEC WRLD)     ; nil or (REASON . DETAILS), the same checks

The statement is READ FROM THE WORLD (getpropc NAME 'theorem), so the teeth are for the
literal theorem; a label names a hypothesis by position (or its function symbol when
unique). Emitted, in order: positive assert-event (every Hi and C at the witness); per
hypothesis an assert-event (every retained Hj, not Hi, not C; LOGICAL values under
with-guard-checking :none) and (local (must-fail-checked (defthm NAME-without-Li ...)));
per mutation an assert-event (not M) and must-fail NAME-mutant-L; per corrupt; per
:visits a defthm NAME-visits-K (implies HYPS (<= V B)) (a cost theorem, proved with
:hints), its witness (HYPS and (<= V B)), and the ATTAINS witness (HYPS and (equal V B)):
a bound nothing attains is slack, not a claim. A (table fn-teeth NAME ROW) row records it.
Refused by name: no witness; a hypothesis with no break; no mutation and no :none reason;
a :visits with neither :attains nor :none; a label naming no hypothesis; NAME not a
theorem; teeth declared twice. defkeystone keeps its interface and becomes defthm +
defteeth (plus :visits). A source book cannot include tests/acl2/must-fail-checked, so
teeth stay in test books; a sibling's source-side generator emits its keystones and a
(table fn-teeth-owed NAME) row, and `(defteeth-check)` in the test/image world refuses an
owed keystone with no fn-teeth row (as def-carried-check does).

Static side: ledger.py gains defteeth_expansion (statement from the tree's own theorem
list, not the world); teeth_check counts "generated vs hand" teeth per registry event;
tools/teeth_baseline.json holds the hand count and ONLY SHRINKS (a new registry event
without a defteeth form fails keystone_emit --check). That is the wiring: refusal at
expansion for generated keystones, a ratchet for the 3,850 existing ones.

### (1) def-carried-view: a reader's answer carried by an index over a list

The population (ground truth): fn-wix (two set indexes over the withdrawal list),
fn-nnw (an exact fold, suffix maxima, over the article list), fn-prc (a delta over the
retention ledger), fn-midx/fn-mxc/fn-gidx-refresh (one-step extend else rebuild),
fn-gacc (per-rule cache). Four of six are one shape: a carry (KEY . INDEXES) where KEY is
the list the indexes were built from; a recognizer "INDEX agrees with KEY"; a refresh
that walks the new list to the tail EQUAL to KEY, folds the walked prefix (oldest first)
onto the carried indexes, else rebuilds; readers that take the index's answer only when
the list in hand is EQUAL to KEY and the index answers (negatively, for a set), else the
reference walk. Hand-written: 150-300 lines each, the same five theorems.

    (def-carried-view NAME
      :key WS                                ; the list formal's name -> accessor NAME-WS
      :indexes ((IDX :kind :set  :key-fn F  :put P :hasp H :empty E)   ; complete: every
                                                                        ; (F e) of KEY is in IDX
                (IDX :kind :exact :put P :empty E) ...)                ; IDX = fold P over KEY
      [:elt-pred Q])                         ; elements the indexes see (default t)
    generates: accessors NAME-WS, NAME-IDX; NAME-completep/NAME-okp; NAME-carryp;
    NAME-build (tail-recursive, by def-loop's library); NAME-extend (the walk; (mv found
    IDX...)); NAME-refresh; theorems NAME-carryp-of-nil, NAME-carryp-of-refresh,
    NAME-WS-of-refresh, NAME-refresh-visits-is-the-delta ((equal ws (append new (NAME-WS
    carry))) implies the walk steps exactly (len new) elements: the VISIT bound, derived);
    a (table fn-carried-view NAME ROW). One generic library (constrained put/hasp/key/
    empty; bridges proved once), every instance by :functional-instance, as def-loop.

    (def-carried-reader R (FORMALS)
      :of NAME :carry C :list WS             ; C and WS among FORMALS
      :when PRE                              ; the fast arm's precondition (e.g. (stringp m))
      :probe (H (F-of m) (NAME-IDX C))       ; the index question
      :fast TERM                             ; the answer when the probe is negative
      :reference TERM                        ; the walk, over FORMALS less C
      :by THM                                ; the instance's lemma: (implies (and
                                             ; (NAME-completep ...) PRE (not probe)) (equal
                                             ; REFERENCE FAST)); the only hand proof
      [:name R-is-REF])
    generates R = (if (and PRE (equal WS (NAME-WS C)) (not PROBE)) FAST REFERENCE), the
    keystone (implies (NAME-carryp C) (equal (R ...) REFERENCE)) proved by :use THM in
    minimal theory, (in-theory (disable R)), and REFUSES a :fast term that mentions WS
    (the fast arm cannot visit the list it does not hold: the reader's visit bound,
    structural). A stobj-carried reader (:of a def-carried row) gets the same theorem
    under that row's invariant; writers come from def-carried's completeness.

    (def-carried-view-teeth NAME :list L0 :delta NEW :bad BAD
      :readers ((R :args (...) :fast-at (...) :walk-at (...)) ...))   ; in the test book
    expands to defteeth forms for every generated keystone (refresh of nil, the delta
    walk found, the rebuild, the bad carry as the removal, the "new list + old index"
    mutation; per reader: fast and walk positives, the bad-carry removal).

Fail closed: an undeclared writer. A value carry's writers are NAME-refresh and nil, by
construction; the host global that holds it is policed by tools/owner_globals_check.py's
successor rule "written only by (NAME-refresh ...) or nil" read from the emitted
fn-carried-view table (interface_emit), as the def-carried requirement table does.
Pilot: withdrawal-index-carried (fn-wix, 293 lines; PRF-1231's seven cited names kept)
and the carry half of newnews-cursor (fn-nnw; fn-nnw-car-of-refresh re-cited as
fn-nnw-arts-of-refresh). Diff must be net negative.

### (3) `def-keyset-check` (the mbe keyset pattern)

    (def-keyset-check NAME (XS YS)
      :logic-member M        ; the :logic membership test of one XS element in YS
      :each P                ; a per-element predicate on XS (default t)
      :ys-key F              ; the key an element of YS puts in the set (default identity)
      :base B                ; (null xs) or t
      :when-long t)          ; the linear path only for long lists (fn-ks-longp)
    generates the fill, the bound check, the with-local-stobj wrapper, the bridge
    NAME-ks-is-logic and NAME with :logic the recursion over M/P and :exec the keyset;
    guards verified. Replaces fn-sf-success-listp (store-files) and
    fn-retain-ids-disjointp (retention); fn-ks-subsetp / fn-no-duplicatesp follow.

## State (2026-10-03, lane/generators-2)
- TEETH GENERATOR (contract v1 + c09 must-fixes): books/defkeystone.lisp rewritten; tests/acl2/defkeystone-tests.lisp
  61 forms LOADED on hbox (0 refused); tools/ledger.py mirrors defteeth/defkeystone from the :claim (world-free),
  tests/test_ledger.py 137 pass (ledger.md stale = a regen); tools/keystone_emit.py = the obligation-manifest gate
  (planning/teeth-obligations.json, planning/teeth-base.json fail-closed, --write-manifest apart from --write,
  --bootstrap once); tools/teeth_check.py expands defteeth from the claim. 26 existing defkeystone forms converted
  (:deferred exemptions, :logical breaks, edit mutations with :fault). Farm run of the affected closure:
  run-20261002T225730Z-a272 (hbox), pending.
- DEF-CARRIED-VIEW: books/def-carried-view.lisp library (41 forms) + generators (def-carried-view :set/:exact,
  def-carried-reader negative filter) admitted on hbox; tests/acl2/def-carried-view-tests.lisp (fixtures of both
  kinds, a reader, defteeth on the generated keystones, refusals) loading. The list EQUAL stays in v1 with the
  equal-hit arm rebased (c04 4c); the identity-keyed refresh waits on the owner view's version
  (fn-own-view-version exists; the relation is the owner's to prove -- STAGE-5B).
- TEETH GENERATOR certified: hbox certify-20261002T231403Z-1883604 (affected closure of books/defkeystone: 5 certified,
  2 cached roots, 0 failed, no book over 10 s) and certify-20261002T232922Z-2220863 (books/defkeystone recertified with
  its 7 affected roots: 7/0), both cited in planning/evidence-index.tsv. planning/teeth-obligations.json (3797 entries:
  35 generated, 3762 hand) committed at 4e5a4b8bb; planning/teeth-base.json names that revision. check-lane running. origin/dev's keystone_emit --check already exits 1 on this tree (22 registry findings in the
  resource-vector books: subjects reached by no host line, three forms without :id) -- pre-existing, not this lane's.
- DEF-KEYSET-CHECK: books/def-keyset-check.lisp (library + generator) and tests/acl2/def-keyset-check-tests.lisp green on
  hbox (34/34): :absent identity keys with the :long policy, :present keyed records with an adopted :keys and a named
  :member-is, both arms at 0/7/8/9, dotted tails, the owed bridges' defteeth + defteeth-check, refusals. The two hand
  uses (fn-sf-success-listp, fn-retain-ids-disjointp) are NOT yet replaced (store-files defers guard verification; the
  generator verifies inline -- needs a :verify-guards option or the book's order).
- DEF-CARRIED-VIEW fixture GREEN on hbox (tests/acl2/def-carried-view-tests 55/55): the :set view with two indexes,
  the :exact view, the negative-filter reader, defteeth on every generated keystone, both defteeth-checks, refusals.
  Lessons that cost a cycle each: ACL2 normalizes a ground nullary call in a stored body (:normalize nil on the
  generated defuns that mention the empty tuple); the functional-instance theories must be exactly the owed
  equations plus the two constraint lemmas (anything more and the rewriter unrolls the fold); the build bridge is
  disabled on exit (an instance enables it where it wants it).
  fn-wix PILOT written as declarations (books/withdrawal-index-carried.lisp 184 lines vs 293; tests -24 lines; PRF-1231's
  seven cited names generated by construction) and loading on hbox. tools/ledger.py mirrors all three generators
  (tests/test_ledger.py GeneratorMirrorTests pins the names).
- Obligation manifest: planning/teeth-obligations.json is being written on hbox (--write-manifest --bootstrap; the
  gate's first manifest) and fetched; planning/teeth-base.json then names the commit that holds it.
- PILOTS: fn-nnw carry half DECLARED and green (books/newnews-cursor 53/53, tests 41/41 on hbox; -92 lines;
  fn-nnw-car-of-refresh re-cited as fn-nnw-arts-of-refresh in PRF-1232; the owed defteeth in the test book).
  fn-wix DECLARED (184 vs 293 lines; two :set indexes, two negative-filter readers, the seven PRF-1231 names
  generated; owed defteeth added to its test book); the view's admission on hbox is the open item (the last
  refusal: :lemmas naming a function; fixed).
- STAMPS (def-entry round two; c04 4c): `:stamp (:stamped (lambda (stamp ws) R) :determines THM)` on a view
  generates NAME-fresh (the relation, one place), NAME-stamp, NAME-stampedp, NAME-list-carryp (the list layout's
  recognizer, over which the walk/fold/rebuild theorems are proved), NAME-carryp (the stamped layout),
  NAME-refresh-stamped (an equal stamp: the carry rebased on the current pair in O(1), indexes kept, by
  :determines; else the list refresh under the new stamp) with NAME-carryp-of-refresh-stamped under (carryp,
  stampedp, fresh), NAME-stampedp-of-refresh-stamped, NAME-stamp-of-refresh-stamped; a reader `:stamp S` tests
  (equal S (NAME-stamp C)) -- ONE visit for def-cost -- and its keystone adds (NAME-stampedp C) and
  (NAME-fresh S WS). What the relation means and that the owner never reuses a stamp for another list (no ABA
  across recovery/reclaim/reconfiguration/withdrawal) is the owner's theorem: for the wix pilot, STAGE-5B's
  "fn-own-view-version determines fn-own-view-withdrawals within an owner lifetime" (the host passes
  (fn-own-view-version v) and (fn-own-view-withdrawals v)); until it exists the pilot stays list-keyed and the
  stamped form is exercised on the fixture (cvs in tests/acl2/def-carried-view-tests.lisp: refresh by stamp,
  rebase, delta, rebuild, the stamped reader, three removal witnesses per keystone incl. the ABA-shaped one). The
  walk of a delta refresh still compares lists (counted visits); a lineage stamp bounding the delta without a
  comparison is the next option.
- DEF-KEYSET-CHECK: BOTH hand uses replaced and admitted on hbox -- books/retention.lisp fn-retain-ks-disjointp
  (96/96; -30 lines; fn-retain-ids-disjointp keeps its :logic (not (intersection-equal ..)) over the generated
  check; PRF-173 re-cites the walk bridge) and books/store-files.lisp fn-sf-success-listp (194/194; -25 net;
  :keys fn-sf-record-pairs + :member-is fn-sf-record-has-pairp-is-member, disabled after the declaration so the
  kernel's inductions keep their shape; the late guard block verifies the generated executables). Their test
  books (retention-tests, store-files-teeth-tests) loading; then the two closures to the farm (store-files is deep).
- r71-F16 done on the branch: fnn-owner-release-pending-extents (the unlocked wrapper) removed, no caller
  (host bytes change, no module affected: no natives).
- def-cursor (GEN-CURSOR): not started. Consolidation: fn-mpxt measured (311 definitions, 29 reachable from
  other books, 282 internal to the paged index), not cut; paged-catalog onto def-representation not started.
- check-lane at 81ae51d0d on hbox: my steps green (ledger, certified_claims, teeth_check, interface_emit,
  reach_check, null_witness, tests.test_must_fail_check, secrets); keystone_emit red = the tree's 22 registry
  findings (origin/dev's own tool exits 1 on this tree: subjects reached by no host line, three forms without :id in
  the resource-vector books) plus, correctly, the pilots' owed rows -- now declared; the other 24 reds
  (resource_contract on dev's 2026-10-01 certify, host_check extent.lisp, native_source_check, build_lists,
  main_last_check, ...) are the tree's, untouched by this lane.

## Astra's view (consultation c04, gpt-6-astra, read-only at 4aa332295, 1149 s)

### Liaison fact-check (codex-liaison-11, 2026-10-03)
Checked in source myself (worktree build/lanes/codex-c04-generators):
- CONFIRMED 1b: the existing defkeystone refuses a zero-hypothesis theorem with no mutation (books/defkeystone.lisp:220-221
  :no-teeth); the sketch's (:none "why") would let exactly that through (no hypotheses, no breaks, no mutation).
- CONFIRMED 1f: must-fail-checked's default is a 300,000-step limit (tests/acl2/must-fail-checked.lisp:133) and its own
  test shows a TRUE theorem failing at :step-limit 10 (:172-183): a must-fail is proof-search exhaustion, not a counterexample.
- CONFIRMED 2d: make check runs `tools/teeth_check.py --summary` (Makefile:2567), not --strict: the static teeth check
  never fails the build today.
- CONFIRMED 4a premise: fn-wix-refresh returns the OLD carry on an EQUAL hit (books/withdrawal-index-carried.lisp:149-152),
  so an equal-but-unshared list keeps paying a full comparison on every refresh; the EQ-first assumption is a comment (:29-30).
- CONFIRMED (also in the arena-forget note): the reclaim swap does not reset fn-owner-access-cache (no mention in
  books/owner-recovery-retain.lisp or owner-reclaim-pass.lisp).
- NOT CHECKED by me: the ACL2SRC citations (translate/defthm/axioms), the per-population host call-site table in 4b line by
  line (spot-read only: fn-wix and fn-nnw are unwired on dev, as their own books say), keystone_emit/green_check lines.
Liaison's reading: BUILD WITH CHANGES, four in order: (1) bind teeth to the TRANSLATED statement through an explicit
:claim (hypotheses with labels + conclusion) checked against the world, with two witness modes (executable vs named ground
lemma) and positive refutations instead of must-fail as coverage; (2) a mandatory late coverage gate over an obligation
manifest plus a per-theorem (not count) ratchet against a protected base; :none split into :not-applicable / :deferred and
counted; mutations as checked edits of the statement; (3) costs derived from the executed reader/refresh (EQUAL, probe and
fallback included); drop "FAST does not mention WS" as a visit proof; (4) do not force fn-prc, fn-midx/mxc, fn-gidx, fn-gacc
into one (KEY . INDEXES) schema; pilot a narrow suffix-fold generator; replace list EQUAL with an owner-maintained
view identity (epoch + generation with a proved relation), not a length. Decide fn-teeth-events' expansion staging,
refusal semantics, row identity and certification consumer BEFORE the siblings depend on it.

### Astra's answer (verbatim)

BUILD WITH THESE CHANGES, in this order:
1. Freeze a translated-statement binding and executable/proved witness protocol before exposing `fn-teeth-events`.
2. Specify a mandatory, late coverage gate and a per-theorem ratchet; a count and an optional table check are insufficient.
3. Generate costs from the executed reader/refresh, including equality, probes and fallback; drop the claimed structural cost proof.
4. Separate suffix folds, retention deltas and keyed caches; give keyset generation an explicit membership relation and polarity.
Before siblings depend on the helper, decide its staged expansion, refusal semantics, row identity, witness modes, mutation contract and certification consumer.

This is a source consultation, not implementation or certification. The inspected checkout reports HEAD `4aa332295c85f03f5a97d7b0ac2228f9b95ab1e9`, the revision in `build/codex/c04/CONSULT.md:3-5`. No ACL2, builds, make, remote commands or tests were run. Proposed examples below are constructions against the specified interface; their actual macro acceptance is **UNVERIFIED**, because the sketch explicitly says “nothing built yet” (`build/codex/c04/SKETCH.md:124-125`). HOLE means an assurance or interface hole, not that ACL2 will prove a false theorem.

Citation convention: paths are relative to this worktree unless absolute. `ACL2SRC` below abbreviates the inspected local directory `/Users/ember/tools/acl2-fn/acl2-8.7`; this is a source reference, not a claim about the version or settings of a deployed image.

## 1. Vacuity and the teeth interface

### 1a. Retained hypotheses: SOUND in logic; execution domain: WEAK

The essential formula is right. The sketch requires “every retained Hj, not Hi, not C” (`build/codex/c04/SKETCH.md:33-35`), and the existing generator really constructs that conjunction (`books/defkeystone.lisp:279-301`, especially `294-296`). Thus a value making **another retained hypothesis false cannot satisfy that assertion**. Do not report a spurious counterexample to this part of the design.

A guard violation is different. Consider this proposed source theorem and teeth:

```lisp
(defun c04-f (x)
  (declare (xargs :guard (consp x)))
  (if (consp x) 1 0))
(defthm c04-k
  (implies (consp x) (equal (c04-f x) 1)))
(defteeth c04-k
  :hyps (pair)
  :witness ((x '(a)))
  :breaks ((pair ((x nil))))
  :mutations (:none "no proposed mutation"))
```

At `x=nil`, the omitted hypothesis and conclusion both fail in the logical definition. That is a real logical counterexample to dropping `consp`; it is not an executable host-domain case. The optional `:corrupt` label lets this distinction disappear from the report. Existing `fn-dk-logical` explicitly uses `with-guard-checking :none`, because witnesses may be outside guards (`books/defkeystone.lisp:239-243`); the project rule separately says “Label corrupted-state and mutation witnesses separately” (`AGENTS.md:83-89`).

**Change:** distinguish `:logical-removal` from `:reachable-removal` in the row, infer/check the guard-domain result, and require an explanation for a logical witness outside that domain. Do not require all removals to obey the omitted guard—that would make legitimate guard hypotheses untestable. Keep the affirmative checks on every retained hypothesis in both modes.

**WEAK: evaluation is not a universal witness language.** A constrained function without an executable attachment, a non-executable `defun-sk` predicate, and a live stobj do not become ordinary closed data just by selecting `:none`. ACL2's evaluator explicitly retains restrictions on non-compliant live stobj manipulation even with guard checking off (`ACL2SRC/translate.lisp:8771-8798`: “ACL2 does not support non-compliant live stobj manipulation”). The existing witness builder simply wraps each term in a `let*` (`books/defkeystone.lisp:235-250`); the sketch specifies no replacement protocol for these cases (`build/codex/c04/SKETCH.md:19-39`).

Do not silently treat evaluation errors, inability to execute, timeouts, or attached implementations as successful logical checks. A raw/non-logic-valued witness bypass through the proposed implementation is **UNVERIFIED**; there is no implementation to inspect. The concrete refusal case is a theorem whose hypothesis calls an unattached constrained predicate: an ordinary ground `assert-event` cannot discharge the requested evaluation merely because the theorem was admitted.

**Change:** provide two checked modes:

* Closed, pure, logic-valued executable bindings, translated for the actual evaluation context, with errors fatal. Enforce guards for the positive/host witness explicitly rather than inheriting ambient settings. Evaluate bindings once and reuse that substitution for all conjuncts.
* A named ground witness theorem whose **literal generated formula** is checked against the instantiated antecedent/conclusion. This supports non-executable predicates without pretending to execute them. For stobjs, require a local creator/transition trace with the correct input/output arities and state threading; record whether the example establishes logical satisfiability, executable validity, or reachability.

A constrained-function attachment can supply a concrete implementation experiment, but is not a proof of a ground proposition about every constrained interpretation. Keep it classified accordingly. A positive assignment satisfying all hypotheses also does not, by itself, exhibit a reachable composed execution: the subject/reachability rule is explicit (`AGENTS.md:74-79`). Add a checked producer/trace link for that claim, rather than renaming arbitrary hand-built records “reachable.”

### 1b. `:none`: HOLE

Construction against the stated refusal list:

```lisp
(defthm c04-identity (equal x x) :rule-classes nil)
(defteeth c04-identity
  :witness ((x 0))
  :breaks ()
  :mutations (:none "identity theorem; no mutation supplied"))
```

There are zero hypotheses to break. The positive assertion holds. The reason satisfies the mutation exception, and the whole visits field is optional. This can receive a generated-teeth row without any negative tooth. The permissions come directly from `build/codex/c04/SKETCH.md:21-26,39-42`. Unlike this sketch, the existing macro refuses a zero-hypothesis theorem with no mutation (`books/defkeystone.lisp:220-221`: `:no-teeth`). This example establishes the schema hole; it does not establish that existing registry checks would accept this tautology as a keystone. “Cite keystones” remains an independent gate (`AGENTS.md:80-82`).

A weaker but widespread failure needs no tautology: give every legitimate theorem `:mutations (:none "not needed")` and omit visits. Generated coverage can increase while mutation/cost coverage never improves. The sketch promises a table row but defines neither exception counters nor an exception budget (`build/codex/c04/SKETCH.md:39,48-52`).

**Change:** declare mandatory tooth classes in the **source obligation**, not in the test's optional arguments. Separate `:not-applicable` from `:deferred`, with an obligation identity and reason. Export and count both per theorem and per class. New sibling-generated keystones must have no new deferred exemptions by default. An exemption is not a completed tooth. Tightness may legitimately be inapplicable; that does not exempt the bound or its implementation link.

### 1c. Arbitrary mutations: HOLE

Replacing the exception in the preceding form by this is equally uninformative:

```lisp
:mutations ((always-false nil ((x 0))))
```

`(not nil)` holds, and trying to admit `nil` fails. Nothing relates that mutation to `c04-identity`, a host subject, or a plausible implementation error. The sketch emits only `(not M)` and a must-fail (`build/codex/c04/SKETCH.md:36`); existing mutation validation checks shape and bindings, not a relation to the statement (`books/defkeystone.lisp:144-153,305-319`). The latter must-fail may also fail because of rule admissibility rather than the intended claim; see 1f.

**Change:** define mutations as checked edits, for example:

```lisp
:mutations
 ((drop-delta :replace-call refresh-call :with stale-refresh-call
              :at conclusion-path :witness ...))
```

Or expose a small set of generator-owned fault constructors. Preserve the theorem's hypothesis set; check that the selected original occurrence exists exactly once at the path, that the replacement is well typed for the chosen claim, that it changes the term, and that the original and mutant differ only at the declared site. At the mutation witness require `H1 ... Hn`, the original conclusion, and failure of the mutated conclusion. For state/effect mutations, compare the complete relevant result/effects, not an arbitrary Boolean beside them.

A syntactic edit is still not a proof that a fault is meaningful. Reject constant-false replacement conclusions and require a named fault intent tied to the generated subject. There is no decidable general test for “interesting mutation”; the interface should enforce an auditable relationship and leave the remaining judgment visible. The existing withdrawal teeth offer an appropriate concrete pattern: “new list but ... old tries,” then wrong answers for the newly inserted target and cause (`tests/acl2/withdrawal-index-carried-tests.lisp:85-93`).

### 1d. Attainment: SOUND on hypotheses, HOLE on subject linkage

An `:attains` assignment outside the theorem's hypotheses is already excluded **if implemented literally**: the sketch requires `HYPS and (equal V B)` (`build/codex/c04/SKETCH.md:37-39`). Keep that requirement.

The missing requirement is what `V` counts. Choose `V=0`, `B=0`, and the positive witness. The generated bound and attainment both hold regardless of the host's work. More subtly, define `c04-visits` beside the function to count one outer step while the function's `equal`, predicate, index operation or fallback scans a million cells. Nothing in the signature ties that function to execution (`build/codex/c04/SKETCH.md:25,37-39,90-94`).

**Change:** require `:subject`, its actual executable definition/version, a metric, and either an instrumented execution returning `(value, effects, cost)` or a checked transformation linking the counter to that definition. Charge guards and called operations under explicit cost contracts. Generate natural-number obligations for cost and bound. The missing `:subject` on `defteeth` must be recovered from an independently checked obligation/registry link; the older `defkeystone` explicitly requires it (`books/defkeystone.lisp:200-201`).

Also separate **upper bound** from **tightness**. A valid upper bound need not be attained. One attainment at an empty input does not establish asymptotic sharpness: `V=n`, `B=100n` attains at zero. If the claim is “exactly the delta” or “sharp for each size,” generate that quantified size-indexed property; otherwise call the witness a single attaining example. Do not block useful safe bounds merely because they are conservative.

### 1e. Literal statements and labels: HOLE until the representation is specified

**Established from local ACL2 source:** `defthm` translates its input (`ACL2SRC/defthm.lisp:12120-12134`), passes translated and original terms separately to `add-rules` (`ACL2SRC/defthm.lisp:12217`), and stores them separately as `'theorem` and `'untranslated-theorem` (`ACL2SRC/defthm.lisp:10257-10277`). `and` macro-expands into nested `if` (`ACL2SRC/axioms.lisp:2186-2202`). `implies` itself is a logic function, not the `and` macro (`ACL2SRC/axioms.lisp:2098-2100`).

Consequently, for source `(implies (and (p x) (q x)) (r x))`, the world antecedent is an IF-shaped term, not a source list beginning with `and`. Both present source splitters only recognize an outer `implies` and source `and`: `books/defkeystone.lisp:86-102`, `tools/ledger.py:1070-1075`; the hand-teeth checker repeats that convention (`tools/teeth_check.py:1233-1240`). Feeding the world term to that splitter produces one hypothesis where the static side sees two. A break at which both `p` and `q` fail could then discharge the single world tooth; a source-count mirror must not claim two independent removals.

Other constructions:

* `(implies A (implies B C))`: either explicitly support a canonical two-hypothesis claim, with a checked equivalence, or treat the inner implication as the conclusion. Do not silently report separate B coverage.
* `(equal (if P X Y) Z)` or an `iff` statement: an occurrence of `P` is not automatically an antecedent. Zero top-level hypotheses is legitimate; internal branch witnesses are a distinct obligation.
* A single source macro `(both x)` expanding to `(and (p x) (q x))`: decide whether the unit of removal is the source hypothesis or its flattened translated conjuncts. “Literal” alone does not choose.
* `force`, `syntaxp`, `bind-free`, and LET/lambda-bound conditions: proof-search annotations and bound variables must not be treated as ordinary independent executable hypotheses by a textual splitter. Refuse unsupported cases by name until a translation policy and witness semantics exist.
* Reordering `(p x)`, `(p y)` retains the same labels `h1,h2`; a report can silently change what “h1 was broken” means. Unique function-symbol labels do not help repeated predicates. Source restatements, macro changes and inserted hypotheses require renewed statement binding.

**Change:** use an explicit canonical declaration such as `:claim (:hypotheses ((label term) ...) :conclusion term)`. At admission, translate that generated whole claim in the theorem's world and compare it to the stored theorem. For noncanonical forms either require exact structural reconstruction or a **named, separately proved equivalence**, while preserving which literal theorem is covered. Store translated terms plus the label-to-term mapping and formula digest. Do not equate mere logical equivalence with preservation of a particular hypothesis-removal contract.

The static tool should consume a certified normalized record, or verify its source declaration against a world-emitted normalized record bound to dependency digests. It must not independently guess the translation of arbitrary macros. The current approach has a useful seed—a literal expansion pinned in Lisp and checked by Python—but that example is a source-form fixture, not a world/source normalization protocol (`tests/acl2/defkeystone-tests.lisp:50-77`; `tests/test_ledger.py:1386-1397`). Extend it with all the cases above, refusal cases, package-qualified names, duplicate keywords, and generated/sibling forms.

### 1f. Must-fail: SOUND translation preflight; WEAK as evidence and expensive by default

Do not claim the existing checked wrapper accepts a missing theorem name or malformed term unchecked. It requires a fresh event name, translates the term, and translates hints (`tests/acl2/must-fail-checked.lisp:76-93`; `54-58`: `translate-hints+`). The sketch should preserve that protection. Missing static hint references should be refused, not counted as a negative tooth.

It still deliberately accepts bounded proof-search failure: the default is 300,000 steps (`tests/acl2/must-fail-checked.lisp:133,154-170`), and its own test demonstrates a **true theorem** failing at ten steps before being proved normally (`172-183`). The header accurately calls its claim “this does not prove within N steps” (`29-37`). A time/step limit, or a later computed-hint/theory error, cannot become a counterexample. Which particular dynamic errors a proposed generated hint can trigger is **UNVERIFIED** without execution.

The paired complete ground removal assertion supplies the counterexample; must-fail adds no logical refutation. It can test the proof harness, translation, and accidental admission, but should be classified as that. For a theorem admitted elsewhere, “default: NAME's own” hints is underspecified (`build/codex/c04/SKETCH.md:26`): the formula property is not a hints record, and original local lemmas/world settings may no longer be available.

**Change:** make proof-failure probes optional developer regressions, with explicit budgets and failure categories. Require positive checked refutations (evaluated pure ground terms or exact ground lemmas) for coverage. Do not copy hints implicitly across worlds. If retaining a probe, translate it after generating a fresh namespace, never grant `:unchecked`, and report search exhaustion separately from a witnessed false claim. This follows the actual rule: “failed proof search is not a counterexample” (`AGENTS.md:88-89`).

### 1g. Duplicate declarations and orphan test books: WEAK / HOLE

The sketch refuses “teeth declared twice” (`build/codex/c04/SKETCH.md:40-46`). That catches a second declaration **visible in one world**, not two separately certified books each declaring teeth for K. Conversely, two siblings including the same canonical teeth book should not require two owners or create a false conflict.

Construction: A-tests and B-tests independently cover K. Each sees no prior row. A later aggregate includes both and encounters conflicting rows; a different aggregate includes neither and sees no teeth. Or add K-tests to the tree without making it a certification root or dependency. A text scanner sees the form even though no claimed certified closure includes it. Existing discovery literally scans every Lisp file in `books/` and `tests/acl2/`, independently of a root closure (`tools/keystone_emit.py:69-93`). Actual certificate scope is roots and their include closure (`tools/green_check.py:235-244`).

**Change:** one canonical owner per `(theorem identity, statement fingerprint, schema version)`, checked repository-wide as well as in the world. Include paths may share that owner. Refuse conflicting rows; allow normal redundant inclusion of the same certified declaration. Require a named certified consumer root for every obligation and tooth, and make orphan declarations a finding. Record where local events were certified; a table row alone is not proof that its checks executed in the claimed world.

## 2. Fail-open paths and the mandatory consumer

### 2a. `fn-teeth-owed` / `defteeth-check`: HOLE

The proposed wiring names “the test/image world,” but no mandatory book, build hook, root list, late position or evidence consumer (`build/codex/c04/SKETCH.md:43-46`). A source generator can emit K and an owed row; the source certifies; nobody includes K-tests or calls the checker. Alternatively call the checker before including the next sibling's obligations. Both satisfy the described local mechanisms and leave the debt unobserved.

A world containing only tested source books cannot detect a missing source book; a checker enumerating only owed rows cannot detect a generator that forgot to emit its owed row. Ordinary source-only certification must remain possible, but it cannot be reported as completed teeth coverage.

**Concrete design change:** define a checked obligation manifest independently from the test forms, covering all registry keystones plus every sibling-generated keystone. Give each obligation its theorem formula, subject, required tooth classes, owner test root and schema version. Check both set inclusions: every expected obligation exists; every expected tooth has a successfully certified owner at matching bytes. Source admission records debt, never discharges it. Run the late checker after all declarations for each claimed closure; the external coverage consumer must refuse missing checker results, omitted roots, stale dependencies and unexpected exemptions. Make that consumer mandatory in the existing check/evidence path, not an optional CLI convention.

Do not solve this by making production source include all tests. A test aggregation world can include the source/image interface world; production can consume the resulting digest-bound evidence. Shard certification if necessary, but compare the union with the independently generated expected set. The current rule explicitly separates source, proof, image and deployment (`AGENTS.md:24-27`), and requires a cited manifest for changed behavior (`AGENTS.md:105-107`).

### 2b. Comparison with `def-carried`: SOUND in its checked boundary; narrower than advertised

There is real wiring to reuse, not just a similar macro name:

* `def-carried-check` takes a **name** and reruns `fn-cd-problem` against the then-current world (`books/def-carried.lisp:1072-1083`). Completeness enumerates `fn-interfaces` entries returning the carried stobj, including congruent stobjs (`753-759,777-809`), not arbitrary host writes.
* `definterface :raw-with (:carried NAME)` calls `fn-cd-raw-problem` (`books/definterface.lisp:542-561`), which rechecks generated statements and the row (`books/def-carried.lisp:1257-1277`).
* The native installer rechecks the loaded interface table and errors on refused declarations (`host/native/io.lisp:1205-1225`). It is called by the normal, DTN and store-test image builders (`host/native/build.lisp:430`; `host/native/build-dtn.lisp:327`; `host/native/build-store-test.lisp:114`). This catches late interface additions at that boundary.
* The static counterpart rejects undeclared dispatches when a carried raw declaration depends on completeness (`tools/interface_emit.py:445-455`), in addition to the raw-host access restriction described at `49-52`.

Therefore it is wrong to say this mechanism has no consumer. It is also wrong to treat it as a universal final audit of every carried row. Value-state rows require an enumeration rationale (`books/def-carried.lisp:801-804`) and are explicitly refused for raw dispatch (`1270-1272`). Rows not used at such a checked boundary need an explicit late consumer of their own. The sketch's value carries cannot inherit stobj completeness simply by emitting a table.

### 2c. Baseline ratchet: HOLE if it is a count; WEAK without history anchoring

The sketch says the hand count “ONLY SHRINKS” (`build/codex/c04/SKETCH.md:48-52`). A count permits replacing one old covered event with a new ungenerated event, or deleting an old tooth and adding an unrelated one, while preserving the total. Deleting and re-adding a name, or changing its theorem under the same name, must not reset its coverage class.

There is an instructive existing counterexample to trusting the adjective “only”: `owner_globals_check` compares to the **working-tree** JSON (`tools/owner_globals_check.py:127-139`). Its writer refuses increases for paths already in the baseline, but can add a new path (`129-135`). A hand edit can change the comparison point. This is a count lint, not a proof of historical monotonicity.

**Change:** baseline a set of grandfathered obligations, keyed by theorem/subject identity and fingerprint, not only a number. Compare it to an immutable integration-base record in the mandatory gate; reject growth, regenerated re-grandfathering, and generated-to-hand downgrades. Formula changes are new obligations unless an explicit checked migration preserves the binding. Preserve retired identities in history so deletion/re-addition cannot launder them. Independently check that removing a registry event did not remove coverage still required by its consumer. Generate counts from those sets.

### 2d. New events, the static mirror and certificates: HOLE without reverse checks

The present registry emitter starts from **forms**, then asks whether their IDs and citations exist (`tools/keystone_emit.py:163-206,248-269`). It does not implement the proposed reverse rule “every new registry event has a defteeth.” Adding only that new rule for forms already found would still miss an event with no form.

The present hand-teeth logic calls its citation counts a “CONVENTION” and a “heuristic” (`tools/teeth_check.py:1243-1269`), and its per-hypothesis check says “a floor and not a verdict” (`1348-1380`). The Makefile's teeth invocation is `--summary`, whereas the script returns nonzero for findings under `--strict` (`Makefile:2558-2567`; `tools/teeth_check.py:1709`). `keystone_emit --check` and interface checks are already mandatory commands (`Makefile:2763-2764`); they are appropriate consumers to extend, but today's behavior is not the promised ratchet.

**Change:** enumerate required registry/source events first, then look for teeth. Missing/unsupported static expansion must be a named failure, not an empty expansion credited as zero obligations. Compare certified world-normalized rows with the source declarations. Pin positive and negative fixtures across both implementations; the existing one-example parity check is necessary but not sufficient for world-dependent splitting (`tools/ledger.py:1177-1233`; `tests/acl2/defkeystone-tests.lisp:64-77`). Do not transfer a successful certificate to changed macro dependencies.

## 3. Carried readers: semantics and cost are separate contracts

### 3a. Negative set readers: SOUND with the actual bridge

For a complete set index, a negative probe excludes the key from the list; a positive probe may be a false positive. Returning FAST only in the negative arm and REFERENCE otherwise is sound **when the generated theorem proves the instantiated bridge and carry-to-completeness fact**. This is exactly the existing withdrawal design: “Soundness is not needed: a reader trusts only a negative answer” (`books/withdrawal-index-carried.lisp:21-30`); the definitions and bridge theorems show both branches (`85-129`).

There is no sound positive membership answer from completeness alone. Construct an index with an extra key absent from WS. `hasp` is true, so returning “present” would be wrong; the reference fallback remains correct. For `targets-of`, even an exact membership bit cannot reconstruct the target list and its order/multiplicity. Keep the fallback or use a richer exact index and a corresponding theorem.

**Change:** call this a negative filter, declare false positives permissible, and require branch-specific witnesses including false-positive fallback and stale carry. A “walk-at” witness must affirmatively check which branch ran; equality of answers on a tiny list does not show that.

### 3b. Exact folds and the rest of the population: WEAK, not one schema

The IF proof principle works for any sound sufficient condition. It does not make every index a negative membership filter. NEWNEWS carries suffix maxima and stops on `consp maxes`, a natural horizon, and a numeric threshold (`books/newnews-cursor.lisp:265-286`); its start transfers maxima only on a matching article list (`454-458`). Its exact fold depends on **oldest-first** processing (`73-83,176-212`). An arbitrary `hasp/key` probe does not describe that cursor or its residual-output invariant.

The other differences are substantive:

* `fn-prc` relates a trie **exactly** to known IDs from both pins and releases (`books/post-retain-carried.lisp:329-333,448-459`). Its reader uses both positive and negative trie results on an equal ledger (`774-791`); its delta removes/aligns pins while adding release IDs (`534-546,577-598`). A one-list prepend fold is insufficient.
* `fn-midx-refresh` and `fn-mxc-refresh` take an index and **separate** old/new article lists, and support unchanged, one-cons extension or rebuild (`books/msgid-index.lisp:213-219`; `books/msgid-index-concrete.lisp:105-111`). They are not `(KEY . INDEXES)` values.
* `fn-gidx-refresh` additionally treats nil buckets as a rebuild request, with a conditional correspondence premise (`books/owner.lisp:1121-1135`). That premise is not automatically the proposed uniform `carryp`.
* `fn-gacc` keys entries by rule text, archive and control; the refresh also checks a control cut (`books/group-access-cache.lisp:39-62,173-199`). Its reader returns a cached view or nil; the caller supplies the fallback (`93-115`; `books/served-catalog-chain.lisp:710-715,741-745`). It is a cache of views, not a single set over one list.

**Change:** pilot a narrow suffix-fold generator and explicitly parameterize fold order, empty representation, element/key domains, and index preservation laws. For exact indexes, generate a right-fold/model definition and prove its delta composition. For sets, require empty completeness and preservation of existing membership plus insertion of the new key. A constrained generic theorem needs these laws and an explicit functional substitution; naming `P/H/F/E` is not enough. The precedent says functional instances owe the defining equations **and constraints** (`books/def-loop.lisp:111-116`).

Make readers generic over a certified fast condition/answer pair; distinguish `:negative-filter`, `:exact-answer`, and cursor use. Keep retention deltas and per-rule caches as separate generators or hand-written clients of shared lower-level fold machinery. For nil carries, define accessors to return each index's `E`, or require `E=nil`; otherwise an arbitrary nonnil exact-fold base need not satisfy `carryp(nil)` even though the sketch promises that theorem (`build/codex/c04/SKETCH.md:68-75`).

### 3c. “FAST does not mention WS”: HOLE as a visit proof

Construction:

```lisp
:fast (c04-hidden-walk C) ; its body traverses (NAME-WS C)
```

Or pass another formal `YS` equal to WS. Neither contains the forbidden symbol WS. PRE or PROBE can itself do a whole-list traversal. Most directly, the generated IF evaluates `(equal WS (NAME-WS C))` before FAST (`build/codex/c04/SKETCH.md:90-94`). The forbidden-variable test cannot bound any of those costs.

**Change:** remove the claim that symbol absence is a structural visit bound. It can be a conservative syntactic warning. Derive the cost of the **whole reader**, including transitive callees, from an instrumented definition or explicit checked cost contracts. Audit both logical and executable bodies, including representation attachments; a theorem about an unused logical helper does not meet the subject rule (`AGENTS.md:74-79`).

### 3d. Honest reader cost and positive/stale paths: WEAK unless explicitly scoped

Let `A` be the actual short-circuit condition. The useful accounting is:

```
T_R = T_condition + (if A then T_fast else T_reference)
```

`T_condition` charges precisely the PRE, equality and probe evaluations actually reached. A negative set hit may avoid the reference's WS visits, while still paying equality and index work. A positive set probe, failed PRE, stale carry or nil carry can execute the whole reference scan. The existing targeted reader really recurses through withdrawals (`books/post-identity-index.lisp:86-91`), and PRF-1231 explicitly scopes its fast figures to the negative path and leaves the positive O(W) path (`planning/proofs.json:21233`).

**Change:** generate a cost theorem over R, with named fresh-negative, fresh-positive, stale and absent-carry arms; distinguish list cells, key characters, trie/hash operations, allocation and output bytes as needed. Include a fallback bound rather than excluding fallback from the claim. If fallback cannot fit the served quantum, make it resumable or require a proved preparation/freshness precondition at the serving boundary. “Correct but always rebuilding” is not a bounded served implementation under the rule to bound work per scheduling step (`AGENTS.md:41-54`).

## 4. Sharing, EQUAL, recovery and the actual host population

### 4a. The general cost claim: HOLE, even with a shared suffix

Take `old` to be N copies of `1`, and `ws` to be N further copies consed onto that **same old object**. Each nonmatching `(equal tail old)` can compare N equal elements before discovering a length difference. There are N such comparisons before the shared tail is reached. The outer walk visits N new elements, but comparisons do Θ(N²) list work. This is admitted by the generic default element predicate `t` and the stated append hypothesis (`build/codex/c04/SKETCH.md:71,75-76`). Sharing makes the final successful comparison cheap; it does not make every failed comparison cheap.

A second construction is a fresh copy of `old` with the same contents. An equality hit costs Θ(N), and a refresh returning the **old carry unchanged** preserves the old pointer. Every subsequent reader can keep paying Θ(N). That return behavior is present in `fn-wix-refresh`, `fn-nnw-refresh`, `fn-prc-refresh`, and `fn-gacc-refresh` (`books/withdrawal-index-carried.lisp:149-160`; `books/newnews-cursor.lisp:204-212`; `books/post-retain-carried.lisp:590-598`; `books/group-access-cache.lisp:182-199`). A semantic “key-of-refresh equals input” theorem proves EQUAL, not EQ.

Do not conflate these constructions: two completely equal lists cause an immediate equality **success**, so the loop stops; they do not by themselves cause full comparisons at every later step. Quadratic behavior needs a sequence of costly unsuccessful comparisons, such as repeated elements/long common prefixes.

The exact SBCL implementation and measured timings on the served image are **UNVERIFIED** here. The source itself states an EQ-first sharing assumption (`books/withdrawal-index-carried.lisp:29-30`; `books/group-access-cache.lisp:136-139`); I have not converted that comment into qualification evidence. Counting only outer iterations is inadequate even under that assumption.

### 4b. Host call-site and lifecycle inventory

The following distinguishes direct calls, calls through wrappers, and absent wiring. A name in a comment, theorem or instrumentation list is not a host call.

| Population | Refresh path and source of key | Reader path and consequence |
| --- | --- | --- |
| `fn-wix` | No active host refresh found at this revision. The book explicitly says “once wired” (`books/withdrawal-index-carried.lisp:42-50`); the host still says the tries are pending (`host/owner-host.lisp:2875-2877`). | The two primitive readers are `fn-wix-targetedp` and `fn-wix-targets-of` (`books/withdrawal-index-carried.lisp:85-99`); wrappers are `fn-wix-find-article-cat` and `fn-wix-existing-action-cat` (`242-285`). PRF-1231 names their **intended**, not existing, host replacements (`planning/proofs.json:21233`). There is no current host carry lifecycle to assert is shared. |
| `fn-nnw` | No active host refresh found. “fn-nnw-response is called by nothing served yet”; refreshing the carry is explicitly pending (`books/newnews-cursor.lisp:42-46`). | `fn-nnw-start` checks article-list equality (`454-458`); `fn-nnw-step` consumes cursor tail/maxes (`272-295`); response/run bridges are defined (`505-524`). No served recovery/checkpoint/reconfiguration/reclaim carry lifecycle is established by those functions. |
| `fn-prc` | Direct refresh in `fn-owner-prepare`, `fn-owner-prepare-buffer`, and transit preparation (`host/owner-host.lisp:1825-1849,1985-2026,2882-2886`), plus moved host-entry definitions for identity preparation and completion (`books/owner-retain-transitions.lisp:90-98,151-170`). The actual ledger object is taken from the current store node. | Buffer POST calls `fn-ppc-pout-prepare-article-cat` (`host/owner-host.lisp:2010-2012`), whose lower preparation uses `fn-prc-admissiblep` (`books/post-prepare-catalog.lisp:104`); transit uses it via `fn-pta-decide-cat` (`host/owner-host.lisp:2885-2890`; `books/peer-transit-indexed.lisp:151`); identity uses it in `books/identity-retain-carried.lisp:32,93`. This is a real served equality check against the ledger. |
| `fn-midx` / `fn-gidx-refresh` | They run inside `fn-own-refresh` and its indexed counterpart (`books/owner.lisp:1196-1207`; `books/owner-refresh-indexed.lisp:51-69`). Indexed completion reaches that counterpart (`155-165`); a host completion invokes the carried indexed completion (`books/owner-retain-transitions.lisp:165-170`). | Reads use pinned trie/buckets. Example concrete Message-ID reader is `fn-pix-msgid-retrieval-indexed` (`books/peer-offer-indexed.lisp:143-156`); group reads use the pinned command arms, including `fn-gidx-listgroup-command` (`books/nntp.lisp:393-447`; `books/peer-offer-indexed.lisp:169-172`). Bucket article readers call `fn-midx-lookup` (`books/group-bucket-article.lisp:24-38,61-92`). The native occurrence at `host/native/io.lisp:6155` is an instrumentation-list entry, not a direct refresh/lookup call. |
| `fn-mxc` | Its concrete refresh exists (`books/msgid-index-concrete.lisp:105-111`), but the inspected owner refreshes call `fn-midx-refresh` as above. The book itself says concrete extend/build/refresh have no host caller (`24-25`). | The concrete lookup **is** on reader chains: `fn-pix-msgid-retrieval-indexed` calls it (`books/peer-offer-indexed.lisp:152`), and `fn-pidx-find-article` can call it (`books/post-identity-index.lisp:95-102`). These do not establish that the concrete refresh is served. |
| `fn-gacc` | `fn-owner-chunk-span-evaluate` prepares the cache immediately before its read (`host/owner-host.lisp:4230,4271-4276`). `fn-scr-prepare-access` takes the connection's pinned archive/control and invokes `fn-gacc-prepare` (`books/served-catalog-chain.lisp:2588-2599`), which calls refresh (`books/group-access-cache.lisp:213-216`). | The same host read receives the prepared cache; its install function stores it (`host/owner-host.lisp:4271-4288`). `fn-scr-cached-view` invokes `fn-gacc-view`; restricted dispatch consumes that view (`books/served-catalog-chain.lisp:710-715,741-751`). The key is per rule **and pin**, not necessarily the latest owner article list. |

For the trie/group readers, this identifies the source host entry and intervening reader dispatch, not a claim that every legacy reader arm is currently reachable through every command. Exact branch reachability and performance of the deployed native image are **UNVERIFIED** without the forbidden runtime work.

**Recovery and checkpoint reload — SOUND sharing construction for the retention carry.** Native open invokes `fn-owner-recover-from-store-open` (`host/native/owner.lisp:1101`). That host entry installs from the opened result (`host/owner-host.lisp:458-470`). `fn-owner-install-extended` first installs the owner, then calls `fn-prc-refresh nil` on the retention ledger read back from that installed owner (`books/owner-recovery-retain.lisp:168-177`). It does not deserialize an old retention carry independently and compare it against another replay's list. The generated `cons ledger trie` retains this argument (`books/post-retain-carried.lisp:590-598`). Both extended-checkpoint and full-open paths use the same owner installation (`books/owner-checkpoint-open.lisp:47-70`; `host/owner-host.lisp:415-453`). Thus the suggested persistent equal-but-unshared recovery bug is not established for `fn-prc`.

**Reclaim — SOUND retention rebase; WEAK cache lifetime.** The off-mutex rebuild returns an owner and a carry made from **that owner's** ledger (`books/owner-reclaim-carry.lisp:14-26`). Swap installs the rebuilt store/view and its carry field (`books/owner-reclaim-pass.lisp:381-393,423-428`; `books/owner-recovery-retain.lisp:43-55`). The native calls are `fn-owner-orcp-rebuild` and `fn-owner-orcp-swap` (`host/native/owner.lisp:5731-5732,5759`). Again the retention carry is rebuilt against the installed object, not a separately decoded equal copy.

The access-cache global is read/written by the chunk path (`host/owner-host.lisp:1322-1325,4281-4288`); the inspected reclaim swap resets other carries but does not explicitly reset this cache (`books/owner-recovery-retain.lisp:43-76`). Re-pinning moves connections to rebuilt views (`books/owner-reclaim-pass.lisp:377-393`). Therefore the next access refresh can compare an old cache key against a rebuilt archive/control. If equal but unshared, the equality-hit branch returns the old entry; if unequal late, at least that refresh pays the comparison before rebuilding. **UNVERIFIED:** a complete legal reclaim trace yielding a large equal-but-unshared key, or a particular late mismatch, including payload-handle allocation and native eligibility. Do not count “no-op reclaim” as such a trace: the native `:none` decision returns before rebuild (`host/native/owner.lisp:5680-5687`).

**Ordinary writes — mixed; inspect the operation, not the word “copy.”** Retention admission conses onto the existing pins (`books/retention.lisp:382-390`). Release's loop copies the prefix but returns `revappend acc (cdr pins)` at the removed pin, preserving the remaining tail (`205-221,424-429`). `fn-prc-pins-walk` deliberately sets `check=nil` while aligned heads match (`books/post-retain-carried.lisp:534-546`), avoiding a whole-suffix equality at every aligned element. Removing that flag while “unifying” the walk would regress it. A release is still proportional to the affected prefix, not a constant-time carry update.

The owner keeps old-visible for unchanged raw/verdict inputs and generally conses an ordinary new article onto it; withdrawal filtering and rebuild arms can copy it (`books/control-visible.lisp:113-123,685-691`). Withdrawal resolution calls `fn-ctl-set-tlocks` and can reconstruct the list (`668-684`; its loop/wrapper at `611-640`). Those are real list-rewriting paths. PRF-1231 already records the resulting unbounded refresh as owed before wiring (`planning/proofs.json:21233`). A new macro must not replace that open item with the outer-delta count.

**Reconfiguration — no evidence of a blanket list-copy bug.** The staged config completion arm retains the same owner and publishes configuration separately (`books/owner-config.lisp:498-509`). New/advanced connections have their own configuration pins (`529-546,548-556`); the access cache keys its rule and pinned archive/control (`books/group-access-cache.lisp:39-62,182-199`). Changed rule/control may rebuild. A theorem about a list suffix does not cover those keys, but claiming every config edit copies the ledger/articles would also be unsupported.

**Reachable quadratic verdict: UNVERIFIED for the actual served population.** The generic repeated-element construction is decisive against the unrestricted macro cost claim. It is not automatically a reachable article history: article-state invariants require distinct Message-IDs (`books/acceptance.lisp:111-124,371-374`), and early differing IDs can make unsuccessful comparisons cheap. The current retention refresh also has the mitigation just described. No complete source-established/native-observed quadratic served trace was obtained here. Conversely, there is no sharing/nonmatching-prefix invariant in the proposed interface sufficient to justify its unconditional cost claim. Do not claim either universal quadratic behavior or universal constant-time equality.

### 4c. Representation choices: WEAK as sketched; prefer explicit provenance

**Minimal improvement:** on semantic equality, rebuild just the carry's outer key cell using the *current input object* and reuse the indexes; likewise rebase equal cache keys. This prevents repeatedly retaining an obsolete pointer after one expensive comparison. It does not make that first comparison cheap or bound unsuccessful comparisons.

**Length option:** carry a validated length, with `n=len(key)`, and provide/maintain the new input length. Compare tail lengths first and perform structural equality only at the possible matching length. This removes the repeated-list quadratic construction but still needs a possible O(N) equality at that point and a fallback bound. Calling `len` at every iteration recreates quadratic work; calling it once on every request is still whole-list work. Length alone cannot distinguish different lists of the same size.

**Recommended direction:** an owner-maintained history/view identity with epoch plus generation/root identity, and a proved relation between that identity, the list/model projection, and the index. A carry invariant should say `index = fold(alpha(root))` (or completeness over it), plus validity of the identity. For delta extension, prove that the new version's projection is `append delta old-projection`; for rebuild, establish correspondence to the new root. Equality of stamps may replace list comparison **only if** the owner invariant guarantees that equal stamps identify the same relevant view in the compared domain. Version counters alone without that invariant are another correctness hole. Recovery/reclaim/reconfiguration/withdrawal and pinned readers must preserve or invalidate the right epoch/view keys. Include wrap/representation bounds and profile compatibility. This is consistent with the agreed page/root direction (`planning/decisions.md:1674-1676`) and D27's representation obligations (`AGENTS.md:41-54`); it is a recommendation, not existing machinery supplied by this sketch.

**Do not prescribe `(mbe :logic (equal a b) :exec (eq a b))` as a magic fix.** Equal cons lists need not be EQ. ACL2's own `eq` guard requires one operand to be a symbol (`ACL2SRC/axioms.lisp:2073-2078`), so plain EQ on arbitrary list arguments does not even provide the proposed guard-verified primitive. An identity-based optimization needs a supported concrete facility and a refinement of the **whole operation**: identity success safely reuses the index, failure takes a correct fallback. It cannot prove structural equality and identity equivalent on unrestricted lists. Honsing likewise needs a canonicalization/lifetime invariant and allocation accounting; it is not free. Which supported identity/hons facility is appropriate for the selected runtime is **UNVERIFIED** in this consultation.

## 5. Writer policing

### 5a. Textual right-hand-side policing: HOLE as a semantic guarantee

The proposed rule is “written only by (NAME-refresh ...) or nil” (`build/codex/c04/SKETCH.md:103-106`). Three counterconstructions:

```lisp
(f-put-global 'carry (NAME-refresh fabricated-bad-carry ws) state)
(let ((x (NAME-refresh valid-carry ws))) (carry-put x state))
(carry-put (c04-helper-returning-arbitrary-data) state)
```

The first has the allowed spelling but lacks the refresh preservation premise. The second is a legitimate write that a literal-RHS rule rejects. The third can be invisible if scanning only direct global operations. `setf`, aliases, computed names, `funcall`, raw Lisp, another global holding the carry, and stobj fields widen that discrepancy. These are language-level constructions; acceptance by an unbuilt successor checker is **UNVERIFIED**.

The existing retention setter illustrates the real issue: it accepts an arbitrary carry argument and performs `f-put-global`; its documentation explicitly says its effect equations do not establish the invariant of a whole owner transition (`books/owner-retain-state.lisp:1-16`). Reclaim's legitimate writer receives `(nth 2 rebuilt)`, not a textual refresh (`books/owner-recovery-retain.lisp:55`), and the cache installer receives its `cache` parameter (`host/owner-host.lisp:4281-4286`).

**Change:** prefer generated encapsulated state transitions with an establishment theorem, preservation theorem and producer/return-value link. Enumerate and restrict raw boundary access, then check the actual caller/value provenance in the supported language subset; reject opaque access rather than assuming safety. A conservative syntactic checker can be useful inside that restricted subset, but it is not an unrestricted Lisp alias analysis. Inventory all storage locations and all updaters; moving a carry from a global to a stobj field must not erase the obligation. Keep host-boundary evidence distinct from logical preservation.

### 5b. “or nil”: SOUND for value correctness only when proved; HOLE for progress/cost

If `carryp(nil)` holds and the reader really falls back, repeatedly clearing a carry can remain semantically correct while scanning the entire list forever. The existing withdrawal reader's branches make that construction concrete (`books/withdrawal-index-carried.lisp:79-99`). The sketch allows nil writers without a frequency or scheduling contract (`build/codex/c04/SKETCH.md:103-106`).

**Change:** distinguish invalidation from preparation. Permit invalidation at named lifecycle events; prove the serving path either prepares a current carry or follows a bounded/resumable fallback. Emit hit/miss/rebuild counters and retain performance scenarios that fail if a writer changes to “always nil.” Do not ban legitimate invalidation or confuse the value invariant with the freshness invariant. For arbitrary `:empty E`, first establish that nil really is a valid representation (3b).

### 5c. What existing rules actually check: SOUND, narrowly

`owner_globals_check` counts distinct quoted `fn-owner-*` names following an accessor token ending in `-global`, per file (`tools/owner_globals_check.py:16-22,43-44,79-90`). It does not inspect their values, prove provenance, or load a carried-view table. Its baseline is per-file counts (`94-107`).

`def-carried` is substantially stronger but different. It derives stobj outputs from the world and refuses value-state raw dispatch (`books/def-carried.lisp:86-96,1270-1272`); checks every declared interface returning that state is established or preserved (`753-809`); regenerates statement obligations (`516-528,720-751`); and has a requirement table distinguishing transitions and opens (`1171-1175`). Transitions may not add unestablished `:hyps`; conditional opens need witnessed reachability and exact producers and must not be callable through undeclared producer paths/attachments (`1177-1238`). Its literal-producer-call check deliberately rejects computed/let-bound actuals it cannot justify (`1098-1117`).

That is a checked-world policy plus host access restrictions, not a host regex saying “refresh or nil.” Reuse the policy architecture and extend it with explicit value-state provenance if needed; do not claim its existing guarantees for a new table just because `interface_emit` can print it.

## 6. What the sketch misses

### 6a. Keyset interface and bridge: HOLE until the relation is explicit

`:logic-member M`, `:ys-key F`, `:each P` and `:base B` do not specify whether the per-element query asks for membership, nonmembership or incremental distinctness (`build/codex/c04/SKETCH.md:113-122`). The proposed first clients differ exactly there: successes require a bound pair plus `fn-sf-pairp` and a null terminal tail (`books/store-files.lisp:518-545`); retention requires every ID **unbound** (`books/retention.lisp:22-46`). Distinctness must check before inserting each element, rather than fill all of XS and then query it (`books/acceptance-alloc.lisp:140-168`).

Counterconstruction: choose `F` constantly zero while M is ordinary membership. Two different keys collapse; a query can hit a key not in the original YS. A generic theorem assuming “membership agrees” would not apply automatically to this instance. ACL2 should refuse the bridge; the interface must make the owed obligation explicit rather than promise automatic generation for arbitrary M/F.

**Change:** require `:sense :present|:absent` for the fill/check family, explicit XS query-key and YS insertion-key terms, declared equality relation, guards/domain predicates, and a **named membership correspondence theorem**. Handle distinctness as its own scan/insert shape. Generate and discharge both directions of the appropriate membership equivalence under the precise domain. Preserve dotted-list behavior (`:base (null xs)` versus `t`) rather than silently normalizing to a true list.

The empty-table premise matters. Existing fill/check bridges require `(not (consp (nth 0 fn-keyset)))` (`books/retention.lisp:29-34`; `books/store-files.lisp:1184-1189`; `books/acceptance-alloc.lisp:202-207`). A table initially containing a key can make `XS=(key), YS=nil` incorrectly pass subset or fail disjointness. The local wrapper discharges emptiness by construction; that is why its full-result theorem can be unconditional (`books/acceptance-alloc.lisp:209-218`). Generate the stronger arbitrary-table membership-union lemma and the empty-table specialization, then the wrapper bridge. Verify guards for fill, scan, wrapper and dispatch, not only the public name.

### 6b. Threshold, local stobj and costs: WEAK

The current threshold is eight cons cells, checked by a fixed sequence of `consp` tests (`books/acceptance-alloc.lisp:220-224`); retention dispatches on YS (`books/retention.lisp:62-69`). The success-list path has a different valuable shortcut: no successes means no table allocation/fill (`books/store-files.lisp:542-545`). A uniform `:when-long t` can accidentally erase that shortcut.

**Change:** make the branch policy explicit and preserve empty-XS behavior. Generate bridges for both short-walk and keyset branches plus the composed MBE. Teeth should cover 0, threshold−1, threshold, threshold+1, success and failure in both paths, malformed/dotted tails where guards allow them, a lossy-key mutation, inverted membership, forgotten per-element predicate, and a contaminated-table mutation. Include a nonempty accepted witness; an empty input can hide broken membership in either branch.

A local stobj supplies isolation, not a time or space bound. The concrete keyset is a hash table with EQUAL keys (`books/acceptance-alloc.lisp:124`); fill and scan execute one operation per reached list element (`170-182`). State the visit bound as insertions/lookups plus key extraction, hashing/equality, allocation and initialization costs. An unconditional worst-case linear **runtime** claim for arbitrary long keys or adversarial hash behavior is **UNVERIFIED**. If the wrapper runs on a scheduling path, its whole-table allocation/scan must fit the declared profile/quantum or become resumable. Do not reintroduce whole-state revalidation on each served request (`AGENTS.md:95-96`).

### 6c. Pilot and naming: WEAK

Withdrawal is a good semantic pilot for **two negative filters**, but its pending host wiring and list-rewrite cost are already explicit (`books/withdrawal-index-carried.lisp:42-50`; `planning/proofs.json:21233`). NEWNEWS is a good second pilot for an exact, order-sensitive fold, not evidence of a served reader speedup (`books/newnews-cursor.lisp:42-46,73-83`). Keep those pilot claims source-scoped until their actual producer/reader paths exist.

There are naming collisions before any hypothetical future instance: `fn-wix-ws`, `fn-wix-carryp`, `fn-wix-refresh`, and the proposed theorem names already exist (`books/withdrawal-index-carried.lisp:60-80,149,221-232`). The sketch promises to preserve PRF-1231's names and rename `fn-nnw-car-of-refresh` (`build/codex/c04/SKETCH.md:107-109`); that NEWNEWS name is still in the proof row's statement (`planning/proofs.json:21253`). At the inspected revision both pilot rows are `planned`, and their names are in prose rather than an `events` array (`planning/proofs.json:21231-21265`). Do not call them already generated registry citations.

**Change:** precompute the complete generated namespace, check collisions in source and world, and define whether the macro **defines** or **adopts** an existing function. Preserve existing names by options where practical; otherwise update every registry/curated citation, host interface, test and consumer together. If compatibility aliases remain, label them as aliases/restatements rather than new keystones (`AGENTS.md:80-82`).

A further overpromise: “bad carry as the removal” cannot apply uniformly to every generated theorem (`build/codex/c04/SKETCH.md:97-101`). `carryp-of-nil` and key-of-refresh may have no hypotheses; a particular rebuild path may repair a bad carry, while another retains it. Derive each tooth from its actual theorem and arm. Do not attach one canned bad-carry example to every generated name.

### 6d. D27, `def-representation`, and the library boundary: WEAK

A concise generator can still institutionalize the wrong representation. D27 requires concrete executable representations, guard verification and correspondence at host-called boundaries (`planning/decisions.md:1204-1210`; `AGENTS.md:48-54`); D41 selects typed pages, byte pools and root records (`planning/decisions.md:1674-1676`). A carry holding an entire old list also retains that list; a per-rule cache can retain several old views. Count retained storage and invalidation lifetime, not only new conses during refresh.

The existing representation generator already supports abstract/concrete exports, scalar logical views and generic attachments (`books/def-representation.lisp:10-47`), and checks attachment ancestors of recognizers/correspondence (`18-27`). An arbitrary constrained key/put/has function reachable from a generated recognizer can interact with those restrictions. Proof sharing through functional instantiation does not remove attachment or guard obligations.

**Change:** keep list folds as logical specifications while allowing a concrete index/root representation with explicit abstraction. Generate bridges for results and any stobj effects. Compose the carried invariant with the representation invariant; do not materialize the entire logical list merely to refresh or check freshness. Scope the list pilot honestly if the concrete integration is a separate stage. Reuse `def-loop` for supported loop shapes, but do not assume it already generates arbitrary stateful folds: it explicitly excludes a loop threading a stobj and accumulating (`books/def-loop.lisp:103-106`).

### 6e. Certification cost and counting: WEAK

The sketch's arithmetic is already imprecise: “3,860 keystone events” and “other 3,850” are written beside “7 uses” (`build/codex/c04/SKETCH.md:12-15`). A read-only stdlib JSON count of this checkout finds 3,860 **event references**, but 3,762 distinct event names, using the `events` lists in `planning/proofs.json:1` (the same iteration shape as `tools/teeth_check.py:1337-1344`). A simple column-zero source scan finds 31 `defkeystone` forms across six test files, including the macro test; examples beyond the claimed seven are at `tests/acl2/resource-vector-tests.lisp:210-415`, `tests/acl2/resource-vector-tree-tests.lisp:132-180`, `tests/acl2/log-sink-tests.lisp:47-87`, `tests/acl2/feed-connection-teeth-tests.lisp:193-453`, `tests/acl2/resource-vector-relations-tests.lisp:68-95`, and `tests/acl2/defkeystone-tests.lisp:34`. This lexical count is not a certified coverage count.

Deduplicate theorem obligations while retaining all registry consumers. Let H be the number of removal probes and M mutation probes: the proposed default can spend up to roughly `300000*(H+M)` prover steps in failed searches before considering positive/bound proofs; 3,860 probes alone correspond to 1.158 billion budgeted steps, not a prediction of actual work (`tests/acl2/must-fail-checked.lisp:133,154-170`). Removing default failed re-proofs in favor of checked ground refutations is both stronger evidence and a better scaling choice.

**Change:** certify the shared schema and its adversarial fixtures once; instantiate cheap witness checks; reserve bounded failed-search experiments for selected generator/harness regressions. Measure instance proof steps and changed-root critical paths, reuse matching certificates, and account for sibling fan-in. The project explicitly wants affected roots rather than lane closure runs (`AGENTS.md:126-127`); no consultation-time certification was performed here.

### 6f. Program-mode sibling API: HOLE if the helper is a bare emitter

The source generator cannot construct `(defthm K ...)` and immediately ask `fn-teeth-events` to read K from the **same pre-admission WRLD**. K is not there yet. Nor can a helper trust a caller-supplied stale world after later events change declarations. This follows directly from the proposed “NAME an admitted theorem in this world” contract (`build/codex/c04/SKETCH.md:19,28-31`) versus sibling source-side generation (`43-46`).

Other failure constructions: a sibling calls the emitter without the refusal function; splices only the assertions but forgets the row/owed event; marks only some generated theorems as owed; places all checks inside `local` but exports an unbound completion row; forwards quoted terms with captured helper variables; generates colliding names; or allows an arbitrary `make-event`/program call inside witness values. Not all would admit in ACL2, but the API should fail predictably and never convert an error into empty coverage.

**Change before any sibling takes a dependency:**

1. A single checked entry point performs normalization, refusal and emission; failure is an error result, never an empty event list. The explanatory refusal function calls the same validator.
2. Source expansion defines K, then emits a staged `make-event` that reads the **current** world to register its exact obligation. The test-side staged event reads admitted K and emits checked teeth; callers do not supply their own statement split or completion row.
3. Versioned rows include theorem/formula identity, subject, hypothesis mapping, required classes, witness modes, exceptions, canonical test owner and generated names. Row presence is not itself successful evaluation/certification.
4. Fail on unknown/duplicate keywords, repeated labels, incomplete binding maps, unexpected free variables, unsupported evaluation/effect modes and name collisions. Specify inheritance/override order of witness bindings; do not accidentally change the existing `let*` override convention (`books/defkeystone.lisp:224-237`).
5. Add sibling integration fixtures: sequential admission, late obligations, two includes of one owner, two competing owners, missing tests/checker, translated/source disagreement, and a source theorem changed without updating its teeth.

The macro must also specify the one constraint its signature currently omits: how its source-only obligations and test-only evidence compose without source books depending on `tests/acl2/must-fail-checked`. The existing macro intentionally leaves that include to test clients (`books/defkeystone.lisp:66-70`); moving it implicitly into sibling source expansion would break the stated layering.

### 6g. “Net negative diff”: WEAK acceptance criterion

“Diff must be net negative” is a proposed pilot requirement (`build/codex/c04/SKETCH.md:107-109`), not evidence of correctness or simplification. Deleting witnesses, replacing explicit costs with unlinked counters, or putting complexity into a second static expander can all make the diff smaller.

Use acceptance criteria that the sketch can actually satisfy: unchanged observable behavior and literal claims (or explicit approved theorem migrations); generated, certified teeth tied to the host subject; mandatory coverage with no new uncounted exemptions; matching source/world schema; verified guards and representation bridges; bounded reader/refresh branches with honest fallback costs; and measured reduction in maintained duplication and proof work across at least the two distinct pilot kinds. Net source reduction is useful supporting evidence after those obligations are met, not a gate that encourages hiding them.

The consultation leaves runtime equality timings, concrete reachable worst-case traces, actual new macro acceptance, and new certification results **UNVERIFIED**. Those are implementation/qualification questions, not reasons to let siblings depend on an undefined evidence contract.

## TEETH CONTRACT v1 (2026-10-03, after c04; what DEF-ENTRY / DEF-COMMAND / DEF-HOLDER call)

### The form
    (defteeth NAME
      :claim (((L1 H1) ... (Ln Hn)) C)       ; REQUIRED: labelled source hypotheses + conclusion
      [:subject FN]                           ; the host-called function; REQUIRED when a bound is stated
      :witness ((VAR VAL) ...) | :witness-lemma THM
      :breaks ((Li ((VAR VAL) ...) [:logical "why outside the guard domain"]) ...)   ; one per Li
      :mutations ((L (:conclusion C2) | (:hypothesis Li H2) ((VAR VAL) ...)) ...)
                 | (:not-applicable "why") | (:deferred "why")
      [:corrupt ((L ((VAR VAL) ...)) ...)]
      [:visits ((L V B :attains ((VAR VAL) ...) | :not-attained "why" [:rests-on (A ...)] [:hints H]) ...)]
      [:allocation (... the same shape ...)]
      [:must-fail t]                          ; also register the weakened/mutant statements as
                                              ; must-fail-checked (off by default: proof-search
                                              ; exhaustion is not a counterexample; c04 1f/6e)
      [:hints H])
    (defkeystone NAME TERM :subject FN [:id ..] [:restates ..] . SPEC)   ; = defthm + defteeth, the
                                              ; :claim derived from TERM (source `implies'/`and')

### Binding (c04 1e): the TRANSLATED statement
At admission `(implies (and H1 .. Hn) C)` is translated in the current world and must be EQUAL to
(getpropc NAME 'theorem); else refused `:claim-differs` (the message prints both). Labels bind to the
DECLARED source hypotheses, so a removal is per declared hypothesis, never per translated conjunct; a
theorem whose literal form is not `(implies (and ...) C)` declares the claim that IS its statement
(e.g. one hypothesis, or none) or is refused. The static side reads the :claim, never the world; it
reports a `claim-vs-source` finding when the source statement is an `(implies (and ...) C)` whose
parts differ from the claim (consistency only; the world check at certification is the authority).

### Witness modes (c04 1a)
- executable: closed, logic-valued bindings; the positive witness and each bound witness run UNDER
  GUARDS (a guard violation fails the book); a removal/mutation/corrupt witness runs logically
  (with-guard-checking :none) ONLY when its entry says `:logical "why"`, else under guards; the row
  records :reachable-removal / :logical-removal per label.
- :witness-lemma THM: a named ground theorem whose formula must EQUAL the translated instantiated
  claim (and H1[s] .. Hn[s] C[s]); for predicates no evaluator runs. (Stobj traces: not in v1;
  a stobj formal is left unbound and the live stobj is the witness.)

### Mutations (c04 1c): checked edits, never a free term
(:conclusion C2): the mutant is the claim with C2 for C; refused when C2 is C, or a constant
(nil/t). (:hypothesis Li H2): the mutant has H2 for Hi; refused when H2 is Hi or t. At the
mutation witness every Hi holds, C holds, and the edited part fails (for :conclusion, (not C2);
for :hypothesis, H2 holds and C fails). :not-applicable and :deferred are recorded and COUNTED per
theorem and per class; a deferred mutation is not a tooth.

### Bounds (c04 1d): :visits / :allocation
NAME-visits-L / NAME-allocation-L : (implies (and H...) (<= V B)), proved with the entry's :hints;
evaluated at the witness; :attains evaluated under guards, or :not-attained "why" recorded. A bound
without :subject is refused. V is the caller's visit-counting term; this generator records, it does
not derive (COST-GATE / DEF-ENTRY tie V to the executed definition).

### Staging for a sibling generator (c04 6f)
A source-side macro cannot read K from the world before admitting it. It emits, in its progn, in order:
    (defthm K ...)                                        ; the keystone
    (table fn-teeth-owed 'K '(:by MACRO :claim CLAIM [:subject FN] [:visits ((V B [:rests-on ..]) ..)]
                              [:allocation (..)]))        ; the debt: what the teeth MUST say
and either, when the witnesses are in hand (a test-side macro), `(defteeth K :claim CLAIM ...)` as a
LATER event of the same progn (defteeth expands in a make-event that runs after the defthm), or
nothing more. Program-mode entry points, world-free: (fn-teeth-refusal NAME SPEC) -> nil or
(REASON . DETAILS) over the SPEC alone (claim shape, labels, breaks, mutations, bounds);
(fn-teeth-form NAME SPEC) -> the make-event form to splice (it binds to the world when it runs:
claim-vs-theorem, :witness-lemma formula, declared-twice). No helper takes a WRLD argument.

### Row identity
(table fn-teeth 'K ROW): ROW = (:by defteeth|defkeystone :claim CLAIM :formula FORMULA :subject FN
:hyps (L...) :removals ((L :reachable|:logical) ...) :mutations ((L :conclusion|:hypothesis) ...)
| :not-applicable | :deferred :corrupt (L...) :visits ((L V B :attains|:not-attained :rests-on (A...))
...) :allocation (...)). FORMULA is the translated theorem at declaration, so a later restatement
under the same name is a new obligation (the row no longer matches the world; defteeth-check
refuses). Declared once per name.

### Consumers
1. At expansion: every refusal above, a soft error naming the gap.
2. At certification of a teeth book: `(defteeth-check)` (last form of every book that declares
   teeth for a generator's keystones): every fn-teeth-owed row of the included books has a row whose
   :claim, :subject, every owed bound (V, B, :rests-on) are EQUAL, and whose :formula is still the
   world's theorem.
3. The mandatory late gate (c04 2a/2c/2d), in `make check` through `tools/keystone_emit.py --check`
   (already a failing step): the OBLIGATION MANIFEST planning/teeth-obligations.json, one entry per
   registry event (deduplicated by name) and per owed row the ledger reads from source books:
   {name, class: generated|hand, claim_digest, subject, bounds, owner_book}. The check regenerates
   the manifest from the tree and compares it with the committed one (the protected base =
   origin/dev's copy when reachable, else HEAD's): a name whose base class is `generated` must still
   be generated at the same or a new digest (a downgrade fails); a name absent from the base must be
   generated (new keystones declare their teeth); a `hand` entry may only move to `generated`; an
   owed row with no matching declared row fails; a registry event with neither fails; the counts
   (generated, hand, not-applicable, deferred, bounds without attainment) are printed from the sets.
   `--write` regenerates the manifest under those rules and refuses to launder.

## Astra's view on TEETH CONTRACT v1 (delta consultation c09, gpt-6-astra, read-only at lane head 319c1da87, 234 s)

### Liaison fact-check (codex-liaison-11, 2026-10-03)
- CONFIRMED tools/keystone_emit.py writes the registries when `write` is set BEFORE/regardless of findings (:217-221) and
  returns 0 on findings unless --check (:343): must-fix 8.
- CONFIRMED the contract's protected base is "origin/dev's copy when reachable, else HEAD's" (CONTRACT v1 line ~83): must-fix 7.
- CONFIRMED defkeystone's refusal tests only that :mutations is PRESENT (books/defkeystone.lisp:321), then accepts
  fn-dk-nonep or fn-dk-mutationsp; an empty list passing fn-dk-mutationsp is Astra's reading (not run).
- NOT CHECKED by me: the K:420/439/613-636/668-700 and ledger.py:1518-1523 citations.
Verdict DOES NOT CLOSE: 0 of 7 points closed in code; 1c and 1d OPEN (mutation semantics; V caller-written), the rest
PARTIAL. Nine must-fixes; three items acceptable as counted v1 debt.

### Astra's answer (verbatim)

DOES NOT CLOSE

Read-only review at `319c1da87ce10c6a06487ff00e32f7ac1558181f`, including the specified diff.
`C` below means `build/codex/c09/CONTRACT-v1.md`; `K` means `books/defkeystone.lisp`.
Statuses cover both specification and delivered code. Runtime acceptance/certification: UNVERIFIED; no tests, ACL2 or builds run.

| c04 point | Status | Why |
| --- | --- | --- |
| 1a: witness domain/modes | PARTIAL | C:31–37 distinguishes logical evaluation but supplies neither the lemma substitution nor checked reachability; K:420 still disables guards for every removal. |
| 1b: exemptions/no teeth | PARTIAL | C:43–44 counts exceptions but never forbids new deferred classes or requires classes in owed rows (C:55); K:321–323 accepts `:mutations nil`. |
| 1c: meaningful mutations | OPEN | C:42–43 requires both C and not-C for hypothesis edits; K:439 checks only an arbitrary mutant's negation. |
| 1d: cost/attainment linkage | OPEN | C:49–50 explicitly leaves V caller-written: V=B=0 still proves and attains a bound unrelated to execution. |
| 1e: statement/label binding | PARTIAL | C:21–28 closes the central prose issue; K:613–636 still splits `untranslate`, and K:508–520 stores no formula/claim. |
| 1f: must-fail classification | PARTIAL | C:14–16 correctly makes probes optional; K:425–428,443–446 still emits them unconditionally. |
| 1g: duplicates/orphans | PARTIAL | C:70,81 names uniqueness/owner but supplies no certified-root coverage rule; `tools/keystone_emit.py:231–240` unions names across the tree. |

Must-fix

1. Make witness classification checked, not self-attested. A `:logical` removal is legitimate logical evidence only if it still checks every retained hypothesis, not-Hi and not-C; it must not discharge reachable coverage.
   Check guard-domain status, evaluate pure bindings once, and require a producer/trace for reachability. Define an explicit closed substitution alongside `:witness-lemma`; exact ground conjunction equality proves logical satisfiability, not guards or reachability. Refuse unsupported stobj modes instead of using an unbound live stobj (C:37).

2. Put required tooth classes and exception identities/reasons in source obligations, then compare satisfaction per class. Reject new deferred obligations by default and reject empty mutation lists without an explicit exception.
   Otherwise zero hypotheses plus `:mutations (:deferred "later")` and omitted bounds yields “generated” with no negative tooth (C:5–13,43–44,55–56). Generated declarations and completed obligations need separate counts.

3. Correct hypothesis mutation semantics to `all Hj (j != i) AND H2 AND NOT Hi AND NOT C`; keep the original positive witness separate. Conclusion mutations require all original Hi, C and not-C2.
   Require a named fault intent and a subject-linked edit site/constructor: replacing all C by `(not (equal x x))` evades the literal nil/t ban while testing nothing useful (C:40–43).

4. Require a checked cost-derivation record linking V to the selected subject definition, execution route, metric and dependency digests; derive guards, primitive/callee costs, branches, loops and allocation. Unknown costs refuse qualification.
   Prove naturalness and the bound on that derived counter. Delegation to DEF-ENTRY is fine only with a mandatory checked link; COST-GATE measurements cannot provide it (C:46–50; `c06-ANSWER.md:61–67`).

5. Implement the specified translated-claim binding and staged API before siblings consume it: one validator/emitter, exact formula/subject/bounds matching, versioned rows, duplicate-key/name refusal, and source/world parity fixtures.
   The current `fn-teeth-refusal`/`fn-teeth-events` still take W (K:619,630); `fn-teeth-form` is absent; `defteeth-check` checks only row presence and bounds (K:668–700). These are implementation gaps, not closed contract points.

6. Make the late gate consume digest-bound successful certification records for every expected registry/source obligation, with one canonical owner and a final checker after all included obligations. Reject orphan/duplicate owners and forged bare rows.
   Today even `(table fn-teeth 'K ...)` earns static credit (`tools/ledger.py:1518–1523`), and absent declarations are automatically called hand teeth (`tools/keystone_emit.py:237–240`). A source manifest alone cannot establish executed assertions.

7. Replace HEAD fallback with an externally selected immutable integration-base revision; missing baseline evidence must fail closed. Preserve retired identities and make changed hand-claim digests new obligations unless explicitly migrated.
   C:83 allows committing a downgraded manifest, losing the origin/dev reference, then comparing HEAD against itself. C:85 also permits an old hand name with a changed statement to remain hand; digest storage alone is no ratchet.

8. Give `--write` the same full validation as `--check`, nonzero failure regardless of flags, and no writes until validation succeeds; it must never choose/reseed its own baseline.
   Actual code writes registries before teeth findings (`tools/keystone_emit.py:217–221,329–330`), reads only a working-tree count baseline (:248–260), and returns success on findings without `--check` (:343). C:88 is not implemented.

9. Implement the optional probe switch; record bounded proof-search outcomes separately from ground refutations, with explicit budgets/failure categories. Do not count timeout or hint failure as a tooth (C:14–16; K:425–428).

Acceptable as v1 debt

- Stobj traces and unsupported cost derivations: count unresolved obligations by theorem/class; exclude them from reachable/cost-qualified completion.
- Conservative unattained bounds: count `not-attained` per bound, retaining the proved bound and implementation link; one attainment claims only one example.
- Grandfathered hand teeth and justified mutation inapplicability: count protected identity sets per theorem/class, retaining reasons; no new deferred exemptions disguised as completed teeth.

## CONTINUATION (wind-down 2026-10-03; branch lane/generators-2 at ef9baca4d, pushed, sent to the runner a8c1198f67920c411)

### Jobs left running on hbox (ids; harvest, do not re-run)
- fixture REPL `cvt` (tests/acl2/def-carried-view-tests; after the fresh-determines fix): bbivt3cm0 -- forms 1-55 admitted
  before; the stamped reader keystone (form 56) was the open proof; `proof_repl.py --host hbox status cvt`.
- wix pilot REPL `wix` (books/withdrawal-index-carried; after the :lemmas fix): bndu60b71.
- farm retention + def-keyset-check closure: biro1e0ml (`farm.py status hbox`); farm store-files closure: bu5ojuks6.
- the gate run (`keystone_emit --write-manifest; --check`, log /tank/fn/scratch/generators-2-gate.log): b48v0w73o --
  it ran BEFORE the keying fix 280bcd80d; regenerate the manifest once more after the merge.
- regen (ledger/current-view, `remote_check --regen`, log /tank/fn/scratch/generators-2-regen.log): bu49k925z.
Stop the REPL sessions when harvested (`proof_repl.py --host hbox stop cvt|wix`). Remove /tank/fn/gates/generators-2-repl*
and the lane worktree when the branch lands.

### Teeth generator vs c09's ten must-fixes (code, not prose)
1 :logical removal checks every retained Hj, not-Hi, not-C (fn-dk-removals -> fn-dk-witness-event: same terms, logical
  wrapper only) and the row records :logical; the manifest counts it as debt (complete = no logical removals). DONE.
2 :witness-lemma / :lemma: fn-dt-lemma-problem checks the substitution is closed (every claim variable bound,
  values variable-free, no stobj) and the lemma's formula EQUALs the instantiated claim; row :witness :lemma /
  removal :lemma; counted as debt. DONE.
3 V linked by :derived-by RECORD (a symbol, recorded in the row; the manifest's bound.derived); an underived bound is
  debt (complete requires derived). DEF-ENTRY's def-cost supplies the record; the Lisp does not yet CHECK the record
  exists in the world (fn-dk-bound-entryp accepts any symbol) -- next: refuse a :derived-by that is not a def-cost row.
4 planning/teeth-base.json (revision 4e5a4b8bb; `git show REV:planning/teeth-obligations.json`); missing -> fails closed,
  no HEAD fallback. DONE.
5 keystone_emit: --write (registry) and --write-manifest (gate) validate first and write nothing on their own gate's
  findings; findings exit 1 with or without --check; --bootstrap only when neither base nor manifest exists. DONE.
6 hypothesis mutation asserts other Hj, H2, not-Hi, not-C; conclusion mutation needs :fault "intent"; constants and
  no-op edits refused (:bad-edit). DONE.
7 exemptions (:not-applicable | :deferred "why") recorded and counted; a NEW name with :deferred is rejected by the
  gate; an edits->deferred move is a downgrade finding. DONE (per-obligation "required tooth classes" = the manifest's
  removals/mutations/bounds fields; no separate class list yet).
8 fn-teeth-form / fn-teeth-refusal (world-free) + fn-dt-expand (the one world-binding emitter) exist; defkeystone =
  defthm + (make-event (fn-dt-expand ...)). DONE.
9 the gate reads declared teeth only from defkeystone/defteeth FORMS (a bare (table fn-teeth ..) earns nothing) and
  "certified" from green_check at the book's digest; declared keyed by the RESTATED name (280bcd80d). DONE.
10 probe switch: n/a.
Known: keystone_emit --check exits 1 on the tree's 22 pre-existing registry findings (dev's own tool does too).
Certified: certify-20261002T231403Z-1883604, certify-20261002T232922Z-2220863 (cited).

### Pilots
- nnw (books/newnews-cursor): GREEN (53/53; tests 41/41 with the owed defteeth + defteeth-check); -92 lines.
- wix (books/withdrawal-index-carried): declaration written (184 vs 293; test book has the owed defteeth); the view's
  admission on hbox was the open item (job bndu60b71). If it still refuses: send the view with --full and read the first
  failing generated event; the fixture (cvt, two :set indexes) admits, so the difference is in fn-wix-key/fn-rit-*.
- :stamp (def-entry round two): generator + mirror + fixture written; the stamped VIEW admitted (forms through 55);
  the stamped READER keystone was failing because the fixture relation opened -- fixed by the generated
  NAME-fresh-determines (keeps NAME-fresh closed); job bbivt3cm0 is that retry. The owner-side stamp relation for
  wix is STAGE-5B's ("fn-own-view-version determines fn-own-view-withdrawals within an owner lifetime").

### Keyset
- def-keyset-check + tests green; BOTH hand uses replaced and green with their test books (retention 96/96 + 91/91;
  store-files 194/194 + 109/109). Closures on the farm (biro1e0ml, bu5ojuks6): cite the manifests when they pass;
  store-files is deep (many includers), expect a long run.

### Next steps, in order
1. After the merge: base on origin/dev; `keystone_emit --write-manifest` on hbox, commit the manifest (the base revision
   stays 4e5a4b8bb); harvest the six jobs; cite the farm manifests; fix forward any red.
2. GEN-CARRIED-VIEW: get the wix view and the stamped fixture green (above), certify books/def-carried-view +
   tests + the two pilots' closures (`farm.py submit hbox --affected-by books/def-carried-view.lisp`).
3. :derived-by must name a def-cost row (fix 3's gap) once DEF-ENTRY lands books/def-cost.lisp.
4. GEN-CURSOR (def-cursor: step, run = reference, per-quantum VISIT bound, residual, progress; instances fn-nnw sections
   4-5 and OVER's fn-ovw on lane/served-catalog-live); DEF-COMMAND owns the :quantum column.
5. Consolidation: fn-mpxt (311 definitions in msgid-pages-exec; 29 reachable from other books, 282 internal) -- a cut
   needs the host path through msgid-linear-exec/probe-cursor/tag-exec kept; paged-catalog onto def-representation
   not started; D26 >10 s: planning/proof-cost-baseline.json has no book over 10 s today.
