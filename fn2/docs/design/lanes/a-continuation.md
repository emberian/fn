# fn2 A+D DSL continuation (layer A's forms and what B, C and D build on; present state, rewritten whole)

Seat: Opus, writing the code itself. Brief: `build/coordinator/briefs/FN2-SEAT-COMMON.md` (dev is the
branch; shared tree /Users/ember/dev/fn on dev; `git commit -F msg -- <paths>`, a new file `git add -- <it>`
first; foundation edits in a worktree; **a foundation commit certifies the whole tree** with the export
green, A's seven drivers rc 0 with the 113 A4 blocks identical, and sim-layer-d-evidence when conn or the
ledger is touched; OWED.md regenerated only in a commit that changes rows; READY per commit). Syntax notes
owned here: `lanes/a-to-d-arm-contracts.md`, `lanes/a-to-bcd-ranges.md` (not yet updated for S1's
listener offer and books-p; add a paragraph under "Admission"; A-S7's :taken when it lands).

## Landed this session (dev and origin/dev)
| sha | what |
|---|---|
| 867e87a23 | the core's wfp closes per child: core.lisp generates FN2-CORE-WFP-OF-UPDATE-X and T-WFP-OF-X per child and disables fn2-core-wfp; the per-field/scalar/partition setters prove through them; machines-a-access's UPDATE-FN2-<K>-TABLE-WFP twins deleted. Forge: assembly-core 51-57 -> 13.5 s, assembly-access 82-99 -> 29 s (replaces the per-kind split main asked for; 21e61b943 superseded, never landed). B's commit.lisp -CHILD-WFP/-UPDATE-WFP are now twins (B's) |
| e3573e0af | defcost :tables (:layers L ...) groups (arms.lisp fn2-cost-tables-p / fn2-cost-tables; a machine table counts as its machine's layer; resolved at the arm :uses check); control in machines-a-unit |
| b58ca579d | Q1 step 3: tests/q1-controls.lsp (four-way harness: baseline, shared, concrete-only, restored; invocation counts) -> tests/evidence/q1-controls.lisp; tests/q1-controls-check.lisp (CTRL-K per kind, judge controls); q1.lisp names :independent CONTRACT-K and :shared-handler-mutation CTRL-K per kind's cases (squares.lisp joins :independent to the correspondence contract) |
| 6bde0055b | MV nesting: fn2-core-init as a chain of groups of <= 16 children (fn2-core-init-chunks, FN2-CORE-INIT-GROUP-k with type facts); fn2-ref-copy-core per-child chain. D4 at 33 children: assembly-init 46.2 s |
| 22034c7c6 | fn2-scribe-reads-back against recover-stub's v1 decoder (runner fn2-scribe-served-cycle on the simulator's device) |
| edacad611 | fn2-listener-admits-within-ledger in tests/q1-contracts.lisp (ledger conserved and within limit at every round; exact at quiescence; at most LIMIT greeted, the rest 400+closed); runner fn2-listener-ledger-run |
| bd945afae | new book fn2/tests/q1-contracts.lisp (in owed-export): fn2-conn-wire-correct (WIRE model oracle over the solo wire), fn2-echo-replies-its-input (runner fn2-echo-solo); teeth asserted. Found: WIRE accepts a closed wire cut before its final 205 (reported to D through main) |
| 96fefad1a | fn2-machine-dec deleted: take-credit with no credit and terminal with nothing pending stop (:machine-write); fn2-machine-dec-control |
| 84e6bb293 | Q1 classification step 1: the 67 case rows `:claim :representation` with per-label `:shared` (registry lookup through :generated; unregistered shared functions as (:function NAME)) and `:shared-provenance` (fn2-q1-shared-functions, q1.lisp); squares.lisp bindings carry :shared/:claim/:shared-provenance/:shared-handler-mutation; `:independent` contract key is a metadata role |
| 9f3f24ab4 | (4b) both reclaims stop on a zero active count before any field changes; fn2-machine-reclaim-control |
| fac32c58b | OWN at the pool's exports (read, write, scan, compare, fold, copy-range, drop-prefix; drop-prefix observed before its move); fn2-own-hook-range-control; D's run checks 186,819 conn bytes; A4 blocks identical |
| b1422d632 | tests/q1-teeth.lisp: per-label positive/negative fixtures for every catalogue case, asserted (12.3 s) |
| 252e859fc | ledger: deflayout ROUNDTRIP/CANONICAL `:g1 :representation :shared ((:layout N))` with sides; folds-served SUMMARY rows `:compiler` shared; rowp refuses a function on both :sides undeclared in :shared (decision-1 rule fires on 150 rows; owed-unit controls); schemas for blake3, crash-model, merkle, format-check, ribbon, q1 partition. :assertion 210 -> 46, :semantic 405 -> 251. Directory scalar/partition setters stop on over-width (control in machines-a-unit) |
| a95b2c88e | DM3 2/n: fn2/tests/sim-layer-d-evidence.lsp runs D's sim-layer-d.lsp unchanged under TRACE per case (persistent reference), the own-read hook and OWN per turn (q1-case-hook.lsp fn2-q1-hook-install-turn); tally fn2/tests/evidence/q1-d-tally.lisp; q1-evidence adds it as a second record. Coverage 53 -> 67; 43 Q1 cases checked incl. conn's 10. D's gate: `SECS=7200 sh fn2/tools/forge-driver.sh sim-layer-d-evidence` (~25 s) |

Earlier this lane: 6c8f3d1a0, 57054a247 (S6), 7fd40d0b7 (S4), 578174649 (C2c words), 91950f63a (S3 weights;
fn2-profile-weights disabled on purpose), 63a7412fe (S2), b31e5d4de (S5), ba644c1de (S1).

Lessons: callback language: no `&` binders (mv-let + declare ignore); an observer branches at the top; read
row fields before rebinding; a guard naming a non-recursive profile helper needs it disabled. Raw-Lisp
hooks: an ACL2 stobj updater result must be let-bound before the next stobj call; `format nil` returns a
base-string that with-standard-io-syntax prints as #A (coerce to `(simple-array character (*))`) and
pretty-prints multi-line (bind *print-pretty* nil). Certify the one touched book alone before a
whole-tree run (`forge-certify.sh sim/check-trace.lisp`, seconds).

## In flight
Landed (READY sent for each): 424f3f9ef (fn2-upload's contract and control), c16d5d862 + bdeea0a6c
(P-DUP-FIELD: all nine upload fixtures claimed), eb905b08d (fn2-recovery-machine's contract
`fn2-recovery-machine-recovers` in tests/q1-contracts-b.lisp and its control), 94486a83f (fn2-sealer's
`fn2-sealer-seals-the-directory` in tests/q1-contracts-c.lisp; mutation: fn2-run-install's entries
one short, with the stepping core found through a wrapper on fn2-sealer-step), 369a6a32c (fn2-txn's
`fn2-txn-answers-by-identity` in tests/q1-contracts-d.lisp; oracles WIRE, H's model over a seeded
store (*fn2-txn-model-cases*), IDENTITY over seeded offers plus the reply's answer as a query;
premise :b-s2-admission-interim in *fn2-q1t-premises*; mutation: fn2-identity-step answers
:conflict as :stored). Parked for B5-4.

What exists now:
- Contracts: q1-contracts.lisp (conn, echo, listener, scribe, upload), q1-contracts-b.lisp (recovery),
  q1-contracts-c.lisp (sealer), q1-contracts-d.lisp (txn). All are in owed-export.lsp and the harness;
  land.sh on forge certifies them.
- Controls: q1-controls.lsp, one run-kind per kind; the judge q1-controls-check.lisp asserts eight
  CTRLs and refuses fn2-commit by name. *fn2-q1-kind-contracts* in books/q1.lisp names
  contract and control per kind. An oracle that signals is recorded :error (the judge refuses it).
- q1-case-hook.lsp re-reads TRACE's reference after host calls outside the arms (the list
  `(fn2-recovery-start fn2-tu-seed-all)` in fn2-q1-hook-install-turn): add any new host-side start there.
- B's runners never call fn2-turn (fn2-b-rec-drive, fn2-b-rounds step fn2-exec-harvest and
  fn2-exec-principal), so TRACE never sees B's kinds. q1-contracts-b's fn2-q1r-case reuses B's workload,
  death, faults, truth and history, runs fn2-init-executor :null on the fresh core, then turns
  (take-prefix, fn2-turn, take-prefix, fn2-sim-advance-with-clients nil nil).

Next, in main's order:
1. Done: fn2-sealer (94486a83f).
2. fn2-commit: PARKED until main sends a sha. Ember ruled the machine form is rewritten before more
   arms are written, so the contract waits for B's port of the twelve commit arms into the NEW form
   (generator G1 on dev at d04660248; placement P1-P4 follow), not the old-form port. B's workloads
   now drive fn2-turn (747afb64c): use that, not a private turn-driven copy. Oracle: B's crash-model
   differential and HISTORY.
3. Done: fn2-txn (369a6a32c). When B-S2 lands: :accept becomes the model's 240 pattern, the served
   answer an :offer with outcome :ok, and the premise comes out of *fn2-q1t-premises*.

Landing procedure that worked (the shared tree is often dirty or moving):
- Develop on forge in /build/lanes/aq1. Whole gate: `build/combo2.sh NAME` (closure, D evidence,
  harness, judge, export, A's seven drivers; build/acc/NAME/result). The first certify fails on
  q1-controls-check whenever a new CTRL is asserted before the harness has written its records; the
  later certify-evidence step makes it green.
- Land from a local worktree off origin/dev (`git worktree add --detach build/lanes/fn2/aq1-land
  origin/dev`; it exists at eb905b08d now), never from the shared tree. On a moved tip: rebase,
  take the tip's OWED.md on conflict, push the commit to forge as refs/heads/aq1-land, `git reset
  --hard FETCH_HEAD` in aq1, then run `sh build/land.sh; sh build/land2.sh` (own books, harness,
  judge, export; then closure and export) and once more `build/land.sh` so the harness runs over the
  recertified closure. Fold the regenerated OWED.md and evidence into the unpushed commit, push.
- Never `git checkout -- .` in aq1 without first copying modified files out (it cost a rerun).
- Never `--amend` in the shared tree (another seat may have committed on top).
- forge resets ssh under many quick connections: wrap each ssh or scp in an until-loop.

## A5r, the native adapter redone, and A's files (seat: A5r Opus; rewritten whole after every commit)
Landed (origin/dev): f6485baea (Accept peer ABI), 03b4a2f41 (native loop + ENVELOPE), 1b0892045
(socket session), 852fd6a02 (darwin record), f794c78f3 (configured listener :listener-port /
:listener-address; tests/native-serve.lsp), f363dd1ae (reference view as a chain of section books:
assembly-reference 75.2 -> 39.1 + 25.6 + 34.2 s).
Ember's ruling (2026-10-31): the machine form is being redesigned; STOP splitting assembly books
by hand. The last split landed: cee416335, the row readers per layer (assembly-rows-a/-b/-c/
-other between assembly-access and callbacks-a): assembly-access 74.0 -> 36.1 s, rows books 17.5,
17.6, 9.7, 28.4 s; whole-tree gate green (113 A4 identical). Measured and NOT landed: moving each
kind's admit/take into its layer's rows book put assembly-rows-other at 67.4 s (D's three kinds'
operations, each proven over the whole core recognizer). Now: stand by for main's statement of the
new machine form, then implement A's side of it.

### The measured anatomy of an assembly book's cost (for the new form's statement)
Instance at dev 369a6a32c: 9 machine kinds (listener echo scribe | commit recovery-machine |
sealer | conn upload txn), 22 defcorechild children plus the core's own (the registry), 252
row-field readers, 399 field-dispatch cases, 158 fn2-core-preserves sites, 95 defmachine-callback
sites. Forge, -j 8, load 4-8 (CPU = wall). What each book pays, by generated family, and why the
cost does not stay with the kind that caused it:

| family (generator) | book | cost | scales with | why it re-proves across kinds |
|---|---|---|---|---|
| per-kind row readers K-ROW-f + -WIDTH (machines.lisp fn2-machine-all-snapshots) | assembly-access (now assembly-rows-*) | 37.4 s for 252 readers | every field of every kind | emitted for all kinds in one book: the book pays for kinds it never uses; each reader's guard opens fn2-core-wfp and the kind's table recognizer |
| cross-kind field dispatchers (fn2-machine-all-field-events, fn2-machine-field-cases) | assembly-access | 14.7 s for 399 cases | fields x kinds | one function per field name with a `case` arm per kind that has it; adding a kind adds an arm to every shared field's dispatcher and re-proves its guard and type facts |
| admit-K / take-K / reclaim-K + -TYPE/-WFP (fn2-machine-admission-kind-events, -taken-kind-events) | assembly-callbacks-a | 41.6 s (take-upload alone 7.2 + 12.5) | admitted/taken kinds x their ranges and copies | all kinds' operations emitted in A's first callback section; each TYPE/WFP proof walks the whole core recognizer (all children), not the touched children |
| fn2-core-preserves NAME -> NAME-PRESERVES-TYPE / -WFP (core.lisp's generated -PRESERVES macro, columns.lisp lines 215-664) | every assembly book (executor: fn2-transition 10.8 + 13.7, fn2-exec-service 9.6 + 9.4; callbacks-d: conn-feed-pool 8.6 + 8.5, conn-run-answer 8.3 + 8.8) | about 1-25 s per site, 158 sites | core children x functions | the type theorem is over fn2-corep, a conjunction over every child; a function that touches 2 children proves frames for all 22+. 867e87a23 closed wfp per child (FN2-CORE-WFP-OF-UPDATE-X), but corep is still whole-core |
| callback guards under fn2-machine-with-work (machines-a-access.lisp 384) | every callback section (callbacks-a/-b/-c/-d/-t) | the bulk of their prove time (callbacks-t: recovery-stop-bounds 53 s; -b 51.7 s) | kinds x callbacks | the charge check reads (fn2-machine-kind id fn2-core) from the directory, so fn2-machine-work-fits-p case-splits over every kind's caps (fn2-machine-charge's `case`); nothing states that an issue keeps the directory, so every post-issue guard re-splits (C's departure 3) |
| the init (fn2-core-init-group-K, core.lisp 557) | assembly-init | group 0: 45.9 s; init-wfp 11.8 s | children | the group guard enables fn2-core-profilep / fn2-machines-profilep / fn2-profilep whole, so each group pays every child's capacity arithmetic; groups of 16 put the heavy children (pool, ops, machine tables) in one guard |
| the reference view (reference-state.lisp) | assembly-reference(-children) | 22.7 s before the split | children x columns | per-child reference stobjs and copy/diff traversals; split into a chain (f363dd1ae) |
| includes | every book | 6-9 s per book | the closure | each section includes the previous one's whole world |

What the generator must emit per kind so that no book pays for a kind it does not name:
1. Per-kind artifacts (row readers, field writers, admit/take/reclaim, arm charge, callbacks, their
   TYPE/WFP facts) in the kind's own section, proven against the kind's own table child and the
   children its declared :tables name, never against fn2-corep whole.
2. Frame theorems per child instead of per core: for every core operation, "children not in its
   :tables are unchanged", stated once per operation over the child accessors (so a callback's
   type/wfp obligation is the union of its operations' declared children).
3. No cross-kind dispatch in a guard: the dispatcher (run, observe, charge, field cases) gets a
   per-kind rewrite "kind = K implies dispatch = K's function" so a K callback's obligation never
   case-splits; the issue operations export "the directory's kind of every id is unchanged"
   (also the ruling owed to C: a kind may then declare descriptor cap 0).
4. The init and its profile facts per child (each child's init guard from the child's own profile
   predicate), so a new child adds one cheap group.

### Generated mv sites a form rewrite would replace
- The arm calling convention: every continuation returns `(mv bytes steps descriptors runnable
  fn2-core)` (machines.lisp fn2-machine-arm-call, 692; machine-dispatch.lisp fn2-machine-run).
- Observers and routers: `(id event outcome reason count aux0 aux1 fn2-core)` in, `(mv wake
  fn2-core)` out (machines.lisp 1000, 1031; executor.lisp fn2-exec-harvest).
- The result cell: fn2-op-cell (vocab.lisp 929) returns 8 values; fn2-harvest-one (core.lisp
  373-416) returns 11; fn2-post-result takes 9 scalars (and fn2-post-accept-result 12).
- The descriptor: fn2-host-action (host-boundary.lisp 49) returns 15 values; fn2-op-range 4,
  fn2-op-capability 2, fn2-op-storage 2, fn2-op-wake 2.
- The admission dispatcher: fn2-machine-admit (target index nonce + 9 offer fields), fn2-machine-
  take-K (waiter + copies).
- Per-field row readers (K-ROW-f, one call per field read: the read set is passed as scalars).
- Pool handles: (slot gen off len) quadruples and (okind oslot ogen) owner triples on every pool
  export (fn2-pool-read/-write/-scan/-compare/-copy-range, fn2-core-read/-write).

### Per-octet export sites (one checked export call per byte) a form rewrite would replace
- fn2-core-write / fn2-core-read loops: commit.lisp 360, 368-370 (B's batch copy), machines-a-
  scribe.lisp 47, 58, 163 (the scribe's sector fill and checksum), owed-cursor.lisp 37.
- fn2-pool-write / fn2-pool-read loops: layout.lisp 122-124 (the generated codec's field copy),
  machines-c-bind.lisp 24-32 (identity bind copy, A-S8 pending), machines-c-groups.lisp 235,
  ribbon.lisp 108, 232, 526, runs-page.lisp 61, 592, 620, recovery.lisp 76, 83, blake3.lisp 182,
  490, grammar.lisp 41, 405, format-check.lisp 115, 265.
- fn2-pool-adapter-write (pool.lisp 245): the simulator (sim-transfer.lisp), the cw view
  (owed-conn.lisp) and ENVELOPE's replay (check-envelope.lisp) write a receive's octets one call
  each; the native adapter writes the loan's span physically and posts once.
The pool already has range exports (fn2-pool-scan, -compare, -copy-range, -drop-prefix, -fold);
every site above is a copy or fill that a range-copy/range-fill export (or the deflayout codec
compiled to one) replaces.

Orphans reported to main for ember's kill word, untouched: laptop SBCL 79307 (group 79303, port
56981) and 87696 (group 87695, port 60811); forge session 2830337 (SBCL 2830338).
Worktree /Users/ember/dev/fn/build/lanes/fn2/a5r: branch fn2/a5r-rows at cee416335, clean. Pitfalls: ACL2 defun has no &optional; the raw REPL prints `* ` before output
(print ready lines after a newline); tools/acl2 is a wrapper (signal the group); timeout's SIGTERM
skips Python's finally unless trapped; the shared tree's dev can lag origin (push from the
worktree).

## Queue (main's order)
(3), (4), (5) done; teeth landed; OWN range hooks landed; Q1 classification step 1 landed. Waiting until a POST is durable: A-S8, the R6a1
rest (build/lanes/fn2/a-r6a1 PARKED), R6a2, R6b, A6. A5r has its own seat.

## Forge
- /build/lanes/a3b: my acceptance clone. `build/forge-accept.sh SHA[:certify]` (checks out SHA) or
  `build/accept-combo.sh NAME` (the tree as checked out plus overlays: certify, sim-layer-d-evidence,
  q1-evidence, export, A's seven drivers) or `build/d-evidence.sh NAME` (D evidence + export only); results
  build/acc/NAME/. Detached: `setsid sh -c "echo \$\$ > build/accept.pid; exec sh build/accept-combo.sh N"`;
  stop with `kill -- -$(cat build/accept.pid)`. The A4 driver rewrites fn2/tests/evidence/q1-a4-tally.lisp:
  `git checkout -- fn2/tests/evidence fn2/docs/OWED.md` before the next run.
- Compare: `python3 build/seat-ad/compare.py <dir with sim-layer-a-a4-driver.log> build/seat-ad/baseline-r5e2-a4.log`.
- /build/lanes/a3: older clone at b25c1ea51, free.
- Slowest books after 867e87a23 (forge, load 6-8): assembly-callbacks-d 53.0, assembly-reference 45.2,
  executor 42.7, assembly-init 41.5, sim-adapter-base 40.1, assembly-access 29.0, assembly-core 13.5.

## Rules
PID files only (group leader); never stash / add -A; named paths; secrets check before push; one certify
at a time; a book over 60 s blocks the commit; disk < 60 GiB: stop.
