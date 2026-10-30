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
- Nothing uncommitted.
- Waiting on shas from main:
  - fn2-upload's contract and control, once D4 2/n lands: add the kind to *fn2-q1-kind-contracts*
    (q1.lisp), a row with teeth in tests/q1-contracts.lisp, a mutation site in tests/q1-controls.lsp
    and its CTRL in tests/q1-controls-check.lisp. Then rerun the harness, the judge and the export,
    in that order:
    `tools/acl2 < fn2/tests/q1-controls.lsp`; `forge-certify.sh tests/q1-controls-check.lisp`;
    `certify.sh --export-owed`.
  - fn2-commit's contract and control, after B5.
- WIRE gap reported to D: a closed wire cut before its final reply passes.
- 46 rows left on :assertion in B's and C's open books: proposals sent through main.

## A5r, the native adapter redone (seat: A5r Opus; rewritten whole after every commit)
Design: fn2/docs/a-pool-host-sim.md 4.1 (statement first; Astra's read
build/coordinator/fn2/lanes/a5r-quests/astra-1.md, corrections taken: latch on every cell,
listener offer extended, the cell table per the simulator's normalizer, closed-waiting, EAGAIN
pending, the quiet marker carries the output count, ENVELOPE an execution checker by replay).
Worktree /Users/ember/dev/fn/build/lanes/fn2/a5r (branch fn2/a5r, rebased on dev 57601292a);
forge clone /build/lanes/a5r (helpers in the worktree's build/: forge-run.sh NAME CMD..., which
rsyncs fn2/ and starts CMD detached as a session leader with build/NAME.pid on forge;
forge-wait.sh NAME; accept-combo.sh on forge = the whole-tree gate, results build/acc/NAME/).

| commit | what | state |
|---|---|---|
| aad0c5d2d (1/3) | the peer record: vocab columns + fn2-post-accept-result + harvest latch; fn2-core-observed-peer; listener peer fields; listener offer + fn2-machine-admit +6 args; owed-host.lisp fn2-accept-peer-delivered; tests/host-unit.lisp | on fn2/a5r; whole-tree gate abi1 running on forge |
| 99be12ffb (2/3) | host-boundary.lisp, host/ffi.lisp, host/adapter.lisp, sim/check-envelope.lisp, owed-native.lisp fn2-native-envelope-refines, tests/native-unit.lisp + evidence trace, tests/native-loop.lsp (NATIVE LOOP PASS on forge: 21 clients, ENVELOPE pass, 7 controls) | on fn2/a5r; lands after 1/3 with its own books + export recertified |
| (3/3) | the socket session: tests/native-session.lsp, host/native-session-raw.lisp, tests/surface/fn2_native_session.py (hook FN2_SURFACE_SIM_NNTP=fn2.tests.surface.fn2_native_session:session); then H's nntp S form against it (h8-run.py, H's seat on main's word) | written, untested |

Inner loops: native loop on forge `build/nl.sh` (certify + `tools/acl2 < fn2/tests/native-loop.lsp`,
~3 min), log build/native-loop.log; a REPL-style debug `tools/acl2 < build/dbg.lsp` (end with
(good-bye)). Pitfalls hit: a library book cannot define a function over fn2-core (put it inside
machines-a-access's events macro); put-assoc-equal appends a new key; slots are reused, so map a
post to its op by the latest take of that slot; a defstruct slot named control clobbers a
same-named function; mv-let has no & binder.
Reported/owed to D through main: the conn :copy form for the peer record; the WIRE gap (an
unterminated 511+ octet line answered 501+close is refused as :unasked-reply under small chunks).

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
