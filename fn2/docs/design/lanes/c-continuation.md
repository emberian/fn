# fn2 layer C continuation (present state, rewritten whole after every commit)

Seat: Opus, layer C (the ordered-run metadata engine). Ninth seat, distilled twice (2026-10-31);
the next continuation is a fresh seat started from this file. I own C and decide inside it; main carries
cross-layer seams. Order: `build/coordinator/fn2/BRICKS-20261031.md` §5. Layer doc on dev:
`fn2/docs/c-ordered-runs.md`. Lane worktree: `/Users/ember/dev/fn/build/lanes/fn2/c-wake` (branch
fn2/c-wake, rebased onto origin/dev before each landing, pushed as HEAD:dev). Forge tree:
`/build/lanes/c` (rsync fn2/ minus certs; certify with `build/cN.sh` under setsid,
PID file `build/cN.pid`; forge only while hbox is down).

## Landed (READY sent for each)
- Earlier: C1a .. C-S3 c82104671, D5's seams 294055805, :sealable source 83ced3bf9, C1c engine half
  30ead9b23, sealer machine 429702ef1, C-S3a ebcc65eea, sealer named stops e2448ef3b, §4a statement
  219184b5d and refinement b0fbb77e9, octet fold keys and the :published frontier 93ede3b02,
  :answers and :child 381507ecd, S-ARTICLE-LOCATION doc 186a84b7d, C-FOLD-UNCHANGED 523f747c6,
  C-UNION-STAGE and (:new K) 80bd41b85, exact :answers on P4 89f965079.
- §4a's one landing (sha in the READY; see "In flight" if not yet pushed): the identity records,
  the decision, the txn switch, and the deletion of the old record. As built, with four departures,
  in the layer doc's §4a "As built". In short:
  - The records (identity.lisp): evidence 1, history 11, candidates 12, summary 13, article index 14.
  - The decision (machines-c-groups.lisp): `fn2-identity-decide-start` / `-decide` / `-facts`, two
    `fn2-xl-step` lookups. D's `fn2-read-identity` is the article index, then the summary.
  - The admission: `fn2-txn-put-identity tx mslot mgen moff mlen dslot dgen doff okind oslot ogen h
    principal local` (txn.lisp; slots 0-4).
  - The engine: 24 slots, a 2048-row stripe (B's `*fn2-b-txn-field-rows*`), and the sealer's
    filter on summary runs.
  - The schema compare is now generated as a chain of one function per key field: a nine-field key
    took minutes nested, and the certify stalled four hours.
  - Deleted: identity-unit, sim-layer-c (M3) and its sweep, the conflict bound, and the upload word
    :identity-conflict-bound.

## Method (WORKFLOW-20261031, binding)
No whole-tree gate, no OWED regeneration, no export per commit. Land on: my changed books certify,
my units pass, my own reading of the diff; rebase on dev; secrets check (`python3
tools/secrets_check.py`, NOT a .sh); push; one-line READY. Fix forward. At ~400K ask main for the
distill.

## Rulings in force (main, 10-31)
- Ember: spine only until D's cursor and B's member land. §4a's single landing IS the spine (D's
  txn port is written against fn2-identity-decide and the four slots), so it goes on. Paused: E's
  peering seams, coverage gaps, funded admission, any breadth. The location field's bind comes
  with D's txn port when D asks.
- A kind lands with its producer (D46). E's five peering schemas stay design (e-surface.md §13).
  fn2-withdrawals waits for the cancel verb (D5 3/n). The fn2-outcome widening stays in my order
  (the txn writes it today).
- fn2-outcome's principal key: D7's (b). (:id principal) keys on fn2-account-principal-id =
  slot*2^32 + incarnation (u60). The outcome keystone takes D's fn2-account-principal-id-unique as
  its premise. D7 4/n-a 00c493d32 PROVED fn2-account-principal-id-unique and -rebind-fresh, so the
  premise is a theorem; key on it when the widening lands with E's op id. D's fn2-read-frontier
  (c7972899d) reads my published column.
- Wire words: record kinds are named by the protocol verb that writes and reads them.
- G2 (7a0edee7a): :sealable is a defwait in my sealer kind book. Kind :stops exist, so the sealer's
  :sealer-full / :sealer-cache and inner-phase stops leave exec-state's enum at the sealer's port,
  which waits for G3's :sub and :genesis.

## In flight
If the §4a landing is not on dev: lane fn2/c-wake holds commit "WIP §4a landing" plus the edits
after it (runs-schema's compare chain, the layer doc's §4a "As built" and §1 rows). Certify on
forge: `build/c7.sh` (setsid; PID `build/c7.pid`; out `build/c7.out`). Its targets are
sim/check-identity and the units identity-core, txn, groups, runs, range, sealer, sealer-machine,
read, cursor, conn-answer and q1-contracts-d. Expected values I could not run yet:
- identity-core-unit's decision `:steps 4`;
- check-identity's good-trace facts order;
- runs-unit's page expectations (the entry is larger now);
- sealer-unit's summary image.
Fix each from the REPL (build/iddrun.sh is the REPL pattern: a driver .lsp, `--timeout`, a PID
file). Then squash into one commit by path. The message names other owners' files: D's txn,
owed-cursor, upload, conn-answer, read and txn units, machines-c-read; B's machines-b; Q1's
q1-contracts-d and q1-controls; A's owed-export. Rebase, run the secrets check, push, and send
READY. The READY names `*fn2-b-txn-field-rows*` for B, and the API for D's port.

## Next (in order; main 10-31: spine seams only, nothing beyond these)
1. Narrow the read ops' :child returns (ember's certify-time push). Each fn2-read-X-children
   returns only the children it changes; a lookup changes fn2-reads and fn2-fields, not the run
   tables. The cursor's seek arm pays one shape-lemma pair (~11 s) per returned child; the arms
   narrow by construction under the per-arm tuples (24fce1ecd). Measured by the cursor's time.
2. E's consumer machine seams (exact forms in lanes/e-continuation.md, its blockers):
   (a) the fold `fn2-consumer-names`: key ((principal (:id principal)) (name (:octets 64))),
       value ((consumer (:id consumer))), :unique, written by register's transaction (D's txn
       port's :consumer mode), so a wire name maps to the cursor fold's consumer id;
   (b) `(defcost fn2-successor-stream-member :child ... :answers (:ok :done :state))` -> (mv code
       stream position next), listing a published batch's fn2-addr writes, for E's attachment of
       fn2-commit-stream-wake.
3. §4a steps 3-4 (layer doc): the three reads at a named view; the checker's rewrite, M3 over
   the new decision, and the keystones as defthm-owed rows.
4. C-SEAL-NO-ROW is dead since B5-4a: delete the :no-row branch and the doc's interim entry.
5. The device half when B5-4's :run-replacement is usable; then C5.
6. Owed: the machines-c-stage shave; the sealer's descriptor cap 4 -> 0 after A's frame lemmas;
   fn2-xl-step skipping a run on the summary filter.

## The fn2-sealer arm table (as built at 429702ef1; input to the new form)
The machine has one row (capacity 1, gen 1, local slot 0). Its fields are `stopped :bool` plus the
row control fields (phase, wait-reason, ready links). Budget is 4096 bytes / 32 steps / 4
descriptors (the cap is unused; departure 3). Its engine state lives in its own table
`fn2-core-seals` (one row: phase idle/build/filter/install/failed, sub
open/clear/add/drive/finish/solve, the overlay O and position POS, run and unit counters, writer
and field bases, checker row, owner triple). So the machine has two arms, but the real state
machine is the seal row's, below the machine's contract.

| arm (machine phase) | reads | writes | effects | cost | next | refusals |
|---|---|---|---|---|---|---|
| `fn2-sealer-seal` (:sealing) | the row's id; through fn2-sealer-step, the seal row and 16 core children (seals, overlays, overlay-index, run-installed, run-builds, run-writers, run-restarts, run-cache, ribbon-builds, ribbon-band, fields, pool, fc, fc-context, b3, digests) | row: wait-reason (park on :sealable), phase (-> :stopped), stopped; the 16 children through the step | one seal step; pool reserve/release (64 KiB page workspaces, the hash workspace, the overlay arena on retire), page writes and seals, cache installs, the run install and the overlay retire; on refusal `fn2-core-stop :sealer` | fn2-sealer-step 4096 bytes + transition steps; 0 descriptors | :sealing (runnable on :more/:retired/:done; parked on :sealable on :idle), :stopped on any other code (:full stops :sealer-full, :cache :sealer-cache, since e2448ef3b) | every non-listed code (:bounds, :state, :capacity, and callee codes) stops the core (:sealer) and moves the row to :stopped |
| `fn2-sealer-idle` (:stopped) | the row | nothing | fn2-machine-idle | fn2-machine-idle's steps | :stopped | none |

The seal row's phases are what one `fn2-seal-step` does, by phase. These are the candidate arms
of a form that can name them:

| seal phase | does | answers | next seal phase |
|---|---|---|---|
| idle (`fn2-seal-start`) | pick the sealable overlay (least SEQ of its schema among frozen/private/active, and itself frozen); empty: retire it; else hand out a run id, reserve the hash workspace, start the build | :idle (none), :retired, :more, :full (pool exhausted), :capacity (no class), :bounds | build |
| build (`fn2-seal-build` -> root / next / cache / page) | drive `fn2-run-build-work` and act: a sealed page -> cache it (`fn2-seal-unit`: :cache if its direct-mapped row holds another page); promote; :need-page -> unit + 64 KiB workspace (:full); idle -> add the overlay's next entry or finish; the root sealed -> name it | :more, :cache, :full, :bounds, callee codes | filter (identity) or install |
| filter (`-filter-open`, `fn2-seal-filter`) | open the filter page on writer WBASE+6, clear the band, add each entry's Message-ID hash, finish, solve, seal | :more, :bounds, callee codes | install |
| install (`fn2-seal-install-run`, `fn2-seal-install`) | take a free installed-run row (the run version moves), name the filter, retire the overlay (frozen -> free, arena released), release the hash workspace | :done, :full (no free run row), :bounds | idle |

## What the sealer's arm bodies do that the restricted arm language cannot say
1. **Dispatch on an operation's answer code.** The arm cases on fn2-sealer-step's code into three
   outcomes: stay runnable, park, or stop. The checked language moves phase and writes own fields;
   the code-to-outcome map is hand-written in the callback.
2. **Park on a wait kind.** It writes the row control field wait-reason := :sealable, which is not
   an own field. The waker is outside the form: a `defattach` of the grant service's :sealable
   pair (fn2-sealer-ready / -grant), whose readiness reads another table (seals + overlays).
3. **Stop the core.** `fn2-sealer-refuse` = `fn2-core-stop :sealer` inside an arm, and the stop
   reason has to be appended to A's exec-state enum by hand.
4. **An internal state machine under one defcost.** The seal row's phase x sub (above) is invisible
   to the machine contract: totality, bound and frame rows cover :sealing/:stopped only. The cost
   is one 4096-byte defcost over 16 tables, whatever the phase does.
5. **Genesis outside any arm.** `fn2-sealer-start-row` (from fn2-engine-genesis in the executor's
   fn2-init-engine) writes the row's phase/wait-reason/stopped: park, or stop for C-SEAL-NO-ROW.
6. **The owner triple before the index.** The engine's pool owner is (kind position, 0, 1), made by
   make-event in machines-c-successor, because the owner is used before the machine index exists.
   It is checked against *fn2-sealer-kind* only after the index.
7. **The descriptor cap** is 4 although the kind issues nothing (departure 3).

**Defect found while tabulating (fix it in the new form; no old-form arm work):** the
backpressure codes park the row, but the wake predicate `fn2-seal-pending-p` needs the seal row
in phase idle and an overlay sealable.
- `:cache` and `:full` from the build (seal phase build) and `:full` from install (seal phase
  install) park the row with pending-p false. Nothing wakes it: the sealer stalls silently until
  something else runs it.
- `:full` at start (seal phase idle, an overlay sealable) makes pending-p true at once, so the row
  is granted every turn: a bounded spin.

The new form's wake for the sealer must be "work pending in the seal row" (phase not idle, or idle
and sealable) plus a resource wake for backpressure: a cache row or an installed-run row freed
(M2's eviction), or pool capacity. Until eviction exists, :cache is permanent, so it should stop
loudly instead of parking. Reported to main.

## Landing mechanics learned this seat
- The shared tree /Users/ember/dev/fn has a local dev that can diverge from origin/dev (10-31
  00:00: a local D6 5b65f7154 vs the pushed c01f87b6a), plus other seats' uncommitted Q1 edits. Do
  NOT ff-merge there. Land from the lane worktree: rebase onto origin/dev, then `git push origin
  fn2/<lane>:dev`.
- A rebase onto a moved tip whose only overlap is OWED.md: take origin's OWED.md, rerun the export
  alone (build/ex.sh, ex.pid), copy forge's fn2/docs/OWED.md in, amend the lane commit (never in
  the shared tree), push.
- `git rebase` of a stacked lane branch after its base was rebased re-applies the old base commit:
  use `git rebase --onto <new base> HEAD~1`.
- Use the session scratchpad for temp files, never /tmp.

## C1c design (settled; the engine half above implements its first part)
Facts learned that fix the design:
- **Owner.** Pool owners are opaque triples `(fn2-pool-mrefp kind slot gen)`; nothing checks them
  against machine rows. Machine kind numbers are the position in `(fn2-machine-names world)`
  (registration order: A's kinds, fn2-commit, then C's, then fn2-conn), constants `*K-KIND*` made
  only at `fn2-machine-index-events` (assembly-index). Plan: declare `(defmachine fn2-sealer ...)` in
  a new book `machines-c-sealer-kind.lisp` included at the top of machines-c-successor (after
  machines-c, so after fn2-commit), then `(make-event ... (defconst *fn2-idc-owner-kind* <position
  of fn2-sealer in fn2-machine-names>))` replacing 254; slot 0 (capacity 1, local slot), gen 1 (the
  row is never retired); after the index, `(assert-event (equal *fn2-sealer-kind*
  *fn2-idc-owner-kind*))` in assembly-callbacks-c. Record as C-ENGINE-OWNER (as built): local slot,
  not the global id, because the owner constants are used before the index exists.
- **Resources the sealer needs** (all C's own children, sized by C profile keys, so nothing goes
  into B's stripes): `fn2-run-builds` (1), `fn2-run-writers` (levels + 1 for the filter writer),
  `fn2-run-restarts` ((levels+1) x capacity), `fn2-ribbon-builds` (1), `fn2-ribbon-band`
  (`fn2-ribbon-slots` of the overlay entry capacity). Field rows: the build's writers need
  6 x writer-fields + entry rows (> 1000, more than a 1024 transaction stripe): give the sealer its
  own `fn2-fields` child. ACL2 accepts two children of one stobj type (tested 2026-10-30: `(defstobj
  top (a :type sub) (b :type sub))`, each bound by its accessor in stobj-let). Format row: B's map
  says the sealer's checker row is `3 + :large-upload-windows`, read through `fn2-fc-rows`; digest rows
  in that row's stripe (`fn2-digest-slot row r`, regions 129-134 for the six levels' parent hashes,
  135 the filter hash; 0-128 the hasher and previous seal).
- **Pages in the engine half** stay resident: physical identity from an engine counter (unit,
  counter), each sealed page installed in `fn2-run-cache`; the cache is direct mapped by unit, so
  the sealer refuses (`:cache`, backpressure) to install over a ready row of another page: no
  eviction until M2's cold leg can reload. Served capacity is then cache rows of pages.
- **Order.** The sealable overlay: a `:frozen` overlay of schema S whose SEQ is least among S's
  overlays in `:frozen`, `:private` or `:active` (a newer frozen one sealed before an older private
  one would put newer rows in a run that the older overlay outranks). Install and retire in one
  step (the run version moves; readers refuse `:stale` or restart).
- **Arms** (defmachine with full contracts; arms call C ops through defcosts, as D's do):
  `:idle` (pick; none: park), `:build` (drive `fn2-run-build-work` and act: `:sealed` record and
  cache, `:promote`, `:need-page` reserve a 64 KiB workspace under the owner, `:idle` add the next
  overlay entry via `fn2-ov-entry` then `fn2-run-build-add`, or finish), `:filter` (identity only:
  ribbon start/add/finish/work as `fn2-ida-filter` does), `:install` (fn2-run-install +
  install-filter, manifest descriptor, retire the overlay: frozen -> free, arena released),
  `:stopped`. Wake: publish (fn2-succ-publish) wakes the sealer row (or the sealer polls on its
  own wake; decide when writing the arms: a cross-kind wake from B's publish path needs a defcost
  with the machines table).
- **Manifest schema** `runs-manifest.lisp`: `(defrunschema fn2-manifest :id 10 :key ((schema (:id
  schema)) (run (:id run))) :value (height pages entries ROOT- ref FILTER- ref) :merge :latest
  :page-kind :manifest)`; the per-schema MIN-/MAX- fences are not in the manifest value (they differ
  per schema; recoverable from the root page): record as a decision.
- **Keystones** (defthm-owed into fn2-squares, statements before code): `fn2-sealer-run-equals-overlay`
  (the run built by the real sealer arms from frozen overlays in SEQ order answers every lookup and
  scan as the overlays did; teeth: a sealer that skips the last overlay; one that keeps an older
  :latest row) and `fn2-manifest-replacement-atomic` (engine half over the list model now; tiny
  exhaustive death cuts with B5's recovery and GC2 later).
- Also owed: the lookup's run leg and resolve's run leg tested on real runs once the sealer
  installs them; machines-c-stage shave (52.2 s on forge today).

## Seam state
- D: D5 2/n codes against C-S3 plus the seams above.
- B: calls `fn2-successor-publish` / `-drop` (to become hooks with C's attachments, B5-4);
  asked earlier (a) admit-txn returns the commit position, (b) drops in batch order, (c) uncertain
  batches stay in the tip.
- A: A-S8 `fn2-pool-copy-across` replaces `fn2-idc-copy`.

## Pitfalls (this seat and earlier)
- A shape lemma's callee hyps must all be discharged: `(< b (X-rows ...))` needs an explicit
  run-time `(< 0 (X-rows ...))` check (fn2-run-buildp is disabled, so its row fact is invisible)
  and the X-rows functions disabled in the guard hints, else they open to `(nth *X-ROWS* ...)` and
  the callee's rows rewrite never fires. `(natp budget)` is not a stobj hyp of the generated shape:
  check it at run time in any function whose callees' shapes need it.
- A reads list naming a macro (fn2-ribbon-row-ok) breaks the theory expression; reads lists are
  macro arguments, never evaluated (no `,@*const*` inside them).
- The Ribbon phase helpers had no shape lemmas: each now has one in sealer.lisp.
- A dispatcher with many answer branches and twelve stobjs makes a slow shape (17 s): put each
  branch's work in a helper with its own shape (fn2-seal-root, fn2-seal-next): 10 s.
- Unbalanced parens swallow the rest of the file into one form: the REPL ends with "end of file";
  check balance before a run.
- In a test's b*, a macro in binder position is not expanded: fn2-su-defun rewrites
  `(fn2-su-bind vars call)` into `((mv vars... stobjs...) call)` (fn2-su-expand).
- Rsync every edited file before a gate (owed-export.lsp edited after the sync left the export
  without the unit once; rerun the export alone, `build/ex.sh`).
- Earlier: recursive multi-stobj functions blow up their op-shape (split step and loop);
  re-check row counts after a helper returning a stobj; wrap new steps in existing guard hints in
  their own disabled function; digest field value 1; explicit run-time index checks; fold reads
  (C-SHAPE-READS); never `(mv :ok (setter ...))`; no formal named `state`; time lemmas in a
  certified world.

## Commands that work
- Sync to forge: `rsync -a --exclude '*.cert*' --exclude '*.fasl' --exclude '*.port' --exclude
  '*.time' --exclude '*.out' fn2/ forge:/build/lanes/c/fn2/` from the c-found worktree (now at
  30ead9b23 = dev).
- Forge REPL of a book: `build/sedrv.lsp` + `build/serun.sh` (PID build/se.pid; edit the include
  and the ld'd file); a unit: `build/sudrv.lsp` + `build/surun.sh` (su.pid); values:
  `build/vudrv.lsp` + `build/vurun.sh` (vu.pid). Start: `ssh forge 'cd /build/lanes/c && (setsid sh
  -c "echo \$\$ > build/X.pid; exec sh build/Xrun.sh" < /dev/null > /dev/null 2>&1 &)'`; wait:
  `until ! ssh forge 'kill -0 $(cat /build/lanes/c/build/X.pid) 2>/dev/null'; do sleep 15; done`;
  stop: `kill -- -$(cat build/X.pid)`. Errors: grep "ACL2 Error"; per event: awk over "Form:"/"Time:".
- Cert chain: `swarm-build sh fn2/tools/forge-certify.sh BOOKS` detached (cc.pid). Gate:
  `build/c1.sh` detached (c1.pid): closure then export; export alone `build/ex.sh` (ex.pid).
  Times: `python3 fn2/tools/certify-times.py . build/certify-closure.log`.
- Landing: commit in build/lanes/fn2/c-found (`git commit --no-gpg-sign -F msg -- paths`; new files
  `git add -N` first); in /Users/ember/dev/fn `git merge --ff-only fn2/c-found`, `python3
  tools/secrets_check.py`, `git push origin dev`.

## Certify times (forge, 10-31 01:40, load 3-5, closure at 429702ef1 + C-S3a)
| book | s |
|---|---|
| sealer-machine-unit / sealer-unit / identity-core-unit | 17.3 / 6.2 / 15.8 |
| machines-c-successor / -stage / -bind / -groups / -sealer / -sealer-events | 27.1 / 55.4 / 20.1 / 24.2 / 5.3 / 5.3 |
| assembly-callbacks-c-prepare / -c-commit / -c | 33.5 / 28.2 / 25.9 |
| assembly-reference (A's split, f363dd1ae) children / children-b / reference | 38.3 / 25.7 / 33.9 |
