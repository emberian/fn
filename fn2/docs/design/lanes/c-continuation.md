# fn2 layer C continuation (present state, rewritten whole after every commit)

Seat: Opus, layer C (the ordered-run metadata engine). The next seat starts from this file (and
`cv show` of the last seat's transcript for detail). Order: `build/coordinator/fn2/BRICKS-20261031.md`
§5. Layer doc on dev: `fn2/docs/c-ordered-runs.md`. Worktrees on the Mac:
`/Users/ember/dev/fn/build/lanes/fn2/c-wake` (branch fn2/c-wake) and `.../c-next` (branch
fn2/c-next); both are at dev as of c65141708. Rebase onto origin/dev before a landing, push as
`git push origin <branch>:dev`. **CONVERGE (ember, 11-01): the fleet stopped so Gemini can take a turn.
Do nothing until main wakes the seat.**

## Method (WORKFLOW-20261031, binding)
No whole-tree gate, no OWED regeneration, no export per commit. Land when: the books you changed
certify, your units pass, and you have read your diff. Then rebase, run `python3 tools/secrets_check.py`,
push, send a one-line READY. Fix forward. Near 400K context, ask main for a distill.

## Landed (READY sent for each)
- Earlier: C1a .. C-S3 c82104671, D5's seams 294055805, :sealable 83ced3bf9, C1c engine half
  30ead9b23, sealer machine 429702ef1, C-S3a ebcc65eea, sealer stops e2448ef3b, §4a statement
  219184b5d / refinement b0fbb77e9, 93ede3b02, 381507ecd, 186a84b7d, 523f747c6, 80bd41b85, 89f965079.
- **§4a, 0022ac2f8:** the identity records (evidence 1, history 11, candidates 12, summary 13,
  article index 14). fn2-identity-decide-start/-decide/-facts. fn2-txn-put-identity, whose helpers run
  in this order: put-local (history), -evidence, -summary, -candidate, -index (last, because the
  index's ordinal is the summary's :out). fn2-txn-put-post (identity and article, the one call
  declare-1 makes). Stage of a fold whose key sits in an overlay re-copies the key fields from the
  args. Test profiles resized. B's txn stripe is *fn2-b-txn-field-rows* = 2048.
- **c65141708:** *fn2-idc-overlays-default* = 48; fn2-succ-unstage (a bind or a drop returns every
  other :staged txn to :open, the tip scan's invariant enforced, §8 item 15); fn2-consumer-names (id
  15, §8 item 16); fn2-successor-stream-member (§8 item 17); fn2-icu-tips unit; doc §5 capacity and
  minimal C5, §4a claim stability restated, §8 item 18 (one encoding, proposed). The targets
  certified green on hbox at the c-next tree: check-identity and the identity-core, txn, groups, runs,
  range, sealer, sealer-machine, read, cursor, conn-answer and q1-contracts-d units.
- :child narrowing of the read ops: nothing to change (main agreed; the per-child PRESERVED facts go
  to the form seat).

## Next, exact (when main wakes the seat)
1. **fn2-successor-emit (D's txn port waits on it; main's exact form):**
   `(fn2-successor-emit tx wslot wgen woff wmax okind oslot ogen fn2-core) -> (mv code len fn2-core)`,
   :answers (:ok :room :state :bounds). Callable after an :ok stage, and :state unless the txn is
   staged and unbound. It writes one record per non-empty staged slot, in slot order, into
   [woff, woff+wmax) of wslot/wgen: B's fn2-format-txn-record frame (kind, length) and then the body.
   It answers :room when wmax is short and returns the octets written. Fill-octets (Xref) runs before
   it. Write it as a defcost with :bytes per slot x 24 and a :child over the children it reads
   (succ-txns, succ-slots, id-decides, fields, fc, pool). Body: the schema's entry codec,
   `fn2-run-layout-encode sid 0 entry slot gen off okind oslot ogen fn2-fields fn2-pool`, the same
   encoding the overlay arena holds (see fn2-ov-write in runs-assemble.lisp). A fold slot carries its
   post-image. Replay: C attaches fn2-member-replay, which decodes each record by its kind, fills the
   :event fields from the header's event, and inserts through fn2-succ-bind-slot.
   **Record kinds for B** (one per schema a transaction stages; main relays this list to B, who
   extends *fn2-commit-txn-record-kinds* and its admission decoder):
   `:article-acceptance` (B's existing record; stays), `:article` (sid 2), `:overview` (3),
   `:addr` (4), `:group-accept` / `:group-withdraw` (5, the counts fold's events), `:cursor-ack` /
   `:cursor-rebase` (6), `:charge` / `:refund` (7), `:outcome` (9), `:identity-evidence` (1),
   `:identity-history` (11), `:identity-candidate` (12, :admit), `:identity-summary` (13, :admit),
   `:identity-article` (14), `:consumer-name` (15). Each body is that schema's layout codec. The
   "membership" D named is the overview row plus the group accept; there is no separate kind.
   The design alternative in doc §8 item 18 is one :staged-write kind tagged by schema. D asked for
   one kind per schema; take D's form.
2. :child bodies for fn2-successor-put, -arg, -arg-octets, -arg-octets-late, -resolve, -stage,
   -fill-octets, -out, -bind, -release, fn2-identity-decide-start, -decide and fn2-group-lookup. Each
   :child is the stobj-let body over its children; the idc-stripe wrappers are the real work. Land
   them as one commit after the emit, so D's txn flips to :children.
3. Concrete profile: tell the profile's owner (through main) that C needs its own pool class. That is
   48 x 64 KiB for the overlay arenas (or :identity-arena-bytes 4096 plus 48 x 4 KiB slots), plus
   64 KiB slots for resident run pages. Also set :identity-runs 512 before helm's concrete run.
4. Minimal C5 (doc §5): a sealer merge phase over at most eight live runs of one schema, size-tiered.
5. §4a steps 3-4 (the reads at a named view; the checker, M3, the keystones as defthm-owed rows).
   C-SEAL-NO-ROW's dead :no-row branch. Owed: the machines-c-stage shave, the descriptor cap
   4 -> 0, and fn2-xl-step skipping runs on the summary filter.

## Capacity numbers (doc §5)
- Installed runs: 64 rows, one table shared by every schema (:identity-runs). Each frozen overlay
  seals into its own run. A POST writes 8 schemas (10 with overview and addr), so 64 rows last 6 to 8
  POSTs. Then the install answers :full and the core stops :sealer-full. Nothing reclaims a row
  before C5.
- Pages: each run's pages stay resident, one 64 KiB slot each, so the 64 KiB class bounds the runs
  first.
- Overlays: one per (batch, schema). The default is now 48 (16 schemas x 3 batches). The old default
  of 8 never staged a 10-schema POST.
- Resolve and lookup walk every live run of a schema: one step per run. Each lookup grows with
  the run count until C5 merges.

## Boxes
- hbox is the certify box. Tree ~/fn2-c/tree, synced with `rsync -ac --exclude '*.cert*' --exclude
  '*.fasl' --exclude '*.port' --exclude '*.out' --exclude '*.time' fn2/ hbox-saas:fn2-c/tree/fn2/`
  (-c keeps unchanged files' mtimes, so certs stay warm). Certify: `(setsid nohup sh cert.sh BOOKS >
  /dev/null 2>&1 & echo $! > cert.pid)` in ~/fn2-c. Stop: `kill -- -$(cat cert.pid)`. The assembly
  chain takes about 1 h at hbox's load.
- REPL loop (minutes): ~/fn2-c/vu.sh runs vu.lsp from tree/fn2/tests (vu.pid, vu.out). It includes
  the certified assembly and sets `(set-ld-redefinition-action '(:doit . :overwrite) state)`. Then
  `(ld "../books/X-new.lisp" :ld-error-action :continue)` loads each edited book. For txn.lisp,
  follow it with `(fn2-txn-op-events) (fn2-txn-events)`; its core functions live in those macros.
  A redefined owed-* book needs its include-book first. Then ld the units and grep "Assertion
  failed". A defun that fails inside a macro's progn leaves the old definitions in force, so grep
  for Errors first. A new schema cannot be tried this way.
- forge /build/lanes/c is stale; do not use it.

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
- A long `fn2-txn-chain` (about 30 calls) with `if`s inside stalls its guard proof for hours. Split it
  into small functions, each with its own `fn2-core-preserves` and disabled before use. The chain
  macro binds `c`: never name a local `c` inside it.
- Generated code nested once per key field (the schema compare) took about 290 s per nine-field
  schema to define. Generate a chain of shallow functions instead (runs-schema does now).
- A certify with no new .cert for ten minutes is a stalled proof: read the newest .cert.out's tail,
  stop the run by its PID file, split the proof.
- rd-shape and idc shape lemmas state positions >= 1 (`(mv-nth 0 x)` normalizes to `(car x)` and
  never matches): a function's stobjs follow a leading code. A shape lemma's hypotheses are stobj
  facts only, so the function checks its own bounds (guard t) rather than relying on its guard.
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
