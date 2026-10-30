# fn2 layer C continuation (present state, rewritten whole after every commit)

Seat: Opus, layer C (the ordered-run metadata engine). Eighth seat since 2026-10-30 (handed off near its ceiling, 2026-10-30 late; a ninth seat starts from this file). Method of
2026-10-29 (`briefs/FN2-SEAT-COMMON.md`, path `build/coordinator/briefs/`): dev is the branch; Opus
writes the code; Codex only for bounded pieces with real signatures pasted; READY to main per
commit (SendMessage to "main"). Brief: `build/coordinator/briefs/FN2-LAYER-C-ORDERED-RUNS.md`. Layer
doc on dev: `fn2/docs/c-ordered-runs.md`. Spine (REVIEW-20261030): **C1c the sealer** is C's one
quest; C4b, C5, C6 wait until a POST is durable. New rule (main, 2026-10-30, "Landing on a moved
tip"): a commit gated whole at its base lands on a moved tip without a second whole gate when the
commits in between touched nothing in its dependency closure and carried their own gates (rebase,
recertify own books and the export, fast-forward); overlap (B5-3: machines-b, owed-export; B5-4:
the commit kind) means regate whole.

## Landed (READY sent for each)
- Earlier seats: C1a 181df0df0, C1b 8dfba6db2, C1b' 1e823b06f, run assembly 1c603fcdd, C2a-C2d, C3a,
  C3b, C-S1 d21ffb2b3, C-S2, C4a 34e106dca, C-S3 c82104671, review items b2ec7dda1, D5's seams
  294055805 (S-GROUP `fn2-groups` id 8, S-OUTCOME `fn2-outcome` id 9, S-ARTICLE-ID; book
  machines-c-groups.lisp; unit groups-unit).
- **:sealable grant source 83ced3bf9** (see Next 0).
- **C1c engine half 30ead9b23** (dev, pushed; READY sent): `books/sealer.lisp`,
  `books/runs-manifest.lisp` (fn2-manifest id 10, included by runs-served), `tests/sealer-unit.lisp`
  (registered in tools/owed-export.lsp after folds-unit). Gate on forge at e3573e0af: closure rc=0,
  export PASS, OWED.md 416 -> 451. Layer doc §5 (sealer), §7 (C-MANIFEST-ENTRY, C-SEAL-ORDER,
  C-SEAL-RESIDENT), §9 (two keystones), §10. Unit values reviewed (forge `build/vudrv.lsp`): three
  overlapping batches answer from each batch, two absent; 48-entry batches at fill 400 (multi-level)
  right; phases end free; the private-older rule leaves (frozen private); cut views exactly
  before/after for groups (30 rows) and identity with filter (20 facts).
  Sealer structure: fn2-seal-init, pick (older-p/sealable-p/pick), retire, start, unit, take-page,
  page, cache, callee shapes (build-work/add/promote/finish, the seven Ribbon phase helpers,
  ribbon-work), fn2-seal-root, fn2-seal-next, fn2-seal-build (dispatcher), filter-begin/-open/
  fn2-seal-filter, free-row, fn2-seal-install-run, fn2-seal-install, fn2-seal-step (macro
  fn2-seal-mv). The step returns refusals; nothing sets phase :failed yet (the machine arm will:
  fix the comment above fn2-seal-step in the machine commit, it claims the row goes :failed).

## Next (in order)
0. **Landed: the :sealable grant source, 83ced3bf9** (dev, pushed, READY sent). The constrained pair
   fn2-sealable-ready-p / -grant-one sits at the head of fn2-machine-access-events. It exports a
   cons/true-list type, the corep/wfp shape, and liveness `fn2-sealable-grant-one-live`. Defaults
   are attached in ONE defattach; C's attachment also attaches both together.
1. **The sealer machine: 7a6680f71 on the lane branch fn2/c-found ONLY (not dev, not pushed).
   Whole gate GREEN on forge at 83ced3bf9** (closure rc=0, export PASS). OWED rows go 484 ->
   491 (FN2-Q1-CASE-77/78, FN2-SEALER-PHASE-TOTALITY, -SEALING-/-STOPPED-BOUND/-FRAME), so
   regenerate OWED.md in the landing commit from that gate's export. **One red before landing:
   assembly-reference (A's) 65.7 s at load 7** (event: the reference copy/snapshot generation,
   'other' time, grows with the six new children). Remeasure on a quiet box (`tools/boxes.sh
   reserve forge`). If it is still over 60, ask main and A5r for a split of assembly-reference.
   Files:
   - `books/machines-c-sealer-kind.lisp` (new). Includes machines-all, then machines-c, so the
     registry order is A, commit, sealer, the same as in the assembly. It holds `defmachine
     fn2-sealer` (states :sealing :stopped; field stopped; budget 4096/32/4; capacity 1; initial
     wait none) and the defcosts fn2-sealer-step (16 tables) and fn2-sealer-refuse.
   - `machines-c-successor.lisp`: includes the kind book. `*fn2-idc-owner-kind*` is now the
     sealer's registry position (make-event; it is 4), with an assert that it is not 254.
   - `books/machines-c-sealer.lisp` (new, includes sealer). The six children through
     fn2-sealer-child (profilep fn2-sealer-profilep), fn2-sealer-windows (:large-upload-windows,
     default 16), and fn2-sealer-fbase. The stripe is just below the transaction stripes:
     rows - 1024 t - 1280. Also fn2-seal-genesis (:no-row when 3 + windows >= fc rows) and
     fn2-seal-pending-p.
   - `books/machines-c-sealer-events.lisp` (new). The macro fn2-sealer-core-events, emitted in
     assembly-callbacks-c (now 47 s): fn2-sealer-step, fn2-sealer-genesis, fn2-sealer-pending-p,
     fn2-sealer-ready, fn2-sealer-grant, the lemmas fn2-sealer-ready-id / -grant-live /
     -grant-type, the defattach of the pair, fn2-sealer-refuse (+ preserves), fn2-sealer-start-row
     (park on :sealable, or stop the row), fn2-engine-genesis (groups, then sealer), and the
     callbacks fn2-sealer-seal / fn2-sealer-idle plus defmachine-run.
   - assembly-index includes machines-c-sealer instead of machines-c-groups. assembly-callbacks-c
     includes the events book and calls (fn2-sealer-core-events). executor.lisp's
     fn2-init-engine calls fn2-engine-genesis. exec-state gets the stop reason :sealer.
   - machines-b: `*fn2-b-seal-field-rows*` 1280 added to fn2-b-field-rows (main's ruling: C
     carries it, named in the commit message, B reads it after). machines-c: fn2-idc-profilep
     and the field-rows assert gain the term.
   - tests/sealer-machine-unit.lisp (new; GREEN). The real executor, tiny profile plus groups,
     :format-slots 5, :large-upload-windows 1. Before: no run, the overlay frozen, the row
     (sealing, :sealable=24). After 400 turns: run (8 1 3 0), overlay free, the row parked
     again, executor :idle, no stop, lookups (:ok 7) (:ok 11) (:absent 0). The no-row profile
     shows the row stopped and the overlay frozen. Evaluated in assert-event, NOT defconst:
     attachments are ignored in a defconst's evaluation.
   - Other seats' tests, fixed for the new kind: q1-unit (catalogue pinned 79 with (:run
     fn2-sealer :sealing) (:run fn2-sealer :stopped) after commit; coverage 79), q1-teeth
     (profile gains :large-upload-windows 2 and :format-slots 6; a stopped sealer row labels
     :outside-catalogue). sim-acquisition failed on the sealer's initial :sealable waiter;
     fixed by initial wait none, with genesis parking the row.
   - Layer doc: C-ENGINE-OWNER (as built), C-SEALER-MACHINE, C-SEAL-NO-ROW, departure 3 (the
     sealer's descriptor cap is 4 only because A's guard proofs range over every kind's caps).
   - Still to do before landing: (a) assembly-reference's time (above); assembly-init was
     58.9 s, executor 55.0 s, machines-c-stage 53.9 s at the same load. (b) The comment above fn2-seal-step in sealer.lisp still says the row goes :failed.
     (c) After B5-3's sha: rebase (B5-3 touches machines-b and owed-export, so a real overlap),
     regate whole, land (commit message names the machines-b line for B, the Q1 test edits for
     the Q1 owner, executor/exec-state for A5r), READY. Another seat has uncommitted Q1 edits
     in the shared tree (q1.lisp, q1-contracts, q1-controls*): tell main that the sealer's two
     cases need their controls too.
2. **C-S3a (mine, promised to main):** late octet args. `(fn2-successor-arg-octets-late t i j
   max)` at :prepare (max at most the slot's octet capacity, else :bounds), and
   `(fn2-successor-fill-octets t i j slot gen off len okind oslot ogen)` between stage and bind
   (:state unless staged and not bound; :bounds if len > max). Bind refuses :state while a late
   arg is unfilled. In machines-c-stage / -bind, whole gate.
3. **C-S4 (D writes machines-c-read.lisp, I read the diff).** My amendments are sent: reads
   stripes below the sealer's; re-check the source at every step (overlay phase plus arena gen,
   run version); the frontier comes from a :published column in fn2-id-engine set by publish
   (C adds it); LIST is a whole-schema ordered scan, not the range engine; identity through the
   real lookup.
4. The device half when B5-4 lands (as before). Owed: machines-c-stage shave (52.7 s).

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

## Certify times (forge, 2026-10-30 evening, closure at e3573e0af + C1c)
| book | s |
|---|---|
| sealer / runs-manifest / sealer-unit | 40.4 / 6.9 / 5.5 |
| runs-served / range-served | 38.8 / 29.2 |
| machines-c / -successor / -stage / -bind / -groups | 10.9 / 23.9 / 52.7 / 18.2 / 21.9 |
| executor | 45.0 |
| assembly-reference / assembly-init / assembly-callbacks-c | 45.6 / 43.7 / 31.2 |
