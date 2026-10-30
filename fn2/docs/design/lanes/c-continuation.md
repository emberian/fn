# fn2 layer C continuation (present state, rewritten whole after every commit)

Seat: Opus, layer C (the ordered-run metadata engine). Eighth seat since 2026-10-30. Method of
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
0. **Landed: the :sealable grant source, 83ced3bf9** (dev, pushed; READY sent; whole gate on
   03b4a2f41 green). The constrained pair fn2-sealable-ready-p / -grant-one is at the head of
   fn2-machine-access-events in machines-a-access.lisp. It exports cons/true-list type, the
   corep/wfp shape, and liveness `fn2-sealable-grant-one-live` (ready implies the grant's id is
   not *fn2-none*). The defaults fn2-sealable-ready-none / -grant-none are attached in ONE
   defattach form, and C's real attachment must also attach both together and prove liveness.
   :sealable is rank 23 in resources.lisp, giving `*fn2-wait-sealable*`. Waiting for B5-3's sha
   to write machines-c-sealer.lisp.
1. **machines-c-sealer.lisp.** Rulings and facts so far:
   - **Field stripe (main's ruling).** The sealer needs *fn2-seal-field-rows* = 1280. That is more
     than one 1024-row transaction stripe, and a second fn2-fields core child is refused
     (defcorechild: "unique stobj"). In this commit, after B5-3 lands, change machines-b.lisp:
     add `(defconst *fn2-b-seal-field-rows* 1280)` and add it to the sum in fn2-b-field-rows.
     Name the change in the commit message; B reads the diff after. C's side:
     `(assert-event (<= *fn2-seal-field-rows* *fn2-b-seal-field-rows*))`, and fn2-idc-profilep's
     field inequality gains `+ *fn2-b-seal-field-rows*`. FBASE = 128*format-slots + 1024*t.
     Regate whole.
   - **B's answers (2026-10-30).** (1) fn2-fc, fn2-fc-context and fn2-b3 take their row count
     from :format-slots (default 3, floor 3), so checker row 3 + windows exists only when the
     profile sets it. Ruled: B5-4a derives it, with default and floor (+ 4
     (:large-upload-windows profile)), and refuses a lower setting. Until B5-4a lands, the
     machine's unit test profile sets :format-slots to 4 + its windows explicitly, and the
     sealer reads its row through fn2-fc-rows with a run-time check. (2) Digest regions 129-135
     are free on every per-row stripe (*fn2-digest-stride* = 136; B's named regions are 0-128).
   - **Wake (main's ruling, 2026-10-30).** Neither the direct wake-id write nor B's :notify.
     The sealer parks on a new D0 wait kind, :sealable, and the grant service wakes it as its
     fifth grant source, following S5 (b31e5d4de, the ledger as the fourth). C writes this as a
     small foundation commit under the whole-tree gate, named in the message. The A5r seat (A's
     owner) reads the diff. It lands with, or just before, machines-c-sealer. Plan:
     * `fn2/books/resources.lisp` (D's book): append `(:sealable :rank 23 :unit :overlay :bound
       (:profile :identity-overlays) :reserve nil :why "...a pure wait, never held...")` to
       *fn2-resource-order*. Appending keeps every existing enum value; rank 23 is above every
       held kind, so rule (c) holds for a waiter holding nothing. Update `(assert-event (equal (len
       *fn2-resource-order*) 22))` to 23 and the printed form in fn2/docs/d-machines-nntp.md §3.
       The wait enum `fn2-wait` comes from strip-cars (machines.lisp:13), so it gains
       `*fn2-wait-sealable*`. Check tests/resources-unit.lisp: its fixture appends a duplicate at
       rank 23.
     * A constrained pair, declared in the assembly world before `(fn2-machine-access-events)`
       in assembly-access.lisp (where S5 put `(fn2-account-events)`): `(fn2-sealable-ready-p
       fn2-core) => *` and `(fn2-sealable-grant-one fn2-core) => (mv * fn2-core)`, with exported
       corep/wfp lemmas for the grant (what fn2-core-preserves gives). Default attachments: nil,
       and `(mv *fn2-none* fn2-core)`. Tested on forge: defattach accepts stobj input and
       `(mv * st)` output.
     * machines-a-access.lisp: `fn2-machine-grant-ready-p` gains `(fn2-sealable-ready-p
       fn2-core)`, and `fn2-machine-grant-one` gains the clause `((fn2-sealable-ready-p fn2-core)
       (fn2-sealable-grant-one fn2-core))` before `(t ...)`. Mirror S5's edits to
       tests/core-child-assembly-access.lisp / -index.lisp.
     * C's attachments go in assembly-callbacks-c. Ready: the sealer row's wait reason is
       :sealable, the seal row is :idle and `fn2-seal-pick` finds one. Grant-one: clear that
       wait reason and return the sealer's id.
     * The sealer's :sealing arm parks on :sealable when the step answers :idle, :full or
       :cache.
   - **Kind and owner.** Declare `(defmachine fn2-sealer ...)` before fn2-machine-index-events
     (assembly-index includes machines-b, then machines-c-groups, then conn). Put it in a book
     included at the top of machines-c-successor, after machines-c, so it comes after fn2-commit.
     Then `*fn2-idc-owner-kind*` = its position in `(fn2-machine-names world)` through
     make-event, replacing 254: every owner triple changes, so all C books recertify. After the
     index: `(assert-event (equal *fn2-sealer-kind* *fn2-idc-owner-kind*))`.
   - **Children (C's own, unique types).** fn2-seals (1), fn2-run-builds (1), fn2-run-writers
     (*fn2-seal-writer-rows* = 7), fn2-run-restarts (7 x capacity), fn2-ribbon-builds (1),
     fn2-ribbon-band (`fn2-ribbon-slots` of :identity-overlay-entries), with C profile keys, as
     fn2-idc-child does in machines-c.lisp. Existing children it uses: overlays, overlay-index,
     run-installed, run-cache, fields, pool (C/B) and fc, fc-context, b3, digests (B).
   - **Core wrapper and costs.** `fn2-sealer-step (budget fn2-core)`: a stobj-let of the 16
     children, emitted in assembly-callbacks-c like fn2-identity-core-events, with
     fn2-core-preserves. defcost :bytes 4096 :tables (the 16 fn2-core-* children). Init through
     fn2-seal-init in fn2-init-engine (executor.lisp; same pattern as fn2-groups-genesis), with
     wbase 0, fbase as above, crow 3 + windows, fill 64 KiB, and the owner (kind 0 1).
   - **Arms.** :sealing calls fn2-sealer-step. On :more, :retired or :done it stays runnable. On
     :idle, :full or :cache it parks (woken by publish). Any other code stops the core: add a stop
     reason :sealer in exec-state.lisp. :stopped is terminal. Fix the comment above
     fn2-seal-step, which says the row goes :failed. Models: machines-a.lisp (scribe: the checked
     language, fn2-machine-result, park), machines-a-costs.lisp (defcost forms),
     lanes/a-to-d-arm-contracts.md (contract syntax, :holds, postures).
   - Then the production assembly move of the C units; land; READY.
2. **The device half**, when B5-4's :run-replacement member sha arrives: fn2-commit-admit-runs,
   the defattach of fn2-runs-install, manifests one level deep (the sealer writes the manifest
   run), M2's cold leg, M3's device leg, and the device half of the death-cut keystone. Inside
   B5-4's foundation commit: rename the wrappers to fn2-succ-core-publish / -drop (reply (3)
   given), with the lemma "a release by another owner leaves that slot unchanged".
3. **Owed.** Test the lookup's and resolve's run legs on real runs (the sealer installs them
   now). Shave machines-c-stage (52.7 s). runs-served is 38.8 s.

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
