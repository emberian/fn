# fn2 layer C continuation (present state, rewritten whole after every commit)

Seat: Opus, layer C (the ordered-run metadata engine). Ninth seat (2026-10-30 night; the eighth handed off near its ceiling). Method of
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
  294055805, :sealable grant source 83ced3bf9, C1c engine half 30ead9b23.
- **C1c the sealer machine 429702ef1** (dev, pushed, READY sent; ninth seat). It was rebased onto B5-2
  5674cae12 and gated whole there (closure rc=0, export PASS). The moved tips f794c78f3 (A5r) and
  c01f87b6a (D6) got an own-books recertify plus the export. OWED went 557 -> 564. The Q1 pin is 100
  (B's 98 + 2). machines-b has format-slots 3 (recovery) and *fn2-b-seal-field-rows*. Stop reasons
  end `:recovery-release :sealer`. The owner kind is 5 now (recovery registers first; computed).
  The comment above fn2-seal-step is fixed (a refusal stops the executor with :sealer and the row
  is :stopped). RED named in the message, as main allowed: assembly-reference 74.3 s at load 9-11.
  The A5r seat's fix follows. Other assembly includers were also over 60 at that load (access
  72.7, callbacks-a 71.8, -d 65.4, init 64.5, executor 64.1, machines-a-unit 61.5, callbacks-t
  60.1) and need a quiet remeasure.
- Owed to me from others: A's frame lemmas (fn2-machine-kind preserved by each fn2-issue-K).
  When main sends their sha, set the sealer's descriptor cap 4 -> 0 in my own commit (departure 3
  closes). Q1's owner owes controls for the sealer's two cases.

## Next (in order)
1. **C-S3a, late octet args: written, on lane branch fn2/c-s3a (worktree build/lanes/fn2/c-s3a),
   WIP commit d1c7cef66 on 429702ef1. Whole gate running on forge /build/lanes/c (build/c1.pid,
   started 00:23 10-31).** The design (also layer doc §8 item 12):
   - fn2-succ-slots gains LATE and FILLED (u32 masks). fn2-succ-touch takes LATE. arg and
     arg-octets clear the arg's late bit.
   - `fn2-succ-arg-octets-late` (machines-c-successor) writes the raw row with ref-len = MAX, so
     stage sizes the entry at MAX. It refuses `:kind` for a key field, a digest, an integer field
     or a non-insert, and `:bounds` for MAX past the field's bound.
   - `fn2-succ-fill-octets` (machines-c-stage) writes the ENTRY row, so the transaction stays
     :staged. It refuses `:state` unless the transaction is :staged, `:kind` unless the arg is late,
     `:bounds` if LEN > the raw ref-len, and `:owner` against the slot's owner (it sets the owner if
     none is set).
   - stage-insert resets FILLED. bind refuses `:state` before binding anything if
     `fn2-succ-unfilled` (machines-c-bind).
   - Defcosts and core wrappers are `fn2-successor-arg-octets-late (tx i j max)` and
     `fn2-successor-fill-octets (tx i j slot gen off len okind oslot ogen)`.
   - Unit: identity-core-unit `fn2-icu-late`. It expects `(:declare :kind :kind :bounds :ok :early
     :state :staged :ok :ok :fill :kind :bounds :state :ok :owner :again :ok :state :ok :ok :ok
     :arena 20 0)`. The arena counts are the 83s (S) and 84s (T) in the frozen overview overlay.
     The REPL pass of the three books on forge (/build/lanes/c3a, a scratch copy) had no errors.
     The unit has NOT been run yet: the gate runs it.
   - Landing: squash the WIP with a real message (`git commit -F`), regenerate OWED.md from the
     gate's export (expect no new rows), rebase onto origin/dev, recertify on a moved tip per the
     rule, run the secrets check, `git push origin fn2/c-s3a:dev`, READY to main and D (D5 2/n
     waits on it).
2. **C-S4 (D writes machines-c-read.lisp, I read the diff)** when main sends the branch: READY-TO-LAND
   or what must change. My predecessor's five amendments: reads stripes below the sealer's;
   re-check the source at every step (overlay phase plus arena gen, run version); the frontier
   comes from a :published column in fn2-id-engine set by publish (C adds it); LIST is a
   whole-schema ordered scan, not the range engine; identity through the real lookup.
3. The device half when B5-4's :run-replacement member lands (main sends the sha):
   fn2-commit-admit-runs, the defattach of fn2-runs-install, manifests one level deep, M2's cold
   leg, M3's device leg.
4. Then C5 compaction. Owed: the machines-c-stage shave (52.6 s).

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

## Certify times (forge, 2026-10-30 evening, closure at e3573e0af + C1c)
| book | s |
|---|---|
| sealer / runs-manifest / sealer-unit | 40.4 / 6.9 / 5.5 |
| runs-served / range-served | 38.8 / 29.2 |
| machines-c / -successor / -stage / -bind / -groups | 10.9 / 23.9 / 52.7 / 18.2 / 21.9 |
| executor | 45.0 |
| assembly-reference / assembly-init / assembly-callbacks-c | 45.6 / 43.7 / 31.2 |
