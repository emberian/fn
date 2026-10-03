# LANEDUMP stage-5b (Opus 5.5, 2026-10-03) -- continuation

## Branches (all pushed to origin)
1. lane/stage-5b 89c779f78 = TIER A, READY CONTENT (origin/dev merged at 355a5c843).
   - f98e1ff1b: tier A admitted form by form in the hbox image-world REPL (owner-host.lisp 451 forms +
     host/owner-retain-host.lisp, 0 refused). Body fixes: fn-owner-take reads the queue head under consp;
     fn-owner-io REFUSES an unsafe observation in its body (:unsafe-observation, state unchanged) instead of an
     argument guard (D40 refuses argument conjuncts); minimal-theory guard hints. Guard-proof steps before->after:
     take 21.9M FAILED -> 662; control-submit 6.77M -> 791; apply-limit-profile 2.93M -> 286. 13 preservation
     theorems 30..3,375 steps. Hand lemmas: fn-owner-io-refuses-an-unsafe-observation (+2 ground witnesses),
     fn-owner-idrp-install-preserves-lgoc. This is the frozen tier-A coordinate DEF-ENTRY reproduces.
   - 843b68d68: regen (interface_emit --check 0, host_check books/load 0, ledger 0, reach --strict 0, secrets 0).
   - NATIVES hbox s5b at 843b68d68: ALL GREEN (owner 19/19, log 4/4, recovery 13/13, init_publication 4/4,
     crash_model 6/6, reader_clients 10/10). Dir hbox:/tank/fn/scratch/stage-5b/native-s5b.
   - 89c779f78: merge of origin/dev; the post-merge regen/fast checks were started but NOT harvested (generated
     files may need `interface_emit --write` etc. after the runner's merge). No certify run of the closure.
2. lane/sf-records 393d9143e (from origin/dev) = X05 INTERIM, coordinator-approved: fn-sf-record-listp gets an
   mbe :exec walk (fn-sf-record-list-walkp) over fn-sf-event-fields, which dispatches the event kinds ONCE per
   record (the logical walk ran fn-held-p ~6x per record). Logic unchanged; fn-sf-event-fields-are-the-readers and
   fn-sf-record-list-walkp-is-record-listp proved before verify-guards. books/store-files.lisp admitted in full in
   the hbox REPL (0 refused). UNVERIFIED: the exec-vs-logic teeth appended to tests/acl2/store-files-teeth-tests.lisp
   (never run); no certify of store-files' closure (big fan-in: use farm --affected-by books/store-files); no cost
   measurement (expect ~3x on fn-sf-record-listp; COST-GATE had 63 ms at N=1000).
3. lane/stage-5b-carrier fa32ac06f = CARRIER MOVE WIP, NOT READY, does not build.
   - books/owner-carrier.lisp: defstobj fn-owner-st (fn-ost-ocfg, fn-ost-installedp, fn-ost-carry); accessors
     fn-owner-boundp/-ocfg/-retain-carry, the ONLY updaters fn-owner-install-ocfg / fn-owner-retain-carry-put, and
     their effect/frame lemmas (same names as before, so tier-A hints mostly survive).
   - tools/owner_carrier/: the transformer. xf.py (classifier: R reader / O owner-only writer returning the stobj /
     M mixed writer returning stobj+state; rewrites formals, stobjs, guards, let/mv-let/stobj-let bindings, tail
     value/mv, call sites; rewrites theorem events; DELETE/RENAME/DEAD lists for the old state-global frame lemmas),
     world.py (reads sigs2.txt), sexp.py, run.py (fixed point dropping unused STATE from internal readers; prints
     FLAGS = unclassified sites, must be empty), hand.py + hand/ (hand-written books spliced in), redo.sh.
     SCRATCH PATHS ARE HARD-CODED in run.py/hand.py: make them relative to tools/owner_carrier before use.
     sigs2.txt was dumped from the image world (s5-dump2 in the iw5 REPL: formals, stobjs-in/out, class, touch/
     writer/entry flags; closure = every function whose body or guard reaches 'fn-owner / 'fn-owner-retain-carry):
     277 touchers, 104 writers. REGENERATE it at landing time on then-current dev (the coordinator wants the move
     re-run on dev in one held batch, not rebased).
   - Admitted from source (hbox REPL): owner-carrier, owner-state-accessors, owner-retain-state,
     owner-obligation-state, owner-retain-transitions, owner-config-state, owner-connection-state,
     owner-recovery-retain, owner-cursor-domain, owner-retain-carried (def-carried row needs the extra
     (create-fn-owner-st) witness: hand.py adds it).
   - NEXT FAILURE: books/owner-connection-callbacks fn-owner-callback-reader-view-preserves-owner-bound: a :use
     :instance substitution term mentions STATE where the hint's pairs were rewritten; xf_event mishandles
     (:instance thm (var term)) pairs (it treats the pair as a call). Fix: in xf_event, rewrite only the TERM of each
     instance pair. Then: owner-connection-callback-refinement, host files in the image world (tools/rd3-prefix.lisp
     + build/s5-rest.lisp pattern from this lanedump's session: ld prefix, set-cbd host, send-range owner-host, then
     the rest of world-host's lds), host/native: fnn-arena-then-state must pass the live fn-owner-st before state
     (add fn-owner-st to fnn-trailing-kind's run and fnn-live-stobj), tests/acl2 users, owner_globals_check baseline
     (X16) retired, interface_emit regen, natives owner/log/recovery/init_publication/crash_model/reader_clients.
   - Also in the carrier WIP: SWEEP-OPS's fn-owner-transit-verdict-buffer and sweep-ops-cfg's two wrappers are
     covered automatically IF sigs2.txt is regenerated on the dev that contains them.

## Decisions/answers given (coordinator agreed)
- fn-owner-io's guard CANNOT be narrowed: every fn-sf step is (if (mbe :logic (fn-sf-statep s) :exec t) STEP s),
  so guard => fn-sf-statep is forced up the chain. Option (1) (unconditional steps, shape guards, twins under
  fn-sn-statep) recorded by the coordinator as a design question for Astra; do NOT start it.
- No :raw-with until DEF-ENTRY's definterface boot-strap-primitive fix is on dev.
- Tiers B/C: only as def-owner-writer forms (DEF-ENTRY, lane/def-entry) over the stobj carrier profile
  (books/owner-retain-frame.lisp fn-owner-retain), after the carrier move lands.
- The image-level trap (origin/lane/rd3-trap) stays deferred until a real raw-dispatched entry exists.

## Ledger
X05 in-progress (interim lane/sf-records 393d9143e), cg-owner-io-guard in-progress (same), X16 open (carrier move).

## Next, in order
1. Runner: land lane/stage-5b 89c779f78 (tier A; natives s5b green). Regenerate generated files after the merge.
2. lane/sf-records: run the teeth (REPL tests/acl2/store-files-teeth-tests with --source-deps store-files), farm
   --affected-by books/store-files on hbox, measure fn-sf-record-listp at 1k/10k/100k guards-on vs before; READY.
3. Carrier move per item 3 above; then def-owner-writer tiers B/C; then :raw-with on fn-owner-io + trap redesign +
   per-call guard measurement at 1k/10k/100k on realistic state.

## In flight / sessions
No REPL sessions should be live (sft may be; stop with `python3 tools/proof_repl.py stop sft --host hbox`).
Worktrees: build/lanes/stage-5b, build/lanes/sf-records, build/lanes/stage-5b-carrier (remove after landing).
