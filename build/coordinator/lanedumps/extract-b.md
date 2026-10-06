# LANEDUMP extract-b (2026-10-05, successor of extract; card D, D40)

## State
- Worktree build/lanes/extract-b, branch lane/extract-b, from dev 319aee828.
- Commit 913113600 (this lane): D40 raw-dispatch verdicts judged in the ACL2
  world, carried as data. Salvaged the overnight lane/extract WIP (+205/-60);
  nothing of that WIP remains unmerged (check `git -C build/lanes/extract diff`
  only if 913113600 is somehow reverted -- its message lists every file).
- Uncommitted (being finished now): tests/acl2/raw-dispatch-verdict-tests.lisp
  section 4 -- defteeth for both keystones. Status: written, hand-verified
  against the macro (books/defkeystone.lisp), laptop certify pending.

## Design (10 lines)
1. fn-raw-dispatch-verdicts: table NAME -> (DIGEST PROBLEM TARGET CREATORP),
   one row per raw-declared fn-interfaces entry, written by
   host/raw-dispatch-verdicts.lisp (a make-event) after the last declaration;
   loaded by host/native/build.lisp, build-dtn.lisp, tools/extract/world*.lisp.
2. The table's guard re-judges every pair: no event writes a verdict the world
   does not give (fn-rdv-verdict-okp calls fn-rdv-judge).
3. DIGEST = fn-blake3 of fn-sdg-canon octets of fn-rdv-row (name, kvs,
   formals, stobjs-in/out, guard, symbol-class) -- every accessor the core's
   runtime (tools/extract/clruntime.lisp) answers from the snapshot.
4. fn-rdv-admit (logic mode, guard t): (mv PROBLEM TARGET CREATORP); clean only
   when a verdict judged exactly this name+digest row with no problem.
5. Keystones: fn-rdv-admits-only-a-clean-judged-row,
   fn-rdv-admit-returns-the-judged-target (books/raw-dispatch-verdict.lisp).
6. fnn-install-raw-dispatch (host/native/raw-trap.lisp): ONE path for image and
   core; each raw-declared row admitted by fn-rdv-admit over the digest the
   world it has computes; refused/unjudged/changed row stops the build BY NAME.
7. tools/extract/core-export.lisp xt-core-verdicts: re-judges at export,
   refuses a world whose table is not its own judgment, ships the table in the
   core snapshot; a refused export writes nothing.
8. Fixes the core dying at load since 633e3cdec ("Selected ACL2 table
   metadata is unavailable for FN-CARRIED"): the core no longer re-judges.
9. tests/test_native_raw_dispatch_trap.py: SBCL driver over a minimal ACL2
   shim loads the book's VERDICT_FORMS; test_only_a_clean_judged_row... pins
   refused/changed/unjudged each stopping the install by name.
10. Digest does NOT cover the target's compiled code or the world beyond the
    row (books/raw-dispatch-verdict.lisp header says what it does not cover).

## Exact continuation
1. [DONE this session] The teeth are green:
   - Laptop certify-20261006T015538Z-86958 PASSED (books/defkeystone,
     tests/acl2/defkeystone-tests, tests/acl2/raw-dispatch-verdict-tests);
     manifest filed (planning/evidence/manifests/...json, indexed).
   - The macro gap and its fix (workq EXTRACT-VERDICT-TEETH, worker
     extract-b): defteeth's assert-event cannot evaluate `(mv-nth k
     (mv-fn ...))` claims (ACL2 forbids a multiply valued call as an
     argument outside a theorem context, :DOC mv-nth); the :lemma path
     cannot express a let-conclusion either (the check demands equality
     with the SUBSTITUTED TRANSLATED claim; a let closes into a 4-formal
     lambda under substitution, a 1-formal one written directly).  FIX:
     books/defkeystone.lisp fn-dt-expand now runs fn-dt-bridge-events over
     the emitted events -- each assert-event's value re-translated
     (stobjs-out T) with every >1-output call wrapped in (mv-list k ...),
     definitionally the identity; unused lambda formals whose actuals are
     variables/constants are dropped (source lambdas name no unused
     formal).  Identity for mv-free claims; the three pinned expansions
     unchanged; new mv sample fn-dkt-two-first-is-x pins the bridge.
     TRAPS: (stobjs-out 'if w) HARD-ERRORS -- read (getpropc fn
     'stobjs-out nil w); translated let-lambdas carry ignorable formals.
   - tools/teeth_check.py: defkeystone/defteeth-expansion assert-events
     are now marked generated and exempt from the hand-written
     multi-valued-in-evaluation check (the macro bridges them); the 21
     remaining findings are other books' pre-existing hand debt.
   - NO defteeth-check in this book: its closure (raw-dispatch-verdict ->
     state-digest -> ... -> def-keyset-check) carries other books'
     fn-teeth-owed rows (dev-wide gate debt); comment in the file says so.
2. [NEXT] Commit (tests + defkeystone + defkeystone-tests + teeth_check),
   secrets_check, push lane/extract-b; HARDEN.md row; hbox narrow certify
   (farm.py submit hbox --lane --affected-by tests/acl2/raw-dispatch-
   verdict-tests.lisp -- one heavy job, expect queue delay behind
   m1d5-head/span-borrow).
3. Mission remainder (card D): (a) core LOAD-side digest check -- the core
   computes each row's digest from its snapshot at load and refuses BY NAME on
   mismatch (fnn-install-raw-dispatch already does this in the image path;
   confirm the extracted-core path uses the same fnn-install and the snapshot
   carries fn-interfaces + fn-raw-dispatch-verdicts); (b) wire xt-core-verdicts
   into the export the release actually runs (check tools/extract/core.sh and
   release-tarball FN_RELEASE_SERVED=extracted); (c) qualification smoke/core/
   peer with the same pass/fail set as the ACL2 image; (d) close
   planning/decisions.md item 8 (the D40 row); HARDEN.md row once certified.
4. Context docs: build/coordinator/OVERNIGHT.md "Added to the queue",
   lanedumps/integrator5-START.md, tools/extract/core-export.lisp.

## Notes / traps
- keystone_emit --check: 165 pre-existing findings (base "?", whole dev), none
  name fn-rdv-*; the manifest is stale dev-wide, NOT this lane's to rewrite.
- teeth_obligations gate scans defkeystone forms only; plain defthm+defteeth
  (our shape) does not add gate rows.
- certify on hbox: ONE narrow `farm.py submit hbox --lane --affected-by
  tests/acl2/raw-dispatch-verdict-tests` when laptop is green; box is busy
  (m1d5-head then span-borrow images; check certs.py/run.sh first).
- ledger --book on the tests file parses clean, --strict clean.
