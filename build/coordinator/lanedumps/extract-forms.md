# extract-forms continuation (2026-10-07, after ~370K context; stop here, resume fresh from this file)
Branch lane/extract-forms (merged origin/lane/extract-c 5ded71b9c). Worktree /Users/ember/dev/fn/build/lanes/extract-forms.
hbox scratch: /tank/fn/scratch/extract-forms/{tree (synced lisp via /tmp/extract-forms-sync.sh), out, *.log}; Oct 5 world image
 /tank/fn/scratch/extract-cache/world-18bcd401.../world (key TESTKEY used in scratch runs). NO kill/pkill on hbox (incident rule); always `timeout`.

DONE (all pushed):
 (i) spike (tools/extract/spike/).
 (ii) tools/extract/forms-export.lisp: xt-fe-export (emitter) + xt-verify-defs (X1) + fe-check-closure (X2) + fe-verify-core (pure).
   Units in defs.lisp are ";;;; UNIT <id>" blocks; manifest.tsv = id, sha256(block), origin (+ #world_key, #file lines);
   runtime.tsv = names the forms call that clruntime.lisp defines; gaps.txt = names nothing provides (core.sh refuses).
   Oct 5 world, host tokens: 1957 roots -> 25376 units, 26 runtime refs, 0 gaps; bare SBCL `load` of defs.lisp: 0 undefined fns, 0 WARNINGs;
   xt-verify-defs OK; export ~25 s. ACL2-system part derived from /tank/fn/acl2-8.7 sources (228 defuns+defstruct+defconst, file sha+line).
   Canonicalisation: uninterned gensyms, ONEIFY<n>, gentemp T<n> renamed by first occurrence per unit.
   Tests: tests/test_extract_forms.py (11 laptop sbcl tests; 3 world tests on hbox with FN_EXTRACT_FORMS_WORLD/OUT/KEY) all green.
 core.sh / core-main.lisp EDITED (UNTESTED end to end): cl.py call removed; export.lsp now also runs xt-fe-export (:deadline 900, outer timeout),
   gaps.txt refusal, separate xt-verify-defs run, defs.lisp.verified-sha256 recheck, one with-compilation-unit through host-block loading
   defs.lisp as SOURCE (defglobal inits are evaluated at compile time), core.sh greps sbcl.log for "Undefined functions/variables" (X2 at END of build).
NEXT:
 1. Needs the dev-tree extraction world image (asked Deputy E; GO pending; one hbox job, world_image.sh, timeout 3000). Then run core.sh on hbox
    with FN_EXTRACT_IMAGE=/tank/fn/images/<sha>/fn-host-developer; expect host-defined constrained fns (FN-PGS-FILL-FRAME, FN-DURABLE-REALIZE-*,
    FN-ARENA-STORED, FN-SIG-VERIFY, FNN-COUNTERPART) defined by host-block so no undefined at end; classify the 9 names (E's list in his message) in the
    report; ARITY/FORMALS/FMT0/KNOWN-PACKAGE-ALIST/SPECIAL-TERM-NUM/STATE-P1 are reached: classify, flag world readers to E (do not shim).
    FN-CAT live var: emitted by decl:specials/stobj unit? verify on dev world (fn-cat absstobj live var).
 2. clruntime.lisp: shrink to the 26 refs + host needs (state globals, world snapshot [extract-c owns table-alist/rows], live stobjs registry,
    errors, fast alists, fmt-to-comment-window). DELETE xl-* total primitives, xl-resize, xl-halt, xl-guard-violation, stobj-table keys
    (registry unit in forms-export.lisp still calls xl-register-stobj-names: drop that form + the keys there). Pin each remaining entry to ACL2 source
    line or a differential vector (runtime.tsv column 3 says host-only for the rest; add reasons). tests/test_extract_fastalist.py stays.
 3. Delete (iii): chicken.py cl.py *.scm fcheck* (fcheck.py fcheck-main.scm fcheck.lisp?) hostio.scm native.scm runtime.scm served-main.scm, CHICKEN branches of
    build.sh, compare*.sh, check.sh, measure.sh, probes.py, stateful.py, gate.py, declared-blockers.json; tests depending on cl.CL/chicken
    (test_extract_runtime_constructors, incoming_controller, saved_registry, callback_world, primitive_counterparts, stobj_table, + tests/extract/stobj_table_path_drivers.py)
    are tests OF the deleted translator: delete with it. Docs naming CHICKEN: planning/current.md, packaging/release-tarball.sh, tools/extract headers,
    Makefile, tools/current_view.py, host/store-write-host.lisp comments (grep -rli chicken; skip planning/archive and review docs).
    frontend.lisp's JSON IR + core-export's core.json/packages.json writers become dead: trim AFTER extract-c lands (core-export.lisp is theirs).
 4. Re-target gate.py (646 lines; CHICKEN-shaped: build/csc/served/fcheck steps) to compare fn-core against the ACL2 image: transcripts, probes, store,
    stateful, owner steps keep their image-vs-X shape with X = fn-core; drop the chicken side and the functions/fcheck step or re-aim it at `fn-core --xl-load`.
    tests/test_extract_gate.py (651 lines) uses stand-ins: update with it.
 5. READY needs: hbox core.sh green with zero undefined names on the dev world; filtered tests/test_extract_forms.py + remaining test_extract*; push.
