# extract-chicken continuation (2026-10-07; base lane/extract-forms bb002d3c1)
DONE: (iii) CHICKEN extractor deleted; (iv) gate.py re-targeted fn-core vs image. Laptop-only, no hbox work.
Deleted: chicken.py cl.py fcheck.py fcheck.lisp *.scm(5) build.sh compare.sh compare-post.sh measure.sh post-ref.lisp declared-blockers.json;
 tests: test_extract_{runtime_constructors,incoming_controller,saved_registry,callback_world,primitive_counterparts,stobj_table}.py + tests/extract/* (all imported cl/chicken; fixtures under tests/fixtures/evidence kept).
 core.sh at bb002d3c1 does not invoke cl.py (grep-confirmed before deleting).
Edited: gate.py (steps: core, manifest, transcripts, probes, store, stateful, owner; no build/functions step; the functions step is DROPPED, not re-aimed:
 `--xl-load` is a developer-load hook, fcheck gen needed the CHICKEN IR; per-function evidence is X1/X2 inside core.sh), tests/test_extract_gate.py (28 tests, stand-ins),
 probes.py (scheme verb gone), stateful.py (--core flag gone, always fn-core), transcripts.py (POST sessions gone: only compare-post consumed them), check.sh, Makefile,
 current_view.py (+ regenerated planning/current.md), specs/failures.md A-EXTRACT row, host/store-write-host.lisp comments, comment-only in clruntime.lisp/core-main.lisp/core.sh/interface_emit.py.
NEW gate checks (fail-closed, named): gaps.txt nonempty; defs.lisp != defs.lisp.verified-sha256; manifest.tsv no units; build/core/lib not the image's lib; missing libfn-*.
Left for others (comment-only chicken refs, not mine this round): frontend.lisp:5,572,605 and core-export.lisp:64 (extract-core owns), host/interfaces.lisp:14,71,159,308,
 host/store-open-host.lisp:20, host/native/signatures.lisp:353 (host digests would churn), forms-export.lisp:647 "as cl.py did".
DEAD now (extract-core to trim): frontend.lisp's JSON IR emitters + core-export's core.json/packages.json writers (core.sh still requires core.json; nothing but core.sh/gate consumes it);
 inventory.json no longer produced; bench.py (image vs "served" programs: chicken-era verbs, no caller); store-write-host.lisp hx stubs have no realizer now.
 roots.sh stays (depth_check.py, interface_emit.py consume it).
Gate: tests.test_extract_gate (28), test_extract_forms, fastalist, core_launcher green; red-before: old gate.py against new test file -> TypeError Tools.__init__ missing csc/chicken_lib/swarm/build.
Unrun here: the gate end to end on hbox (needs a built fn-core).
