# Host adapter

The files here are the host lines of a build: the images
(`native/build.lisp`, `native/build-dtn.lisp`), the extraction world the served
product is extracted from (`../tools/extract/world-host.lisp`) and the store-test
image (`native/build-store-test.lisp`) load them with `ld` or raw `load`.
`tools/host_loaded_check.py` refuses a file here that no build loads: a
prototype or a retired host goes (its record stays in `planning/evidence`, the
path in `planning/retired-paths.json`), and a test harness lives in `tests/`
(the deterministic acceptance simulator is `tests/acl2/simulator.lisp`, run by
`python3 tools/run_simulator.py` after certification).

Read the [host contract](../specs/host.md) before changing packaging or an
event loop. Do not create a second implementation of core semantics to make the
host easier to package: ACL2 owns every decision, the host performs I/O and
calls it.
