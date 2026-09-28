#!/bin/sh
# tools/extract/check.sh TREE IMAGE -- the extraction differential (e4, lane
# extract-2; fail-closed gate, lane extract-gate): A-EXTRACT's qualification
# of one build (specs/failures.md).  Run on hbox, in a tree whose books are
# certified and whose developer image IMAGE is built (tools/hbox_native.sh
# makes both; `make extract-check' runs this there).  The gate is
# tools/extract/gate.py: build, transcripts, probes, store, functions, each
# fatal, every child's exit status checked, every stage's output held to
# its manifest.  Writes TREE/build/extract/check/ (status.json,
# extraction-manifest.json, the logs) and prints `extract-check: PASS' or
# `extract-check: FAIL at STEP: REASON'; exits 0 only on PASS.
# Environment: FN_EXTRACT_ACL2, CHICKEN, EXTRACT_STORE, EXTRACT_FCHECK_PER,
# FN_EXTRACT_SOURCE (the source id for the manifest; default git HEAD).
[ $# = 2 ] || { echo "usage: check.sh TREE IMAGE" >&2; exit 2; }
TREE=$(cd "$1" && pwd) || { echo "extract-check: FAIL at setup: no tree $1"; exit 1; }
exec python3 "$TREE/tools/extract/gate.py" "$TREE" "$2"
