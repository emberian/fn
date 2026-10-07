# extract-measure continuation (2026-10-07)
M0 done; see build/coordinator/mem-evidence-20261007-extract/RESULTS.md. Raw: hbox:/tank/fn/scratch/extract-measure/{core-m0,tree,*.log}.
M1 waits for origin/lane/extract-c. To redo: `git fetch`, rsync tree to hbox:.../tree, run `core.sh` (or core-nocheck.sh with FN_EXTRACT_WORLD_IMAGE=world-18bcd... until a world at the sha exists), then idle-core.sh on build/core/fn-core.core and `fn-core identity`. heap-inventory.lisp via --load with INV_OUT.
