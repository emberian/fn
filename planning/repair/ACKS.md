# Deliberately-unfixed items (the ACKs file)

# One line per item that is open on purpose, so "waiting on someone" is visible
# and not lost.  Format, one per line, em dashes (U+2014) as separators:

#     id — reason — who/what un-parks it

# `id` is a repair-ledger item id, a scenario id (SCN-nnn) or a native module
# (tests.test_native_x).  Every ACK must cite a written decision (a decisions.md
# entry, an item note, a coordinator ruling) in its reason; an ACK written only to
# make tools/coverage_gap.py green is a defect.  The report fails on a malformed
# line or an id that names nothing.  Lines starting with # are comments.
# Spec: build/coordinator/COORDINATOR-SOP.md.

#
# No entries yet (2026-10-06).  Candidates checked and refused: S152 is IN-FLIGHT
# (reclaim-funding; ember's figure-growth decision is escalated, not made);
# deferred items (DC04, X13, PROOF-SWEEP-20261003 -- ember paused Luna proof
# waves 2026-10-03 -- FILL-STORE-LINEAGE-DIVERGED-CHECKPOINT) are already PARKED
# by their own state and written note, so they need no ACK.
