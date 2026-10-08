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
MEM-014 — needs a reader-lifetime statement (no reader, feed resolution or publication reads the retained history root after its release) before the retained generation can be released ahead of the candidate's allocation; not for the train-27 push (S, 2026-10-08) — N opens the lane once MEM-013 B' lands
MEM-013-LIVE-ROOT — the live history root moves onto MEM-013's canonical placement only after B' lands for the checkpoint image; urgency waits on N's 25k probe on the train-27 developer image (held ruling 20) — S, once B' is READY and the 25k probe reports
ATTACH-ORDER-IMPLICIT — the attach order is guarded today by host_check --attach-order and by the umbrella's generated line order, which lane n-tls-chain keeps byte-identical; making it an explicit dependency world.py reads is C's lane once n-tls-chain lands — C, after n-tls-chain merges
ratchet:owner_globals_check:host/owner-host.lisp — fn-owner-sco-serial (RL-02 publication-capture serial, 431bb1981) joins the baselined publication-capture family fn-owner-sco-* / orc-pass, which moves together into the carried owner value; coordinator option (a), 2026-10-08 13:40; the other two over-baseline names, fn-owner-reclaim-live and fn-owner-history-root-status, are NOT admitted — OWNER-CARRIER-GLOBALS (family 1 retires the raise; planning/design/owner-carrier-2026-10-04.md)
