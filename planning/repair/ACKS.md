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
ratchet:keystone_emit:fn-zpl-decode-bufs-from-the-empty-pool — stobj-bound claim (fn-zin-* stobjs) defteeth cannot express (item DEFTEETH-STOBJ-AND-ASSUMPTION (1)); teeth meanwhile: tests/acl2/deflate-pool-tests.lisp:89 defthm dpt-empty-pool-witness (every hypothesis and the whole conclusion on the held-out stream) — lane p-defteeth-stobj landing removes the name from teeth-ceiling.json (deputy-P)
ratchet:keystone_emit:fn-psrv-store-prepare-next-keeps-the-stored-octets — stobj-bound claim (fn-arena) defteeth cannot express (item DEFTEETH-STOBJ-AND-ASSUMPTION (1)); teeth meanwhile: tests/acl2/store-budget-stored-post-tests.lisp:83-87,93 assert-events on *sbsp-st1* (POST 1 stage: the relation before and after, staged row, arena count; sbsp-stage at :67 runs it under with-local-stobj) — lane p-defteeth-stobj landing removes the name from teeth-ceiling.json (deputy-P)
ratchet:keystone_emit:fn-lgc-failed-barrier-recovers-a-prefix — hypothesis fn-lg-platform-tears-p is the named assumption fn-assume-crash-tearp, no executable break (item DEFTEETH-STOBJ-AND-ASSUMPTION (2)); teeth meanwhile: tests/acl2/owner-batch-tests.lisp:325 assert-event (all four hypotheses incl. the tear, the whole conclusion incl. the committed-record conjunct) — lane p-defteeth-stobj landing removes the name from teeth-ceiling.json (deputy-P)
ratchet:keystone_emit:fn-dl-thread-loop-is-revappend — abstract generator lemma over the non-executable fn-dl-th-* stand-ins (books/def-loop.lisp:518), so no executable witness exists (item DEFTEETH-STOBJ-AND-ASSUMPTION (3); its fold twin is in the ceiling already); teeth meanwhile: tests/acl2/def-loop-tests.lisp:875-878 assert-events, the :thread instance dlt-th-run equal to its loop on ground lists — lane p-defteeth-stobj landing removes the name from teeth-ceiling.json (deputy-P)
ATTACH-ORDER-IMPLICIT — the attach order is guarded today by host_check --attach-order and by the umbrella's generated line order, which lane n-tls-chain keeps byte-identical; making it an explicit dependency world.py reads is C's lane once n-tls-chain lands — C, after n-tls-chain merges
