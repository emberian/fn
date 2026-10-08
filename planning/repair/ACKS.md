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
ratchet:owner_globals_check:books/account-adoption-input-source.lisp — C q0: measure existing books-side owner-global funnels (OWNER-CARRIER-GLOBALS), including the catalog-root pair consolidated into one slot — OWNER-CARRIER-GLOBALS S6 removes the globals
ratchet:owner_globals_check:books/account-adoption-turn-state.lisp — C q0: measure existing books-side owner-global funnels (OWNER-CARRIER-GLOBALS), including the catalog-root pair consolidated into one slot — OWNER-CARRIER-GLOBALS S6 removes the globals
ratchet:owner_globals_check:books/account-replay-source.lisp — C q0: measure existing books-side owner-global funnels (OWNER-CARRIER-GLOBALS), including the catalog-root pair consolidated into one slot — OWNER-CARRIER-GLOBALS S6 removes the globals
ratchet:owner_globals_check:books/admission-preallocation-resources.lisp — C q0: measure existing books-side owner-global funnels (OWNER-CARRIER-GLOBALS), including the catalog-root pair consolidated into one slot — OWNER-CARRIER-GLOBALS S6 removes the globals
ratchet:owner_globals_check:books/admission-preparation-source-capture.lisp — C q0: measure existing books-side owner-global funnels (OWNER-CARRIER-GLOBALS), including the catalog-root pair consolidated into one slot — OWNER-CARRIER-GLOBALS S6 removes the globals
ratchet:owner_globals_check:books/admission-semantic-census-begin-refinement.lisp — C q0: measure existing books-side owner-global funnels (OWNER-CARRIER-GLOBALS), including the catalog-root pair consolidated into one slot — OWNER-CARRIER-GLOBALS S6 removes the globals
ratchet:owner_globals_check:books/admission-semantic-census-initial-order-refinement.lisp — C q0: measure existing books-side owner-global funnels (OWNER-CARRIER-GLOBALS), including the catalog-root pair consolidated into one slot — OWNER-CARRIER-GLOBALS S6 removes the globals
ratchet:owner_globals_check:books/admission-semantic-census-initial-refinement.lisp — C q0: measure existing books-side owner-global funnels (OWNER-CARRIER-GLOBALS), including the catalog-root pair consolidated into one slot — OWNER-CARRIER-GLOBALS S6 removes the globals
ratchet:owner_globals_check:books/admission-semantic-census-owner-refinement.lisp — C q0: measure existing books-side owner-global funnels (OWNER-CARRIER-GLOBALS), including the catalog-root pair consolidated into one slot — OWNER-CARRIER-GLOBALS S6 removes the globals
ratchet:owner_globals_check:books/admission-semantic-census-step-refinement.lisp — C q0: measure existing books-side owner-global funnels (OWNER-CARRIER-GLOBALS), including the catalog-root pair consolidated into one slot — OWNER-CARRIER-GLOBALS S6 removes the globals
ratchet:owner_globals_check:books/admission-semantic-exclusion.lisp — C q0: measure existing books-side owner-global funnels (OWNER-CARRIER-GLOBALS), including the catalog-root pair consolidated into one slot — OWNER-CARRIER-GLOBALS S6 removes the globals
ratchet:owner_globals_check:books/consumer-account-adoption-state.lisp — C q0: measure existing books-side owner-global funnels (OWNER-CARRIER-GLOBALS), including the catalog-root pair consolidated into one slot — OWNER-CARRIER-GLOBALS S6 removes the globals
ratchet:owner_globals_check:books/consumer-account-carries-state.lisp — C q0: measure existing books-side owner-global funnels (OWNER-CARRIER-GLOBALS), including the catalog-root pair consolidated into one slot — OWNER-CARRIER-GLOBALS S6 removes the globals
ratchet:owner_globals_check:books/consumer-account-durable-outcome-state.lisp — C q0: measure existing books-side owner-global funnels (OWNER-CARRIER-GLOBALS), including the catalog-root pair consolidated into one slot — OWNER-CARRIER-GLOBALS S6 removes the globals
ratchet:owner_globals_check:books/consumer-account-operation-state.lisp — C q0: measure existing books-side owner-global funnels (OWNER-CARRIER-GLOBALS), including the catalog-root pair consolidated into one slot — OWNER-CARRIER-GLOBALS S6 removes the globals
ratchet:owner_globals_check:books/consumer-account-state.lisp — C q0: measure existing books-side owner-global funnels (OWNER-CARRIER-GLOBALS), including the catalog-root pair consolidated into one slot — OWNER-CARRIER-GLOBALS S6 removes the globals
ratchet:owner_globals_check:books/consumer-remote-source-scan.lisp — C q0: measure existing books-side owner-global funnels (OWNER-CARRIER-GLOBALS), including the catalog-root pair consolidated into one slot — OWNER-CARRIER-GLOBALS S6 removes the globals
ratchet:owner_globals_check:books/consumer-remote-terminal-state.lisp — C q0: measure existing books-side owner-global funnels (OWNER-CARRIER-GLOBALS), including the catalog-root pair consolidated into one slot — OWNER-CARRIER-GLOBALS S6 removes the globals
ratchet:owner_globals_check:books/history-capture-state.lisp — C q0: measure existing books-side owner-global funnels (OWNER-CARRIER-GLOBALS), including the catalog-root pair consolidated into one slot — OWNER-CARRIER-GLOBALS S6 removes the globals
ratchet:owner_globals_check:books/history-config-journal-state.lisp — C q0: measure existing books-side owner-global funnels (OWNER-CARRIER-GLOBALS), including the catalog-root pair consolidated into one slot — OWNER-CARRIER-GLOBALS S6 removes the globals
ratchet:owner_globals_check:books/history-event-backing.lisp — C q0: measure existing books-side owner-global funnels (OWNER-CARRIER-GLOBALS), including the catalog-root pair consolidated into one slot — OWNER-CARRIER-GLOBALS S6 removes the globals
ratchet:owner_globals_check:books/history-operation-observation.lisp — C q0: measure existing books-side owner-global funnels (OWNER-CARRIER-GLOBALS), including the catalog-root pair consolidated into one slot — OWNER-CARRIER-GLOBALS S6 removes the globals
ratchet:owner_globals_check:books/history-semantic-writer-state.lisp — C q0: measure existing books-side owner-global funnels (OWNER-CARRIER-GLOBALS), including the catalog-root pair consolidated into one slot — OWNER-CARRIER-GLOBALS S6 removes the globals
ratchet:owner_globals_check:books/history-semantic-writer.lisp — C q0: measure existing books-side owner-global funnels (OWNER-CARRIER-GLOBALS), including the catalog-root pair consolidated into one slot — OWNER-CARRIER-GLOBALS S6 removes the globals
ratchet:owner_globals_check:books/history-source-capture.lisp — C q0: measure existing books-side owner-global funnels (OWNER-CARRIER-GLOBALS), including the catalog-root pair consolidated into one slot — OWNER-CARRIER-GLOBALS S6 removes the globals
ratchet:owner_globals_check:books/index-writer-ticket.lisp — C q0: measure existing books-side owner-global funnels (OWNER-CARRIER-GLOBALS), including the catalog-root pair consolidated into one slot — OWNER-CARRIER-GLOBALS S6 removes the globals
ratchet:owner_globals_check:books/owner-authority-proposal-state.lisp — C q0: measure existing books-side owner-global funnels (OWNER-CARRIER-GLOBALS), including the catalog-root pair consolidated into one slot — OWNER-CARRIER-GLOBALS S6 removes the globals
ratchet:owner_globals_check:books/owner-canonical-epoch.lisp — C q0: measure existing books-side owner-global funnels (OWNER-CARRIER-GLOBALS), including the catalog-root pair consolidated into one slot — OWNER-CARRIER-GLOBALS S6 removes the globals
ratchet:owner_globals_check:books/owner-canonical-read-state.lisp — C q0: measure existing books-side owner-global funnels (OWNER-CARRIER-GLOBALS), including the catalog-root pair consolidated into one slot — OWNER-CARRIER-GLOBALS S6 removes the globals
ratchet:owner_globals_check:books/owner-canonical-state.lisp — C q0: measure existing books-side owner-global funnels (OWNER-CARRIER-GLOBALS), including the catalog-root pair consolidated into one slot — OWNER-CARRIER-GLOBALS S6 removes the globals
ratchet:owner_globals_check:books/owner-catalog-root-state.lisp — C q0: measure existing books-side owner-global funnels (OWNER-CARRIER-GLOBALS), including the catalog-root pair consolidated into one slot — OWNER-CARRIER-GLOBALS S6 removes the globals
ratchet:owner_globals_check:books/owner-connection-callback-refinement.lisp — C q0: measure existing books-side owner-global funnels (OWNER-CARRIER-GLOBALS), including the catalog-root pair consolidated into one slot — OWNER-CARRIER-GLOBALS S6 removes the globals
ratchet:owner_globals_check:books/owner-connection-callbacks.lisp — C q0: measure existing books-side owner-global funnels (OWNER-CARRIER-GLOBALS), including the catalog-root pair consolidated into one slot — OWNER-CARRIER-GLOBALS S6 removes the globals
ratchet:owner_globals_check:books/owner-connection-state.lisp — C q0: measure existing books-side owner-global funnels (OWNER-CARRIER-GLOBALS), including the catalog-root pair consolidated into one slot — OWNER-CARRIER-GLOBALS S6 removes the globals
ratchet:owner_globals_check:books/owner-incoming-context.lisp — C q0: measure existing books-side owner-global funnels (OWNER-CARRIER-GLOBALS), including the catalog-root pair consolidated into one slot — OWNER-CARRIER-GLOBALS S6 removes the globals
ratchet:owner_globals_check:books/owner-incoming-freshness.lisp — C q0: measure existing books-side owner-global funnels (OWNER-CARRIER-GLOBALS), including the catalog-root pair consolidated into one slot — OWNER-CARRIER-GLOBALS S6 removes the globals
ratchet:owner_globals_check:books/owner-obligation-state.lisp — C q0: measure existing books-side owner-global funnels (OWNER-CARRIER-GLOBALS), including the catalog-root pair consolidated into one slot — OWNER-CARRIER-GLOBALS S6 removes the globals
ratchet:owner_globals_check:books/owner-operation-report.lisp — C q0: measure existing books-side owner-global funnels (OWNER-CARRIER-GLOBALS), including the catalog-root pair consolidated into one slot — OWNER-CARRIER-GLOBALS S6 removes the globals
ratchet:owner_globals_check:books/owner-post-carried.lisp — C q0: measure existing books-side owner-global funnels (OWNER-CARRIER-GLOBALS), including the catalog-root pair consolidated into one slot — OWNER-CARRIER-GLOBALS S6 removes the globals
ratchet:owner_globals_check:books/owner-recovery-retain.lisp — C q0: measure existing books-side owner-global funnels (OWNER-CARRIER-GLOBALS), including the catalog-root pair consolidated into one slot — OWNER-CARRIER-GLOBALS S6 removes the globals
ratchet:owner_globals_check:books/owner-report-capture.lisp — C q0: measure existing books-side owner-global funnels (OWNER-CARRIER-GLOBALS), including the catalog-root pair consolidated into one slot — OWNER-CARRIER-GLOBALS S6 removes the globals
ratchet:owner_globals_check:books/owner-report-reservation.lisp — C q0: measure existing books-side owner-global funnels (OWNER-CARRIER-GLOBALS), including the catalog-root pair consolidated into one slot — OWNER-CARRIER-GLOBALS S6 removes the globals
ratchet:owner_globals_check:books/owner-retain-state.lisp — C q0: measure existing books-side owner-global funnels (OWNER-CARRIER-GLOBALS), including the catalog-root pair consolidated into one slot — OWNER-CARRIER-GLOBALS S6 removes the globals
ratchet:owner_globals_check:books/owner-retain-transitions.lisp — C q0: measure existing books-side owner-global funnels (OWNER-CARRIER-GLOBALS), including the catalog-root pair consolidated into one slot — OWNER-CARRIER-GLOBALS S6 removes the globals
ratchet:owner_globals_check:books/owner-state-accessors.lisp — C q0: measure existing books-side owner-global funnels (OWNER-CARRIER-GLOBALS), including the catalog-root pair consolidated into one slot — OWNER-CARRIER-GLOBALS S6 removes the globals
ratchet:owner_globals_check:books/query-payload-state.lisp — C q0: measure existing books-side owner-global funnels (OWNER-CARRIER-GLOBALS), including the catalog-root pair consolidated into one slot — OWNER-CARRIER-GLOBALS S6 removes the globals
ratchet:owner_globals_check:books/runtime-operation-installed-source.lisp — C q0: measure existing books-side owner-global funnels (OWNER-CARRIER-GLOBALS), including the catalog-root pair consolidated into one slot — OWNER-CARRIER-GLOBALS S6 removes the globals
ratchet:owner_globals_check:books/runtime-operation-source.lisp — C q0: measure existing books-side owner-global funnels (OWNER-CARRIER-GLOBALS), including the catalog-root pair consolidated into one slot — OWNER-CARRIER-GLOBALS S6 removes the globals
ratchet:owner_globals_check:books/substrate-completed-source.lisp — C q0: measure existing books-side owner-global funnels (OWNER-CARRIER-GLOBALS), including the catalog-root pair consolidated into one slot — OWNER-CARRIER-GLOBALS S6 removes the globals
ratchet:owner_globals_check:books/owner-publication-state.lisp — C q0: measure the single funnel replacing ten publication globals under OWNER-CARRIER-GLOBALS — OWNER-CARRIER-GLOBALS S6 moves the slot out of ACL2 globals

ratchet:owner_globals_check:host/admission-preparation-host.lisp — OWNER-CARRIER-GLOBALS: measure quoted wrapper globals in live include-book closure; no new state — carrier3 C8 scanner repair; retire with carried families/S6
ratchet:owner_globals_check:host/admission-semantic-census-host.lisp — OWNER-CARRIER-GLOBALS: measure quoted wrapper globals in live include-book closure; no new state — carrier3 C8 scanner repair; retire with carried families/S6
ratchet:owner_globals_check:host/admission-semantic-node-host.lisp — OWNER-CARRIER-GLOBALS: measure quoted wrapper globals in live include-book closure; no new state — carrier3 C8 scanner repair; retire with carried families/S6
ratchet:owner_globals_check:host/index-connection-repin-prepare-host.lisp — OWNER-CARRIER-GLOBALS: measure quoted wrapper globals in live include-book closure; no new state — carrier3 C8 scanner repair; retire with carried families/S6
ratchet:owner_globals_check:host/index-reader-request-host.lisp — OWNER-CARRIER-GLOBALS: measure quoted wrapper globals in live include-book closure; no new state — carrier3 C8 scanner repair; retire with carried families/S6
ratchet:owner_globals_check:host/owner-exposure-host.lisp — OWNER-CARRIER-GLOBALS: measure quoted wrapper globals in live include-book closure; no new state — carrier3 C8 scanner repair; retire with carried families/S6
ratchet:owner_globals_check:host/payload-view-host.lisp — OWNER-CARRIER-GLOBALS: measure quoted wrapper globals in live include-book closure; no new state — carrier3 C8 scanner repair; retire with carried families/S6
ratchet:owner_globals_check:host/receiver-repin-source-host.lisp — OWNER-CARRIER-GLOBALS: measure quoted wrapper globals in live include-book closure; no new state — carrier3 C8 scanner repair; retire with carried families/S6
ratchet:owner_globals_check:host/receiver-source-gate-host.lisp — OWNER-CARRIER-GLOBALS: measure quoted wrapper globals in live include-book closure; no new state — carrier3 C8 scanner repair; retire with carried families/S6
ratchet:owner_globals_check:host/recovery-payload-view-state.lisp — OWNER-CARRIER-GLOBALS: measure quoted wrapper globals in live include-book closure; no new state — carrier3 C8 scanner repair; retire with carried families/S6

ratchet:owner_globals_check:books/owner-admission-state.lisp — OWNER-CARRIER-GLOBALS: count carried admission funnel until S6; reclaim-live moved from host, no additional state — carrier3 C8 admission migration

ratchet:owner_globals_check:books/owner-authority-state.lisp — OWNER-CARRIER-GLOBALS: measure carried authority funnel using former canonical key; three observations moved together, no additional state — carrier3 C8 authority migration
