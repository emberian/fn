# LANEDUMP arena-forget (Opus 5.5), wound down 2026-10-03

Worktree /Users/ember/dev/fn/build/lanes/arena-forget, branch lane/arena-forget, head a42d5764e (pushed;
handed to runner a8c1198f67920c411 under the all-to-dev directive). Merges origin/lane/reclaim-retention
37456df07; NOT merged with current origin/dev. Design and decisions:
build/coordinator/decisions/arena-forget-2026-10-03.md (sections 8-9, c05/c08/c10 DECISION block).
No REPL sessions left running.

## Ledger
- X02 (deferred reclaim leaks sealed tombstones): state=ready sha a42d5764e. books/owner-reclaim-seal.lisp
  (predict off the mutex, seal in the swap quantum after fn-orcs-seal-word; KEYSTONE
  fn-orcs-seal-is-the-intern, hypothesis (not (fn-orcs-has-bad rows))) + driver in host/native/owner.lisp.
  At a42d5764e the book REPL-ADMITS in full on hbox (19 forms; the two farm failures run-...9213 and
  run-...d510 were the keystone's missing :bad hypothesis, then fn-orcs-predict's guard over member-equal;
  both fixed). NOT yet certified; teeth tests/acl2/owner-reclaim-seal-tests.lisp sent to the REPL, result
  not seen (session stopped).
- X03 (refused POST prepare after seal): in-progress. books/catalog-may-seal.lisp + fn-owner-cat-may-seal
  (pure, per STAGE-5B) + gate in fnn-owner-attempt + labelled selector FN_NATIVE_TEST_CAT_SEAL_REFUSE;
  uncertified; overlaps SWEEP-OPS S002 in fnn-owner-attempt (was to land after it).
- X04 (the forget): in-progress, NOT WIRED into the host (verified: no host reference). Built: fn-arena-forget
  (generic + extent attachment, :forgotten entry), keystones fn-arena-forget-payload, fn-arx-forget-file-count,
  fn-arf-apply-released-payload, fn-arf-changed-handles-are-unnamed, fn-scol-okp-of-forget
  (books/arena-forget-columns.lisp, never admitted), PRF-1235 planned. Certified in run-...b22f
  (1050/1051; the one red index-backing-request-adoption is the known dev timeout root).

## NEXT (exact order)
1. Rebase on origin/dev after the runner's merge. Certify owner-reclaim-seal + its tests + catalog-may-seal +
   arena-forget-columns (`farm.py submit hbox <those> --affected-by books/owner-reclaim-seal`).
2. Build images; natives: test_native_over_pins (3 deferrals with unchanged arena=, and :moved),
   test_native_post_seal_gate, test_native_reclaim_in_flight (needs SWEEP-OPS S038's host half),
   page_io, owner, recovery, crash_model; opt-in test_native_reclaim_seal_cost with
   FN_NATIVE_RECLAIM_SEAL_SCALE=500,2000,8000 for the seal-us curve (coordinator wants this in X02's READY).
3. X04, per DECISION c08 section h in order: (a) per-handle NAME COUNT over declared roots in the rebuild walk
   (def-holder's PRF-1240 keystone takes `(fn-arf-disjointp (fn-arf-changed-handles old new) NAMED)`; prove
   that from count = 0 and cite it); (b) fail-stop named forgotten-payload fault at the raw read boundary
   (fn-arx-forgotten-p); (c) lifecycle-status refusal on every reseat path (commit place, fn-xrt-reseat-one,
   direct reseats; the zero-length refusal was withdrawn); (e) :forgotten cut placement and crash
   composition; (f) release scheduled by root count + leases; c10: rebind the BP workflow node at the swap,
   cover/idle-exclude Astra's 14 globals. Host wiring waits for RECLAIM-RETENTION's holder fix.
   Then Astra's eight-phase native.
