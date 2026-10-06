# cold-start-2 (GLM seat, 2026-10-06) — the three-item close-out

Worktree /Users/ember/dev/fn/build/lanes/cold-start-2. Seat branch for the edits:
`lane/cold-start-2-close` (off origin/dev 93c692e38). The historical branch
`lane/cold-start-2` @79f0a997a is FULLY MERGED into dev (rollup rehearsal be6c3670b,
with lane/scenarios-2 6d6de4b50 and lane/peer-default in the same series) — the seat
brief's "not on dev since 10-05" premise was stale; nothing was re-derived.

## Decision (recorded per the brief's step 2)
Complete-and-land: the branch's green-after work is not owed by this seat because the
code AND its verification already landed through other seats. What was actually owed:
the repair-ledger dispositions, which nobody had written. Done here, registry-only
(planning/repair/items/*.json + STATUS.md regen; no code, no books, no workq claims —
repair.py's ALWAYS_ALLOWED set covers exactly these paths).

## The three items, with the evidence they close on
1. SCEN-INSTALLED-HEAP-NOT-HELD -> landed/LOCAL. Fix = 8aa5a7268..79f0a997a
   (fn-prstartup-launch-floor in books/page-read-startup.lisp; host/native/heap.lisp
   passes PROFILE+OBSERVED). Merged by the rehearsal; D27-safe: the floor derives from
   the image FILE bound (fn-prstartup-image-bound) parameterized by profile/observed,
   NOT a new fixed cap — no D27 escalation was needed. Red-before: smoke-6107ceb56
   (23 refused starts, 5/15). Green-after: prlane2 installed_start OK on the
   PRODUCTION image (pool-refusal lane run, tree containing 79f0a997a) + set 3a9806784
   (bq10050400-0135) peer_catchup OK at decided-launch heaps.
2. FILL-PEER-COLD-STARTUP-INVALID-CAPTURE -> landed/DISSOLVES-IN (the heap item's
   predecessor, closed WITH it as the brief allowed). The word :invalid-default-pool-capture
   still exists (page-read-startup.lisp:106) but its trigger is gone: the figure is
   FILE-bound + read-reserved. Named natives: peer_catchup OK 5/5 (bq10050400-0135),
   peering 23/24 with full_store PASSING (sole error =
   test_transit_hygiene_refused_offer_memory_and_relay_checks, a different seam),
   peer_pull trickling OK (prlane3).
3. POOL-DIRECT-READ-REFUSAL-FAULTS -> landed/LOCAL. Landed by 234b07446
   (feed-pace carrying pool-refusal@671e54932; allow_forbidden grant integrator-3 10-05).
   w-window.md §B's three next steps are each covered on dev: (1) the :DISCOVERY holder
   is the release's per-frame lease held ACROSS the fnn-call while fn-arx-commit-place
   reads the old extent — NESTED same-thread read, not concurrency; (2) exhaustion is a
   named refusal the publication survives (:defer-publication/:defer-frame via
   fn-orln-read-refusal-outcome; 'fnn-extent-read-refused under the section envelope);
   (3) startup refuses by name (:default-pool-read-headroom-unavailable, reserve =
   WORKERS x segment extent). Red->green: bq10050324-0132 (ecf10066f) -> bq10050400-0135
   (3a9806784). Residual known-red on that set, NOT this item's: operator_walk 9/10
   (SCEN-WALK-INSTALL-NO-OPENSSL, owner w-serve) and peering transit-hygiene (1 error).

## What this seat requests of the integrator (no natives run here, per brief)
Add to the next dev image batch's verdict set: the installed smoke tier
(tests/scenarios/tiers.tsv smoke modules), tests.test_native_installed_start,
tests.test_native_install (the upgrade-beside/rollback walk e2e case),
tests.test_native_hybrid_author, and peer_catchup/peering/peer_pull — the re-verdict
of all three closed rows on a dev-published set. Expected green except the two
separately-owned residuals above.

## State at commit
- lane/cold-start-2-close: 3 item JSONs + STATUS.md regen + this lanedump, one commit.
- No other files touched; shared checkout untouched; no stash used.
- Successor: nothing owed in this seat. If the image batch reds any requested module
  with a cold-start refusal word, reopen against the new evidence, do not re-derive.
