# sweep-ops-cfg (S033) lanedump, 2026-10-03

Branch lane/sweep-ops-cfg, head ab3834272 (pushed; base origin/dev 355a5c843). Handed to runner a8c1198f67920c411 as WIP. Ledger S033 = ready (note lists gaps).

## Done
- books/config-owner-live-authorize-carried.lisp: fn-olau-next-name, fn-olau-authorize-carried; KEYSTONE
  fn-olau-authorize-carried-is-the-observed-authorization (REPL-admitted on hbox).
- tests/acl2/config-owner-live-authorize-carried-tests.lisp: positive (accepted, occupied), removal per hypothesis
  (forged invariant, wrong OCCUPIED), mutations (stale generation, no lock); REPL-admitted.
- host/owner-host.lisp: fn-owner-cfg-next-name, fn-owner-cfg-native-admin-authorize-carried (:logic; guard
  verification NOT yet checked by any load/image); old fn-owner-cfg-native-admin-authorize removed.
- host/native/admin.lisp: one lstat replaces the config history read under the mutex; heap history observation
  off the mutex in fnn-owner-limit-serialized (re-taken inside only if the carried profile moved).
- host/interfaces.lisp, tools/depth_baseline.json, PRF-298 row updated.
- tests/test_native_live_reconfiguration.py LiveReconfigurationCostTests (500 generations vs fresh; occupied refusal).

## In flight (check, then act)
- hbox native s033-before: `tools/hbox_native.sh status s033-before` (image set 45e05c7fd = dev host bytes;
  rev c9c7b3af1 = dev + the test; local commit only). Gives the BEFORE control hold numbers.
- remote_check (regen worlds + interface_emit --write + fast checks): log hbox:/tank/fn/scratch/sweep-ops-cfg-check.log;
  local scratch s033-rc.log; `tools/remote_check.sh attach hbox` from the worktree fetches the regenerated files.
- proof_repl `olc` start with --certify-missing (hbox certcache lacked 46 dep certs at these bytes).

## NEXT
1. Commit the regenerated books/image-world*.lisp, tools/extract/world*.lisp, planning/interfaces.json,
   tools/extract/roots.sh, planning/interfaces-gaps.md (from the remote_check fetch) if the runner has not.
2. Certify the new book's closure on hbox (tools/farm.py submit hbox --affected-by books/config-owner-live-authorize-carried).
3. AFTER native: tools/hbox_native.sh --box hbox --label s033-after --images production --mem 32G --allow-skips <sha>
   tests.test_native_live_reconfiguration.LiveReconfigurationCostTests (plus the module's existing classes);
   compare control held-us/holds with s033-before.
4. Open: carry the config-only fold in owner state to make the authorization O(1).
- olc REPL --certify-missing finished: proof-repl olc: LOADED books/config-owner-live-authorize-carried: 11 forms
