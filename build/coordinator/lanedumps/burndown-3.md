# burndown-3 (Sonnet) lanedump, branch lane/burndown-3

## Fixed (committed, pushed; verify exit 0 unless noted)
- CL08, CL09: SCN-063 cites tests/test_native_payload_lifecycle_raw.sh (witness_check green).
- BM08, CL20: 12 stale spec citations repaired (cold-line paragraph rewritten for persistent workers; PRF-1170/1171 prose says not in tree; fn-ocfg-read-step; fn-proto-served-tablep; 2 reasoned exemptions); stale list empty, test holds it.
- CL10: harness_check acl2-arity green (two Python fixtures renamed to synthetic names).
- CL12: payload_kind_check 0 findings (14 fn-payload-kind declarations, tables only). Not yet run through repair.py verify; commit 1491fc709 (claimed, budget 60).
## In flight
- CL11: raw-guarded teeth now `:unchecked "reason"`; REPL load on hbox LOADED 30 forms. store-config-generation and bp-native-app-replay-bridge REPL loads were started, results not harvested (sessions b3-<book>; stop with proof_repl --host hbox stop).
## Not done
- CL04 (check_scaffold: many findings: unreciprocal PRF-1143, stale ledger, SCN logs missing; plus ~8000 lines of export-hygiene WARN), CL21 (keystone_emit, belongs to GENERATORS), CL24 (premise_audit: 382 NEW premises, baseline needs regen decision), CL25 (hot_path_check: 13 NEW, 2 STALE; `--refresh-stale` + owner packets), X19 (productive-transfer.lisp:30 raw `<=` on fn-clock-monotonic mirrors peer-feed.lisp:858 fn-feed-selection; clock_unit_check also flags feed-live-carried.lisp:29; no clock-unit function covers monotonic yet, so it is a baseline/design call, not routing).
